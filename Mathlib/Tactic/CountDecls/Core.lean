/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Lean.Elab.Command
public import Lean.AutoDecl
public import Mathlib.Init

/-!
# Core logic for counting data vs. proof declarations

This module contains the shared, non-meta logic behind the `#count_decls` command (see
`Mathlib.Tactic.CountDecls`) and the `lake exe count_decls` executable (see
`scripts/count_decls.lean`). It classifies the declarations in a namespace as data or proofs,
tallies them overall and per file, and renders both a textual report and a Graphviz dependency
graph.

Declarations are split by whether their type is a `Prop`, not by the keyword used to introduce them:
a `def foo : a = b := …` counts as a proof and a `Prop`-valued `instance` counts as a proof, while a
data-carrying `instance` counts as data. Auto-generated declarations (constructors, recursors,
`.noConfusion`, projections, matchers and other internal details) are skipped, so the counts reflect
what a human actually wrote.
-/

public section

namespace Mathlib.CountDecls

open Lean Meta

/-- A declaration is "boring" (auto-generated / internal) and should not be counted on its own.

This covers internal-detail names, auxiliary recursors, `.noConfusion`, projections and matchers, as
well as the declarations that Lean generates for every inductive type / structure via
`Lean.isAutoDeclOrPrivate_Internal` (e.g. `.ctorIdx`, `.noConfusionType` and the equation lemmas
`.injEq` / `.inj` / `.sizeOf_spec`). -/
def isBoring (declName : Name) : MetaM Bool := do
  let env ← getEnv
  return declName.isInternalDetail
    || (← isAutoDeclOrPrivate_Internal declName)
    || isAuxRecursor env declName
    || isNoConfusion env declName
    || (← isProjectionFn declName)
    || (← isMatcher declName)

/-- The tally accumulated while scanning a namespace. -/
structure Tally where
  /-- Data `def`s (non-instance). -/
  defs : Nat := 0
  /-- `structure`/`inductive`/`class` declarations. -/
  structures : Nat := 0
  /-- Data-carrying `instance`s. -/
  dataInsts : Nat := 0
  /-- `theorem`s / `lemma`s. -/
  thms : Nat := 0
  /-- `Prop`-valued `instance`s. -/
  propInsts : Nat := 0
  deriving Inhabited

/-- Add two tallies field-wise. -/
def Tally.add (a b : Tally) : Tally where
  defs := a.defs + b.defs
  structures := a.structures + b.structures
  dataInsts := a.dataInsts + b.dataInsts
  thms := a.thms + b.thms
  propInsts := a.propInsts + b.propInsts

/-- The number of data-carrying declarations in the tally. -/
def Tally.data (t : Tally) : Nat := t.defs + t.structures + t.dataInsts

/-- The number of proof declarations in the tally. -/
def Tally.proof (t : Tally) : Nat := t.thms + t.propInsts

/-- The total number of counted declarations in the tally. -/
def Tally.total (t : Tally) : Nat := t.data + t.proof

/-- Format `num / den` as a percentage with one decimal place (e.g. `"12.5"`), using integer
arithmetic. Returns `"0.0"` when `den = 0`. -/
def percent (num den : Nat) : String :=
  if den == 0 then "0.0"
  else
    let permille := num * 1000 / den
    s!"{permille / 10}.{permille % 10}"

/-- One-line summary of a tally: `data D / proof P  (R%)`, where `R` is the data-to-total ratio. -/
def Tally.summary (t : Tally) : String :=
  s!"data {t.data} / proof {t.proof}  ({percent t.data t.total}%)"

/-- A Graphviz HSV colour string (`"h s v"`) encoding the data-to-total ratio `num / den`: the hue
runs from blue (`0.660`, all proofs) through green to red (`0.000`, all data). The fixed saturation
and value keep the fill light enough for black label text. -/
def hsvColor (num den : Nat) : String :=
  let ratio := if den == 0 then 0 else num * 1000 / den  -- ratio in thousandths, `0..1000`
  let hue := (1000 - ratio) * 660 / 1000                 -- `0.660` (blue) .. `0.000` (red)
  let hueStr := if hue < 10 then s!"00{hue}" else if hue < 100 then s!"0{hue}" else s!"{hue}"
  s!"0.{hueStr} 0.550 0.950"

/-- Render the tally for a single namespace as a printable block. `perFile` is the per-file
breakdown (already filtered to files with a nonzero count), sorted for stable output. -/
def Tally.report (t : Tally) (nsName : Name) (all : Bool) (perFile : Array (Name × Tally)) :
    String :=
  let header := String.intercalate "\n" [
    (if all then "all declarations" else s!"namespace `{nsName}`"),
    s!"── data ({t.data}) ──────────────",
    s!"    definitions : {t.defs}",
    s!"    structures  : {t.structures}",
    s!"    instances   : {t.dataInsts}",
    s!"── proofs ({t.proof}) ──────────────",
    s!"    theorems    : {t.thms}",
    s!"    instances   : {t.propInsts}",
    s!"data : proof  =  {t.data} : {t.proof}",
    s!"data / total  =  {t.data} / {t.total}  ({percent t.data t.total}%)",
    s!"── per file ({perFile.size}) ──────────────"]
  let fileLines := perFile.map fun (mod, ft) => s!"    {mod} : {ft.summary}"
  String.intercalate "\n" (header :: fileLines.toList)

/-- Classify a single `ConstantInfo`, updating the tally. Returns the tally unchanged for
auto-generated / skipped declarations. -/
def classify (t : Tally) (ci : ConstantInfo) : MetaM Tally := do
  if (← isBoring ci.name) then return t
  match ci with
  | .ctorInfo .. | .recInfo .. => return t          -- auto-generated
  | .inductInfo .. => return { t with structures := t.structures + 1 }
  | _ =>
    let isPrp ← isProp ci.type
    let isInst ← Meta.isInstance ci.name
    match isPrp, isInst with
    | true, true => return { t with propInsts := t.propInsts + 1 }
    | true, false => return { t with thms := t.thms + 1 }
    | false, true => return { t with dataInsts := t.dataInsts + 1 }
    | false, false => return { t with defs := t.defs + 1 }

/-- Build a Graphviz `digraph` of the import dependencies between the files in `perFile` (which is
assumed to already be filtered to files with a nonzero count). Only edges between two files that are
both present in `perFile` are drawn; each node is labelled with its data/proof/ratio numbers. -/
def dependencyGraph (env : Environment) (perFile : Array (Name × Tally)) : String := Id.run do
  let present : Std.HashSet Name := perFile.foldl (fun s (mod, _) => s.insert mod) {}
  let nodes := perFile.map fun (mod, ft) =>
    s!"  \"{mod}\" [style=filled, fillcolor=\"{hsvColor ft.data ft.total}\", \
       label=\"{mod}\\ndata {ft.data} / proof {ft.proof}\\n{percent ft.data ft.total}%\"];"
  let mut edges : Array String := #[]
  for (mod, _) in perFile do
    if let some idx := env.getModuleIdx? mod then
      for imp in env.header.moduleData[idx.toNat]!.imports do
        if imp.module != mod && present.contains imp.module then
          edges := edges.push s!"  \"{mod}\" -> \"{imp.module}\";"
  String.intercalate "\n" (["digraph count_decls {"] ++ nodes.toList ++ edges.toList ++ ["}"])

/-- Scan the current environment and accumulate the overall `Tally` for the namespace `nsName`
(`_root_` meaning "all declarations") together with the per-file breakdown, sorted by module name
and restricted to files with a nonzero count. -/
def tallyNamespace (nsName : Name) : MetaM (Tally × Array (Name × Tally)) := do
  let env ← getEnv
  -- `_root_` is the sentinel for "all declarations"; otherwise filter by prefix.
  let all := nsName == `_root_
  let mut t : Tally := {}
  let mut perFile : Std.HashMap Name Tally := {}
  for (name, ci) in env.constants do
    if all || nsName.isPrefixOf name then
      -- Classify against an empty tally to obtain this declaration's contribution, then add it to
      -- both the overall total and the file it lives in (skipping non-counted declarations).
      let delta ← classify {} ci
      t := t.add delta
      if delta.total > 0 then
        let mod := (← findModuleOf? name).getD (← getMainModule)
        perFile := perFile.insert mod ((perFile.getD mod {}).add delta)
  return (t, perFile.toArray.qsort fun a b => a.1.lt b.1)

/-- The printable output for a single namespace: the textual report followed by the Graphviz
dependency graph, or — when `graphOnly` is set — just the graph (empty when the namespace has no
counted declarations). -/
def render (nsName : Name) (graphOnly : Bool := false) : MetaM String := do
  let (t, files) ← tallyNamespace nsName
  let env ← getEnv
  let graph := if files.isEmpty then "" else dependencyGraph env files
  if graphOnly then
    return graph
  let rep := t.report nsName (nsName == `_root_) files
  return if graph.isEmpty then rep else s!"{rep}\n\n{graph}"

end Mathlib.CountDecls

end
