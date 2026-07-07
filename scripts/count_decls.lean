/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.Tactic.CountDecls.Core

/-!
# The `count_decls` executable

`lake exe count_decls [--graph-only] <namespace>...` is the command-line counterpart of the
`#count_decls` command (see `Mathlib.Tactic.CountDecls`). It loads the whole `Mathlib` environment
and, for each namespace passed as an argument, prints a data-vs-proof breakdown, a per-file
breakdown and a Graphviz dependency graph of the files involved.

* Pass `_root_` to inspect every declaration in the environment.
* Pass `--graph-only` to print just the Graphviz `digraph` (suitable for piping into `dot`), e.g.
  `lake exe count_decls --graph-only Finset | dot -Tpng -o finset.png`.
-/

open Lean Mathlib.CountDecls

/-- Entry point for `lake exe count_decls`. -/
public unsafe def main (args : List String) : IO Unit := do
  let graphOnly := args.contains "--graph-only"
  let namespaces := args.filter (· != "--graph-only")
  if namespaces.isEmpty then
    IO.eprintln "usage: lake exe count_decls [--graph-only] <namespace>...\n\
      Pass `_root_` to inspect every declaration in the environment."
    IO.Process.exit 1
  initSearchPath (← findSysroot)
  withImportModules #[`Mathlib] {} (trustLevel := 1024) fun env => do
    let ctx : Core.Context := { fileName := "count_decls", fileMap := default }
    let state : Core.State := { env }
    for ns in namespaces do
      let (out, _, _) ← (render ns.toName graphOnly).toIO ctx state
      IO.println out
