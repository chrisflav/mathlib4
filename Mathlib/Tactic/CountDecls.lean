/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public meta import Mathlib.Tactic.CountDecls.Core

/-!
# The `#count_decls` command

`#count_decls Foo.Bar` prints how many declarations in the namespace `Foo.Bar` carry data
(`def`s, `structure`/`inductive`/`class` declarations and data-carrying `instance`s) versus how
many are proofs (`theorem`s / `lemma`s and `Prop`-valued instances), the ratio of data-carrying
declarations to the total, a per-file breakdown of the counts (files with no counted declarations
are omitted), and a Graphviz `digraph` of the import dependencies between those files, with each
node annotated by its data/proof/ratio numbers and colour-coded by ratio (blue for proof-heavy
through to red for data-heavy).

The split is by whether a declaration's type is a `Prop`, not by the keyword used to introduce it;
see `Mathlib.Tactic.CountDecls.Core` for the details of the classification.

Use `#count_decls _root_` to inspect every declaration in the environment. Several namespaces may be
passed at once, as in `#count_decls Finset Filter`, and each is reported separately.

The same functionality is available on the command line via `lake exe count_decls`; see
`scripts/count_decls.lean`.
-/

public meta section

namespace Mathlib.CountDecls

open Lean Elab Command

/--
`#count_decls Foo.Bar` prints a data-vs-proof breakdown of the declarations living in the namespace
`Foo.Bar`, together with the ratio of data-carrying declarations to the total, a per-file breakdown
(files with no counted declarations are omitted), and a Graphviz dependency graph of those files.
Several namespaces may be passed at once, as in `#count_decls Finset Filter`; each is reported
separately. Use `#count_decls _root_` to inspect every declaration in the environment.

Declarations are split by whether their type is a `Prop`: `def`s, `structure`/`inductive`/`class`
declarations and data-carrying `instance`s count as data, while `theorem`s / `lemma`s and
`Prop`-valued instances count as proofs. Auto-generated and internal declarations are skipped.
-/
elab "#count_decls " nss:ident+ : command => do
  liftTermElabM do
    for ns in nss do
      logInfo (← render ns.getId)

end Mathlib.CountDecls

end
