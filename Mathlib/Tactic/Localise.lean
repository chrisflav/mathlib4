import Mathlib

macro "localise" c:Aesop.tactic_clause* : tactic =>
  `(tactic|aesop $c* (rule_sets := [$(Lean.mkIdent `Localise):ident]))

macro "localise?" c:Aesop.tactic_clause* : tactic =>
`(tactic|aesop? $c* (rule_sets := [$(Lean.mkIdent `Localise):ident]))

declare_aesop_rule_sets [Localise]
