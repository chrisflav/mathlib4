/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Sites.Whiskering
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Topology.Sheaves.Sheaf

/-!
# Sheafification instances for the site of opens of a topological space

The category of opens `Opens X` of a topological space `X` (with the Grothendieck topology
`Opens.grothendieckTopology X`) is essentially small, so the abstract essentially-small-site
machinery provides sheafification of `AddCommGrpCat`-valued presheaves, both on the site itself
and on every slice. These instances make the sheaf-of-modules finite-type API (which is stated for
a general site under such hypotheses) applicable over a topological space.
-/

@[expose] public section

universe u

open CategoryTheory TopologicalSpace

variable (X : TopCat.{u})

noncomputable instance :
    HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u} :=
  hasSheafifyEssentiallySmallSite _ _

instance :
    (Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u} :=
  .ofEssentiallySmall _

noncomputable instance (U : Opens X) :
    HasSheafify ((Opens.grothendieckTopology X).over U) AddCommGrpCat.{u} :=
  hasSheafifyEssentiallySmallSite _ _

instance (U : Opens X) :
    ((Opens.grothendieckTopology X).over U).WEqualsLocallyBijective AddCommGrpCat.{u} :=
  .ofEssentiallySmall _

set_option synthInstance.maxHeartbeats 100000 in
-- Synthesizing `HasSheafCompose` searches for limit preservation of
-- `forget₂ RingCat AddCommGrpCat` through several `forget₂` layers, needing a larger budget.
instance :
    (Opens.grothendieckTopology X).HasSheafCompose
      (forget₂ RingCat.{u} AddCommGrpCat.{u}) :=
  inferInstance

set_option synthInstance.maxHeartbeats 100000 in
-- See the comment on the base-site instance above.
instance (U : Opens X) :
    ((Opens.grothendieckTopology X).over U).HasSheafCompose
      (forget₂ RingCat.{u} AddCommGrpCat.{u}) :=
  inferInstance
