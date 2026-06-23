/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Monoidal.Cartesian.Mod
public import Mathlib.CategoryTheory.Sites.CoversTop.Basic
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over

/-!

-/

@[expose] public section

open CategoryTheory MonoidalCategory CartesianMonoidalCategory
open MonObj

universe v u

namespace CategoryTheory

namespace ModObj

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]

variable {M : C} [MonObj M] {X Y : C} [ModObj M Y] [ModObj M X]

instance :
    letI : ModObj M M := regular M
    IsIso (leftSMul M M) :=
  sorry

lemma adsfasdf (f : X ⟶ Y) [IsModHom M f] [IsIso (leftSMul M X)] [IsIso (leftSMul M Y)] :
    IsIso f :=
  sorry

attribute [local instance] ModObj.regular

variable (M X) in
def IsTrivial : Prop :=
  ∃ (e : M ⟶ X), IsIso e ∧ IsModHom M e

open Limits

variable [HasBinaryProducts C] [HasPullbacks C]

attribute [local instance] Over.cartesianMonoidalCategory Over.braidedCategory

noncomputable
instance (U : C) : (Over.star U).Monoidal := .ofChosenFiniteProducts _

noncomputable
instance (U : C) : MonObj ((Over.star U).obj M) :=
  ((Over.star U).mapMon.obj (Mon.mk M)).mon

noncomputable
instance (U : C) : ModObj ((Over.star U).obj M) ((Over.star U).obj X) :=
  ((Over.star U).mapMod.obj (Mon.mk M)).mon

variable (J : GrothendieckTopology C)
variable (M X) in
class IsTorsor where
  isIso_leftSMul : IsIso (leftSMul M X)
  exists_coversTop : ∃ (ι : Type u) (U : ι → C) (h : J.CoversTop U),
    ∀ (i : ι), IsTrivial M X

def adfsasdf (s : SplitEpi (toUnit X)) : M ≅ X where
  hom := (ρ_ _).inv ≫ M ◁ s.section_ ≫ γ[M, X]
  inv := sorry
  hom_inv_id := sorry
  inv_hom_id := sorry

lemma isSplitEpi_toUnit_iff : True :=
  sorry

end ModObj

end CategoryTheory
