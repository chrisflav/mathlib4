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
# Torsors in a cartesian monoidal category

A module object `X` over a monoid object `M` is a torsor for the topology
`J` if `M` acts simply transitively on `X` and `J`-locally `X` is trivial.
-/

@[expose] public section

universe v u

namespace CategoryTheory.ModObj

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
variable {M : C} [MonObj M] {X Y : C} [ModObj M Y] [ModObj M X]

open Limits

open CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj

variable (J : GrothendieckTopology C)

/-- A module object `X` is homogeneous over `M`, if the action is simply transitive, i.e.,
the morphism `(m, x) ↦ (m • x, x)` is an isomorphism. -/
abbrev IsHomogeneous (M : C) [MonObj M] (X : C) [ModObj M X] : Prop :=
  IsIso (leftSMul M X)

/-- A homogeneous module object is trivial over `U : C`, if there exists a morphism `U ⟶ X ⊗ U`. -/
class IsTrivialOver (M : C) [MonObj M] (X : C) [ModObj M X] (U : C) [IsHomogeneous M X] where
  nonempty_hom : Nonempty (U ⟶ X ⊗ U)

@[simp]
lemma isTrivialOver_one_iff [IsHomogeneous M X] :
    IsTrivialOver M X (𝟙_ C) ↔ Nonempty (𝟙_ C ⟶ X) :=
  ⟨fun h ↦ ⟨h.nonempty_hom.some ≫ fst _ _⟩, fun h ↦ ⟨⟨h.some ≫ (ρ_ _).inv⟩⟩⟩

variable (M X) in
/-- A module object `X` over a monoid object `M` is a torsor for the Grothendieck topology `J`,
if `M` acts simply transitively on `X` and there exists a `J`-covering that trivializes `X`. -/
class IsTorsor (J : GrothendieckTopology C) (M : C) [MonObj M] (X : C) [ModObj M X] where
  isHomogeneous : IsHomogeneous M X
  exists_coversTop : ∃ (I : Type max u v) (U : I → C),
    J.CoversTop U ∧ ∀ (i : I), IsTrivialOver M X (U i)

namespace IsTorsor

attribute [local instance] ModObj.regular

instance : IsTorsor J M M where
  isHomogeneous := by
    simp
    sorry
  exists_coversTop := by
    refine ⟨PUnit, fun _ ↦ 𝟙_ _, ?_, ?_⟩
    · rw [J.coversTop_iff_of_isTerminal _ isTerminalTensorUnit,
        Sieve.pullback_ofObjects_eq_top (i := ⟨⟩) _ (𝟙 _)]
      simp
    · simp only [isTrivialOver_one_iff, forall_const]
      exact ⟨η⟩

end IsTorsor

@[reassoc (attr := simp)]
lemma inv_leftSMul_snd [IsIso (leftSMul M X)] :
    inv (leftSMul M X) ≫ snd M X = snd _ _ := by
  simp

variable (M) in
noncomputable
def isoOfSection' {U : C} (s : U ⟶ X) [IsIso (leftSMul M X)] :
    M ⊗ U ≅ X ⊗ U where
  hom := lift (𝟙 _ ⊗ₘ s) (snd _ _) ≫ γ[M, X] ▷ U
  inv := lift (𝟙 _ ⊗ₘ s) (snd _ _) ≫ inv (leftSMul M X) ▷ U ≫ fst _ _ ▷ U
  hom_inv_id := by
    have : (lift (𝟙 M ⊗ₘ s) (snd M U) ≫ γ[M, X] ▷ U) ≫ lift (𝟙 X ⊗ₘ s) (snd X U) =
        lift (𝟙 M ⊗ₘ s) (snd _ _) ≫ leftSMul M X ▷ U := by
      ext <;> simp
    rw [Category.assoc, reassoc_of% this]
    simp
  inv_hom_id := by
    have h1 :
        lift (𝟙 X ⊗ₘ s) (snd X U) ≫ inv (leftSMul M X) ▷ U ≫ fst M X ▷ U ≫
          lift (𝟙 M ⊗ₘ s) (snd M U) =
          lift (𝟙 X ⊗ₘ s) (snd X U) ≫ inv (leftSMul M X) ▷ U := by
      ext <;> simp
    have h2 : inv (leftSMul M X) ≫ γ[M, X] = fst X X := by simp
    simp only [Category.assoc, reassoc_of% h1]
    simp [h2]

@[reassoc (attr := simp)]
lemma isoOfSection'_hom_fst {U : C} (s : U ⟶ X) [IsIso (leftSMul M X)] :
    (isoOfSection' M s).hom ≫ fst _ _ = _ ◁ s ≫ γ[M, X] := by
  simp [isoOfSection']

@[reassoc (attr := simp)]
lemma isoOfSection'_hom_snd {U : C} (s : U ⟶ X) [IsIso (leftSMul M X)] :
    (isoOfSection' M s).hom ≫ snd _ _ = snd _ _ := by
  simp [isoOfSection']

@[reassoc (attr := simp)]
lemma isoOfSection'_inv_snd {U : C} (s : U ⟶ X) [IsIso (leftSMul M X)] :
    (isoOfSection' M s).inv ≫ snd _ _ = snd _ _ := by
  simp [isoOfSection']

noncomputable
def isoOfSection (s : 𝟙_ C ⟶ X) [IsIso (leftSMul M X)] : M ≅ X where
  hom := lift (𝟙 _) (toUnit _ ≫ s) ≫ γ[M, X]
  inv := lift (𝟙 _) (toUnit _ ≫ s) ≫ inv (leftSMul M X) ≫ fst _ _
  hom_inv_id := by
    have : lift (𝟙 M) (toUnit M ≫ s) ≫ γ[M, X] ≫ lift (𝟙 X) (toUnit X ≫ s) =
        lift (𝟙 _) (toUnit M ≫ s) ≫ leftSMul M X := by
      ext <;> simp
    simp [reassoc_of% this]
  inv_hom_id := by
    have h1 :
      lift (𝟙 X) (toUnit X ≫ s) ≫ inv (leftSMul M X) ≫ fst M X ≫
        lift (𝟙 M) (toUnit M ≫ s) =
        lift (𝟙 X) (toUnit X ≫ s) ≫ inv (leftSMul M X) := by
      ext <;> simp
    have h2 : inv (leftSMul M X) ≫ γ[M, X] = fst X X := by simp
    simp [reassoc_of% h1, h2]

lemma isSplitEpi_toUnit_iff [IsIso (leftSMul M X)] :
    True :=
  sorry

end CategoryTheory.ModObj
