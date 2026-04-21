module

public import Mathlib.CategoryTheory.Monoidal.Cartesian.MulAction

public section

namespace CategoryTheory

open MonoidalCategory CartesianMonoidalCategory MonObj

variable {C : Type*} [Category* C] [CartesianMonoidalCategory C]

variable {M : C} [MonObj M] {X : C} [MulActionObj M X]

namespace MulActionObj

variable (M X) in
def transitivity : M ⊗ X ⟶ X ⊗ X :=
  lift MulActionObj.smul (snd _ _)

lemma asdfasdf : IsIso (transitivity M X) ↔
    (∀ (Y : C),
      MulAction.IsPretransitive (Y ⟶ M) (Y ⟶ X) ∧ FaithfulSMul (Y ⟶ M) (Y ⟶ X)) := by
  refine ⟨?_, ?_⟩
  · intro h Y
    refine ⟨?_, ?_⟩
    · constructor
      intro y₁ y₂
      use lift y₁ y₂ ≫ inv (transitivity M X) ≫ fst _ _
      rw [Hom.smul_def]
      sorry
    · sorry
  · sorry

class SimplyTransitive (M : C) [MonObj M] (X : C) [MulActionObj M X] : Prop where
  isIso : IsIso (transitivity M X)

end MulActionObj

end CategoryTheory
