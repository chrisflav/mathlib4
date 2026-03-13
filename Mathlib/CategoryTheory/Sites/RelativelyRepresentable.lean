/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Sites.Hypercover.ZeroFamily

/-!

-/

universe w v₁ u₁ v₂ u₂

@[expose] public section

namespace CategoryTheory

open Limits

section

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D] (F : C ⥤ D)

namespace Presieve

def relativelyRepresentable {X : D} (R : Presieve X) : Prop :=
  ∀ ⦃a : C⦄ ⦃Y : D⦄ (f : Y ⟶ X) (_ : R f)
    (g : F.obj a ⟶ X), ∃ (b : C) (snd : b ⟶ a)
    (fst : F.obj b ⟶ Y), IsPullback fst (F.map snd) f g

end Presieve

@[simps]
def PreZeroHypercover.whiskerRight {X S : C} (f : X ⟶ S)
    (E : PreZeroHypercover.{w} X) :
    PreZeroHypercover.{w} S where
  __ := E
  f i := E.f i ≫ f

set_option backward.isDefEq.respectTransparency false in
noncomputable
def PreZeroHypercover.pullback₁Fst {X S : C}
    (g : X ⟶ S) (F : PreZeroHypercover.{w} S)
    [∀ (i : F.I₀), Limits.HasPullback g (F.f i)] :
    (F.pullback₁ g).whiskerRight g ⟶ F where
  s₀ := id
  h₀ _ := pullback.snd _ _
  w₀ _ := pullback.condition.symm

def PreZeroHypercover.IsPullback {X S : C}
    (F : PreZeroHypercover.{w} S)
    (g : X ⟶ S)
    (G : PreZeroHypercover.{w} X)
    (a : G.whiskerRight g ⟶ F) :
    Prop :=
  ∀ i : G.I₀, CategoryTheory.IsPullback (a.h₀ i) (G.f i) (F.f (a.s₀ i)) g

lemma PreZeroHypercover.isPullback_pullback₁ {X S : C}
    (g : X ⟶ S) (F : PreZeroHypercover.{w} S)
    [∀ (i : F.I₀), Limits.HasPullback g (F.f i)] :
    IsPullback F g (F.pullback₁ g) (F.pullback₁Fst g) :=
  sorry

namespace Precoverage

variable (J : Precoverage C)

def preRelativelyRepresentable : Precoverage D where
  coverings _ R := R.relativelyRepresentable F

structure Presieve.RelativelyRepresentable {X : D} (R : Presieve X) : Prop where
  ex : R.relativelyRepresentable F
  mem : ∀ (A : C) (g : F.obj A ⟶ X) (T : Presieve A), True

/-
fun X Y f ↦ F.relativelyRepresentable f ∧
  ∀ ⦃a b : C⦄ (g : F.obj a ⟶ Y) (fst : F.obj b ⟶ X) (snd : b ⟶ a)
    (_ : IsPullback fst (F.map snd) f g), P snd
-/
def foobar : PreZeroHypercoverFamily D where
  property X E := ∀ ⦃a : C⦄ ⦃b : E.I₀ → C⦄ (g : F.obj a ⟶ X)
    (fst : ∀ i, F.obj (b i) ⟶ E.X i) (snd : ∀ i, b i ⟶ a),
    (∀ i, IsPullback (fst i) (F.map (snd i)) (E.f i) g) →
    Presieve.ofArrows _ snd ∈ J a
  iff_shrink {X} E := by
    refine ⟨?_, ?_⟩
    · intro H a b g fst snd h
      sorry
    · intro H a b g fst snd h
      sorry

end Precoverage

end

variable {C : Type*} [Category* C] {D : Type*} [Category* D] (J : Precoverage C)

-- def Presieve.relativelyRepresentable

namespace Precoverage

def relativelyRepresentable (J : Precoverage C) (F : C ⥤ D) : Precoverage D where
  coverings X := { R | True }

end Precoverage

end CategoryTheory
