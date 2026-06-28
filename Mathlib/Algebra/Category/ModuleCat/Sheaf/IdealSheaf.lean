/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Annihilator

/-!
# Ideal sheaves over a sheaf of rings

We define an ideal sheaf over a sheaf of rings `R` on a site as a sub-sheaf of modules of the
unit `unit R` (i.e. `R` viewed as a module over itself), given concretely by a restriction-stable
family of ideals whose associated presheaf of modules is a sheaf.

This is the general notion behind the scheme-theoretic `AlgebraicGeometry.Scheme.IdealSheafData`,
which is currently a placeholder for "actual subsheaves of `𝒪ₓ`": for a scheme `X`, an
`IdealSheaf X.ringCatSheaf` is precisely such a subsheaf of the structure sheaf, and
`IdealSheaf.ideal` reads off the ideal of sections over every open (not only the affine ones).

## Main definitions

* `SheafOfModules.IdealSheaf R`: an ideal sheaf over `R`.
* `SheafOfModules.IdealSheaf.ideal`: the ideal of sections over each object.
* `SheafOfModules.IdealSheaf.toSheafOfModules`/`ι`: the underlying sheaf of modules and its
  inclusion monomorphism into `unit R`.
* `SheafOfModules.annihilatorIdealSheaf M`: the annihilator of `M` as an ideal sheaf.

## Relation to `Scheme.IdealSheafData`

For a scheme `X` (with structure sheaf `R = X.ringCatSheaf`), evaluating `IdealSheaf.ideal` on
affine opens produces a family of ideals of `Γ(X, U)`. Conversely, `Scheme.IdealSheafData`
records such a family on affine opens together with the localization compatibility
`map_ideal_basicOpen`. Translating between the two is a *quasi-coherence* statement: a general
`IdealSheaf` need not be quasi-coherent (its restriction maps need not be localizations), and an
`IdealSheafData` only constrains affine opens. The order isomorphism between quasi-coherent ideal
sheaves and `IdealSheafData` is built in `AlgebraicGeometry/IdealSheaf/Quasicoherent.lean`
(`AlgebraicGeometry.Scheme.IdealSheafData.orderIsoQuasicoherentIdealSheaf`); this file provides the
target notion of "actual subsheaf of `𝒪ₓ`" that such a correspondence requires.

-/

@[expose] public section

universe v v₁ u₁ u

open CategoryTheory

namespace SheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C} (R : Sheaf J RingCat.{u})

/-- An ideal sheaf over a sheaf of rings `R` is a restriction-stable family of ideals of `R`
whose associated presheaf of modules (a sub-presheaf of `unit R`) is a sheaf. It is the
sheaf-of-modules incarnation of a sheaf of ideals. -/
structure IdealSheaf where
  /-- the underlying restriction-stable family of ideals -/
  toSubmodule : (PresheafOfModules.unit R.obj).Submodule
  /-- the associated presheaf of modules is a sheaf -/
  isSheaf : Presheaf.IsSheaf J toSubmodule.toPresheafOfModules.presheaf

namespace IdealSheaf

variable {R}

/-- The ideal of sections of an ideal sheaf over `X`. -/
def ideal (I : IdealSheaf R) (X : Cᵒᵖ) : Ideal (R.obj.obj X) :=
  I.toSubmodule.toSubmodule X

@[ext]
lemma ext {I J : IdealSheaf R} (h : ∀ X, I.ideal X = J.ideal X) : I = J := by
  obtain ⟨I, _⟩ := I
  obtain ⟨J, _⟩ := J
  congr 1
  exact PresheafOfModules.Submodule.ext h

instance : PartialOrder (IdealSheaf R) :=
  PartialOrder.lift ideal (fun _ _ h ↦ ext (congrFun h))

lemma le_def {I J : IdealSheaf R} : I ≤ J ↔ ∀ X, I.ideal X ≤ J.ideal X := Iff.rfl

/-- The underlying sheaf of modules of an ideal sheaf. -/
noncomputable def toSheafOfModules (I : IdealSheaf R) : SheafOfModules.{u} R where
  val := I.toSubmodule.toPresheafOfModules
  isSheaf := I.isSheaf

variable [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]

/-- The inclusion of an ideal sheaf into the unit `unit R`. -/
noncomputable def ι (I : IdealSheaf R) : I.toSheafOfModules ⟶ unit R :=
  ⟨I.toSubmodule.ι⟩

instance (I : IdealSheaf R) : Mono I.ι.val :=
  inferInstanceAs (Mono I.toSubmodule.ι)

end IdealSheaf

variable [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]

/-- The annihilator of a sheaf of modules `M`, packaged as an ideal sheaf over `R`. -/
noncomputable def annihilatorIdealSheaf {R : Sheaf J RingCat.{max v₁ u₁}}
    [J.HasSheafCompose (forget₂ RingCat.{max v₁ u₁} AddCommGrpCat.{max v₁ u₁})]
    (M : SheafOfModules.{v} R) : IdealSheaf R where
  toSubmodule := M.val.annihilatorSubmodule
  isSheaf := M.annihilator.isSheaf

end SheafOfModules
