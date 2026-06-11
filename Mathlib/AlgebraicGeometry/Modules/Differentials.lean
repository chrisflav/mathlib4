/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou, Christian Merten
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Differentials.Sheaf
public import Mathlib.AlgebraicGeometry.Modules.Sheaf

/-!
# The sheaf of relative differentials of a morphism of schemes

In this file, given a morphism of schemes `f : X ⟶ S`, we construct the sheaf
of relative differentials `Ω[f] : X.Modules` together with its universal
derivation `f.derivation`, and we establish the universal property: morphisms
`Ω[f] ⟶ M` of sheaves of modules over `X` naturally identify to `M`-valued
derivations relative to `f` (see `Scheme.Hom.differentialsHomEquiv`).

The construction does not use locality in any way: it makes sense for any
morphism of sheafed spaces in commutative rings, see
`AlgebraicGeometry.SheafedSpace.differentials`. (In particular, for a morphism
of locally ringed spaces `f`, one may apply this to the underlying morphism
of sheafed spaces.)

## TODO

- Show that `Ω[f]` is quasi-coherent, and identify `Ω[Spec.map φ]` with the
  sheaf of modules attached to the module of Kähler differentials of `φ`.
- Obtain the exact sequence `f*Ω[g] ⟶ Ω[g ∘ f] ⟶ Ω[f] ⟶ 0`.

-/

@[expose] public section

-- As in `Mathlib/Algebra/Category/ModuleCat/Differentials/Presheaf.lean`,
-- the proofs in this file rely on defeq unfoldings that require
-- the backward-compatibility flags below.
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory TopologicalSpace Opposite

namespace AlgebraicGeometry

namespace SheafedSpace

variable {X Y : SheafedSpace CommRingCat.{u}} (f : X ⟶ Y)

/-- The sheaf of relative differentials of a morphism of sheafed spaces in
commutative rings: it is the sheaf of modules over `X` which represents
derivations relative to `f`. -/
noncomputable def differentials :
    SheafOfModules.{u} ((sheafCompose (Opens.grothendieckTopology (X : TopCat))
      (forget₂ CommRingCat RingCat.{u})).obj X.sheaf) :=
  SheafOfModules.relativeDifferentials
    (J := Opens.grothendieckTopology (Y : TopCat))
    (K := Opens.grothendieckTopology (X : TopCat))
    (S := Y.sheaf) (R := X.sheaf) (F := Opens.map f.hom.base) (sheafMap f)

/-- The universal derivation with values in the sheaf of relative
differentials of a morphism of sheafed spaces in commutative rings. -/
noncomputable def derivation :
    SheafOfModules.Derivation (differentials f) (F := Opens.map f.hom.base) (sheafMap f) :=
  SheafOfModules.universalDerivation (F := Opens.map f.hom.base) (sheafMap f)

/-- The derivation `SheafedSpace.derivation f` is universal. -/
noncomputable def derivationUniversal : (derivation f).Universal :=
  SheafOfModules.universalUniversalDerivation (F := Opens.map f.hom.base) (sheafMap f)

end SheafedSpace

namespace Scheme

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- The morphism of sheaves of commutative rings corresponding to
a morphism of schemes. (See `Scheme.Hom.toRingCatSheafHom` for the
`RingCat`-valued version.) -/
def Hom.toCommRingCatSheafHom (f : X.Hom S) :
    S.sheaf ⟶ ((Opens.map f.base).sheafPushforwardContinuous
      CommRingCat.{u} _ _).obj X.sheaf where
  hom := f.c

lemma Hom.toRingCatSheafHom_hom (f : X.Hom S) :
    f.toRingCatSheafHom.hom =
      Functor.whiskerRight f.toCommRingCatSheafHom.hom (forget₂ CommRingCat RingCat) :=
  rfl

/-- The sheaf of relative differentials `Ω[f]` of a morphism of schemes
`f : X ⟶ S`, as a sheaf of modules over `X`. -/
noncomputable def Hom.differentials (f : X.Hom S) : X.Modules :=
  SheafOfModules.relativeDifferentials
    (J := Opens.grothendieckTopology S) (K := Opens.grothendieckTopology X)
    (S := S.sheaf) (R := X.sheaf) (F := Opens.map f.base) f.toCommRingCatSheafHom

/-- `Ω[f]` is the sheaf of relative differentials of a morphism of
schemes `f : X ⟶ S`. -/
scoped notation3 "Ω[" f "]" => Scheme.Hom.differentials f

/-- The universal derivation of a morphism of schemes `f : X ⟶ S`, with
values in the sheaf of relative differentials `Ω[f]`. Given a section
`a : Γ(X, U)`, the corresponding section of `Γ(Ω[f], U)` is `f.derivation.d a`. -/
noncomputable def Hom.derivation (f : X.Hom S) :
    SheafOfModules.Derivation Ω[f] (F := Opens.map f.base) f.toCommRingCatSheafHom :=
  SheafOfModules.universalDerivation (F := Opens.map f.base) f.toCommRingCatSheafHom

/-- The derivation `f.derivation` of a morphism of schemes `f : X ⟶ S` is
universal. -/
noncomputable def Hom.derivationUniversal (f : X.Hom S) : f.derivation.Universal :=
  SheafOfModules.universalUniversalDerivation (F := Opens.map f.base) f.toCommRingCatSheafHom

namespace Hom

@[simp]
lemma derivation_d_one (U : X.Opens) :
    f.derivation.d (X := op U) 1 = 0 :=
  f.derivation.d_one _

/-- The Leibniz rule for the universal derivation of a morphism of schemes. -/
lemma derivation_d_mul {U : X.Opens} (a b : Γ(X, U)) :
    f.derivation.d (a * b) = a • f.derivation.d b + b • f.derivation.d a :=
  f.derivation.d_mul a b

/-- The universal derivation of a morphism of schemes is compatible with the
restriction maps. -/
lemma derivation_d_map {U V : X.Opens} (i : U ⟶ V) (a : Γ(X, V)) :
    f.derivation.d (X.presheaf.map i.op a) =
      (Ω[f]).presheaf.map i.op (f.derivation.d a) :=
  f.derivation.d_map i.op a

/-- The universal derivation of a morphism of schemes `f : X ⟶ S` vanishes
on sections pulled back from `S`. -/
@[simp]
lemma derivation_d_app {V : S.Opens} (a : Γ(S, V)) :
    f.derivation.d (f.app V a) = 0 :=
  f.derivation.d_app (X := op V) a

/-- The universal derivation of a morphism of schemes `f : X ⟶ S` vanishes
on sections pulled back from `S` (`appLE` version). -/
@[simp]
lemma derivation_d_appLE {V : S.Opens} {U : X.Opens} (e : U ≤ f ⁻¹ᵁ V)
    (a : Γ(S, V)) :
    f.derivation.d (f.appLE V U e a) = 0 := by
  rw [Scheme.Hom.appLE, CommRingCat.comp_apply, derivation_d_map, derivation_d_app,
    map_zero]

/-- Two morphisms of sheaves of modules `Ω[f] ⟶ M` coincide if they agree on
the images of the universal derivation. -/
@[ext]
lemma differentials_hom_ext {M : X.Modules} {α β : Ω[f] ⟶ M}
    (h : ∀ (U : X.Opens) (a : Γ(X, U)),
      α.app U (f.derivation.d a) = β.app U (f.derivation.d a)) :
    α = β :=
  f.derivationUniversal.postcomp_injective (by
    ext U a
    exact h U.unop a)

/-- The universal property of the sheaf of relative differentials of
a morphism of schemes `f : X ⟶ S`: morphisms of sheaves of modules
`Ω[f] ⟶ M` identify to `M`-valued derivations relative to `f`. -/
noncomputable def differentialsHomEquiv (f : X.Hom S) (M : X.Modules) :
    (Ω[f] ⟶ M) ≃
      SheafOfModules.Derivation M (F := Opens.map f.base) f.toCommRingCatSheafHom where
  toFun α := f.derivation.postcomp α
  invFun d := f.derivationUniversal.desc d
  left_inv _ := f.derivationUniversal.postcomp_injective
    (f.derivationUniversal.fac _)
  right_inv d := f.derivationUniversal.fac d

@[simp]
lemma differentialsHomEquiv_symm_d {M : X.Modules}
    (d : SheafOfModules.Derivation M (F := Opens.map f.base) f.toCommRingCatSheafHom)
    {U : X.Opens} (a : Γ(X, U)) :
    ((f.differentialsHomEquiv M).symm d).app U (f.derivation.d a) = d.d a :=
  PresheafOfModules.Derivation.congr_d (f.derivationUniversal.fac d) a

end Hom

end Scheme

end AlgebraicGeometry
