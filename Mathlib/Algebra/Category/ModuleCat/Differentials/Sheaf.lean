/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Differentials.Presheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous

/-!
# The sheaf of differentials of a continuous functor between commutatively ringed sites

Let `F : C ⥤ D` be a functor which is continuous with respect to Grothendieck
topologies `J` on `C` and `K` on `D`. Let `S` (resp. `R`) be a sheaf of
commutative rings on `(C, J)` (resp. `(D, K)`), and
`φ : S ⟶ (F.sheafPushforwardContinuous CommRingCat J K).obj R` a morphism
of sheaves of rings. In this file, we define the type `M.Derivation φ` of
derivations relative to `φ` with values in a sheaf of `R`-modules `M`, the
corresponding universal property `Derivation.Universal`, and we show that a
universal derivation exists (i.e. there is a "sheaf of relative differentials"
of `φ`) whenever there is one at the level of the underlying presheaves:
the universal derivation is obtained by sheafifying the universal presheaf
derivation (see `PresheafOfModules.Derivation.Universal.sheafify`).

-/

@[expose] public section

-- As in `Mathlib/Algebra/Category/ModuleCat/Differentials/Presheaf.lean`,
-- the proofs in this file rely on defeq unfoldings that require
-- the backward-compatibility flags below.
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe v u v₁ v₂ u₁ u₂

open CategoryTheory

instance : HasForget₂ CommRingCat.{u} AddCommGrpCat.{u} :=
  HasForget₂.trans _ RingCat.{u} _

namespace SheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  {S : Sheaf J CommRingCat.{u}} {R : Sheaf K CommRingCat.{u}}
  {F : C ⥤ D}
  [K.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Functor.IsContinuous F J K]
  (M : SheafOfModules.{u} ((sheafCompose K (forget₂ CommRingCat RingCat)).obj R))
  (φ : S ⟶ (F.sheafPushforwardContinuous CommRingCat.{u} J K).obj R)

/-- Given a morphism of sheaves of commutative rings `φ` (between sheaves over
two sites related by a continuous functor `F`), this is the type of relative
`φ`-derivations of a sheaf of `R`-modules `M`, i.e. of derivations of the
underlying presheaf of modules. -/
def Derivation : Type _ := M.val.Derivation (F := F) φ.hom

namespace Derivation

variable {M φ}

@[ext]
lemma ext {d d' : M.Derivation φ}
    (h : ∀ (X : Dᵒᵖ) (x : R.obj.obj X), d.d x = d'.d x) : d = d' := by
  dsimp only [Derivation]
  ext
  apply h

/-- The postcomposition of a derivation by a morphism of sheaves of modules. -/
def postcomp (d : M.Derivation φ) {N} (f : M ⟶ N) : N.Derivation φ :=
  PresheafOfModules.Derivation.postcomp d f.val

/-- The morphism of sheaves of abelian groups `R ⟶ M` underlying
a derivation of `M`. -/
@[simps hom_app]
def abSheafHom (d : M.Derivation φ)
    [K.HasSheafCompose (forget₂ CommRingCat.{u} AddCommGrpCat.{u})] :
    (sheafCompose K (forget₂ CommRingCat AddCommGrpCat)).obj R ⟶ (toSheaf _).obj M where
  hom :=
    { app := fun _ ↦ AddCommGrpCat.ofHom d.d
      naturality := fun _ _ f ↦ by ext; apply d.d_map }

lemma abSheafHom_injective
    {d d' : M.Derivation φ} [K.HasSheafCompose (forget₂ CommRingCat.{u} AddCommGrpCat.{u})]
    (h : d.abSheafHom = d'.abSheafHom) : d = d' := by
  ext X x
  change (d.abSheafHom.hom.app X).hom x = (d'.abSheafHom.hom.app X).hom x
  rw [h]

end Derivation

instance : AddCommGroup (M.Derivation φ) :=
  inferInstanceAs (AddCommGroup (M.val.Derivation (F := F) φ.hom))

/-- Given a morphism of sheaves of commutative rings `φ`, this is the functor
which sends a sheaf of modules `M` to the abelian group `M.Derivation φ` of
relative `φ`-derivations. -/
def derivationFunctor :
    SheafOfModules.{u} ((sheafCompose K (forget₂ CommRingCat RingCat)).obj R) ⥤ Ab :=
  forget _ ⋙ PresheafOfModules.derivationFunctor.{u} (F := F) φ.hom

lemma derivationFunctor_obj
    (M : SheafOfModules.{u} ((sheafCompose K (forget₂ CommRingCat RingCat)).obj R)) :
    (derivationFunctor φ).obj M = AddCommGrpCat.of (M.Derivation φ) := rfl

variable {M} in
@[simp]
lemma derivationFunctor_map (d : M.Derivation φ) {N} (f : M ⟶ N) :
    ((derivationFunctor φ).map f).hom d = d.postcomp f := rfl

namespace Derivation

variable {M φ} (d : M.Derivation φ)

/-- The universal property that a derivation `d : M.Derivation φ` must
satisfy so that the sheaf of modules `M` can be considered as the sheaf of
(relative) differentials of a morphism of sheaves of commutative rings `φ`. -/
structure Universal where
  /-- A derivation of `M'` descends as a morphism `M ⟶ M'`. -/
  desc {M' : SheafOfModules _} (d' : M'.Derivation φ) : M ⟶ M'
  fac {M' : SheafOfModules _} (d' : M'.Derivation φ) :
    d.postcomp (desc d') = d' := by cat_disch
  postcomp_injective {M' : SheafOfModules _}
    {φ φ' : M ⟶ M'} (h : d.postcomp φ = d.postcomp φ') : φ = φ' := by cat_disch

end Derivation

/-- The property that there exists a universal derivation for
a morphism of sheaves of commutative rings `φ`. -/
class HasDifferentials : Prop where
  exists_universal_derivation : ∃ (M : SheafOfModules _)
    (d : M.Derivation φ), Nonempty d.Universal

variable {M φ} in
lemma Derivation.Universal.hasDifferentials {d : M.Derivation φ} (hd : d.Universal) :
    HasDifferentials φ := ⟨_, _, ⟨hd⟩⟩

section

variable [HasDifferentials φ]

/-- A choice of sheaf of relative differentials of a morphism of sheaves
of commutative rings `φ` such that `HasDifferentials φ` holds. -/
noncomputable def relativeDifferentials :
    SheafOfModules.{u} ((sheafCompose K (forget₂ CommRingCat RingCat)).obj R) :=
  (HasDifferentials.exists_universal_derivation (φ := φ)).choose

/-- The universal derivation with values in `relativeDifferentials φ`. -/
noncomputable def universalDerivation : (relativeDifferentials φ).Derivation φ :=
  (HasDifferentials.exists_universal_derivation (φ := φ)).choose_spec.choose

/-- The derivation `universalDerivation φ` is universal. -/
noncomputable def universalUniversalDerivation : (universalDerivation φ).Universal :=
  (HasDifferentials.exists_universal_derivation (φ := φ)).choose_spec.choose_spec.some

end

section

variable {M φ} (h : (derivationFunctor φ ⋙ CategoryTheory.forget _).CorepresentableBy M)

/-- The derivation attached to a corepresentation of the functor of
relative `φ`-derivations by a sheaf of modules `M`. -/
def ofCorepresentableBy : M.Derivation φ := h.homEquiv (𝟙 _)

lemma ofCorepresentableBy_postcomp {M' : SheafOfModules _} (f : M ⟶ M') :
    (ofCorepresentableBy h).postcomp f = h.homEquiv f := by
  have h' := h.homEquiv_comp f (𝟙 M)
  rw [Category.id_comp] at h'
  exact h'.symm

/-- The derivation `ofCorepresentableBy h` attached to a corepresentation of the
functor of relative `φ`-derivations by a sheaf of modules `M` is universal. -/
def universalOfCorepresentableBy : (ofCorepresentableBy h).Universal where
  desc d := h.homEquiv.symm d
  fac {M'} d := by
    rw [ofCorepresentableBy_postcomp]
    apply Equiv.apply_symm_apply
  postcomp_injective {M' f f'} H :=
    h.homEquiv.injective ((ofCorepresentableBy_postcomp h f).symm.trans
      (H.trans (ofCorepresentableBy_postcomp h f')))

end

end SheafOfModules

namespace PresheafOfModules

namespace Derivation

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  {S : Sheaf J CommRingCat.{u}} {R : Sheaf K CommRingCat.{u}}
  {F : C ⥤ D}
  [K.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Functor.IsContinuous F J K]
  {φ : S ⟶ (F.sheafPushforwardContinuous CommRingCat.{u} J K).obj R}
  {M₀ : PresheafOfModules.{u} (R.obj ⋙ forget₂ _ _)}
  (d₀ : M₀.Derivation (F := F) φ.hom)
  [K.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasWeakSheafify K AddCommGrpCat.{u}]

variable (R) in
/-- The sheafification functor for presheaves of modules over the underlying
presheaf of rings of a sheaf of commutative rings `R`. -/
noncomputable abbrev sheafificationComm :=
  PresheafOfModules.sheafification
    (R₀ := R.obj ⋙ forget₂ _ _)
    (R := (sheafCompose K (forget₂ CommRingCat RingCat)).obj R) (α := 𝟙 _)

variable (R) in
/-- The sheafification adjunction for presheaves of modules over the underlying
presheaf of rings of a sheaf of commutative rings `R`. -/
noncomputable abbrev sheafificationAdjunctionComm :=
  PresheafOfModules.sheafificationAdjunction
    (R₀ := R.obj ⋙ forget₂ _ _)
    (R := (sheafCompose K (forget₂ CommRingCat RingCat)).obj R) (α := 𝟙 _)

/-- The sheaf derivation induced by a presheaf derivation `d₀ : M₀.Derivation φ.hom`
with values in the sheafification of `M₀`. -/
noncomputable def sheafify : ((sheafificationComm R).obj M₀).Derivation φ :=
  d₀.postcomp ((sheafificationAdjunctionComm R).unit.app M₀)

variable {d₀}

/-- If `d₀` is a universal presheaf derivation, then the induced derivation
with values in the sheafification of `M₀` is a universal sheaf derivation. -/
noncomputable def Universal.sheafify (hd₀ : d₀.Universal) : d₀.sheafify.Universal where
  desc d :=
    ((sheafificationAdjunctionComm R).homEquiv _ _).symm (hd₀.desc d)
  fac {M'} d := by
    dsimp [Derivation.sheafify, SheafOfModules.Derivation.postcomp]
    rw [← postcomp_comp]
    erw [Adjunction.unit_naturality_assoc, Adjunction.right_triangle_components]
    rw [Category.comp_id, hd₀.fac d]
  postcomp_injective {M' f f'} h :=
    ((sheafificationAdjunctionComm R).homEquiv _ _).injective (hd₀.postcomp_injective h)

end Derivation

end PresheafOfModules

namespace SheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  {S : Sheaf J CommRingCat.{u}} {R : Sheaf K CommRingCat.{u}}
  {F : C ⥤ D}
  [K.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Functor.IsContinuous F J K]
  (φ : S ⟶ (F.sheafPushforwardContinuous CommRingCat.{u} J K).obj R)
  [K.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasWeakSheafify K AddCommGrpCat.{u}]

instance [PresheafOfModules.HasDifferentials (F := F) φ.hom] :
    SheafOfModules.HasDifferentials φ :=
  (PresheafOfModules.universalUniversalDerivation _).sheafify.hasDifferentials

end SheafOfModules
