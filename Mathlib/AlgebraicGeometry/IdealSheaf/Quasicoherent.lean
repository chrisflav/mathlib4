/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.IdealSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.Algebra.Category.ModuleCat.Topology.SheafifyInstances
public import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
public import Mathlib.AlgebraicGeometry.Modules.Presheaf
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.CategoryTheory.Sites.Spaces
public import Mathlib.RingTheory.LocalProperties.Basic

/-!
# Ideal sheaves from `IdealSheafData`

For a scheme `X`, the structure `AlgebraicGeometry.Scheme.IdealSheafData X` records the data of an
ideal sheaf via its ideals on affine opens. In this file we build the correspondence between
`IdealSheafData X` and quasi-coherent ideal sheaves of the structure sheaf. To a datum `D` we
associate an honest subsheaf of modules `D.toIdealSheaf` of `𝒪ₓ`, given by the family of ideals

`r ∈ (D.toIdealSheaf).ideal U ↔ ∀ (V : X.affineOpens) (h : V.1 ≤ U), r|_V ∈ D.ideal V`,

and conversely, to a quasi-coherent ideal sheaf `I` we associate the datum `I.toIdealSheafData` of
its sections on affine opens.

## Main definitions

* `SheafOfModules.IdealSheaf.IsQuasicoherent`: a thin wrapper saying that the underlying sheaf of
  modules of an ideal sheaf is quasi-coherent.
* `AlgebraicGeometry.Scheme.IdealSheafData.toIdealSheaf`: the ideal subsheaf of `𝒪ₓ` determined by
  an `IdealSheafData`.
* `SheafOfModules.IdealSheaf.toIdealSheafData`: the `IdealSheafData` of sections of a quasi-coherent
  ideal sheaf.

## Main results

* `AlgebraicGeometry.Scheme.IdealSheafData.toIdealSheaf_ideal`: on affine opens, `toIdealSheaf`
  recovers the given ideals.
* `AlgebraicGeometry.Scheme.IdealSheafData.toIdealSheaf_mono`: `toIdealSheaf` is monotone.
* `AlgebraicGeometry.Scheme.IdealSheafData.toIdealSheaf_isQuasicoherent`: `toIdealSheaf` is
  quasi-coherent.
* `SheafOfModules.IdealSheaf.over_isQuasicoherent_iff`: the affine-local criterion (the *engine* of
  the correspondence) characterising quasi-coherence over an affine open by the basic-open
  localization condition on sections.

The resulting order isomorphism is left for future work.
-/

@[expose] public section

universe v₁ u₁ u

open CategoryTheory Opposite TopologicalSpace

namespace SheafOfModules.IdealSheaf

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{u}}
  [∀ X, (J.over X).HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
  [∀ X, HasWeakSheafify (J.over X) AddCommGrpCat.{u}]
  [∀ X, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- An ideal sheaf is quasi-coherent if its underlying sheaf of modules is. -/
def IsQuasicoherent (I : IdealSheaf R) : Prop :=
  I.toSheafOfModules.IsQuasicoherent

end SheafOfModules.IdealSheaf

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X : Scheme.{u}}

/-- The underlying type-valued presheaf of an `AddCommGrpCat`-valued sheaf is a sheaf of types.
A local copy of the (private) lemma of the same name in `Sheaf/Annihilator.lean`. -/
private lemma presieveIsSheaf_comp_forget {C : Type u₁} [Category.{v₁} C]
    {J : GrothendieckTopology C} {A : Cᵒᵖ ⥤ AddCommGrpCat.{u}} (h : Presheaf.IsSheaf J A) :
    Presieve.IsSheaf J (A ⋙ CategoryTheory.forget AddCommGrpCat.{u}) :=
  Presieve.isSheaf_iso J (Functor.isoWhiskerLeft A AddCommGrpCat.coyonedaObjIsoForget)
    (h (AddCommGrpCat.of (ULift.{u} ℤ)))

/-- An element of `Γ(X, W)` (with `W` affine) lies in `D.ideal W` as soon as, locally on a cover of
`W` by basic opens, its restriction lies in the corresponding ideal of the datum. -/
private lemma mem_ideal_of_basicOpen_cover (D : X.IdealSheafData) {W : X.affineOpens}
    {s : Γ(X, W.1)}
    (H : ∀ x : W.1, ∃ g : Γ(X, W.1), (x : X) ∈ X.basicOpen g ∧
      (X.ringCatSheaf.obj.map (homOfLE (X.basicOpen_le g)).op).hom s ∈
        D.ideal (X.affineBasicOpen g)) :
    s ∈ D.ideal W := by
  choose g hxg hg using H
  have hspan : Ideal.span (Set.range g) = ⊤ := by
    rw [← W.2.self_le_iSup_basicOpen_iff]
    intro x hx
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨g ⟨x, hx⟩, ⟨x, hx⟩, rfl⟩, hxg ⟨x, hx⟩⟩
  have inst := W.2.isLocalization_basicOpen
  refine Submodule.mem_of_isLocalized_span (Set.range g) hspan
    (fun i ↦ Γ(X, X.basicOpen i.1)) (fun i ↦ Algebra.linearMap Γ(X, W.1) Γ(X, X.basicOpen i.1)) ?_
  rintro ⟨_, j, rfl⟩
  rw [Ideal.localized₀_eq_restrictScalars_map, Submodule.restrictScalars_mem,
    show algebraMap Γ(X, W.1) Γ(X, X.basicOpen (g j)) =
      (X.presheaf.map (homOfLE (X.basicOpen_le (g j))).op).hom from rfl,
    D.map_ideal_basicOpen W (g j)]
  exact hg j

variable (D : X.IdealSheafData)

set_option backward.isDefEq.respectTransparency false in
/-- The submodule system on `unit 𝒪ₓ` cut out by an `IdealSheafData`: over an open `V`, the sections
`r` whose restriction to every affine open `W ≤ V` lies in `D.ideal W`. -/
noncomputable def toSubmoduleSystem :
    (PresheafOfModules.unit X.ringCatSheaf.obj).SubmoduleSystem :=
  let R : Sheaf _ RingCat.{u} := X.ringCatSheaf
  { toSubmodule := fun V ↦
      { carrier := { r | ∀ (W : X.affineOpens) (i : V ⟶ op W.1),
          (R.obj.map i).hom r ∈ D.ideal W }
        add_mem' := fun ha hb W i ↦ by rw [map_add]; exact add_mem (ha W i) (hb W i)
        zero_mem' := fun W i ↦ by rw [map_zero]; exact zero_mem _
        smul_mem' := fun c r hr W i ↦ by
          rw [smul_eq_mul, map_mul]; exact Ideal.mul_mem_left _ _ (hr W i) }
    map_mem := @fun U V f m hm W i ↦ by
      have comp : (R.obj.map i).hom ((R.obj.map f).hom m) = (R.obj.map (f ≫ i)).hom m := by
        rw [R.obj.map_comp, RingCat.hom_comp, RingHom.comp_apply]
      rw [show (PresheafOfModules.unit R.obj).map f m = (R.obj.map f).hom m from rfl, comp]
      exact hm W (f ≫ i) }

set_option backward.isDefEq.respectTransparency false in
/-- The ideal subsheaf of `𝒪ₓ` determined by an `IdealSheafData`. -/
noncomputable def toIdealSheaf : SheafOfModules.IdealSheaf X.ringCatSheaf where
  toSubmoduleSystem := D.toSubmoduleSystem
  isSheaf := by
    let R : Sheaf _ RingCat.{u} := X.ringCatSheaf
    have comp : ∀ {A B E : (Opens X)ᵒᵖ} (p : A ⟶ B) (q : B ⟶ E) (t : R.obj.obj A),
        (R.obj.map (p ≫ q)).hom t = (R.obj.map q).hom ((R.obj.map p).hom t) :=
      fun p q t ↦ by rw [R.obj.map_comp, RingCat.hom_comp, RingHom.comp_apply]
    let F : (Opens X)ᵒᵖ ⥤ Type u :=
      (PresheafOfModules.unit R.obj).presheaf ⋙ CategoryTheory.forget AddCommGrpCat.{u}
    have hF : Presieve.IsSheaf (Opens.grothendieckTopology X) F :=
      presieveIsSheaf_comp_forget (SheafOfModules.unit R).isSheaf
    let G : Subfunctor F :=
      { obj := fun V ↦ { r : R.obj.obj V | ∀ (W : X.affineOpens) (i : V ⟶ op W.1),
          (R.obj.map i).hom r ∈ D.ideal W }
        map := @fun U V f m hm ↦ D.toSubmoduleSystem.map_mem f hm }
    have hG : Presieve.IsSheaf (Opens.grothendieckTopology X) G.toFunctor := by
      rw [G.isSheaf_iff hF]
      intro U s hs W i
      apply D.mem_ideal_of_basicOpen_cover
      intro x
      have hW : W.1 ≤ U.unop := leOfHom i.unop
      rw [Opens.mem_grothendieckTopology] at hs
      obtain ⟨V, f, hVf, hxV⟩ := hs x.1 (hW x.2)
      obtain ⟨g, hgV, hxg⟩ := W.2.exists_basicOpen_le (V := V) ⟨x.1, hxV⟩ x.2
      refine ⟨g, hxg, ?_⟩
      have hmem := hVf (X.affineBasicOpen g) (homOfLE hgV).op
      -- `hmem : (R.obj.map (homOfLE hgV).op).hom (F.map f.op s) ∈ D.ideal (X.affineBasicOpen g)`
      rw [show F.map f.op s = (R.obj.map f.op).hom s from rfl, ← comp] at hmem
      change (R.obj.map (homOfLE (X.basicOpen_le g)).op).hom ((R.obj.map i).hom s) ∈ _
      rw [← comp, Subsingleton.elim (i ≫ (homOfLE (X.basicOpen_le g)).op)
        (f.op ≫ (homOfLE hgV).op)]
      exact hmem
    rw [Presheaf.isSheaf_iff_isSheaf_forget (J := Opens.grothendieckTopology X)
        (s := CategoryTheory.forget AddCommGrpCat.{u}), isSheaf_iff_isSheaf_of_type]
    exact Presieve.isSheaf_iso (Opens.grothendieckTopology X)
      (NatIso.ofComponents (fun _ ↦ Iso.refl _) (by intros; rfl)) hG

set_option backward.isDefEq.respectTransparency false in
lemma toIdealSheaf_ideal (V : X.affineOpens) :
    (D.toIdealSheaf).ideal (op V.1) = D.ideal V := by
  ext r
  constructor
  · intro hr
    have h1 := hr V (𝟙 (op V.1))
    rwa [CategoryTheory.Functor.map_id, RingCat.hom_id, RingHom.id_apply] at h1
  · intro hr W i
    have h : W.1 ≤ V.1 := leOfHom i.unop
    rw [show i = (homOfLE h).op from Subsingleton.elim _ _, ← D.map_ideal h]
    exact Ideal.mem_map_of_mem _ hr

lemma toIdealSheaf_mono : Monotone (toIdealSheaf (X := X)) := by
  intro D D' hD U r hr W i
  exact hD W (hr W i)

end AlgebraicGeometry.Scheme.IdealSheafData

namespace SheafOfModules.IdealSheaf

open AlgebraicGeometry

variable {X : Scheme.{u}}

section Engine

open AlgebraicGeometry.Scheme.Modules CategoryTheory.Limits Submodule IsLocalizedModule

/-- The corestriction `J ⟶ Ideal.map (algebraMap A B) J` of the algebra map exhibits the extended
ideal as a localization away from `f`, whenever `B` is the localization of `A` away from `f`. -/
theorem isLocalizedModule_idealMap {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] (f : A)
    [IsLocalization.Away f B] (J : Ideal A) :
    IsLocalizedModule (.powers f) (Algebra.idealMap B J) := by
  rw [Algebra.idealMap_eq_ofEq_comp_toLocalized₀ B (.powers f) J]
  exact IsLocalizedModule.of_linearEquiv _ _ _

/-- **Algebraic bridge.** For a localization `B` of `A` away from `f`, the corestriction `c` of the
algebra map to ideals `J ⟶ J'` exhibits `J'` as a localization of `J` away from `f` if and only if
`J'` is the extension of scalars `J.map (algebraMap A B)`. -/
theorem isLocalizedModule_corestrict_iff {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (f : A) [IsLocalization.Away f B] (J : Ideal A) (J' : Ideal B)
    (c : J →ₗ[A] J'.restrictScalars A) (hc : ∀ x : J, ((c x : B)) = algebraMap A B (x : A)) :
    IsLocalizedModule (.powers f) c ↔ Ideal.map (algebraMap A B) J = J' := by
  constructor
  · intro hloc
    apply le_antisymm
    · rw [Ideal.map_le_iff_le_comap]
      intro x hx
      rw [Ideal.mem_comap, ← hc ⟨x, hx⟩]
      exact (c ⟨x, hx⟩).2
    · intro y hy
      obtain ⟨⟨m, s⟩, hms⟩ := IsLocalizedModule.surj (.powers f) c ⟨y, hy⟩
      have hval : algebraMap A B (s : A) * y = algebraMap A B (m : A) := by
        have h2 := congr(Subtype.val $hms)
        simp only [SetLike.val_smul, Submonoid.smul_def] at h2
        rw [hc m] at h2
        simpa [Algebra.smul_def] using h2
      have hunit : IsUnit (algebraMap A B (s : A)) := by
        obtain ⟨n, hn⟩ := s.2
        rw [← hn, map_pow]
        exact (IsLocalization.Away.algebraMap_isUnit f).pow n
      obtain ⟨u, hu⟩ := hunit
      have : y = (↑u⁻¹ : B) * algebraMap A B (m : A) := by
        rw [← hval, ← hu, ← mul_assoc, Units.inv_mul, one_mul]
      rw [this]
      exact Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ m.2)
  · intro hJ
    subst hJ
    have hce : c = Algebra.idealMap B J := by ext x; exact hc x
    rw [hce]
    exact isLocalizedModule_idealMap f J

/-- Quasi-coherence is preserved by the equivalence `Scheme.Modules.overEquiv` (which identifies
sheaves of `𝒪_X`-modules over the slice site over `U` with sheaves of `𝒪_U`-modules). -/
private lemma isQuasicoherent_overEquiv_functor {U : X.Opens}
    (K : SheafOfModules (X.ringCatSheaf.over U)) [K.IsQuasicoherent] :
    ((overEquiv U).functor.obj K).IsQuasicoherent := by
  change ((Opens.sheafOfModulesEquivOver U X.ringCatSheaf).functor.obj K).IsQuasicoherent
  unfold Opens.sheafOfModulesEquivOver
  apply +allowSynthFailures SheafOfModules.isQuasicoherent_pushforward_of_isLeftAdjoint
  · exact Opens.sheafOfModulesEquivOverUnit U X.ringCatSheaf
  · intro Y
    set G := (Opens.overEquivalence U).symm.functor
    have hG : G.IsContinuous (Opens.grothendieckTopology ↥U)
        ((Opens.grothendieckTopology ↥X).over U) :=
      inferInstanceAs <| U.overEquivalence.inverse.IsContinuous _ _
    have : RepresentablyFlat (Over.post (X := Y) G) := RepresentablyFlat.of_isRightAdjoint _
    exact Functor.isContinuous_of_coverPreserving
      (compatiblePreservingOfFlat _ (Over.post (X := Y) G))
      ((CoverPreserving.of_isContinuous (F := G) _ _).overPost Y)

private lemma isQuasicoherent_overEquiv_inverse {U : X.Opens} (N : (U : Scheme.{u}).Modules)
    [N.IsQuasicoherent] :
    ((overEquiv U).inverse.obj N).IsQuasicoherent := by
  change ((Opens.sheafOfModulesEquivOver U X.ringCatSheaf).inverse.obj N).IsQuasicoherent
  unfold Opens.sheafOfModulesEquivOver
  apply +allowSynthFailures SheafOfModules.isQuasicoherent_pushforward_of_isLeftAdjoint
  · exact Opens.sheafOfModulesEquivOverInverseUnit U X.ringCatSheaf
  · intro Y
    set G := (Opens.overEquivalence U).symm.inverse
    have hG : G.IsContinuous ((Opens.grothendieckTopology ↥X).over U)
        (Opens.grothendieckTopology ↥U) :=
      inferInstanceAs <| U.overEquivalence.functor.IsContinuous _ _
    have : RepresentablyFlat (Over.post (X := Y) G) := RepresentablyFlat.of_isRightAdjoint _
    exact Functor.isContinuous_of_coverPreserving
      (compatiblePreservingOfFlat _ (Over.post (X := Y) G))
      ((CoverPreserving.of_isContinuous (F := G) _ _).overPost Y)
  · exact ‹N.IsQuasicoherent›

/-- Over an open `U`, the slice-site restriction `M.over U` is quasi-coherent iff its transport
`M.restrict U.ι` to `𝒪_U`-modules is. -/
private lemma over_isQuasicoherent_iff_restrict (M : SheafOfModules X.ringCatSheaf) (U : X.Opens) :
    (M.over U).IsQuasicoherent ↔ ((restrictFunctor U.ι).obj M).IsQuasicoherent := by
  constructor
  · intro h
    haveI := isQuasicoherent_overEquiv_functor (M.over U)
    exact (SheafOfModules.isQuasicoherent (U : Scheme.{u}).ringCatSheaf).prop_of_iso
      ((overFunctorEquiv U).app M) ‹_›
  · intro h
    haveI : ((overEquiv U).functor.obj (M.over U)).IsQuasicoherent :=
      (SheafOfModules.isQuasicoherent (U : Scheme.{u}).ringCatSheaf).prop_of_iso
        ((overFunctorEquiv U).app M).symm h
    haveI := isQuasicoherent_overEquiv_inverse ((overEquiv U).functor.obj (M.over U))
    exact (SheafOfModules.isQuasicoherent (X.ringCatSheaf.over U)).prop_of_iso
      ((overEquiv U).unitIso.app (M.over U)).symm ‹_›

/-- Restriction along an isomorphism of schemes neither creates nor destroys quasi-coherence. -/
private lemma restrictFunctor_isQuasicoherent_iff_of_isIso {Y Z : Scheme.{u}} (g : Y ⟶ Z)
    [IsIso g] (K : Z.Modules) :
    ((restrictFunctor g).obj K).IsQuasicoherent ↔ K.IsQuasicoherent := by
  constructor
  · intro h
    haveI : ((restrictFunctor g).obj K).IsQuasicoherent := h
    haveI := Scheme.Modules.isQuasicoherent_restrictFunctor (inv g) ((restrictFunctor g).obj K)
    have iso : (restrictFunctor g ⋙ restrictFunctor (inv g)).obj K ≅ K :=
      ((restrictFunctorComp (inv g) g).app K).symm ≪≫
        (restrictFunctorCongr (show inv g ≫ g = 𝟙 Z by simp)).app K ≪≫
        (restrictFunctorId).app K
    exact (SheafOfModules.isQuasicoherent Z.ringCatSheaf).prop_of_iso iso ‹_›
  · intro h
    haveI : K.IsQuasicoherent := h
    infer_instance

/-- For an affine open `V`, transporting `M` to `Spec Γ(X, V)` along `IsAffineOpen.fromSpec`
preserves and reflects quasi-coherence. -/
private lemma restrict_isQuasicoherent_iff_fromSpec (V : X.affineOpens)
    (M : SheafOfModules X.ringCatSheaf) :
    ((restrictFunctor V.1.ι).obj M).IsQuasicoherent ↔
      ((restrictFunctor V.2.fromSpec).obj M).IsQuasicoherent := by
  have iso : (restrictFunctor V.2.fromSpec).obj M ≅
      (restrictFunctor V.2.isoSpec.inv).obj ((restrictFunctor V.1.ι).obj M) :=
    (restrictFunctorCongr (show V.2.fromSpec = V.2.isoSpec.inv ≫ V.1.ι from
      (V.2.isoSpec_inv_ι).symm)).app M ≪≫
      (restrictFunctorComp V.2.isoSpec.inv V.1.ι).app M
  constructor
  · intro hN
    haveI : ((restrictFunctor V.2.isoSpec.inv).obj
        ((restrictFunctor V.1.ι).obj M)).IsQuasicoherent :=
      (restrictFunctor_isQuasicoherent_iff_of_isIso V.2.isoSpec.inv _).mpr hN
    exact (SheafOfModules.isQuasicoherent (Spec Γ(X, V.1)).ringCatSheaf).prop_of_iso iso.symm ‹_›
  · intro hP
    haveI : ((restrictFunctor V.2.isoSpec.inv).obj
        ((restrictFunctor V.1.ι).obj M)).IsQuasicoherent :=
      (SheafOfModules.isQuasicoherent (Spec Γ(X, V.1)).ringCatSheaf).prop_of_iso iso hP
    exact (restrictFunctor_isQuasicoherent_iff_of_isIso V.2.isoSpec.inv _).mp ‹_›

/-- Quasi-coherence of `M.over V` for an affine open `V` is equivalent to the `tilde`-localizing
condition on `Spec Γ(X, V)`: the basic-open restriction maps of the transported sheaf are
localizations. This is the categorical core of `over_isQuasicoherent_iff`. -/
lemma over_isQuasicoherent_iff_isLocalizing (V : X.affineOpens)
    (M : SheafOfModules X.ringCatSheaf) :
    (M.over V.1).IsQuasicoherent ↔
      IsLocalizing (modulesSpecToSheaf.obj ((restrictFunctor V.2.fromSpec).obj M)) := by
  rw [over_isQuasicoherent_iff_restrict, restrict_isQuasicoherent_iff_fromSpec,
    AlgebraicGeometry.isQuasicoherent_iff_isIso_fromTildeΓ,
    AlgebraicGeometry.isIso_fromTildeΓ_iff_isLocalizing]

end Engine

set_option backward.isDefEq.respectTransparency false in
/-- **Affine-local engine of the `IdealSheafData ↔ quasi-coherent ideal sheaf` correspondence.**

Over an affine open `V`, the restriction of an ideal subsheaf `I` of `𝒪ₓ` is quasi-coherent if and
only if its sections satisfy the basic-open localization condition: for every `f : Γ(X, V)`, the
ideal on the basic open `D(f)` is obtained from the ideal on `V` by extension of scalars along the
localization map `Γ(X, V) → Γ(X, D(f))`.

This is the affine-local heart of the correspondence between `Scheme.IdealSheafData` and
quasi-coherent ideal sheaves. Both directions reduce, via the equivalence between sheaves of modules
on `𝒪_X` restricted to `V` and sheaves of `𝒪_V`-modules (`Scheme.Modules.overFunctorEquiv`,
`Scheme.Modules.overEquiv`) and the identification `V ≅ Spec Γ(X, V)` (`IsAffineOpen.isoSpec`), to
the `tilde`-equivalence on the affine scheme `Spec Γ(X, V)`: a module on `Spec R` is quasi-coherent
iff its restriction maps to basic opens are localizations
(`AlgebraicGeometry.isIso_fromTildeΓ_iff_isLocalizing`,
`AlgebraicGeometry.isQuasicoherent_iff_isIso_fromTildeΓ`), and for the structure sheaf the localized
sections of an ideal subsheaf are precisely the extension of scalars
(`Submodule.localized₀`, `IsAffineOpen.isLocalization_basicOpen`). -/
lemma over_isQuasicoherent_iff (I : SheafOfModules.IdealSheaf X.ringCatSheaf) (V : X.affineOpens) :
    (I.toSheafOfModules.over V.1).IsQuasicoherent ↔
      ∀ f : Γ(X, V.1),
        (I.ideal (op V.1)).map (X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom =
          I.ideal (op (X.basicOpen f)) := by
  rw [over_isQuasicoherent_iff_isLocalizing V I.toSheafOfModules]
  refine forall_congr' fun f => ?_
  haveI := V.2.isLocalization_basicOpen f
  -- The basic-open restriction map of the transported ideal sheaf on `Spec Γ(X, V)`, identified
  -- via `Scheme.Modules.restrictAppIso` and `IsAffineOpen.fromSpec_image_basicOpen` with the
  -- corestriction of the localization map `Γ(X, V) → Γ(X, D(f))` to the ideals, is a localization
  -- away from `f` if and only if `Ideal.map` recovers the ideal on `D(f)`
  -- (`isLocalizedModule_corestrict_iff`). The remaining step is the `Γ(X, V)`-linear identification
  -- of the section modules `Γ(_, ⊤)` and `Γ(_, D(f))` of the transported sheaf with the ideal
  -- sections of `I`, compatibly with the restriction map.
  set N := (Scheme.Modules.restrictFunctor V.2.fromSpec).obj I.toSheafOfModules with hN
  have e1 : V.2.fromSpec ''ᵁ (⊤ : (Spec Γ(X, V.1)).Opens) = V.1 := by
    rw [Scheme.Hom.image_top_eq_opensRange]; exact V.2.opensRange_fromSpec
  have hW1 : (op V.1 : (Opens X)ᵒᵖ) = op (V.2.fromSpec ''ᵁ ⊤) := congrArg op e1.symm
  have key : (V.2.fromSpec.appIso ⊤).inv ≫ X.presheaf.map (eqToHom hW1.symm) =
      (Scheme.ΓSpecIso Γ(X, V.1)).hom := by
    rw [Iso.inv_comp_eq, Scheme.Hom.appIso_hom, V.2.fromSpec_app_of_le _ e1.ge]
    simp only [Category.assoc]
    rw [← Functor.map_comp_assoc, Subsingleton.elim ((homOfLE le_top).op ≫ _)
        (𝟙 (op (⊤ : (Spec Γ(X, V.1)).Opens))),
      CategoryTheory.Functor.map_id, Category.id_comp, Iso.inv_hom_id, Category.comp_id]
    congr 1
  have key' : (Scheme.ΓSpecIso Γ(X, V.1)).inv ≫ (V.2.fromSpec.appIso ⊤).inv =
      X.presheaf.map (eqToHom hW1) := by
    rw [Iso.inv_comp_eq, ← key]
    simp only [Category.assoc, ← Functor.map_comp, eqToHom_trans, eqToHom_refl,
      CategoryTheory.Functor.map_id, Category.comp_id]
  have gkey : ∀ (U : (Spec Γ(X, V.1)).Opens) (hW : V.2.fromSpec ''ᵁ U ≤ V.1),
      (Scheme.ΓSpecIso Γ(X, V.1)).inv ≫ (Spec Γ(X, V.1)).presheaf.map U.leTop.op ≫
          (V.2.fromSpec.appIso U).inv = X.presheaf.map (homOfLE hW).op := by
    intro U hW
    rw [Scheme.Hom.appIso_inv_naturality]
    calc (Scheme.ΓSpecIso Γ(X, V.1)).inv ≫ (V.2.fromSpec.appIso ⊤).inv ≫
            X.presheaf.map ((Scheme.Hom.opensFunctor V.2.fromSpec).op.map U.leTop.op)
        = ((Scheme.ΓSpecIso Γ(X, V.1)).inv ≫ (V.2.fromSpec.appIso ⊤).inv) ≫
            X.presheaf.map ((Scheme.Hom.opensFunctor V.2.fromSpec).op.map U.leTop.op) := by
          rw [Category.assoc]
      _ = X.presheaf.map (eqToHom hW1) ≫
            X.presheaf.map ((Scheme.Hom.opensFunctor V.2.fromSpec).op.map U.leTop.op) := by
          rw [key']
      _ = X.presheaf.map (homOfLE hW).op := by rw [← Functor.map_comp]; congr 1
  have hact : ∀ (U : (Spec Γ(X, V.1)).Opens) (W' : X.Opens) (hUW : V.2.fromSpec ''ᵁ U = W')
      (hle : W' ≤ V.1) (r : Γ(X, V.1))
      (x : ((modulesSpecToSheaf.obj N).obj.obj (op U))),
      (I.toSheafOfModules.val.map (eqToHom (congrArg op hUW))).hom (r • x) =
        (X.presheaf.map (homOfLE hle).op).hom r •
          (I.toSheafOfModules.val.map (eqToHom (congrArg op hUW))).hom x := by
    intro U W' hUW hle r x
    have hW : V.2.fromSpec ''ᵁ U ≤ V.1 := hUW ▸ hle
    rw [Scheme.Modules.smul_Spec_def (M := N) (U := U), ← Scheme.Modules.smul_apply]
    have h := Scheme.Modules.smul_restrictAppIso_hom (f := V.2.fromSpec) I.toSheafOfModules U
      (((Spec Γ(X, V.1)).presheaf.map U.leTop.op) ((Scheme.ΓSpecIso Γ(X, V.1)).inv r))
    simp only [Scheme.Modules.restrictAppIso, Iso.refl_hom, Category.comp_id, Category.id_comp] at h
    rw [h]
    erw [Scheme.Modules.smul_apply, PresheafOfModules.map_smul]
    congr 1
    have hg := ConcreteCategory.congr_hom (gkey U hW) r
    simp only [CommRingCat.comp_apply] at hg
    rw [show (X.ringCatSheaf.obj.map (eqToHom (congrArg op hUW))).hom
        ((V.2.fromSpec.appIso U).inv (((Spec Γ(X, V.1)).presheaf.map U.leTop.op)
          ((Scheme.ΓSpecIso Γ(X, V.1)).inv r)))
        = (X.ringCatSheaf.obj.map (eqToHom (congrArg op hUW))).hom
            ((X.presheaf.map (homOfLE hW).op).hom r) from by rw [← hg]]
    rw [show (X.ringCatSheaf.obj.map (eqToHom (congrArg op hUW))).hom
          ((X.presheaf.map (homOfLE hW).op).hom r)
        = (X.presheaf.map (eqToHom (congrArg op hUW))).hom
            ((X.presheaf.map (homOfLE hW).op).hom r) from rfl]
    rw [← CommRingCat.comp_apply, ← Functor.map_comp]
    congr 2
  -- basic opens facts
  have e2 : V.2.fromSpec ''ᵁ (PrimeSpectrum.basicOpen f) = X.basicOpen f :=
    V.2.fromSpec_image_basicOpen f
  -- e₁ : M⊤ ≃ₗ[A] ↥(I.ideal (op V.1))
  let e₁ : ((modulesSpecToSheaf.obj N).obj.obj (op ⊤)) ≃ₗ[Γ(X, V.1)] ↥(I.ideal (op V.1)) :=
    { toFun := fun x => (I.toSheafOfModules.val.map (eqToHom (congrArg op e1))).hom x
      invFun := fun y => (I.toSheafOfModules.val.map (eqToHom (congrArg op e1.symm))).hom y
      map_add' := fun a b => by rw [map_add]
      map_smul' := fun r x => by
        simp only [RingHom.id_apply]
        rw [hact ⊤ V.1 e1 le_rfl r x]
        congr 1
        rw [Subsingleton.elim (homOfLE (le_refl V.1)).op (𝟙 (op V.1)),
          CategoryTheory.Functor.map_id]; rfl
      left_inv := fun x => Subtype.ext (by
        change (X.ringCatSheaf.obj.map (eqToHom (congrArg op e1.symm))).hom
            ((X.ringCatSheaf.obj.map (eqToHom (congrArg op e1))).hom x.1) = x.1
        rw [← RingCat.comp_apply, ← Functor.map_comp, eqToHom_trans, eqToHom_refl,
          CategoryTheory.Functor.map_id, RingCat.id_apply])
      right_inv := fun y => Subtype.ext (by
        change (X.ringCatSheaf.obj.map (eqToHom (congrArg op e1))).hom
            ((X.ringCatSheaf.obj.map (eqToHom (congrArg op e1.symm))).hom y.1) = y.1
        rw [← RingCat.comp_apply, ← Functor.map_comp, eqToHom_trans, eqToHom_refl,
          CategoryTheory.Functor.map_id, RingCat.id_apply]) }
  letI : Algebra Γ(X, V.1) ↑(X.ringCatSheaf.obj.obj (op (X.basicOpen f))) :=
    (X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom.toAlgebra
  let e₂ : ((modulesSpecToSheaf.obj N).obj.obj (op (PrimeSpectrum.basicOpen f))) ≃ₗ[Γ(X, V.1)]
      ↥((I.ideal (op (X.basicOpen f))).restrictScalars Γ(X, V.1)) :=
    { toFun := fun x => (I.toSheafOfModules.val.map (eqToHom (congrArg op e2))).hom x
      invFun := fun y => (I.toSheafOfModules.val.map (eqToHom (congrArg op e2.symm))).hom y
      map_add' := fun a b => by rw [map_add]
      map_smul' := fun r x => by
        simp only [RingHom.id_apply]
        rw [hact (PrimeSpectrum.basicOpen f) (X.basicOpen f) e2 (X.basicOpen_le f) r x]
        exact algebraMap_smul Γ(X, X.basicOpen f) r _
      left_inv := fun x => Subtype.ext (by
        change (X.ringCatSheaf.obj.map (eqToHom (congrArg op e2.symm))).hom
            ((X.ringCatSheaf.obj.map (eqToHom (congrArg op e2))).hom x.1) = x.1
        rw [← RingCat.comp_apply, ← Functor.map_comp, eqToHom_trans, eqToHom_refl,
          CategoryTheory.Functor.map_id, RingCat.id_apply])
      right_inv := fun y => Subtype.ext (by
        change (X.ringCatSheaf.obj.map (eqToHom (congrArg op e2))).hom
            ((X.ringCatSheaf.obj.map (eqToHom (congrArg op e2.symm))).hom y.1) = y.1
        rw [← RingCat.comp_apply, ← Functor.map_comp, eqToHom_trans, eqToHom_refl,
          CategoryTheory.Functor.map_id, RingCat.id_apply]) }
  set ψ := ((modulesSpecToSheaf.obj N).obj.map (PrimeSpectrum.basicOpen f).leTop.op).hom with hψ
  let c := e₂.toLinearMap ∘ₗ ψ ∘ₗ e₁.symm.toLinearMap
  have hc : ∀ x : I.ideal (op V.1),
      ((c x).val : Γ(X, X.basicOpen f))
        = algebraMap Γ(X, V.1) Γ(X, X.basicOpen f) x.1 := by
    intro x
    change (X.ringCatSheaf.obj.map (eqToHom (congrArg op e2)))
        ((X.ringCatSheaf.obj.map ((Scheme.Hom.opensFunctor V.2.fromSpec).op.map
            (PrimeSpectrum.basicOpen f).leTop.op))
          ((X.ringCatSheaf.obj.map (eqToHom (congrArg op e1.symm))) x.1))
      = algebraMap Γ(X, V.1) Γ(X, X.basicOpen f) x.1
    have hcomp : X.ringCatSheaf.obj.map (eqToHom (congrArg op e1.symm)) ≫
        X.ringCatSheaf.obj.map ((Scheme.Hom.opensFunctor V.2.fromSpec).op.map
          (PrimeSpectrum.basicOpen f).leTop.op) ≫
        X.ringCatSheaf.obj.map (eqToHom (congrArg op e2))
        = X.ringCatSheaf.obj.map (homOfLE (X.basicOpen_le f)).op := by
      rw [← Functor.map_comp, ← Functor.map_comp]; congr 1
    have hap := ConcreteCategory.congr_hom hcomp x.1
    simp only [RingCat.comp_apply] at hap
    exact hap
  have main := isLocalizedModule_corestrict_iff (A := Γ(X, V.1)) (B := Γ(X, X.basicOpen f)) f
    (I.ideal (op V.1)) (I.ideal (op (X.basicOpen f))) c hc
  have hiff : IsLocalizedModule (.powers f) c ↔ IsLocalizedModule (.powers f) ψ := by
    rw [show c = e₂.toLinearMap ∘ₗ (ψ ∘ₗ e₁.symm.toLinearMap) from rfl]
    rw [IsLocalizedModule.comp_iff_of_bijective_left (Submonoid.powers f) e₂.toLinearMap
      e₂.bijective]
    rw [IsLocalizedModule.comp_iff_of_bijective_right (Submonoid.powers f) e₁.symm.toLinearMap
      e₁.symm.bijective]
  exact hiff.symm.trans main

set_option backward.isDefEq.respectTransparency false in
/-- The forward direction of `over_isQuasicoherent_iff`. -/
lemma map_ideal_eq_of_isQuasicoherent
    (I : SheafOfModules.IdealSheaf X.ringCatSheaf) (hI : I.IsQuasicoherent)
    (V : X.affineOpens) (f : Γ(X, V.1)) :
    (I.ideal (op V.1)).map (X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom =
      I.ideal (op (X.basicOpen f)) := by
  haveI : I.toSheafOfModules.IsQuasicoherent := hI
  exact (I.over_isQuasicoherent_iff V).mp (isQuasicoherent_over I.toSheafOfModules V.1) f

end SheafOfModules.IdealSheaf

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X : Scheme.{u}}

set_option backward.isDefEq.respectTransparency false in
/-- The quasi-coherent ideal sheaf `D.toIdealSheaf` associated to an `IdealSheafData` is indeed
quasi-coherent. -/
theorem toIdealSheaf_isQuasicoherent (D : X.IdealSheafData) :
    (D.toIdealSheaf).IsQuasicoherent := by
  haveI : ∀ V : X.affineOpens,
      (D.toIdealSheaf.toSheafOfModules.over ((fun V : X.affineOpens ↦ V.1) V)).IsQuasicoherent := by
    intro V
    rw [D.toIdealSheaf.over_isQuasicoherent_iff V]
    intro f
    rw [D.toIdealSheaf_ideal V, D.map_ideal_basicOpen V f]
    exact (D.toIdealSheaf_ideal (X.affineBasicOpen f)).symm
  exact SheafOfModules.IsQuasicoherent.of_coversTop D.toIdealSheaf.toSheafOfModules
    (fun V : X.affineOpens ↦ V.1)
    ((Opens.coversTop_iff _ (fun V : X.affineOpens ↦ V.1)).mpr (iSup_affineOpens_eq_top X))

end AlgebraicGeometry.Scheme.IdealSheafData

namespace SheafOfModules.IdealSheaf

open AlgebraicGeometry

variable {X : Scheme.{u}}

set_option backward.isDefEq.respectTransparency false in
/-- The `IdealSheafData` associated to a quasi-coherent ideal sheaf of `𝒪ₓ`. On an affine open `V`
its ideal is the sections `I(V)`; the compatibility with basic opens is exactly the quasi-coherence
of `I` (`SheafOfModules.IdealSheaf.map_ideal_eq_of_isQuasicoherent`). -/
noncomputable def toIdealSheafData (I : SheafOfModules.IdealSheaf X.ringCatSheaf)
    (hI : I.IsQuasicoherent) : X.IdealSheafData where
  ideal V := I.ideal (op V.1)
  map_ideal_basicOpen U f := I.map_ideal_eq_of_isQuasicoherent hI U f

set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma toIdealSheafData_ideal (I : SheafOfModules.IdealSheaf X.ringCatSheaf)
    (hI : I.IsQuasicoherent) (V : X.affineOpens) :
    (I.toIdealSheafData hI).ideal V = I.ideal (op V.1) :=
  rfl

set_option backward.isDefEq.respectTransparency false in
lemma toIdealSheafData_mono {I J : SheafOfModules.IdealSheaf X.ringCatSheaf}
    (hI : I.IsQuasicoherent) (hJ : J.IsQuasicoherent) (hIJ : I ≤ J) :
    I.toIdealSheafData hI ≤ J.toIdealSheafData hJ := by
  rw [AlgebraicGeometry.Scheme.IdealSheafData.le_def]
  intro V
  exact (SheafOfModules.IdealSheaf.le_def.mp hIJ) (op V.1)

set_option backward.isDefEq.respectTransparency false in
/-- The `IdealSheafData` associated to a quasi-coherent ideal sheaf `I` recovers `I`:
`(I.toIdealSheafData hI).toIdealSheaf = I`. The nontrivial inclusion says that a section which is
affine-locally in `I` lies in `I`, and is proved by gluing via `I.isSheaf` (the sieve of affine
opens contained in the given open is covering, since affine opens form a basis). -/
lemma toIdealSheafData_toIdealSheaf (I : SheafOfModules.IdealSheaf X.ringCatSheaf)
    (hI : I.IsQuasicoherent) :
    (I.toIdealSheafData hI).toIdealSheaf = I := by
  letI R : Sheaf _ RingCat.{u} := X.ringCatSheaf
  refine IdealSheaf.ext fun U => le_antisymm ?_ ?_
  · -- nontrivial inclusion: affine-local membership implies membership
    intro r hr
    let F : (Opens X)ᵒᵖ ⥤ Type u :=
      (PresheafOfModules.unit R.obj).presheaf ⋙ CategoryTheory.forget AddCommGrpCat.{u}
    have hF : Presieve.IsSheaf (Opens.grothendieckTopology X) F :=
      AlgebraicGeometry.Scheme.IdealSheafData.presieveIsSheaf_comp_forget
        (SheafOfModules.unit R).isSheaf
    let GI : Subfunctor F :=
      { obj := fun V ↦ { r : R.obj.obj V | r ∈ I.ideal V }
        map := @fun A B f m hm ↦ I.toSubmoduleSystem.map_mem f hm }
    have hGI : Presieve.IsSheaf (Opens.grothendieckTopology X) GI.toFunctor := by
      have hI' : Presieve.IsSheaf (Opens.grothendieckTopology X)
          (I.toSubmoduleSystem.toPresheafOfModules.presheaf ⋙
            CategoryTheory.forget AddCommGrpCat.{u}) :=
        AlgebraicGeometry.Scheme.IdealSheafData.presieveIsSheaf_comp_forget I.isSheaf
      exact Presieve.isSheaf_iso _
        (NatIso.ofComponents (fun _ ↦ Iso.refl _) (by intros; rfl)) hI'
    refine (GI.isSheaf_iff hF).mp hGI U r ?_
    rw [Opens.mem_grothendieckTopology]
    intro x hx
    obtain ⟨W, hWaff, hxW, hWU⟩ := Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens hx
    refine ⟨W, homOfLE hWU, ?_, hxW⟩
    change (R.obj.map (homOfLE hWU).op).hom r ∈ I.ideal (op W)
    exact hr ⟨W, hWaff⟩ (homOfLE hWU).op
  · -- trivial inclusion: `I` is restriction-stable
    intro r hr W i
    have hmem := I.toSubmoduleSystem.map_mem i hr
    rwa [show (PresheafOfModules.unit R.obj).map i r = (R.obj.map i).hom r from rfl] at hmem

end SheafOfModules.IdealSheaf

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X : Scheme.{u}}

set_option backward.isDefEq.respectTransparency false in
/-- **The order isomorphism realizing the equivalence between `Scheme.IdealSheafData X` and
quasi-coherent ideal sheaves of `𝒪ₓ`.** A datum `D` is sent to the quasi-coherent ideal subsheaf
`D.toIdealSheaf`, and a quasi-coherent ideal sheaf `I` to its `IdealSheafData` of affine sections
`I.toIdealSheafData`. -/
noncomputable def orderIsoQuasicoherentIdealSheaf :
    X.IdealSheafData ≃o
      { I : SheafOfModules.IdealSheaf X.ringCatSheaf // I.IsQuasicoherent } where
  toFun D := ⟨D.toIdealSheaf, D.toIdealSheaf_isQuasicoherent⟩
  invFun I := I.1.toIdealSheafData I.2
  left_inv D :=
    AlgebraicGeometry.Scheme.IdealSheafData.ext <| funext fun V => by
      rw [SheafOfModules.IdealSheaf.toIdealSheafData_ideal, D.toIdealSheaf_ideal V]
  right_inv I := Subtype.ext (I.1.toIdealSheafData_toIdealSheaf I.2)
  map_rel_iff' {D D'} := by
    constructor
    · intro h
      rw [AlgebraicGeometry.Scheme.IdealSheafData.le_def]
      intro V
      have hle : D.toIdealSheaf ≤ D'.toIdealSheaf := h
      rw [← D.toIdealSheaf_ideal V, ← D'.toIdealSheaf_ideal V]
      exact SheafOfModules.IdealSheaf.le_def.mp hle (op V.1)
    · intro h
      exact toIdealSheaf_mono h

end AlgebraicGeometry.Scheme.IdealSheafData
