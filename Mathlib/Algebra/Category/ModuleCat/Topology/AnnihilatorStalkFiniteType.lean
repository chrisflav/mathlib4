/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Topology.AnnihilatorStalk
public import Mathlib.Algebra.Category.ModuleCat.Topology.SheafifyInstances
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallySurjective

/-!
# Stalk of the annihilator ideal sheaf of a finite-type sheaf of modules

For a sheaf of modules `M` of finite type over a (commutative) sheaf of rings `R` on a topological
space `X`, the stalk of the annihilator ideal sheaf at a point `x` recovers the module-theoretic
annihilator `Module.annihilator (R.stalk x) (Mₓ)`.

This upgrades `PresheafOfModules.mem_annihilator_stalk_iff`, replacing its explicit local-generation
hypothesis by `[M.IsFiniteType]`. The slice-site sheafification instances needed to even state
`M.IsFiniteType` over the topological site are provided in
`Mathlib.Algebra.Category.ModuleCat.Topology.SheafifyInstances`.
-/

@[expose] public section

universe u

open CategoryTheory TopologicalSpace Opposite TopCat.Presheaf

namespace SheafOfModules

section FreeDecomposition

open CategoryTheory Limits

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
  [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]

/-- A section of the free sheaf of modules `free ι` (for a finite index type `ι`) over an object
`B` is a finite combination `∑ i, (ιFree i)_B (c i)` of the values of the standard basis sections,
with coefficients `c i` sections of `unit R` over `B`. -/
lemma exists_val_obj_eq_sum_ιFree {ι : Type u} [Fintype ι] (B : Cᵒᵖ)
    (b : (free (R := R) ι).val.obj B) :
    ∃ c : ι → R.obj.obj B,
      b = (∑ i, (ιFree i).val.app B (c i) : (free (R := R) ι).val.obj B) := by
  classical
  let f : ι → SheafOfModules.{u} R := fun _ ↦ unit R
  haveI : HasFiniteBiproducts (SheafOfModules.{u} R) := Abelian.hasFiniteBiproducts
  haveI : HasBiproduct f := inferInstance
  let Φ := SheafOfModules.evaluation (R := R) B
  haveI : Φ.Additive :=
    inferInstanceAs (Functor.Additive (forget R ⋙ PresheafOfModules.evaluation R.obj B))
  let e := biproduct.isoCoproduct f
  have hιe : ∀ i, biproduct.ι f i ≫ e.hom = Sigma.ι f i := fun i ↦ by
    rw [biproduct.isoCoproduct_hom, biproduct.ι_desc]
  have key : 𝟙 (⨁ f) = ∑ i, biproduct.π f i ≫ biproduct.ι f i :=
    (IsBilimit.total (biproduct.isBilimit f)).symm
  have hid : 𝟙 (∐ f) = ∑ i, (e.inv ≫ biproduct.π f i) ≫ Sigma.ι f i := by
    have h0 : 𝟙 (∐ f) = e.inv ≫ (𝟙 (⨁ f)) ≫ e.hom := by
      rw [Category.id_comp, e.inv_hom_id]
    rw [h0, key, Preadditive.sum_comp, Preadditive.comp_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    simp only [Category.assoc, hιe i]
  refine ⟨fun i ↦ Φ.map (e.inv ≫ biproduct.π f i) b, ?_⟩
  have hΦ := congr(Φ.map $hid)
  rw [Φ.map_id, Φ.map_sum] at hΦ
  have hb : b = (∑ i, Φ.map ((e.inv ≫ biproduct.π f i) ≫ Sigma.ι f i)).hom b := by
    rw [← hΦ]; rfl
  conv_lhs => rw [hb]
  rw [ModuleCat.hom_sum, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Φ.map_comp]
  rfl

/-- The image under a morphism `φ : free ι ⟶ N` of a section `b` of `free ι` over an object `Z`
is the finite `R(Z)`-linear combination `∑ i, c i • (φ ∘ freeSectionᵢ)(Z)` of the images of the
standard basis sections, for suitable coefficients `c i`. -/
lemma exists_app_eq_sum_smul {ι : Type u} [Fintype ι] {N : SheafOfModules.{u} R}
    (φ : free (R := R) ι ⟶ N) (Z : Cᵒᵖ) (b : (free (R := R) ι).val.obj Z) :
    ∃ c : ι → R.obj.obj Z,
      φ.val.app Z b = ∑ i, c i • (sectionsMap φ (freeSection i)).eval Z := by
  obtain ⟨c, hc⟩ := exists_val_obj_eq_sum_ιFree Z b
  refine ⟨c, ?_⟩
  rw [hc, map_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  have h1 : (ιFree i).val.app Z (c i) = c i • (ιFree i).val.app Z (1 : R.obj.obj Z) := by
    rw [← map_smul]
    congr 1
    exact (mul_one (c i)).symm
  rw [h1, map_smul]
  rfl

end FreeDecomposition

variable {X : TopCat.{u}} {R : Sheaf (Opens.grothendieckTopology X) RingCat.{u}}
  (M : SheafOfModules.{u} R)

set_option backward.isDefEq.respectTransparency false in
open Limits in
/-- The local-generation bridge: if `π : free ι ⟶ M.over U₀` is an epimorphism of sheaves of
modules over the slice site, then every section `m` of `M` over `V ≤ U₀` is, locally around each
of its points, an `R`-linear combination of (the restrictions of) the sections
`(sectionsMap π (freeSectionᵢ))` over `U₀`. -/
lemma exists_localGeneration_of_epi {ι : Type u} [Fintype ι] {U₀ : Opens X}
    (π : free (R := R.over U₀) ι ⟶ M.over U₀) [Epi π] ⦃V : Opens X⦄ (hVU₀ : V ≤ U₀)
    (m : M.val.obj (op V)) ⦃y : X⦄ (hyV : y ∈ V) :
    ∃ (W : Opens X) (hWV : W ≤ V) (_ : y ∈ W) (a : ι → R.obj.obj (op W)),
      M.val.presheaf.map (homOfLE hWV).op m =
        ∑ i, a i • M.val.presheaf.map (homOfLE (le_trans hWV hVU₀)).op
          ((sectionsMap π (freeSection (R := R.over U₀) i)).eval (op (Over.mk (𝟙 U₀)))) := by
  -- `π` is locally surjective on sections over the slice site `J.over U₀`.
  haveI hLS : Presheaf.IsLocallySurjective ((Opens.grothendieckTopology X).over U₀)
      ((PresheafOfModules.toPresheaf (R.over U₀).obj).map π.val) :=
    isLocallySurjective_of_epi _ π
  set g := (PresheafOfModules.toPresheaf (R.over U₀).obj).map π.val with hg
  set A : Over U₀ := Over.mk (homOfLE hVU₀) with hA
  -- `m` is a section of `(M.over U₀).val` (a sheaf on the slice site) over the object `A`.
  let m' : ToType (((PresheafOfModules.toPresheaf (R.over U₀).obj).obj
    (M.over U₀).val).obj (op A)) := m
  have hcov : Presheaf.imageSieve g m' ∈ ((Opens.grothendieckTopology X).over U₀) A :=
    Presheaf.imageSieve_mem _ g _
  rw [GrothendieckTopology.mem_over_iff, Opens.mem_grothendieckTopology] at hcov
  obtain ⟨W, fWV, hSf, hyW⟩ := hcov y hyV
  have hWV : W ≤ V := leOfHom fWV
  rw [show fWV = homOfLE hWV from Subsingleton.elim _ _, Sieve.overEquiv_iff] at hSf
  set B : Over U₀ := Over.mk (homOfLE hWV ≫ A.hom) with hB
  set bhom : B ⟶ A := Over.homMk (homOfLE hWV) with hbhom
  obtain ⟨b, hb⟩ := hSf
  obtain ⟨c, hc⟩ := exists_app_eq_sum_smul π (op B) b
  refine ⟨W, hWV, hyW, c, ?_⟩
  have e1 : π.val.app (op B) b = M.val.presheaf.map (homOfLE hWV).op m := by
    have hL : (g.app (op B)) b = π.val.app (op B) b := rfl
    have hR : (((PresheafOfModules.toPresheaf (R.over U₀).obj).obj (M.over U₀).val).map bhom.op) m'
        = M.val.presheaf.map (homOfLE hWV).op m := rfl
    rw [← hL, ← hR]; exact hb
  rw [← e1, hc]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  congr 1
  exact ((sectionsMap π (freeSection (R := R.over U₀) i)).property
    (Over.homMk (homOfLE (le_trans hWV hVU₀)) : B ⟶ Over.mk (𝟙 U₀)).op).symm

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1000000 in
-- Unifying the slice-site data of `exists_localGeneration_of_epi` against the chart `σ.X i₀`
-- forces some costly unfolding of the `over`/pushforward construction.
/-- A finite-type sheaf of modules over a topological space is, near any point `x`, generated by
a finite family of sections `t` over a neighborhood `U₀` of `x`: every section over `V ≤ U₀` is,
locally around each of its points, an `R`-linear combination of the `t i`. -/
theorem exists_localGeneration_of_isFiniteType [M.IsFiniteType] (x : X) :
    ∃ (ι : Type u) (_ : Fintype ι) (U₀ : Opens X) (_ : x ∈ U₀) (t : ι → M.val.obj (op U₀)),
      ∀ ⦃V : Opens X⦄ (hVU₀ : V ≤ U₀) (m : M.val.obj (op V)) ⦃y : X⦄ (_ : y ∈ V),
        ∃ (W : Opens X) (hWV : W ≤ V) (_ : y ∈ W) (a : ι → R.obj.obj (op W)),
          M.val.presheaf.map (homOfLE hWV).op m =
            ∑ i, a i • M.val.presheaf.map (homOfLE (le_trans hWV hVU₀)).op (t i) := by
  -- Step 1: extract a finite local generation datum and a chart `U₀ = σ.X i₀ ∋ x`.
  obtain ⟨σ, hσ⟩ := IsFiniteType.exists_localGeneratorsData (M := M)
  obtain ⟨i₀, hxi₀⟩ := ((Opens.coversTop_iff (U := σ.X)).mp σ.coversTop).exists_mem x
  letI : (σ.generators i₀).IsFiniteType := hσ.isFiniteType i₀
  haveI : Finite (σ.generators i₀).I := inferInstance
  haveI : Fintype (σ.generators i₀).I := Fintype.ofFinite _
  -- Step 2: turn the generating sections of `M.over (σ.X i₀)` into honest sections over `U₀`.
  refine ⟨(σ.generators i₀).I, inferInstance, σ.X i₀, hxi₀,
    fun i => ((σ.generators i₀).s i).eval (Opposite.op (Over.mk (𝟙 (σ.X i₀)))), ?_⟩
  -- Step 3: the local-generation bridge, applied to the epimorphism `(σ.generators i₀).π`.
  set G := σ.generators i₀ with hG
  intro V hVU₀ m y hyV
  -- `sectionsMap G.π (freeSection i) = G.s i`, so the generators match the chosen sections `t`.
  have hsπ : ∀ i, sectionsMap G.π (freeSection (R := R.over (σ.X i₀)) i) = G.s i := fun i ↦
    sectionsMap_freeHomEquiv_symm_freeSection G.s i
  obtain ⟨W, hWV, hyW, a, ha⟩ := M.exists_localGeneration_of_epi G.π hVU₀ m hyV
  refine ⟨W, hWV, hyW, a, ?_⟩
  rw [ha]
  refine Finset.sum_congr (Finset.ext fun i ↦ by simp) fun i _ ↦ ?_
  rw [hsπ i]

/-- **Stalk of the annihilator ideal sheaf of a finite-type module.**
For a finite-type sheaf of modules `M` over a commutative sheaf of rings `R` on a topological
space, an element `ρ` of the ring stalk at `x` annihilates the module stalk `Mₓ` if and only if it
is the germ of a section of the annihilator ideal sheaf. -/
theorem mem_annihilator_stalk_iff_of_isFiniteType [M.IsFiniteType] {x : X}
    (hRcomm : ∀ (U : (Opens X)ᵒᵖ) (a b : R.obj.obj U), a * b = b * a)
    (ρ : TopCat.Presheaf.stalk (C := RingCat.{u}) (X := X) R.obj x) :
    ρ ∈ Module.annihilator (TopCat.Presheaf.stalk (C := RingCat.{u}) (X := X) R.obj x)
        ↑(TopCat.Presheaf.stalk M.val.presheaf x) ↔
      ∃ (U : Opens X) (hx : x ∈ U) (r : R.obj.obj (op U)),
        r ∈ M.val.annihilatorIdeal (op U) ∧
          TopCat.Presheaf.germ (C := RingCat.{u}) (X := X) R.obj U x hx r = ρ := by
  obtain ⟨ι, hfin, U₀, hx₀, t, hgen⟩ := M.exists_localGeneration_of_isFiniteType x
  letI := hfin
  exact M.val.mem_annihilator_stalk_iff M.isSheaf hRcomm hx₀ t hgen ρ

end SheafOfModules
