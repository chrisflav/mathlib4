/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Stalk
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Annihilator

/-!
# Stalks of the annihilator ideal sheaf

For a presheaf of modules `M` over a presheaf of rings `R` on a topological space `X`, we
compare the stalk of the annihilator ideal (pre)sheaf at a point `x` with the module-theoretic
annihilator `Module.annihilator (R.stalk x) (M.presheaf.stalk x)`.

The germ of any section of the annihilator ideal lands in `Module.annihilator` of the stalks
(`PresheafOfModules.germ_mem_annihilator_stalk`); equality of the two requires a finiteness
hypothesis on `M`.

-/

@[expose] public section

universe u

open CategoryTheory TopologicalSpace Opposite TopCat.Presheaf

namespace PresheafOfModules

variable {X : TopCat.{u}} {R : X.Presheaf RingCat.{u}} (M : PresheafOfModules.{u} R) {x : X}

/-- The germ at `x` of a section `r` of `R` that annihilates `M` locally annihilates the stalk
`M.presheaf.stalk x`. This is the "easy" containment that holds with no finiteness hypothesis. -/
theorem germ_mem_annihilator_stalk {U : Opens X} (hx : x ∈ U) (r : R.obj (op U))
    (hr : r ∈ M.annihilatorIdeal (op U)) :
    R.germ U x hx r ∈ Module.annihilator (R.stalk x) ↑(TopCat.Presheaf.stalk M.presheaf x) := by
  rw [Module.mem_annihilator]
  intro mx
  obtain ⟨V, hxV, m, rfl⟩ := exists_germ_eq M.presheaf mx
  have hxW : x ∈ U ⊓ V := ⟨hx, hxV⟩
  rw [← germ_res_apply R (homOfLE inf_le_left) x hxW r,
    ← germ_res_apply M.presheaf (homOfLE inf_le_right) x hxW m,
    ← M.germ_ringCat_smul x (U ⊓ V) hxW,
    (mem_annihilatorIdeal r).mp hr (homOfLE (inf_le_left : U ⊓ V ≤ U)).op
      (M.presheaf.map (homOfLE inf_le_right).op m)]
  exact map_zero _

/-- **Stalk of the annihilator ideal sheaf.**
Under a finite *local generation* hypothesis, the stalk of the annihilator ideal (pre)sheaf at `x`
recovers the module-theoretic annihilator `Module.annihilator (R.stalk x) (M.presheaf.stalk x)`:
an element `ρ` of the ring stalk annihilates the module stalk if and only if it is the germ of a
section of the annihilator ideal.

The `←` direction is the easy `germ_mem_annihilator_stalk`. The `→` direction is the substantial
one; it uses that `M` is locally generated near `x` by the finite family `t`. Concretely, `hgen`
says that every section over `V ≤ U₀` is, locally around each of its points, an `R`-linear
combination of the (restrictions of the) generators `t i`.

The commutativity hypothesis `hRcomm` is needed because, for a *left* module, the implication
"`r` annihilates the generators ⟹ `r` annihilates the module" requires moving `r` past the
coefficients of a linear combination. -/
theorem mem_annihilator_stalk_iff
    (hM : TopCat.Presheaf.IsSheaf M.presheaf)
    (hRcomm : ∀ (U : (Opens X)ᵒᵖ) (a b : R.obj U), a * b = b * a)
    {ι : Type u} [Fintype ι] {U₀ : Opens X} (hx₀ : x ∈ U₀) (t : ι → M.obj (op U₀))
    (hgen : ∀ ⦃V : Opens X⦄ (hVU₀ : V ≤ U₀) (m : M.obj (op V)) ⦃y : X⦄ (_ : y ∈ V),
      ∃ (W : Opens X) (hWV : W ≤ V) (_ : y ∈ W) (a : ι → R.obj (op W)),
        M.presheaf.map (homOfLE hWV).op m =
          ∑ i, a i • M.presheaf.map (homOfLE (le_trans hWV hVU₀)).op (t i))
    (ρ : R.stalk x) :
    ρ ∈ Module.annihilator (R.stalk x) ↑(TopCat.Presheaf.stalk M.presheaf x) ↔
      ∃ (U : Opens X) (hx : x ∈ U) (r : R.obj (op U)),
        r ∈ M.annihilatorIdeal (op U) ∧ R.germ U x hx r = ρ := by
  -- The action commutes with restriction of sections.
  have hsmul_res : ∀ ⦃U V : (Opens X)ᵒᵖ⦄ (g : U ⟶ V) (r : R.obj U) (m : M.obj U),
      M.presheaf.map g (r • m) = R.map g r • M.presheaf.map g m :=
    fun U V g r m => M.map_smul g r m
  constructor
  · intro hρ
    rw [Module.mem_annihilator] at hρ
    -- Choose a representative `r₀` of `ρ` over some `U_r ≤ U₀`.
    obtain ⟨U_r, hUr, hxUr, r₀, hr₀⟩ := exists_le_germ_eq R ρ hx₀
    -- Each generator is annihilated by `r₀` at the stalk, hence on a neighborhood `W i` of `x`.
    have hg : ∀ i, germ M.presheaf U_r x hxUr (r₀ • M.presheaf.map (homOfLE hUr).op (t i)) =
        germ M.presheaf U_r x hxUr 0 := by
      intro i
      rw [map_zero]
      erw [M.germ_ringCat_smul]
      rw [hr₀]
      exact hρ _
    choose W hxW iU iV he using
      fun i => germ_eq M.presheaf x hxUr hxUr
        (r₀ • M.presheaf.map (homOfLE hUr).op (t i)) 0 (hg i)
    have he' : ∀ i, M.presheaf.map (iU i).op
        (r₀ • M.presheaf.map (homOfLE hUr).op (t i)) = 0 :=
      fun i => (he i).trans (map_zero _)
    -- The common neighborhood on which `r₀` annihilates all generators.
    set U' : Opens X := U_r ⊓ ⨅ i, W i with hU'def
    have hU'Ur : U' ≤ U_r := by rw [hU'def]; exact inf_le_left
    have hU'Wi : ∀ i, U' ≤ W i := fun i => by
      rw [hU'def]; exact le_trans inf_le_right (iInf_le _ i)
    have hxU' : x ∈ U' := by
      rw [hU'def]
      refine ⟨hxUr, ?_⟩
      rw [Opens.coe_iInf]
      exact Set.mem_iInter.mpr fun i => hxW i
    refine ⟨U', hxU', R.map (homOfLE hU'Ur).op r₀, ?_, ?_⟩
    · -- `r₀|_{U'}` lies in the annihilator ideal over `U'`.
      refine (mem_annihilatorIdeal _).mpr ?_
      intro Y f m
      obtain ⟨V, rfl⟩ : ∃ V, Y = op V := ⟨Y.unop, rfl⟩
      have hVU' : V ≤ U' := f.unop.le
      have hVU₀ : V ≤ U₀ := le_trans hVU' (le_trans hU'Ur hUr)
      -- It suffices, by separatedness, to check the equality locally around each point of `V`.
      refine hM.section_ext ?_
      intro y hy
      obtain ⟨Wy, hWyV, hyWy, a, ha⟩ := hgen hVU₀ m hy
      have h1 : Wy ≤ U_r := le_trans hWyV (le_trans hVU' hU'Ur)
      have h2 : Wy ≤ U₀ := le_trans hWyV hVU₀
      have hWyWi : ∀ i, Wy ≤ W i := fun i => le_trans hWyV (le_trans hVU' (hU'Wi i))
      -- `r₀` annihilates each generator already on `Wy`.
      have key : ∀ i, R.map (homOfLE h1).op r₀ •
          M.presheaf.map (homOfLE h2).op (t i) = 0 := by
        intro i
        have hsz : M.presheaf.map (homOfLE h1).op
            (r₀ • M.presheaf.map (homOfLE hUr).op (t i)) = 0 := by
          have hm : (homOfLE h1).op = (iU i).op ≫ (homOfLE (hWyWi i)).op := Subsingleton.elim _ _
          rw [hm, Functor.map_comp, ConcreteCategory.comp_apply, he' i, map_zero]
        erw [hsmul_res] at hsz
        have hm2 : (homOfLE h2).op = (homOfLE hUr).op ≫ (homOfLE h1).op := Subsingleton.elim _ _
        rw [hm2, Functor.map_comp, ConcreteCategory.comp_apply]
        exact hsz
      -- Express `r₀|_V • m` locally as a combination of annihilated generators.
      refine ⟨Wy, hWyV, hyWy, ?_⟩
      have hA : R.map (homOfLE hWyV).op (R.map f (R.map (homOfLE hU'Ur).op r₀)) =
          R.map (homOfLE h1).op r₀ := by
        have hm : (homOfLE h1).op = (homOfLE hU'Ur).op ≫ f ≫ (homOfLE hWyV).op :=
          Subsingleton.elim _ _
        rw [hm]
        simp only [Functor.map_comp, ConcreteCategory.comp_apply]
      erw [hsmul_res]
      rw [hA, ha, Finset.smul_sum]
      refine (Finset.sum_eq_zero fun i _ => ?_).trans (map_zero _).symm
      rw [← mul_smul, hRcomm, mul_smul, key i, smul_zero]
    · -- The germ of `r₀|_{U'}` is `ρ`.
      rw [germ_res_apply]
      exact hr₀
  · rintro ⟨U, hx, r, hr, rfl⟩
    exact germ_mem_annihilator_stalk M hx r hr

end PresheafOfModules
