/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono

/-!
# Subobjects of presheaves of modules from a family of submodules

Given a presheaf of modules `M` over a presheaf of rings `R` and a family of
submodules `N X ≤ M.obj X` that is stable under the restriction maps of `M`,
we construct the corresponding subobject of `M` in the category
`PresheafOfModules R`, together with its inclusion monomorphism.

## Main definitions

* `PresheafOfModules.Submodule M`: a family of submodules of `M`, stable
  under restriction.
* `PresheafOfModules.Submodule.toPresheafOfModules`: the associated
  presheaf of modules.
* `PresheafOfModules.Submodule.ι`: the inclusion into `M`, a monomorphism.

The submodules of `M` form a complete lattice, with order given by pointwise inclusion.

-/

@[expose] public section

universe v v₁ u₁ u

open CategoryTheory

namespace PresheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {R : Cᵒᵖ ⥤ RingCat.{u}}

/-- A family of submodules `N X ≤ M.obj X` of a presheaf of modules `M`, stable
under the restriction maps of `M`. This is the data needed to cut out a
subobject of `M` in `PresheafOfModules R`. -/
protected structure Submodule (M : PresheafOfModules.{v} R) where
  /-- the submodule of `M.obj X` -/
  toSubmodule (X : Cᵒᵖ) : _root_.Submodule (R.obj X) (M.obj X)
  /-- the family is stable under restriction -/
  map_mem ⦃X Y : Cᵒᵖ⦄ (f : X ⟶ Y) ⦃m : M.obj X⦄ (hm : m ∈ toSubmodule X) :
    M.map f m ∈ toSubmodule Y

namespace Submodule

variable {M : PresheafOfModules.{v} R} (N : M.Submodule)

@[ext]
lemma ext {N₁ N₂ : M.Submodule} (h : ∀ X, N₁.toSubmodule X = N₂.toSubmodule X) :
    N₁ = N₂ := by
  cases N₁; cases N₂; congr 1; ext X : 1; exact h X

set_option backward.isDefEq.respectTransparency false in
/-- The subobject of `M` cut out by the family of submodules `N`, as a presheaf of modules: over
`X` it is the submodule `N.toSubmodule X`, with restriction maps induced by those of `M`. -/
noncomputable def toPresheafOfModules : PresheafOfModules.{v} R where
  obj X := ModuleCat.of (R.obj X) (N.toSubmodule X)
  map {X Y} f := ModuleCat.ofHom
      (Y := (ModuleCat.restrictScalars (R.map f).hom).obj (ModuleCat.of (R.obj Y) (N.toSubmodule Y)))
    { toFun := fun m ↦ ⟨M.map f m.val, N.map_mem f m.property⟩
      map_add' := fun a b ↦ Subtype.ext (map_add (M.map f).hom a.val b.val)
      map_smul' := fun r m ↦ Subtype.ext (M.map_smul f r m.val) }

@[simp]
lemma toPresheafOfModules_obj (X : Cᵒᵖ) :
    (N.toPresheafOfModules).obj X = ModuleCat.of _ (N.toSubmodule X) := rfl

@[simp]
lemma toPresheafOfModules_map_apply {X Y : Cᵒᵖ} (f : X ⟶ Y) (m : N.toSubmodule X) :
    ((N.toPresheafOfModules).map f m).val = M.map f m.val := rfl

/-- The inclusion of the subobject cut out by `N` into `M`. -/
noncomputable def ι : N.toPresheafOfModules ⟶ M :=
  homMk { app := fun X ↦ AddCommGrpCat.ofHom (N.toSubmodule X).subtype.toAddMonoidHom
          naturality := fun {X Y} f ↦ by ext m; rfl }
    (fun X r m ↦ rfl)

@[simp]
lemma ι_app_apply (X : Cᵒᵖ) (m : N.toSubmodule X) : (N.ι).app X m = m.val := rfl

lemma ι_app_injective (X : Cᵒᵖ) : Function.Injective ((N.ι).app X) :=
  Subtype.val_injective

instance : Mono N.ι := mono_of_injective N.ι_app_injective

lemma mem_iff {X : Cᵒᵖ} (m : M.obj X) :
    (∃ n : N.toSubmodule X, (N.ι).app X n = m) ↔ m ∈ N.toSubmodule X :=
  ⟨fun ⟨n, hn⟩ ↦ hn ▸ n.property, fun hm ↦ ⟨⟨m, hm⟩, rfl⟩⟩

section Lattice

instance : PartialOrder M.Submodule where
  le N₁ N₂ := ∀ X, N₁.toSubmodule X ≤ N₂.toSubmodule X
  le_refl N X := le_rfl
  le_trans N₁ N₂ N₃ h₁ h₂ X := (h₁ X).trans (h₂ X)
  le_antisymm N₁ N₂ h₁ h₂ := by ext X; exact le_antisymm (h₁ X) (h₂ X)

lemma le_def {N₁ N₂ : M.Submodule} :
    N₁ ≤ N₂ ↔ ∀ X, N₁.toSubmodule X ≤ N₂.toSubmodule X := Iff.rfl

instance : InfSet M.Submodule where
  sInf S :=
    { toSubmodule X := ⨅ N ∈ S, N.toSubmodule X
      map_mem := by
        intro X Y f m hm
        simp only [_root_.Submodule.mem_iInf] at hm ⊢
        exact fun N hN ↦ N.map_mem f (hm N hN) }

@[simp]
lemma sInf_toSubmodule (S : Set M.Submodule) (X : Cᵒᵖ) :
    (sInf S).toSubmodule X = ⨅ N ∈ S, N.toSubmodule X := rfl

instance : CompleteLattice M.Submodule :=
  completeLatticeOfInf _ fun S ↦ by
    refine ⟨fun N hN X ↦ ?_, fun N hN X ↦ ?_⟩
    · simpa only [sInf_toSubmodule] using iInf₂_le N hN
    · simpa only [sInf_toSubmodule] using le_iInf₂ fun N' hN' ↦ hN hN' X

end Lattice

end Submodule

end PresheafOfModules
