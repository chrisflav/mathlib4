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

* `PresheafOfModules.SubmoduleSystem M`: a family of submodules of `M`, stable
  under restriction.
* `PresheafOfModules.SubmoduleSystem.toPresheafOfModules`: the associated
  presheaf of modules.
* `PresheafOfModules.SubmoduleSystem.ι`: the inclusion into `M`, a monomorphism.

-/

@[expose] public section

universe v v₁ u₁ u

open CategoryTheory

namespace PresheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {R : Cᵒᵖ ⥤ RingCat.{u}}

/-- A family of submodules `N X ≤ M.obj X` of a presheaf of modules `M`, stable
under the restriction maps of `M`. This is the data needed to cut out a
subobject of `M` in `PresheafOfModules R`. -/
structure SubmoduleSystem (M : PresheafOfModules.{v} R) where
  /-- the submodule of `M.obj X` -/
  toSubmodule (X : Cᵒᵖ) : Submodule (R.obj X) (M.obj X)
  /-- the family is stable under restriction -/
  map_mem ⦃X Y : Cᵒᵖ⦄ (f : X ⟶ Y) ⦃m : M.obj X⦄ (hm : m ∈ toSubmodule X) :
    M.map f m ∈ toSubmodule Y

namespace SubmoduleSystem

variable {M : PresheafOfModules.{v} R} (N : M.SubmoduleSystem)

@[ext]
lemma ext {N₁ N₂ : M.SubmoduleSystem} (h : ∀ X, N₁.toSubmodule X = N₂.toSubmodule X) :
    N₁ = N₂ := by
  cases N₁; cases N₂; congr 1; ext X : 1; exact h X

/-- The underlying presheaf of abelian groups of the subobject cut out by `N`. -/
noncomputable def presheafAb : Cᵒᵖ ⥤ Ab where
  obj X := AddCommGrpCat.of (N.toSubmodule X)
  map {X Y} f := AddCommGrpCat.ofHom <| AddMonoidHom.mk'
    (fun m ↦ ⟨M.map f m.1, N.map_mem f m.2⟩)
    (fun a b ↦ Subtype.ext (map_add (M.map f).hom a.1 b.1))
  map_id X := by
    ext m
    change M.map (𝟙 X) m.1 = m.1
    rw [← presheaf_map_apply_coe, M.presheaf.map_id]
    rfl
  map_comp {X Y Z} f g := by
    ext m
    exact M.map_comp_apply f g m.1

@[simp]
lemma presheafAb_obj (X : Cᵒᵖ) : (N.presheafAb).obj X = AddCommGrpCat.of (N.toSubmodule X) := rfl

@[simp]
lemma presheafAb_map_apply {X Y : Cᵒᵖ} (f : X ⟶ Y) (m : N.toSubmodule X) :
    ((N.presheafAb).map f m).1 = M.map f m.1 := rfl

instance (X : Cᵒᵖ) : Module (R.obj X) ((N.presheafAb).obj X) :=
  inferInstanceAs (Module (R.obj X) (N.toSubmodule X))

/-- The subobject of `M` cut out by the family of submodules `N`. -/
noncomputable def toPresheafOfModules : PresheafOfModules.{v} R :=
  ofPresheaf N.presheafAb (fun _ _ f r m ↦ Subtype.ext (M.map_smul f r m.1))

@[simp]
lemma toPresheafOfModules_obj (X : Cᵒᵖ) :
    (N.toPresheafOfModules).obj X = ModuleCat.of _ (N.toSubmodule X) := rfl

/-- The inclusion of the subobject cut out by `N` into `M`. -/
noncomputable def ι : N.toPresheafOfModules ⟶ M :=
  homMk { app := fun X ↦ AddCommGrpCat.ofHom (N.toSubmodule X).subtype.toAddMonoidHom
          naturality := fun {X Y} f ↦ by ext m; rfl }
    (fun X r m ↦ rfl)

@[simp]
lemma ι_app_apply (X : Cᵒᵖ) (m : N.toSubmodule X) : (N.ι).app X m = m.1 := rfl

lemma ι_app_injective (X : Cᵒᵖ) : Function.Injective ((N.ι).app X) :=
  Subtype.val_injective

instance : Mono N.ι := mono_of_injective N.ι_app_injective

lemma mem_iff {X : Cᵒᵖ} (m : M.obj X) :
    (∃ n : N.toSubmodule X, (N.ι).app X n = m) ↔ m ∈ N.toSubmodule X :=
  ⟨fun ⟨n, hn⟩ ↦ hn ▸ n.2, fun hm ↦ ⟨⟨m, hm⟩, rfl⟩⟩

end SubmoduleSystem

end PresheafOfModules
