/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Category.Grp.EpiMono
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.CategoryTheory.Sites.EpiMono

/-!
# Epimorphisms of sheaves of modules are locally surjective

In this file, we show that an epimorphism `f : M ⟶ N` of sheaves of modules over a sheaf
of rings `R` is locally surjective on underlying sections, i.e. the underlying morphism of
presheaves of abelian groups `(PresheafOfModules.toPresheaf R.obj).map f.val` is
`Presheaf.IsLocallySurjective`.

## Main results

* `SheafOfModules.toSheaf_preservesEpimorphisms`: the functor `SheafOfModules.toSheaf R`
  preserves epimorphisms.
* `SheafOfModules.isLocallySurjective_of_epi`: an epimorphism of sheaves of modules is
  locally surjective.

-/

@[expose] public section

universe v v' u u'

open CategoryTheory Limits

variable {C : Type u'} [Category.{v'} C] {J : GrothendieckTopology C}

namespace SheafOfModules

variable {R : Sheaf J RingCat.{u}} [HasSheafify J AddCommGrpCat.{v}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{v}]

variable (J) in
/-- A morphism `f` of sheaves of modules is locally surjective if the underlying morphism
of presheaves of abelian groups is locally surjective. -/
abbrev IsLocallySurjective {M N : SheafOfModules.{v} R} (f : M ⟶ N) : Prop :=
  PresheafOfModules.IsLocallySurjective J f.val

/-- The composition `PresheafOfModules.sheafification (𝟙 R.obj) ⋙ SheafOfModules.toSheaf R`
preserves finite colimits: indeed, it is naturally isomorphic to
`PresheafOfModules.toPresheaf R.obj ⋙ presheafToSheaf J AddCommGrpCat`, both factors of
which preserve finite colimits. -/
noncomputable instance :
    PreservesFiniteColimits
      (PresheafOfModules.sheafification (𝟙 R.obj) ⋙ toSheaf.{v} R) :=
  preservesFiniteColimits_of_natIso
    (PresheafOfModules.sheafificationCompToSheaf (𝟙 R.obj)).symm

/-- The functor `SheafOfModules.toSheaf R : SheafOfModules R ⥤ Sheaf J AddCommGrpCat`
preserves epimorphisms.

Since `SheafOfModules R` is the reflective localization of `PresheafOfModules R.obj` along the
sheafification functor `L := PresheafOfModules.sheafification (𝟙 R.obj)`, with fully faithful
right adjoint, a functor out of `SheafOfModules R` preserves colimits of a given shape as soon
as its precomposition with `L` does (`Adjunction.preservesColimitsOfShape_iff`).
Applied with the shape `WalkingSpan` (pushouts), this gives preservation of epimorphisms. -/
noncomputable instance toSheaf_preservesEpimorphisms :
    (toSheaf.{v} R).PreservesEpimorphisms := by
  have adj := PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)
  have : PreservesColimitsOfShape WalkingSpan (toSheaf.{v} R) :=
    (adj.preservesColimitsOfShape_iff (toSheaf R) WalkingSpan).mpr inferInstance
  infer_instance

variable (J) in
/-- An epimorphism of sheaves of modules is locally surjective on underlying sections. -/
theorem isLocallySurjective_of_epi {M N : SheafOfModules.{v} R} (f : M ⟶ N) [Epi f] :
    IsLocallySurjective J f :=
  (Sheaf.isLocallySurjective_iff_epi' (φ := (toSheaf R).map f)).mpr inferInstance

variable (J) in
/-- A morphism of sheaves of modules is an epimorphism if and only if it is locally surjective
on underlying sections. -/
theorem epi_iff_isLocallySurjective {M N : SheafOfModules.{v} R} (f : M ⟶ N) :
    Epi f ↔ IsLocallySurjective J f := by
  refine ⟨fun _ ↦ isLocallySurjective_of_epi J f, fun hf ↦ ?_⟩
  have hf' : Sheaf.IsLocallySurjective ((toSheaf R).map f) := hf
  have : Epi ((toSheaf R).map f) :=
    (Sheaf.isLocallySurjective_iff_epi' (φ := (toSheaf R).map f)).mp hf'
  exact (toSheaf R).epi_of_epi_map this

end SheafOfModules
