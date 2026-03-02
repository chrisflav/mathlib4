/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.Algebra.Category.Ring.Constructions
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.CategoryTheory.Limits.Presentation
import Mathlib.RingTheory.Extension.Presentation.Core

/-!
# foo

-/

universe t u
open TensorProduct CategoryTheory Limits

variable {R : Type u} {S ι σ : Type*} [CommRing R] [CommRing S] [Algebra R S]

variable {P : Algebra.Presentation R S ι σ}

namespace Algebra.Presentation

-- TODO: generalise to `[Small.{u} J]` by generalising
-- `Mathlib.Algebra.Category.Ring.FilteredColimits`
variable {J : Type u} [Category.{u} J]
  (pres : ColimitPresentation J (CommRingCat.of R))

local instance (j : J) : Algebra (pres.diag.obj j) R := (pres.ι.app j).hom.toAlgebra

/-- Any finite presentation over a filtered colimit descends to a finite level. -/
lemma exists_hasCoeffs_of_isFiltered [Finite ι] [Finite σ] [IsFiltered J] :
    letI (j : J) : Algebra (pres.diag.obj j) S := Algebra.compHom _ (R := R) (pres.ι.app j).hom
    haveI (j : J) : IsScalarTower (pres.diag.obj j) R S := .of_algebraMap_eq' rfl
    ∃ (j : J), P.HasCoeffs (pres.diag.obj j) := by
  classical
  have (r : R) : ∃ (j : J), r ∈ Set.range (pres.ι.app j).hom := by
    apply Concrete.isColimit_exists_rep _ pres.isColimit _
  choose rj hrj using this
  let s : Finset J := Finset.image rj P.finite_coeffs.toFinset
  obtain ⟨j, hj⟩ := IsFiltered.sup_objs_exists s
  letI (j : J) : Algebra (pres.diag.obj j) S := Algebra.compHom _ (R := R) (pres.ι.app j).hom
  haveI (j : J) : IsScalarTower (pres.diag.obj j) R S := .of_algebraMap_eq' rfl
  refine ⟨j, ⟨?_⟩⟩ 
  intro r hr
  have : rj r ∈ s := by
    simp only [Finset.mem_image, Set.Finite.mem_toFinset, s]
    use r
  obtain ⟨t⟩ := hj this
  obtain ⟨x, hx⟩ := hrj r
  use pres.diag.map t x
  conv_rhs => rw [← hx]
  exact congr($(pres.ι.naturality t).hom x)

lemma foobar [Finite ι] [Finite σ] [IsFiltered J] :
    ∃ (j : J), True :=
  sorry

end Algebra.Presentation
