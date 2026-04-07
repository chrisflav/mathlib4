/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Sites.Over

/-!

-/

universe w

@[expose] public section

namespace CategoryTheory

variable {C : Type*} [Category* C] {A : Type*} [Category* A]
  {X : C} [LocallySmall.{w} C] [LocallySmall.{w} (Over (shrinkYoneda.{w}.obj X))]
  {H : ((Over X)ᵒᵖ ⥤ Type w) ⥤ Cᵒᵖ ⥤ Type w}

variable (X) in
def diagCostructuredArrowForget (U : C) :
    Discrete (U ⟶ X) ⥤ CostructuredArrow (Over.forget X).op (.op U) :=
  Discrete.functor fun f ↦ CostructuredArrow.mk (Y := .op <| Over.mk f) (𝟙 _)

def asdfasdfasdfasdf {ι : Type*} (F : Discrete ι ⥤ C) (X : C) :
    StructuredArrow X F ≌ Discrete ι :=
  sorry

lemma Functor.Final.of_discrete {ι C : Type*} [Category* C] {F : Discrete ι ⥤ C}
    (h : ∀ X : C, ∃! (i : ι), Nonempty (X ⟶ F.obj ⟨i⟩))
    (h' : ∀ (X : C) (i : ι), Subsingleton (X ⟶ F.obj ⟨i⟩)) :
    F.Final := by
  constructor
  intro X
  obtain ⟨i, ⟨f⟩, huniq⟩ := h X
  have : Nonempty (StructuredArrow X F) := by
    constructor
    exact .mk f
  have : IsPreconnected (StructuredArrow X F) := by
    apply zigzag_isPreconnected
    intro ⟨a₁, ⟨j₁⟩, f₁⟩ ⟨a₂, ⟨j₂⟩, f₂⟩
    obtain rfl := Subsingleton.elim a₁ a₂
    obtain rfl := huniq j₁ ⟨f₁⟩
    obtain rfl := huniq j₂ ⟨f₂⟩
    obtain rfl := (h' X j₂).elim f₁ f₂
    rfl
  constructor

instance (U : C) : (diagCostructuredArrowForget X U).Final := by
  dsimp [diagCostructuredArrowForget]
  refine .of_discrete (fun V ↦ ?_) fun V i ↦ ?_
  · refine ⟨V.hom.unop ≫ V.left.unop.hom, ⟨CostructuredArrow.homMk (Over.homMk V.hom.unop).op⟩, ?_⟩
    intro f ⟨g⟩
    simp [← CostructuredArrow.w g, dsimp% Over.w g.left.unop]
  · dsimp
    refine ⟨fun a b ↦ ?_⟩
    ext
    apply Quiver.Hom.unop_inj
    ext
    apply Quiver.Hom.op_inj
    have := CostructuredArrow.w a
    dsimp at this
    simp only [Category.comp_id] at this
    erw [this]
    have := CostructuredArrow.w b
    dsimp at this
    simp only [Category.comp_id] at this
    erw [this]

variable [∀ (G : (Over X)ᵒᵖ ⥤ Type w), Functor.HasPointwiseLeftKanExtension (Over.forget X).op G]
variable [LocallySmall.{w} (Over X)]

def asdfasdf (U : Over X) :
    (Over.forget X).op.lan.obj (shrinkYoneda.{w}.obj U) ≅ shrinkYoneda.{w}.obj U.left :=
  sorry

noncomputable
def toOver : (Over.forget X).op.lan ⟶ (Functor.const _).obj (shrinkYoneda.{w}.obj X) := by
  letI R := (Functor.whiskeringLeft _ _ (Type w)).obj (Over.forget X).op
  letI u : 𝟭 _ ⟶ (Functor.const _).obj (shrinkYoneda.{w}.obj X) ⋙ R := by
    refine { app := ?_, naturality := ?_ }
    · intro F
      refine { app := ?_, naturality := ?_ }
      · intro U _
        apply shrinkYonedaObjObjEquiv.invFun
        dsimp
        exact U.unop.hom
      · intro U V g
        ext
        dsimp [R]
        rw [shrinkYoneda_obj_map_shrinkYonedaObjObjEquiv_symm]
        simpa using (Over.w g.unop).symm
    · cat_disch
  exact (Functor.leftUnitor _).inv ≫ Functor.whiskerRight u (Over.forget X).op.lan ≫
    (Functor.associator _ _ _).hom ≫ Functor.whiskerLeft _
    ((Over.forget X).op.lanAdjunction _).counit

noncomputable
def asdf :
    (Over X)ᵒᵖ ⥤ Type w ≌ Over (shrinkYoneda.{w}.obj X) where
  functor := Over.lift (Over.forget X).op.lan <| toOver
    --refine { app := ?_, naturality := ?_ }
    --· intro F
    --  dsimp
    --  exact (Over.forget X).op.lan.map
    --    ((Functor.isTerminalConst _ Limits.Types.isTerminalPUnit).from _) ≫
    --    (by dsimp)
    --  sorry
    --· sorry
  inverse :=
    shrinkYoneda ⋙ (Functor.whiskeringLeft _ _ _).obj (Over.post shrinkYoneda).op
  unitIso := by
    refine NatIso.ofComponents ?_ ?_
    · intro F
      dsimp
      refine NatIso.ofComponents ?_ ?_
      · intro ⟨U⟩
        refine Equiv.toIso ?_
        dsimp
        refine Equiv.trans ?_ shrinkYonedaObjObjEquiv.symm
        dsimp
        refine Equiv.trans shrinkYonedaEquiv.symm ?_
        --refine ?_ ≪≫ Equiv.toIso shrinkYonedaObjObjEquiv
        refine { toFun := ?_
                 invFun := ?_
                 left_inv := sorry
                 right_inv := sorry }
        · intro t
          refine Over.homMk ?_ ?_
          · dsimp
            refine { app := ?_, naturality := ?_ }
            · intro V x
              sorry
            · sorry
          · sorry
        · sorry
      · sorry
    · sorry
  counitIso := by
    refine Yoneda.fullyFaithful.preimageIso ?_
    dsimp
    sorry
    --refine NatIso.ofComponents ?_ ?_
    --· intro F
    --  dsimp
    --  refine Over.isoMk ?_ ?_
    --  · dsimp
    --    refine Iso.mk ?_ ?_ ?_ ?_
    --    · apply (adj.homEquiv _ _).invFun
    --      dsimp
    --      refine ⟨?_, ?_⟩
    --      · intro U
    --        dsimp
    --        intro x
    --        apply (shrinkYonedaEquiv (P := F.left) (X := U.unop.left)).toFun
    --        apply shrinkYonedaObjObjEquiv.toFun at x
    --        dsimp at x
    --        exact x.left
    --      · sorry
    --    · refine .mk ?_ ?_
    --      · intro U
    --        dsimp
    --        sorry
    --      · sorry
    --    · sorry
    --    · sorry
    --  · sorry
    --· dsimp
    --  sorry
  functor_unitIso_comp := sorry

end CategoryTheory
