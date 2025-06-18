import Mathlib

open Lean Meta Elab Tactic

def specializeExpr (pf : Expr) (type? : Option Expr) : MetaM Expr :=
  return pf

elab "specialize_of% " t:term " with " p:term : term => do
  -- trick to disable introducing implicit variables as metavariables
  let t : TSyntax `term ← `(@$t)
  logInfo s!"{t}"
  let e ← Term.elabTerm t none
  logInfo s!"{repr e}"
  let ty ← inferType e
  forallTelescope ty fun fvars body => do
    logInfo s!"{fvars}, {← ppExpr body}, {← ppExpr ty}"
    let appE : Expr := mkAppN e fvars
    let mvar ← mkFreshExprMVar none
    let tp : Expr := .forallE `x body mvar .default
    let pE ← Term.elabTerm p tp
    let congred : Expr := mkApp pE appE
    mkLambdaFVars fvars congred

structure Foo where
  foo : Nat → Nat
  hfoo : foo = 3

def specialFoo : Foo := ⟨3, rfl⟩

lemma Foo.id (x : Foo) : specialFoo = x := by
  sorry

example (x : Foo) : specialFoo.foo = x.foo :=
  congr($(Foo.id x).foo)

example (x : Foo) : specialFoo.foo = x.foo := by
  have := specialize_of% Foo.id with
    fun myspecialname ↦ congr($(myspecialname).foo)
  rw [specialize_of% Foo.id with
    fun myspecialname ↦ congr($(myspecialname).foo)]

example (x : Foo) (y : Nat) : specialFoo.foo y = x.foo y := by
  have := specialize_of% Foo.id with
    fun myspecialname z ↦ congr($(myspecialname).foo z)
  exact this x y

open CategoryTheory

axiom C : Type 0
axiom inst : Category.{0} C
axiom X : C
axiom Y : C
axiom Z : C

attribute [instance] inst

axiom f : X ⟶ Y
axiom g : Y ⟶ Z
axiom h : X ⟶ Z

axiom foo : f ≫ g = h

example : f ≫ g ≫ 𝟙 _ = h ≫ 𝟙 _ := by
  have := specialize_of% foo with
    fun myspecialname (Z : C) (u : _ ⟶ Z) ↦ congr($(myspecialname) ≫ u)
  sorry


section

universe u v w t

def NatTrans.naturality' := (@NatTrans.naturality)

#check NatTrans.naturality'

variable {C : Type} {D : Type} [Category.{0} C] [Category.{0} D] (F G : C ⥤ D)
  (α : F ⟶ G)

lemma myfoo ⦃X Y : C⦄ (f : X ⟶ Y) (Z : D) (h : G.obj Y ⟶ Z) :
    F.map f ≫ α.app Y ≫ h = α.app X ≫ G.map f ≫ h := by
  have := specialize_of% NatTrans.naturality'.{0, 0, 0, 0} with
    fun myspecialname Z (u : _ ⟶ Z) ↦ congr($(myspecialname) ≫ u)
  have := this α f Z h
  simp_rw [Category.assoc] at this
  exact this

end
