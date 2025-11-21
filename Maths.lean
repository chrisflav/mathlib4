import Mathlib.RepresentationTheory.Basic
import Maths.Attribute

@[simp]
lemma LinearMap.ker_eq_top_iff {R M N : Type*} [Semiring R] [AddCommMonoid M]
    [Module R M] [AddCommMonoid N] [Module R N]
    {F : Type*} [FunLike F M N] [LinearMapClass F R M N]
    {f : F} :
    LinearMap.ker f = ⊤ ↔ ∀ x, f x = 0 := by
  simp [Submodule.eq_top_iff']

@[simp]
lemma LinearMap.ker_eq_bot_iff {R M N : Type*} [Semiring R] [AddCommMonoid M]
    [Module R M] [AddCommMonoid N] [Module R N]
    {F : Type*} [FunLike F M N] [LinearMapClass F R M N]
    {f : F} :
    LinearMap.ker f = ⊥ ↔ ∀ x, f x = 0 → x = 0 := by
  simp [Submodule.eq_bot_iff]

@[grind]
alias ⟨LinearMap.zero_of_map_zero, _⟩ := LinearMap.ker_eq_bot_iff

lemma Submodule.eq_zero_of_mem {R M : Type*} [Semiring R] [AddCommMonoid M]
    [Module R M] (p : Submodule R M) (hp : p = ⊥) (x : M) (hx : x ∈ p) :
    x = 0 := by
  simpa [hp] using hx

@[grind ←]
lemma Function.Bijective.of_injective_of_surjective {α β : Type*}
    (f : α → β) (hf : f.Injective) (hg : f.Surjective) :
    f.Bijective := ⟨hf, hg⟩

syntax (name := concludeTac) "conclude" : tactic

macro "conclude" : tactic =>
  `(tactic|grind)

macro "contradiction" : tactic =>
  `(tactic|grind)

macro "simplify" : tactic =>
  `(tactic|simp at *)

macro "suffices" " : " t:term : tactic =>
  `(tactic|suffices $t by conclude)

macro "take " x:ident hx:ident " from " " : " t:term : tactic =>
  `(tactic|obtain ⟨$x, $hx⟩ : $t := by observe : $t; assumption)

example [Nontrivial V] [AddCommGroup V] : True := by
  take x hx from : ∃ (x : V), x ≠ 0
  trivial

declare_syntax_cat variable_abbrev

syntax "Field" : variable_abbrev
syntax "Group" : variable_abbrev
syntax "VectorSpace" ident : variable_abbrev
syntax term : variable_abbrev

open Lean Elab Command in
elab "fix" " ( " X:ident " : " t:variable_abbrev " ) " : command => do
  if !(← isInitialised) then
    elabCommand (← liftMacroM `(open Function))
    elabCommand (← liftMacroM `(set_option linter.unusedVariables false))
    elabCommand (← liftMacroM `(set_option linter.unusedSectionVars false))
    let name : TSyntax `ident :=
      ⟨Syntax.ident default default `Representation []⟩
    elabCommand (← liftMacroM `(namespace $name))
    -- elabNamespace (.ident default default `Representation [])
    -- logInfo "hi"
    markInitialised
  let stx ← liftMacroM <| match t with
  | `(variable_abbrev|Group) =>
      `(variable {$X : Type} [_root_.Group $X])
  | `(variable_abbrev|Field) =>
      `(variable {$X : Type} [_root_.Field $X])
  | `(variable_abbrev|VectorSpace $k:ident) =>
      `(variable {$X : Type} [AddCommGroup $X] [Module $k $X] [Nontrivial $X])
  | `(variable_abbrev|$t:term) =>
      `(variable {$X : $t})
  | _ => Lean.Macro.throwUnsupported
  elabCommand stx

fix (k : Field)

notation "Rep" => Representation

namespace Representation

variable {k M N : Type} [CommRing k] [AddCommGroup M] [AddCommGroup N]
  [Module k M] [Module k N]
  {G : Type} [_root_.Group G]

@[ext]
structure Hom (ρ : Representation k G M) (ρ' : Representation k G N) extends M →ₗ[k] N where
  invariant' : ∀ g x, toFun (ρ g x) = ρ' g (toFun x)

notation:25 ρ " →ᵣ " ρ':0 => Hom ρ ρ'

variable {ρ : Representation k G M} {ρ' : Representation k G N}

instance : FunLike (ρ →ᵣ ρ') M N where
  coe f := f.toFun
  coe_injective' _ _ := Hom.ext

@[ext high]
lemma Hom.ext_apply (f g : ρ →ᵣ ρ') (h : ∀ x, f x = g x) : f = g := by
  ext
  apply h

instance : LinearMapClass (ρ →ᵣ ρ') k M N where
  map_add f := f.map_add
  map_smulₛₗ f := f.map_smul

lemma Hom.invariant (f : ρ →ᵣ ρ') (g : G) (x : M) :
    f (ρ g x) = ρ' g (f x) :=
  f.invariant' g x

instance : Zero (ρ →ᵣ ρ') where
  zero := {
    toLinearMap := 0
    invariant' := by simp
  }

@[simp]
lemma zero_apply (x : M) : (0 : ρ →ᵣ ρ') x = 0 := rfl

@[ext]
structure Subrepresentation (ρ : Representation k G M) where
  submodule : Submodule k M
  invariant : ∀ (g : G) (x : M), x ∈ submodule → ρ g x ∈ submodule

notation "SubRep" => Subrepresentation

instance : SetLike (Subrepresentation ρ) M where
  coe P := P.submodule
  coe_injective' P G hPG := Subrepresentation.ext
    (SetLike.coe_injective hPG)

instance : Zero (Subrepresentation ρ) where
  zero := {
    submodule := ⊥
    invariant _ _ _ := by simp_all
  }

instance : Top (Subrepresentation ρ) where
  top := {
    submodule := ⊤
    invariant _ _ _ := by simp_all
  }

@[simps]
def Hom.ker (f : ρ →ᵣ ρ') : Subrepresentation ρ where
  submodule := LinearMap.ker f
  invariant g x hx := by
    simplify
    rw [f.invariant, hx]
    simplify

@[grind]
lemma injective_of_ker_eq_zero (f : ρ →ᵣ ρ') (hf : f.ker = 0) :
    Injective f := by
  have : LinearMap.ker f.toLinearMap = ⊥ := congr($(hf).submodule)
  exact f.toLinearMap.ker_eq_bot.mp this

@[simps]
def Hom.range (f : ρ →ᵣ ρ') : Subrepresentation ρ' where
  submodule := LinearMap.range f
  invariant g y hy := by
    simplify
    obtain ⟨x, hx⟩ := hy
    use ρ g x
    rw [f.invariant, hx]

@[grind]
lemma surjective_of_range_eq_top (f : ρ →ᵣ ρ') (hf : f.range = ⊤) :
    Surjective f := by
  have : LinearMap.range f.toLinearMap = ⊤ := congr($(hf).submodule)
  exact LinearMap.range_eq_top.mp this

lemma mem_ker_iff (f : ρ →ᵣ ρ') (x : M) :
    x ∈ f.ker ↔ f x = 0 := .rfl

@[grind]
lemma ker_ne_top_of_ne_zero (f : ρ →ᵣ ρ') (hf : f ≠ 0) :
    f.ker ≠ ⊤ := by
  intro h
  apply hf
  ext x
  simp only [zero_apply]
  rw [← mem_ker_iff, h]
  trivial

@[grind]
lemma ne_zero_of_mem (P : Subrepresentation ρ) (x : M) (hmem : x ∈ P)
    (hx : x ≠ 0) :
    P ≠ 0 := by
  rintro rfl
  apply hx
  exact hmem

@[grind]
lemma map_mem_range (f : ρ →ᵣ ρ') (x : M) :
    f x ∈ f.range :=
  ⟨x, rfl⟩

end Representation

set_option linter.unusedVariables false


⟶ →
