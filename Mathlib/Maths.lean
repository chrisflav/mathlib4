import Mathlib

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

declare_syntax_cat variable_abbrev

syntax "Field" : variable_abbrev
syntax "Group" : variable_abbrev
syntax "VectorSpace" ident : variable_abbrev
syntax term : variable_abbrev

macro "fix" " ( " X:ident " : " t:variable_abbrev " ) " : command =>
  match t with
  | `(variable_abbrev|Group) =>
      `(variable {$X : Type} [_root_.Group $X])
  | `(variable_abbrev|Field) =>
      `(variable {$X : Type} [_root_.Field $X])
  | `(variable_abbrev|VectorSpace $k:ident) =>
      `(variable {$X : Type} [AddCommGroup $X] [Module $k $X])
  | `(variable_abbrev|$t:term) =>
      `(variable {$X : $t})
  | _ => Lean.Macro.throwUnsupported

namespace Representation

variable {k M N : Type} [CommSemiring k] [AddCommMonoid M] [AddCommMonoid N]
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

end Representation
