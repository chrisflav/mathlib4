import Maths
namespace Representation

fix (k : Field)
fix (M : VectorSpace k)
fix (N : VectorSpace k)
fix (G : Group)

structure Subrepresentation (ρ : Representation k G M) where
  submodule : Submodule k M
  invariant : ∀ (g : G) (x : M), x ∈ submodule → ρ g x ∈ submodule

fix (ρ : Representation k G M)
fix (ρ' : Representation k G N)

def Irreducible (ρ : Representation k G M) : Prop :=
  Nontrivial M ∧ ∀ (P : Subrepresentation ρ), P.submodule = ⊤ ∨ P.submodule = ⊥

@[simp]
def Hom.ker (f : ρ →ᵣ ρ') : Subrepresentation ρ where
  submodule := LinearMap.ker f
  invariant g x hx := by
    simplify
    rewrite [f.invariant, hx]
    simplify

@[simp]
def Hom.range (f : ρ →ᵣ ρ') : Subrepresentation ρ' where
  submodule := LinearMap.range f
  invariant g y hy := by
    obtain ⟨x, rfl⟩ := hy
    use ρ g x
    rw [f.invariant]

lemma schur (ρ : Representation k G M) (ρ' : Representation k G N)
      (hρ : Irreducible ρ) (hρ' : Irreducible ρ') (φ : ρ →ᵣ ρ') :
    Bijective φ ∨ φ = 0 := by
  obtain h | h := hρ.right φ.ker
  · right
    ext x
    simplify
    apply h
  · left
    observe : Injective φ
    obtain hrange_top | hrange_bot := hρ'.right φ.range
    · observe : Surjective φ
      conclude
    · have : Nontrivial M := hρ.left
      observe : ∃ (x : M), x ≠ 0
      obtain ⟨x, hx⟩ := this
      simplify
      observe : φ x ∈ LinearMap.range φ
      observe : φ x = 0
      contradiction

end Representation
