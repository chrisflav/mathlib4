import Maths
namespace Representation

fix (k : Field)
fix (V : VectorSpace k)
fix (W : VectorSpace k)
fix (G : Group)
fix (ρ : Rep k G V)
fix (ρ' : Rep k G W)

def Irreducible (ρ : Rep k G V) : Prop :=
  Nontrivial V ∧ ∀ (P : SubRep ρ), P = ⊤ ∨ P = 0

lemma schur (f : ρ →ᵣ ρ') (h1 : Irreducible ρ) (h2 : Irreducible ρ')
    (h : f ≠ 0) :
    Bijective f := by
  have : Injective f := by
    suffices : f.ker = 0
    have : f.ker = ⊤ ∨ f.ker = 0 := h1.right f.ker
    observe : f.ker ≠ ⊤
    conclude
  have : Surjective f := by
    suffices : f.range = ⊤
    have : f.range = ⊤ ∨ f.range = 0 := h2.right f.range
    suffices : f.range ≠ 0
    take x hx from : ∃ (x : V), x ≠ 0
    observe : f x ≠ 0
    observe : f x ∈ f.range
    conclude
  conclude
