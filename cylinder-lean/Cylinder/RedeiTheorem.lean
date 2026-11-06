import Cylinder.MainTheorem
import Cylinder.RedeiGroups
import Cylinder.RedeiFactors
import Cylinder.RedeiPlaneMoment
import Cylinder.RedeiFactorPlaneCounts

/-! Rédei's normalized factorization conjecture in dimension three.
The group statement below is the manuscript's Theorem 1.2. -/
namespace Cylinder.Redei
open Geometry

/-- The coordinate form. The hypothesis on A and B says that addition
is a bijection from A × B onto the whole vector space. -/
theorem coordinate_factorization (p : ℕ) [Fact p.Prime]
    (A B : Finset (Point p)) (hA : 0 ∈ A) (hB : 0 ∈ B)
    (h : AddSubgroup.IsComplement (A : Set (Point p)) B) :
    Submodule.span (ZMod p) (A : Set (Point p)) ≠ ⊤ ∨
    Submodule.span (ZMod p) (B : Set (Point p)) ≠ ⊤ := by
  apply of_spanning_prime_factor _ A B hA hB h
  intro S T hS hT htile hs ht hspan
  have hdiv := pDivisible_of_spanning_factor p hs ht hS htile hspan
  have hcyl := MainTheorem.strongCylinderConjecture p T ht hdiv
  exact (RedeiPlaneMoment.proper_span_of_cylindrical_factor hs hS hT htile hcyl).resolve_left
    (not_not_intro hspan)

/-- In every normalized factorization of an elementary abelian group of order
p³, at least one factor generates a proper subgroup. -/
theorem redei_factorization (p : ℕ) [Fact p.Prime] {G : Type*}
    [AddCommGroup G] [Finite G] (hcard : Nat.card G = p ^ 3)
    (helem : ∀ x : G, x ≠ 0 → addOrderOf x = p)
    (A B : Set G) (hA : 0 ∈ A) (hB : 0 ∈ B)
    (htile : AddSubgroup.IsComplement A B) :
    AddSubgroup.closure A ≠ ⊤ ∨ AddSubgroup.closure B ≠ ⊤ := by
  classical
  let _ := Fintype.ofFinite G
  have hexp (x : G) : p • x = 0 := by
    by_cases hx : x = 0
    · simp [hx]
    · rw [← helem x hx, addOrderOf_nsmul_eq_zero]
  have hout := group_factorization_of_coordinates (coordinate_factorization p) hcard hexp
    A.toFinset B.toFinset (by simpa using hA) (by simpa using hB) (by simpa using htile)
  simpa using hout

end Cylinder.Redei


#print axioms Cylinder.Redei.pDivisible_of_spanning_factor
#print axioms Cylinder.Redei.coordinate_factorization
#print axioms Cylinder.Redei.redei_factorization
