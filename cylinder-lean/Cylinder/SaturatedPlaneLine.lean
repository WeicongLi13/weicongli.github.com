module

public import Cylinder.GcdGraphSelection
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Finiteness
public import Mathlib.RingTheory.Polynomial.Basic
public import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Actual regular line selection for saturated plane ideals

Saturation is expressed using powers of the actual irrelevant ideal. It
excludes associated primes containing all three variables. A dual functional
on each associated-prime quotient produces a finite nonzero point witness.
Avoiding these witnesses gives a regular line for the actual quotient ring,
including nonreduced ideals.
-/

@[expose] public section
noncomputable section
namespace Cylinder.SaturatedPlaneLine
open MvPolynomial
open Cylinder.HilbertEvaluation Cylinder.PlaneBinaryReduction
open Cylinder.PrimitivePlaneSystem Cylinder.GcdGraphSelection
variable {K : Type*} [Field K]

def irrelevant : Ideal (PlaneRing K) := Ideal.span (Set.range (X : Fin 3 → PlaneRing K))

/-- The ordinary irrelevant-ideal power saturation condition. -/
def Saturated (J : Ideal (PlaneRing K)) : Prop :=
  ∀ P : PlaneRing K, ∀ n : ℕ,
    (∀ Q ∈ irrelevant (K := K) ^ n, Q * P ∈ J) → P ∈ J

theorem saturated_of_variable_multiples (J : Ideal (PlaneRing K)) (hJ : Saturated J)
    (P : PlaneRing K) (hP : ∀ i : Fin 3, X i * P ∈ J) : P ∈ J := by
  have hle : irrelevant (K := K) ≤ J.colon {P} := by
    apply Ideal.span_le.mpr
    rintro Q ⟨i, rfl⟩
    change X i ∈ J.colon {P}
    rw [Submodule.mem_colon_singleton, smul_eq_mul]
    simpa only [mul_comm] using hP i
  apply hJ P 1
  intro Q hQ
  have hm := hle (by simpa using hQ)
  rw [Submodule.mem_colon_singleton, smul_eq_mul] at hm
  exact hm

/-- A genuine associated prime of the quotient cannot contain every variable. -/
theorem associatedPrime_omits_variable (J : Ideal (PlaneRing K)) (hJ : Saturated J)
    (P : Ideal (PlaneRing K)) (hP : P ∈ associatedPrimes (PlaneRing K) ((PlaneRing K) ⧸ J)) :
    ∃ i : Fin 3, X i ∉ P := by
  by_contra! hvars
  obtain ⟨hprime, x, hx⟩ := isAssociatedPrime_iff.mp hP
  have hx0 : x ≠ 0 := by
    intro hz
    apply hprime.ne_top
    rw [hx, hz, Submodule.colon_singleton_zero]
  obtain ⟨A, rfl⟩ := Ideal.Quotient.mk_surjective x
  have hA : A ∈ J := saturated_of_variable_multiples J hJ A (by
    intro i
    have hi := hvars i
    rw [hx, Submodule.mem_colon_singleton, Submodule.mem_bot] at hi
    change X i • (Submodule.Quotient.mk A : (PlaneRing K) ⧸ J) = 0 at hi
    rw [← Submodule.Quotient.mk_smul] at hi
    change Ideal.Quotient.mk J (X i * A) = 0 at hi
    exact Ideal.Quotient.eq_zero_iff_mem.mp hi)
  exact hx0 (Ideal.Quotient.eq_zero_iff_mem.mpr hA)

/-- A linear-form membership witness in a true quotient ideal. -/
theorem quotient_linear_witness (P : Ideal (PlaneRing K))
    (hP : ∃ i : Fin 3, X i ∉ P) :
    ∃ v : Fin 3 → K, v ≠ 0 ∧
      ∀ L : PlaneRing K, L.IsHomogeneous 1 → L ∈ P → eval v L = 0 := by
  obtain ⟨i, hi⟩ := hP
  have hm : Ideal.Quotient.mk P (X i) ≠ 0 := by
    intro hz
    exact hi (Ideal.Quotient.eq_zero_iff_mem.mp hz)
  obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_ne_zero K hm
  let ψ : Module.Dual K (PlaneRing K) := φ.comp (Ideal.Quotient.mkₐ K P).toLinearMap
  let v : Fin 3 → K := fun j => ψ (X j)
  have hv : v ≠ 0 := by
    intro hz
    apply hφ
    exact congrFun hz i
  refine ⟨v, hv, ?_⟩
  intro L hL hLP
  obtain ⟨c, hc⟩ := linear_form_expansion L hL
  have hscalar (a : K) (j : Fin 3) : ψ (C a * X j) = a * v j := by
    rw [← smul_eq_C_mul, map_smul]
    rfl
  have he : eval v L = ψ L := by
    rw [hc]
    simp only [map_add, map_mul, eval_C, eval_X, hscalar]
  rw [he]
  have hzero : Ideal.Quotient.mk P L = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hLP
  change φ (Ideal.Quotient.mk P L) = 0
  rw [hzero, map_zero]

/-- Finitely many actual nonzero representatives witness all associated primes. -/
theorem associatedPrime_witnesses (J : Ideal (PlaneRing K)) (hJ : Saturated J) :
    ∃ v : associatedPrimes (PlaneRing K) ((PlaneRing K) ⧸ J) → Fin 3 → K,
      (∀ i, v i ≠ 0) ∧
        ∀ i L, L.IsHomogeneous 1 → L ∈ i.val → eval (v i) L = 0 := by
  choose v hv hmem using fun i : associatedPrimes (PlaneRing K) ((PlaneRing K) ⧸ J) =>
    quotient_linear_witness i.val (associatedPrime_omits_variable J hJ i.val i.property)
  exact ⟨v, hv, hmem⟩

theorem colon_eq_of_associatedPrime_avoidance (J : Ideal (PlaneRing K))
    (L : PlaneRing K)
    (hL : ∀ P ∈ associatedPrimes (PlaneRing K) ((PlaneRing K) ⧸ J), L ∉ P) :
    J.colon {L} = J := by
  have hregular : ∀ A : PlaneRing K, L * A ∈ J → A ∈ J := by
    intro A hLA
    by_contra hA
    have hmk : Ideal.Quotient.mk J A ≠ 0 := by
      intro hz
      exact hA (Ideal.Quotient.eq_zero_iff_mem.mp hz)
    have hzero : L • Ideal.Quotient.mk J A = 0 := by
      change L • (Submodule.Quotient.mk A : (PlaneRing K) ⧸ J) = 0
      rw [← Submodule.Quotient.mk_smul]
      change Ideal.Quotient.mk J (L * A) = 0
      exact Ideal.Quotient.eq_zero_iff_mem.mpr hLA
    have hz : L ∈ ⋃ P ∈ associatedPrimes (PlaneRing K) ((PlaneRing K) ⧸ J), (P : Set (PlaneRing K)) := by
      rw [biUnion_associatedPrimes_eq_zero_divisors]
      exact ⟨Ideal.Quotient.mk J A, hmk, hzero⟩
    obtain ⟨P, hP⟩ := Set.mem_iUnion.mp hz
    obtain ⟨hpass, hLP⟩ := Set.mem_iUnion.mp hP
    exact hL P hpass hLP
  ext A
  rw [Submodule.mem_colon_singleton, smul_eq_mul]
  exact ⟨fun h => hregular A (by simpa only [mul_comm] using h), fun h => J.mul_mem_right L h⟩

/-- Genuine simultaneous regular-line and gcd selection for a saturated plane
ideal; neither colon regularity nor generic-line gcd preservation is assumed. -/
theorem exists_graph_regular_preserving_gcds [Infinite K]
    (J : Ideal (PlaneRing K)) (hJ : Saturated J) {S : Type*} [Fintype S]
    (I : S → Type*) [∀ s, Fintype (I s)] (f : ∀ s, I s → PlaneRing K) (d : S → ℕ)
    (hhom : ∀ s i, (f s i).IsHomogeneous (d s)) (hf : ∀ s, ∃ i, f s i ≠ 0) :
    ∃ a b : K, J.colon {graphEquation a b} = J ∧
      ∀ s, graphRestriction a b (familyGcd (f s)) ≠ 0 ∧
        (graphRestriction a b (familyGcd (f s))).totalDegree = (familyGcd (f s)).totalDegree ∧
          ∀ D : BinaryRing K,
            (∀ i, D ∣ graphRestriction a b (f s i)) ↔ D ∣ graphRestriction a b (familyGcd (f s)) := by
  let T := associatedPrimes (PlaneRing K) ((PlaneRing K) ⧸ J)
  let : Fintype T := (associatedPrimes.finite (PlaneRing K) ((PlaneRing K) ⧸ J)).fintype
  obtain ⟨v, hv, hwitness⟩ := associatedPrime_witnesses J hJ
  obtain ⟨a, b, havoid, hgcd⟩ := exists_graph_preserving_gcds_avoiding I f d hhom hf v hv
  refine ⟨a, b, colon_eq_of_associatedPrime_avoidance J _ ?_, hgcd⟩
  intro P hP hLP
  exact havoid ⟨P, hP⟩ (hwitness ⟨P, hP⟩ _ (graphEquation_homogeneous a b) hLP)

end Cylinder.SaturatedPlaneLine
end
