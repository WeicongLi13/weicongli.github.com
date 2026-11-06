module

public import Cylinder.CompleteIntersectionKoszul
public import Cylinder.IntersectionBinaryGeneration
public import Mathlib.Algebra.MvPolynomial.Division
public import Mathlib.RingTheory.MvPolynomial.Basic

/-!
# The actual finite binary complete-intersection quotient

Binary cofactor generation proves that every form of degree `e+t-1`
belongs to `(F,G)`. A submonomial argument reduces every polynomial
modulo this ideal to total degree at most `e+t-2`. Thus the real quotient
ring is finite dimensional, with no finiteness or pairing hypothesis.
-/

@[expose] public section

noncomputable section

namespace Cylinder.CompleteIntersectionFinite

open MvPolynomial Module Cylinder.CompleteIntersectionKoszul
open Cylinder.IntersectionBinaryGeneration Cylinder.PlaneBinaryReduction
open scoped BigOperators Classical

variable {K : Type*} [Field K]

theorem binary_subExponent (α : Fin 2 →₀ ℕ) (r : ℕ) (hr : r ≤ α.degree) :
    ∃ β : Fin 2 →₀ ℕ, β ≤ α ∧ β.degree = r := by
  let k := min (α 0) r
  let β : Fin 2 →₀ ℕ := Finsupp.single 0 k + Finsupp.single 1 (r - k)
  have hα : α.degree = α 0 + α 1 := by rw [Finsupp.degree_eq_sum, Fin.sum_univ_two]
  have hk : k ≤ r := Nat.min_le_right _ _
  have hkr : r - k ≤ α 1 := by
    by_cases hmin : α 0 ≤ r
    · dsimp [k]
      rw [Nat.min_eq_left hmin]
      omega
    · dsimp [k]
      rw [Nat.min_eq_right (le_of_not_ge hmin)]
      simp
  refine ⟨β, ?_, ?_⟩
  · intro i
    fin_cases i
    · simpa [β, Finsupp.single_apply, k] using Nat.min_le_left (α 0) r
    · simpa [β, Finsupp.single_apply] using hkr
  · rw [Finsupp.degree_eq_sum, Fin.sum_univ_two]
    simp only [β, Finsupp.add_apply, Finsupp.single_apply]
    norm_num
    omega

theorem homogeneous_bound_mem_ideal
    (F G : BinaryRing K) (e t : ℕ) (he : 0 < e) (ht : 0 < t)
    (hF : F.IsHomogeneous e) (hG : G.IsHomogeneous t) (hF0 : F ≠ 0) (hG0 : G ≠ 0)
    (hcop : IsRelPrime F G) (P : BinaryRing K) (hP : P.IsHomogeneous (e + t - 1)) :
    P ∈ equationsIdeal F G := by
  have hpos : ∀ i : Fin 2, 0 < (![e, t] i) := by intro i; fin_cases i <;> assumption
  have hhom : ∀ i : Fin 2, (![F, G] i).IsHomogeneous (![e, t] i) := by
    intro i; fin_cases i <;> assumption
  have hnonzero : ∀ i : Fin 2, ![F, G] i ≠ 0 := by intro i; fin_cases i <;> assumption
  have hpair : Pairwise (fun i j : Fin 2 => IsRelPrime (![F, G] i) (![F, G] j)) := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · exact False.elim (hij rfl)
    · exact hcop
    · exact hcop.symm
    · exact False.elim (hij rfl)
  obtain ⟨A, hA, hPexp⟩ := exists_binary_cofactor_expansion ![F, G] ![e, t]
    hpos hnonzero hpair hhom P (by simpa [degreeSum, Fin.sum_univ_two] using hP)
  rw [hPexp]
  apply Ideal.sum_mem
  intro i _
  apply Ideal.mul_mem_left
  fin_cases i
  · change IntersectionResolution.cofactor ![F, G] (0 : Fin 2) ∈ equationsIdeal F G
    apply Ideal.mem_of_dvd _ (IntersectionResolution.dvd_other_cofactor ![F, G]
      (1 : Fin 2) 0 (by decide))
    exact Ideal.subset_span (Set.mem_insert_of_mem F (Set.mem_singleton G))
  · change IntersectionResolution.cofactor ![F, G] (1 : Fin 2) ∈ equationsIdeal F G
    apply Ideal.mem_of_dvd _ (IntersectionResolution.dvd_other_cofactor ![F, G]
      (0 : Fin 2) 1 (by decide))
    exact Ideal.subset_span (Set.mem_insert F {G})

theorem high_monomial_mem_ideal
    (F G : BinaryRing K) (e t : ℕ) (he : 0 < e) (ht : 0 < t)
    (hF : F.IsHomogeneous e) (hG : G.IsHomogeneous t) (hF0 : F ≠ 0) (hG0 : G ≠ 0)
    (hcop : IsRelPrime F G) (α : Fin 2 →₀ ℕ) (c : K) (hα : e + t - 1 ≤ α.degree) :
    monomial α c ∈ equationsIdeal F G := by
  obtain ⟨β, hβα, hβ⟩ := binary_subExponent α (e + t - 1) hα
  have hβI := homogeneous_bound_mem_ideal F G e t he ht hF hG hF0 hG0 hcop
    (monomial β 1) (isHomogeneous_monomial _ hβ)
  have hdvd : (monomial β (1 : K) : BinaryRing K) ∣ monomial α c :=
    monomial_dvd_monomial.mpr ⟨Or.inr hβα, one_dvd _⟩
  obtain ⟨Q, hQ⟩ := hdvd
  rw [hQ]
  exact Ideal.mul_mem_right _ _ hβI

theorem exists_low_degree_representative
    (F G : BinaryRing K) (e t : ℕ) (he : 0 < e) (ht : 0 < t)
    (hF : F.IsHomogeneous e) (hG : G.IsHomogeneous t) (hF0 : F ≠ 0) (hG0 : G ≠ 0)
    (hcop : IsRelPrime F G) (P : BinaryRing K) :
    ∃ Q : BinaryRing K, Q.totalDegree ≤ e + t - 2 ∧
      Ideal.Quotient.mk (equationsIdeal F G) Q = Ideal.Quotient.mk (equationsIdeal F G) P := by
  let Q : BinaryRing K := ∑ α ∈ P.support.filter (fun α => α.degree ≤ e + t - 2),
    monomial α (P.coeff α)
  let H : BinaryRing K := ∑ α ∈ P.support.filter (fun α => ¬ α.degree ≤ e + t - 2),
    monomial α (P.coeff α)
  have hQdeg : Q.totalDegree ≤ e + t - 2 := by
    apply totalDegree_finsetSum_le
    intro α hα
    apply (totalDegree_monomial_le α _).trans
    exact (Finset.mem_filter.mp hα).2
  have hHI : H ∈ equationsIdeal F G := by
    apply Ideal.sum_mem
    intro α hα
    apply high_monomial_mem_ideal F G e t he ht hF hG hF0 hG0 hcop
    have hgt := (Finset.mem_filter.mp hα).2
    omega
  have hsplit : Q + H = P :=
    (Finset.sum_filter_add_sum_filter_not P.support (fun α => α.degree ≤ e + t - 2)
      (fun α => monomial α (P.coeff α))).trans (support_sum_monomial_coeff P)
  have hHz : Ideal.Quotient.mk (equationsIdeal F G) H = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hHI
  refine ⟨Q, hQdeg, ?_⟩
  rw [← hsplit, map_add, hHz, add_zero]

def filteredQuotientMap (F G : BinaryRing K) (N : ℕ) :
    restrictTotalDegree (Fin 2) K N →ₗ[K] QuotientRing F G :=
  (Ideal.Quotient.mkₐ K (equationsIdeal F G)).toLinearMap.comp (restrictTotalDegree (Fin 2) K N).subtype

theorem filteredQuotientMap_surjective
    (F G : BinaryRing K) (e t : ℕ) (he : 0 < e) (ht : 0 < t)
    (hF : F.IsHomogeneous e) (hG : G.IsHomogeneous t) (hF0 : F ≠ 0) (hG0 : G ≠ 0)
    (hcop : IsRelPrime F G) : Function.Surjective (filteredQuotientMap F G (e + t - 2)) := by
  intro z
  obtain ⟨P, rfl⟩ := Ideal.Quotient.mk_surjective z
  obtain ⟨Q, hQdeg, hQ⟩ := exists_low_degree_representative F G e t he ht hF hG hF0 hG0 hcop P
  exact ⟨⟨Q, (mem_restrictTotalDegree _ _ _).mpr hQdeg⟩, hQ⟩

/-- Finiteness follows from the proved finite degree cutoff of the actual quotient. -/
theorem quotient_finiteDimensional
    (F G : BinaryRing K) (e t : ℕ) (he : 0 < e) (ht : 0 < t)
    (hF : F.IsHomogeneous e) (hG : G.IsHomogeneous t) (hF0 : F ≠ 0) (hG0 : G ≠ 0)
    (hcop : IsRelPrime F G) : FiniteDimensional K (QuotientRing F G) :=
  FiniteDimensional.of_surjective (filteredQuotientMap F G (e + t - 2))
    (filteredQuotientMap_surjective F G e t he ht hF hG hF0 hG0 hcop)

#print axioms exists_low_degree_representative
#print axioms quotient_finiteDimensional

end Cylinder.CompleteIntersectionFinite

end

