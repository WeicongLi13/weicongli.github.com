module

public import Cylinder.CompleteIntersectionFiltered

/-! Highest homogeneous components of genuine, possibly nonhomogeneous,
binary polynomials: multiplication and cancellation lower total degree. -/

@[expose] public section
noncomputable section

namespace Cylinder.LeadingComponents

open MvPolynomial Module
open Cylinder.PlaneBinaryReduction
open scoped Classical BigOperators

variable {K : Type*} [Field K]

local instance : GradedAlgebra (BinaryForms K) := MvPolynomial.gradedAlgebra

theorem component_mul_left_homogeneous (P Q : BinaryRing K) (e n : ℕ)
    (hP : P.IsHomogeneous e) :
    homogeneousComponent n (P * Q) =
      if e ≤ n then P * homogeneousComponent (n - e) Q else 0 := by
  have h := DirectSum.coe_decompose_mul_of_left_mem (BinaryForms K) n hP (b := Q)
  have hc (R : BinaryRing K) (r : ℕ) :
      (DirectSum.decompose (BinaryForms K) R r : BinaryRing K) = homogeneousComponent r R :=
    MvPolynomial.decomposition.decompose'_apply R r
  rw [hc] at h
  by_cases hen : e ≤ n
  · rw [if_pos hen, hc] at h
    simpa only [hen, ite_true] using h
  · simpa only [hen, ite_false] using h

theorem sum_components_up_to (P : BinaryRing K) (e : ℕ) (hP : P.totalDegree ≤ e) :
    ∑ i ∈ Finset.range (e + 1), homogeneousComponent i P = P := by
  calc
    _ = ∑ i ∈ Finset.range (P.totalDegree + 1), homogeneousComponent i P := by
      symm
      apply Finset.sum_subset (Finset.range_mono (by omega : P.totalDegree + 1 ≤ e + 1))
      intro i hie hiP
      have hlt : P.totalDegree < i := by simp only [Finset.mem_range] at hiP; omega
      exact homogeneousComponent_eq_zero i P hlt
    _ = P := sum_homogeneousComponent P

/-- A bounded polynomial product has the product of the two highest
allowed components as its highest allowed component. -/
theorem highest_component_mul (P Q : BinaryRing K) (e t : ℕ)
    (hP : P.totalDegree ≤ e) (hQ : Q.totalDegree ≤ t) :
    homogeneousComponent (e + t) (P * Q) =
      homogeneousComponent e P * homogeneousComponent t Q := by
  calc
    _ = homogeneousComponent (e + t)
        ((∑ i ∈ Finset.range (e + 1), homogeneousComponent i P) * Q) := by
      rw [sum_components_up_to P e hP]
    _ = ∑ i ∈ Finset.range (e + 1),
        homogeneousComponent (e + t) (homogeneousComponent i P * Q) := by
      rw [Finset.sum_mul, map_sum]
    _ = homogeneousComponent (e + t) (homogeneousComponent e P * Q) := by
      apply Finset.sum_eq_single e
      · intro i hi hine
        have hie : i ≤ e := by have := Finset.mem_range.mp hi; omega
        rw [component_mul_left_homogeneous _ Q i (e + t)
          (homogeneousComponent_isHomogeneous i P), if_pos (by omega : i ≤ e + t)]
        rw [homogeneousComponent_eq_zero _ Q (by omega : Q.totalDegree < e + t - i), mul_zero]
      · intro hen
        exact False.elim (hen (Finset.mem_range.mpr (by omega)))
    _ = homogeneousComponent e P * homogeneousComponent t Q := by
      rw [component_mul_left_homogeneous _ Q e (e + t)
        (homogeneousComponent_isHomogeneous e P), if_pos (by omega : e ≤ e + t)]
      simp

theorem top_component_ne_zero (P : BinaryRing K) (hP : P ≠ 0) :
    homogeneousComponent P.totalDegree P ≠ 0 := by
  have hsupport : P.support.Nonempty := by
    exact Finset.nonempty_iff_ne_empty.mpr (by
      intro h
      apply hP
      exact AddMonoidAlgebra.coeff_eq_zero.mp (Finsupp.support_eq_empty.mp h))
  obtain ⟨α, hα, hdegree⟩ := Finset.exists_mem_eq_sup P.support hsupport (fun β => β.degree)
  have hαdegree : α.degree = P.totalDegree := hdegree.symm
  intro hz
  have hc := congrArg (fun Q : BinaryRing K => Q.coeff α) hz
  rw [coeff_homogeneousComponent, if_pos hαdegree] at hc
  simp only [AddMonoidAlgebra.coeff_zero] at hc
  exact (mem_support_iff.mp hα) hc

/-- Vanishing of the highest permitted component genuinely lowers degree;
the zero case is retained when the bound is zero. -/
theorem eq_zero_or_totalDegree_lt_of_component_zero (P : BinaryRing K) (e : ℕ)
    (hP : P.totalDegree ≤ e) (hc : homogeneousComponent e P = 0) :
    P = 0 ∨ P.totalDegree < e := by
  by_cases hP0 : P = 0
  · exact Or.inl hP0
  · right
    by_contra hn
    have heq : P.totalDegree = e := by omega
    exact top_component_ne_zero P hP0 (heq.symm ▸ hc)

/-- Subtracting the actual top component removes the top degree. -/
theorem remove_top_component (P : BinaryRing K) :
    P - homogeneousComponent P.totalDegree P = 0 ∨
      (P - homogeneousComponent P.totalDegree P).totalDegree < P.totalDegree := by
  apply eq_zero_or_totalDegree_lt_of_component_zero
  · exact (totalDegree_sub _ _).trans
      (max_le (le_refl _) (homogeneousComponent_isHomogeneous _ _).totalDegree_le)
  · rw [map_sub, homogeneousComponent_eq_self (homogeneousComponent_isHomogeneous _ _), sub_self]

#print axioms highest_component_mul
#print axioms top_component_ne_zero
#print axioms remove_top_component

end Cylinder.LeadingComponents

end
