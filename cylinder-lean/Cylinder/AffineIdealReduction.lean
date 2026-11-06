module

public import Cylinder.LeadingComponents

/-! Highest-term cancellation for the ideal of two nonhomogeneous binary
polynomials whose actual top homogeneous forms are relatively prime. -/

@[expose] public section
noncomputable section

namespace Cylinder.AffineIdealReduction

open Module MvPolynomial
open Cylinder.PlaneBinaryReduction Cylinder.CompleteIntersectionKoszul
open Cylinder.BinaryCompleteIntersectionGraded Cylinder.LeadingComponents
open scoped Classical

variable {K : Type*} [Field K]

def CoefficientBound (A : BinaryRing K) (e N : ℕ) : Prop :=
  A = 0 ∨ A.totalDegree + e ≤ N

theorem coefficient_degree_bound (A : BinaryRing K) (e N : ℕ)
    (hA : CoefficientBound A e N) (he : e ≤ N) : A.totalDegree ≤ N - e := by
  rcases hA with rfl | hA
  · simp
  · omega

theorem shiftedProjection_val (e N : ℕ) (he : e ≤ N) (A : BinaryRing K) :
    (shiftedProjection (K := K) e N A).val = homogeneousComponent (N - e) A := by
  simp only [shiftedProjection, dif_pos he, LinearMap.codRestrict_apply]

theorem component_product_of_bound (A f : BinaryRing K) (e N : ℕ)
    (hf : f.totalDegree = e) (hA : CoefficientBound A e N) :
    homogeneousComponent N (A * f) =
      (shiftedProjection (K := K) e N A).val * homogeneousComponent e f := by
  rcases hA with rfl | hA
  · simp
  · have he : e ≤ N := by omega
    rw [shiftedProjection_val e N he A]
    have h := highest_component_mul A f (N - e) e (by omega) (le_of_eq hf)
    have hsum : N - e + e = N := by omega
    simpa only [hsum] using h

theorem strict_bound_of_component_zero (A : BinaryRing K) (e N : ℕ)
    (he : e ≤ N) (hA : A.totalDegree ≤ N - e)
    (hc : homogeneousComponent (N - e) A = 0) :
    A = 0 ∨ A.totalDegree + e < N := by
  rcases eq_zero_or_totalDegree_lt_of_component_zero A (N - e) hA hc with h | h
  · exact Or.inl h
  · exact Or.inr (by omega)

theorem strict_bound_of_shift_zero (A : BinaryRing K) (e N : ℕ)
    (hA : CoefficientBound A e N) (hc : (shiftedProjection (K := K) e N A).val = 0) :
    A = 0 ∨ A.totalDegree + e < N := by
  rcases hA with hA | hA
  · exact Or.inl hA
  · have he : e ≤ N := by omega
    rw [shiftedProjection_val e N he A] at hc
    exact strict_bound_of_component_zero A e N he (by omega) hc

/-- An excessive weighted representation can be replaced by a strictly
smaller real representation. The correction is the actual highest-term
Koszul coefficient, lifted as a homogeneous polynomial. -/
theorem lower_weighted_representation (f g P A B : BinaryRing K) (e t N : ℕ)
    (hf : f.totalDegree = e) (hg : g.totalDegree = t)
    (hfe : homogeneousComponent e f ≠ 0)
    (hcop : IsRelPrime (homogeneousComponent e f) (homogeneousComponent t g))
    (hP : A * f + B * g = P) (hN : P.totalDegree < N)
    (hA : CoefficientBound A e N) (hB : CoefficientBound B t N) :
    ∃ A' B' : BinaryRing K, A' * f + B' * g = P ∧
      (A' = 0 ∨ A'.totalDegree + e < N) ∧ (B' = 0 ∨ B'.totalDegree + t < N) := by
  let α := shiftedProjection (K := K) e N A
  let β := shiftedProjection (K := K) t N B
  have hrel : α.val * homogeneousComponent e f + β.val * homogeneousComponent t g = 0 := by
    have h := congrArg (homogeneousComponent N) hP
    rw [map_add, component_product_of_bound A f e N hf hA,
      component_product_of_bound B g t N hg hB, homogeneousComponent_eq_zero _ _ hN] at h
    exact h
  obtain ⟨c, hcA, hcB⟩ := (koszul_syzygy_iff _ _ hfe hcop α.val β.val).mp hrel
  have hcm := koszul_coefficient_mem (homogeneousComponent e f) (homogeneousComponent t g)
    β.val c e t N (homogeneousComponent_isHomogeneous e f) hfe β.property hcB
  by_cases hs : e + t ≤ N
  · have hch : c.IsHomogeneous (N - (e + t)) := by
      simpa only [hs, ite_true] using (mem_shiftedForms (e + t) N c).mp hcm
    have he : e ≤ N := by omega
    have ht : t ≤ N := by omega
    have hAd := coefficient_degree_bound A e N hA he
    have hBd := coefficient_degree_bound B t N hB ht
    have hgc : (g * c).totalDegree ≤ N - e := by
      have h := totalDegree_mul g c
      have hc := hch.totalDegree_le
      rw [hg] at h
      omega
    have hfc : (f * c).totalDegree ≤ N - t := by
      have h := totalDegree_mul f c
      have hc := hch.totalDegree_le
      rw [hf] at h
      omega
    have hgctop : homogeneousComponent (N - e) (g * c) = homogeneousComponent t g * c := by
      have h := highest_component_mul g c t (N - (e + t)) (le_of_eq hg) hch.totalDegree_le
      have hn : t + (N - (e + t)) = N - e := by omega
      rw [hn, homogeneousComponent_eq_self hch] at h
      exact h
    have hfctop : homogeneousComponent (N - t) (f * c) = homogeneousComponent e f * c := by
      have h := highest_component_mul f c e (N - (e + t)) (le_of_eq hf) hch.totalDegree_le
      have hn : e + (N - (e + t)) = N - t := by omega
      rw [hn, homogeneousComponent_eq_self hch] at h
      exact h
    have hAtop : homogeneousComponent (N - e) (A + g * c) = 0 := by
      have ha : homogeneousComponent (N - e) A = -(homogeneousComponent t g) * c := by
        rw [← shiftedProjection_val e N he A]
        exact hcA
      rw [map_add, hgctop, ha]
      ring
    have hBtop : homogeneousComponent (N - t) (B - f * c) = 0 := by
      have hb : homogeneousComponent (N - t) B = homogeneousComponent e f * c := by
        rw [← shiftedProjection_val t N ht B]
        exact hcB
      rw [map_sub, hfctop, hb, sub_self]
    refine ⟨A + g * c, B - f * c, ?_, ?_, ?_⟩
    · calc
        _ = A * f + B * g := by ring
        _ = P := hP
    · exact strict_bound_of_component_zero _ e N he
        ((totalDegree_add _ _).trans (max_le hAd hgc)) hAtop
    · exact strict_bound_of_component_zero _ t N ht
        ((totalDegree_sub _ _).trans (max_le hBd hfc)) hBtop
  · have hc0 : c = 0 := by
      simpa only [hs, ite_false] using (mem_shiftedForms (e + t) N c).mp hcm
    have hα : α.val = 0 := by rw [hcA, hc0, mul_zero]
    have hβ : β.val = 0 := by rw [hcB, hc0, mul_zero]
    exact ⟨A, B, hP, strict_bound_of_shift_zero A e N hA hα,
      strict_bound_of_shift_zero B t N hB hβ⟩

#print axioms lower_weighted_representation

end Cylinder.AffineIdealReduction

end
