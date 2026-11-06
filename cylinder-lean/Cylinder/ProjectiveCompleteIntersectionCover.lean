module

public import Cylinder.ProjectiveAffineOpen
public import Cylinder.ProjectiveChartData
public import Cylinder.CompleteIntersectionFinite
public import Cylinder.HomogeneousAffineChart
public import Mathlib.RingTheory.MvPolynomial.Ideal

/-! Every scheme point of a complete intersection lies in the actual
avoiding affine chart. This statement concerns all homogeneous primes,
not only the previously represented K-valued points. -/

@[expose] public section
noncomputable section
open scoped Classical

namespace Cylinder.ProjectiveCompleteIntersectionCover

open MvPolynomial Module AlgebraicGeometry
open Cylinder.ProjectivePolynomialChart Cylinder.CurvePolarLocal
open Cylinder.HomogeneousAffineChart Cylinder.CompleteIntersectionKoszul
open Cylinder.ProjectiveChartData Cylinder.HilbertEvaluation
open Cylinder.PlaneLineCoordinates

set_option autoImplicit false
attribute [local instance] MvPolynomial.gradedAlgebra

variable {K : Type*} [Field K]

theorem restriction_eq_mod (J : Ideal (HomogeneousPlanePolynomial (K := K)))
    (hX : (X none : HomogeneousPlanePolynomial (K := K)) ∈ J)
    (H : HomogeneousPlanePolynomial (K := K)) :
    Ideal.Quotient.mk J (rename (some : Fin 2 → Option (Fin 2)) (chartAt 0 H)) =
      Ideal.Quotient.mk J H := by
  have hX0 : Ideal.Quotient.mk J (X none) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hX
  induction H using MvPolynomial.induction_on with
  | C a => simp
  | add F G hF hG => simp only [map_add, hF, hG]
  | mul_X F i hF =>
    cases i <;> simp [map_mul, hF, hX0]

theorem positive_homogeneous_mem_variables (H : HomogeneousPlanePolynomial (K := K))
    (n : ℕ) (hn : 0 < n) (hH : H.IsHomogeneous n) :
    H ∈ idealOfVars (Option (Fin 2)) K := by
  rw [← pow_one (idealOfVars (Option (Fin 2)) K), mem_pow_idealOfVars_iff]
  intro m hm
  have hmdegree : m.degree = n := by
    rw [Finsupp.degree_eq_weight_one]
    exact hH (mem_support_iff.mp hm)
  rw [hmdegree]
  exact hn

theorem not_all_variables_mem (q : ProjectiveSpectrum (grading K)) :
    ¬ ∀ i : Option (Fin 2), (X i : HomogeneousPlanePolynomial (K := K)) ∈
      q.asHomogeneousIdeal := by
  intro h
  have hvars : idealOfVars (Option (Fin 2)) K ≤ q.asHomogeneousIdeal.toIdeal := by
    exact Ideal.span_le.mpr (Set.range_subset_iff.mpr h)
  apply q.not_irrelevant_le
  apply (HomogeneousIdeal.irrelevant_le (grading K)).mpr
  intro n hn H hH
  exact hvars (positive_homogeneous_mem_variables H n hn hH)

theorem no_point_at_infinity (c : Chart K) (F G : PlaneRing K) (e t : ℕ)
    (he : 0 < e) (ht : 0 < t) (hF : F.IsHomogeneous e) (hG : G.IsHomogeneous t)
    (hgood : GoodChart c F G e t) (q : ProjectiveSpectrum (grading K))
    (hqF : c.coordinates F ∈ q.asHomogeneousIdeal)
    (hqG : c.coordinates G ∈ q.asHomogeneousIdeal) :
    (X none : HomogeneousPlanePolynomial (K := K)) ∉ q.asHomogeneousIdeal := by
  intro hX
  let A := chartAt 0 (c.coordinates F)
  let B := chartAt 0 (c.coordinates G)
  have hcF := chartCoordinates_homogeneous c.a c.b c.ha c.hb F e hF
  have hcG := chartCoordinates_homogeneous c.a c.b c.ha c.hb G t hG
  have hA : A.IsHomogeneous e := chartAt_zero_homogeneous e (c.coordinates F) hcF
  have hB : B.IsHomogeneous t := chartAt_zero_homogeneous t (c.coordinates G) hcG
  have hAE : homogeneousComponent e (dehomogenize (c.coordinates F)) = A := by
    rw [← chartAt_one, top_component_chartAt e (c.coordinates F) hcF]
  have hBE : homogeneousComponent t (dehomogenize (c.coordinates G)) = B := by
    rw [← chartAt_one, top_component_chartAt t (c.coordinates G) hcG]
  have hA0 : A ≠ 0 := hAE ▸ hgood.topF
  have hB0 : B ≠ 0 := hBE ▸ hgood.topG
  have hcop : IsRelPrime A B := hAE ▸ hBE ▸ hgood.topcop
  let J := Ideal.comap (rename (some : Fin 2 → Option (Fin 2))) q.asHomogeneousIdeal.toIdeal
  have hAJ : A ∈ J := by
    change rename (some : Fin 2 → Option (Fin 2)) A ∈ q.asHomogeneousIdeal.toIdeal
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    exact (restriction_eq_mod q.asHomogeneousIdeal.toIdeal hX (c.coordinates F)).trans
      (Ideal.Quotient.eq_zero_iff_mem.mpr hqF)
  have hBJ : B ∈ J := by
    change rename (some : Fin 2 → Option (Fin 2)) B ∈ q.asHomogeneousIdeal.toIdeal
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    exact (restriction_eq_mod q.asHomogeneousIdeal.toIdeal hX (c.coordinates G)).trans
      (Ideal.Quotient.eq_zero_iff_mem.mpr hqG)
  have hIJ : equationsIdeal A B ≤ J := by
    apply Ideal.span_le.mpr
    intro H hH
    rcases Set.mem_insert_iff.mp hH with rfl | hH
    · exact hAJ
    · rw [Set.mem_singleton_iff] at hH
      exact hH ▸ hBJ
  have hsome : ∀ i : Fin 2, (X (some i) : HomogeneousPlanePolynomial (K := K)) ∈
      q.asHomogeneousIdeal := by
    intro i
    have hp : (X i : MvPolynomial (Fin 2) K) ^ (e + t - 1) ∈ J :=
      hIJ (CompleteIntersectionFinite.homogeneous_bound_mem_ideal A B e t he ht hA hB hA0 hB0
        hcop (X i ^ (e + t - 1)) (isHomogeneous_X_pow i _))
    have hp' : (X (some i) : HomogeneousPlanePolynomial (K := K)) ^ (e + t - 1) ∈
        q.asHomogeneousIdeal.toIdeal := by
      simpa only [J, Ideal.mem_comap, map_pow, rename_X] using hp
    exact q.isPrime.mem_of_pow_mem (e + t - 1) hp'
  apply not_all_variables_mem q
  intro i
  cases i with
  | none => exact hX
  | some i => exact hsome i

end Cylinder.ProjectiveCompleteIntersectionCover

end
