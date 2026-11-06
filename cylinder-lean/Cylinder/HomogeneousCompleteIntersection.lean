module

public import Cylinder.AffineEvaluationDuality
public import Cylinder.HomogeneousAffineChart

/-! Homogeneous ideal membership is recovered from genuine bounded affine
representations. In the avoiding chart the coordinate is a nonzero divisor
on the actual complete-intersection quotient, including its nilpotents. -/

@[expose] public section
noncomputable section

namespace Cylinder.HomogeneousCompleteIntersection

open Module MvPolynomial
open Cylinder.CurvePolarLocal Cylinder.PlaneHomogenization
open Cylinder.CompleteIntersectionKoszul Cylinder.AffineIdealLeading Cylinder.AffineIdealReduction
open scoped Classical

variable {K : Type*} [Field K]

abbrev HomRing := HomogeneousPlanePolynomial (K := K)
abbrev HomForms (K : Type*) [Field K] := homogeneousSubmodule (Option (Fin 2)) K

local instance : GradedAlgebra (HomForms K) := MvPolynomial.gradedAlgebra

def homogenizedCoefficient (A : Cylinder.PlaneBinaryReduction.BinaryRing K) (e n : ℕ) : HomRing (K := K) :=
  if e ≤ n then homogenize (n - e) A else 0

theorem dehomogenize_coefficient (A : Cylinder.PlaneBinaryReduction.BinaryRing K) (e n : ℕ)
    (hA : CoefficientBound A e n) : dehomogenize (homogenizedCoefficient A e n) = A := by
  by_cases he : e ≤ n
  · simp [homogenizedCoefficient, he, dehomogenize_homogenize]
  · have hA0 : A = 0 := hA.elim id (fun h => by omega)
    simp [homogenizedCoefficient, he, hA0]

theorem coefficient_product_homogeneous (A : Cylinder.PlaneBinaryReduction.BinaryRing K)
    (F : HomRing (K := K)) (e n : ℕ) (hF : F.IsHomogeneous e) (hA : CoefficientBound A e n) :
    (homogenizedCoefficient A e n * F).IsHomogeneous n := by
  by_cases he : e ≤ n
  · have hAd := coefficient_degree_bound A e n hA he
    have hh := (homogenize_homogeneous (n - e) A hAd).mul hF
    simpa [homogenizedCoefficient, he, Nat.sub_add_cancel he] using hh
  · simp [homogenizedCoefficient, he, isHomogeneous_zero]

theorem dehomogenize_mem_equations (F G H : HomRing (K := K))
    (hH : H ∈ equationsIdeal F G) : dehomogenize H ∈ equationsIdeal (dehomogenize F) (dehomogenize G) := by
  obtain ⟨A, B, hAB⟩ := Ideal.mem_span_pair.mp hH
  exact Ideal.mem_span_pair.mpr ⟨dehomogenize A, dehomogenize B,
    by simpa only [map_add, map_mul] using congrArg dehomogenize hAB⟩

/-- Homogeneous membership is exactly membership after dehomogenization.
The reverse implication is proved by degree-controlled actual lifts. -/
theorem homogeneous_mem_iff_dehomogenize_mem (F G H : HomRing (K := K)) (e t n : ℕ)
    (hF : F.IsHomogeneous e) (hG : G.IsHomogeneous t) (hH : H.IsHomogeneous n)
    (hf : (dehomogenize F).totalDegree = e) (hg : (dehomogenize G).totalDegree = t)
    (hfe : homogeneousComponent e (dehomogenize F) ≠ 0)
    (hcop : IsRelPrime (homogeneousComponent e (dehomogenize F))
      (homogeneousComponent t (dehomogenize G))) :
    H ∈ equationsIdeal F G ↔ dehomogenize H ∈ equationsIdeal (dehomogenize F) (dehomogenize G) := by
  constructor
  · exact dehomogenize_mem_equations F G H
  · intro hHI
    obtain ⟨A, B, hAB, hA, hB⟩ := exists_bounded_representation
      (dehomogenize F) (dehomogenize G) (dehomogenize H) e t hf hg hfe hcop hHI
    have hHdeg : (dehomogenize H).totalDegree ≤ n :=
      (dehomogenize_totalDegree_le H).trans hH.totalDegree_le
    have hAn : CoefficientBound A e n := hA.imp_right (fun h => h.trans hHdeg)
    have hBn : CoefficientBound B t n := hB.imp_right (fun h => h.trans hHdeg)
    have hprodF := coefficient_product_homogeneous A F e n hF hAn
    have hprodG := coefficient_product_homogeneous B G t n hG hBn
    have hEq : homogenizedCoefficient A e n * F + homogenizedCoefficient B t n * G = H := by
      apply HomogeneousAffineChart.dehomogenize_injective_on_homogeneous n _ H (hprodF.add hprodG) hH
      rw [map_add, map_mul, map_mul, dehomogenize_coefficient A e n hAn,
        dehomogenize_coefficient B t n hBn]
      exact hAB
    exact Ideal.mem_span_pair.mpr ⟨homogenizedCoefficient A e n, homogenizedCoefficient B t n, hEq⟩

theorem equations_homogeneous (F G : HomRing (K := K)) (e t : ℕ)
    (hF : F.IsHomogeneous e) (hG : G.IsHomogeneous t) :
    (equationsIdeal F G).IsHomogeneous (HomForms K) := by
  apply Ideal.homogeneous_span
  intro H hH
  rcases hH with rfl | hH
  · exact ⟨e, hF⟩
  · have hHG := Set.mem_singleton_iff.mp hH
    subst H
    exact ⟨t, hG⟩

/-- The actual chart coordinate is regular on the actual homogeneous
complete-intersection quotient. -/
theorem coordinate_colon_eq (F G : HomRing (K := K)) (e t : ℕ)
    (hF : F.IsHomogeneous e) (hG : G.IsHomogeneous t)
    (hf : (dehomogenize F).totalDegree = e) (hg : (dehomogenize G).totalDegree = t)
    (hfe : homogeneousComponent e (dehomogenize F) ≠ 0)
    (hcop : IsRelPrime (homogeneousComponent e (dehomogenize F))
      (homogeneousComponent t (dehomogenize G))) :
    (equationsIdeal F G).colon {X none} = equationsIdeal F G := by
  apply le_antisymm
  · intro P hP
    have hXP := Submodule.mem_colon_singleton.mp hP
    change P * X none ∈ equationsIdeal F G at hXP
    rw [mul_comm] at hXP
    have hIW := equations_homogeneous F G e t hF hG
    apply hIW.mem_iff.mpr
    intro d
    have hcomponent := hIW (1 + d) hXP
    rw [DirectSum.coe_decompose_mul_add_of_left_mem (HomForms K) (isHomogeneous_X K none)] at hcomponent
    have hdehom := dehomogenize_mem_equations F G _ hcomponent
    rw [map_mul, dehomogenize_X_none, one_mul] at hdehom
    exact (homogeneous_mem_iff_dehomogenize_mem F G _ e t d hF hG
      (DirectSum.decompose (HomForms K) P d).property hf hg hfe hcop).mpr hdehom
  · exact Ideal.le_colon

#print axioms homogeneous_mem_iff_dehomogenize_mem
#print axioms coordinate_colon_eq

end Cylinder.HomogeneousCompleteIntersection

end
