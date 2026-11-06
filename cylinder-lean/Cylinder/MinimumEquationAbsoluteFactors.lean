module

public import Cylinder.FrobeniusFactorZeros
public import Cylinder.RationalMinimumEquation
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# The factors of a minimum equation of rational points are absolutely irreducible

A proper factor over an algebraic extension contains every rational zero
of the original irreducible factor, by the proved Frobenius norm argument.
Coefficient projection then replaces that factor by an actual smaller
prime-field equation, contradicting the original minimum degree.
-/

@[expose] public section
noncomputable section

namespace Cylinder.MinimumEquationAbsoluteFactors

open MvPolynomial Cylinder.RationalPlaneLine Cylinder.RationalMinimumEquation
open Cylinder.PlaneBinaryReduction Cylinder.EquationScalarDescent Cylinder.PolynomialDivisibilityDescent
open Cylinder.MinimumEquationReduced Cylinder.FrobeniusFactorZeros
open scoped Classical

variable (p : ℕ) [Fact p.Prime]
variable {L : Type*} [Field L] [Algebra (ZMod p) L] [CharP L p] [Algebra.IsAlgebraic (ZMod p) L]

theorem factor_irreducible_after_extension
    (D : Finset (PlanePoint (ZMod p))) (s : ℕ) (hs : InitialDegree (baseRepresentatives D) s)
    (F : MvPolynomial (Fin 3) (ZMod p)) (hF : F.IsHomogeneous s) (hF0 : F ≠ 0)
    (hzero : ∀ P ∈ D, eval P.rep F = 0)
    (G : MvPolynomial (Fin 3) (ZMod p)) (hG : Irreducible G) (hGF : G ∣ F) :
    Irreducible (MvPolynomial.map (algebraMap (ZMod p) L) G) := by
  have hmapG0 : MvPolynomial.map (algebraMap (ZMod p) L) G ≠ 0 := by
    intro hz
    exact hG.ne_zero (MvPolynomial.map_injective (algebraMap (ZMod p) L)
      (algebraMap (ZMod p) L).injective (by simpa only [map_zero] using hz))
  have hmapUnit : ¬ IsUnit (MvPolynomial.map (algebraMap (ZMod p) L) G) := by
    intro hu
    have hd : MvPolynomial.map (algebraMap (ZMod p) L) G ∣
        MvPolynomial.map (algebraMap (ZMod p) L) (1 : MvPolynomial (Fin 3) (ZMod p)) := by
      rw [map_one]
      exact hu.dvd
    exact hG.not_isUnit (isUnit_iff_dvd_one.mpr (dvd_of_mapped_dvd (L := L) G 1 hd))
  have hGhom := HomogeneousFactors.homogeneous_of_dvd G F s hF hF0 hGF
  have hmapGhom := EquationScalarDescent.mapped_homogeneous (L := L) G G.totalDegree hGhom
  refine ⟨hmapUnit, ?_⟩
  intro A B hAB
  by_contra hunit
  obtain ⟨hAunit, hBunit⟩ := not_or.mp hunit
  have hA0 : A ≠ 0 := by intro hz; rw [hz, zero_mul] at hAB; exact hmapG0 hAB
  have hB0 : B ≠ 0 := by intro hz; rw [hz, mul_zero] at hAB; exact hmapG0 hAB
  have hAdvd : A ∣ MvPolynomial.map (algebraMap (ZMod p) L) G := ⟨B, hAB⟩
  have hBdvd : B ∣ MvPolynomial.map (algebraMap (ZMod p) L) G := by
    rw [hAB]
    exact dvd_mul_left B A
  have hAhom := HomogeneousFactors.homogeneous_of_dvd A _ G.totalDegree hmapGhom hmapG0 hAdvd
  have hBpos := positive_degree_of_nonunit B hB0 hBunit
  have hdeg : G.totalDegree = A.totalDegree + B.totalDegree := by
    rw [← hmapGhom.totalDegree hmapG0, hAB, totalDegree_mul_of_isDomain hA0 hB0]
  let V := {v : Fin 3 → ZMod p // eval v G = 0}
  have hAzero : ∀ v : V, eval (fun j => algebraMap (ZMod p) L (v.val j)) A = 0 := by
    intro v
    exact eval_divisor_zero_of_base_irreducible p G hG A hAunit hAdvd v.val v.property
  obtain ⟨Q, hQhom, hQ0, hQzero⟩ := exists_equation_descent (L := L) (fun v : V => v.val)
    A.totalDegree A hAhom hA0 hAzero
  obtain ⟨R, hR⟩ := hGF
  have hR0 : R ≠ 0 := by intro hz; rw [hz, mul_zero] at hR; exact hF0 hR
  have hRdvd : R ∣ F := by rw [hR]; exact dvd_mul_left R G
  have hRhom := HomogeneousFactors.homogeneous_of_dvd R F s hF hF0 hRdvd
  have hFRdeg : s = G.totalDegree + R.totalDegree := by
    rw [← hF.totalDegree hF0, hR, totalDegree_mul_of_isDomain hG.ne_zero hR0]
  have hQRzero : ∀ P : D, eval (baseRepresentatives D P) (Q * R) = 0 := by
    intro P
    have hP := hzero P.val P.property
    rw [hR, map_mul] at hP
    change eval P.val.rep (Q * R) = 0
    rw [map_mul]
    rcases mul_eq_zero.mp hP with hPG | hPR
    · rw [hQzero ⟨P.val.rep, hPG⟩, zero_mul]
    · rw [hPR, mul_zero]
  have hz := equation_zero_of_degree_lt_initial (baseRepresentatives D) s hs (Q * R)
    (A.totalDegree + R.totalDegree) (hQhom.mul hRhom) (by omega) hQRzero
  exact mul_ne_zero hQ0 hR0 hz

theorem factors_irreducible_after_extension
    (D : Finset (PlanePoint (ZMod p))) (s : ℕ) (hs : InitialDegree (baseRepresentatives D) s)
    (F : MvPolynomial (Fin 3) (ZMod p)) (hF : F.IsHomogeneous s) (hF0 : F ≠ 0)
    (hzero : ∀ P ∈ D, eval P.rep F = 0) :
    ∀ G ∈ PlaneCurveFactors.factors F, Irreducible (MvPolynomial.map (algebraMap (ZMod p) L) G) := by
  intro G hG
  exact factor_irreducible_after_extension p D s hs F hF hF0 hzero G
    (PlaneCurveFactors.factor_irreducible F G hG) (PlaneCurveFactors.factor_dvd F G hG)

omit [Field L] [Algebra (ZMod p) L] [CharP L p] [Algebra.IsAlgebraic (ZMod p) L] in
theorem factors_absolutely_irreducible
    (D : Finset (PlanePoint (ZMod p))) (s : ℕ) (hs : InitialDegree (baseRepresentatives D) s)
    (F : MvPolynomial (Fin 3) (ZMod p)) (hF : F.IsHomogeneous s) (hF0 : F ≠ 0)
    (hzero : ∀ P ∈ D, eval P.rep F = 0) :
    ∀ G ∈ PlaneCurveFactors.factors F,
      Irreducible (MvPolynomial.map (algebraMap (ZMod p) (AlgebraicClosure (ZMod p))) G) :=
  factors_irreducible_after_extension p (L := AlgebraicClosure (ZMod p)) D s hs F hF hF0 hzero

omit [Field L] [Algebra (ZMod p) L] [CharP L p] [Algebra.IsAlgebraic (ZMod p) L] in
theorem exists_reduced_base_equation_with_absolute_factors
    (D : Finset (PlanePoint (ZMod p))) (s : ℕ)
    (hs : InitialDegree (RationalPlanePointModel.representatives
      (algebraMap (ZMod p) (AlgebraicClosure (ZMod p))) D) s) :
    ∃ F : MvPolynomial (Fin 3) (ZMod p), F.IsHomogeneous s ∧ F ≠ 0 ∧
      (∀ P ∈ D, eval P.rep F = 0) ∧ Squarefree F ∧
      Squarefree (MvPolynomial.map (algebraMap (ZMod p) (AlgebraicClosure (ZMod p))) F) ∧
      ∀ G ∈ PlaneCurveFactors.factors F,
        Irreducible (MvPolynomial.map (algebraMap (ZMod p) (AlgebraicClosure (ZMod p))) G) := by
  obtain ⟨F, hF, hF0, hzero, hsq, hsqmap⟩ := RationalMinimumEquation.exists_base_equation
    (algebraMap (ZMod p) (AlgebraicClosure (ZMod p))) D s hs
  refine ⟨F, hF, hF0, hzero, hsq, hsqmap, ?_⟩
  exact factors_absolutely_irreducible p D s
    ((RationalMinimumEquation.initialDegree_iff _ D s).mp hs) F hF hF0 hzero

end Cylinder.MinimumEquationAbsoluteFactors

end
