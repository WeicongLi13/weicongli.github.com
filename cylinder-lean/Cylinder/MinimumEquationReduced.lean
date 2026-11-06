module

public import Cylinder.InitialDegreeExists
public import Cylinder.PlaneCurveFactors
public import Mathlib.Algebra.Squarefree.Basic

/-! A genuine minimum-degree homogeneous equation of a point set has no repeated factor. -/

@[expose] public section
noncomputable section

namespace Cylinder.MinimumEquationReduced

open MvPolynomial Cylinder.HilbertEvaluation Cylinder.PlaneNumericalCharacter Cylinder.PlaneBinaryReduction
open scoped Classical

variable {K I : Type*} [Field K]

theorem equation_zero_of_degree_lt_initial (v : I → Fin 3 → K) (s : ℕ) (hs : InitialDegree v s)
    (F : MvPolynomial (Fin 3) K) (d : ℕ) (hF : F.IsHomogeneous d) (hd : d < s)
    (hzero : ∀ i, eval (v i) F = 0) : F = 0 := by
  let P : Forms K d := ⟨F, hF⟩
  have hP : P ∈ idealPiece v d := by
    rw [idealPiece_eq_kernel]
    exact funext hzero
  rw [hs.2 d hd, Submodule.mem_bot] at hP
  exact congrArg Subtype.val hP

theorem positive_degree_of_nonunit (G : MvPolynomial (Fin 3) K) (hG0 : G ≠ 0) (hG : ¬ IsUnit G) :
    0 < G.totalDegree := by
  by_contra hn
  have hC := totalDegree_eq_zero_iff_eq_C.mp (Nat.eq_zero_of_not_pos hn)
  have hc : G.coeff 0 ≠ 0 := by
    intro hz
    exact hG0 (by rw [hC, hz, map_zero])
  apply hG
  rw [hC]
  exact (isUnit_iff_ne_zero.mpr hc).map C

theorem squarefree_of_initialDegree (v : I → Fin 3 → K) (s : ℕ) (hs : InitialDegree v s)
    (F : MvPolynomial (Fin 3) K) (hF : F.IsHomogeneous s) (hF0 : F ≠ 0)
    (hzero : ∀ i, eval (v i) F = 0) : Squarefree F := by
  intro G hGsq
  by_contra hGunit
  obtain ⟨H, heq⟩ := hGsq
  have hG0 : G ≠ 0 := by
    intro hz
    rw [hz, zero_mul, zero_mul] at heq
    exact hF0 heq
  have hH0 : H ≠ 0 := by
    intro hz
    rw [hz, mul_zero] at heq
    exact hF0 heq
  have hGdvd : G ∣ F := by rw [heq]; exact dvd_mul_of_dvd_left (dvd_mul_right G G) H
  have hHdvd : H ∣ F := by rw [heq]; exact dvd_mul_left H (G * G)
  have hGhom := HomogeneousFactors.homogeneous_of_dvd G F s hF hF0 hGdvd
  have hHhom := HomogeneousFactors.homogeneous_of_dvd H F s hF hF0 hHdvd
  have hdeg : s = G.totalDegree + G.totalDegree + H.totalDegree := by
    rw [← hF.totalDegree hF0, heq,
      totalDegree_mul_of_isDomain (mul_ne_zero hG0 hG0) hH0,
      totalDegree_mul_of_isDomain hG0 hG0]
  have hpos := positive_degree_of_nonunit G hG0 hGunit
  have hRzero : ∀ i, eval (v i) (G * H) = 0 := by
    intro i
    have hi := hzero i
    rw [heq, map_mul, map_mul] at hi
    rw [map_mul]
    rcases mul_eq_zero.mp hi with hGG | hHz
    · have hGz := (mul_eq_zero.mp hGG).elim id id
      rw [hGz, zero_mul]
    · rw [hHz, mul_zero]
  have hR := equation_zero_of_degree_lt_initial v s hs (G * H)
    (G.totalDegree + H.totalDegree) (hGhom.mul hHhom) (by omega) hRzero
  exact mul_ne_zero hG0 hH0 hR

end Cylinder.MinimumEquationReduced

end
