module

public import Cylinder.PlaneLineCoordinates
public import Cylinder.CompleteIntersectionFinite

/-!
# A genuine affine chart for a coprime pair of homogeneous plane equations

The selected line has nonzero coprime binary restrictions. Extending that
line to coordinates and dehomogenizing therefore gives the exact original
degrees and coprime nonzero highest-degree parts.
-/

@[expose] public section
noncomputable section

namespace Cylinder.CompleteIntersectionChart

open MvPolynomial Cylinder.GenericPlaneLine Cylinder.PlaneLineCoordinates
open Cylinder.HomogeneousAffineChart Cylinder.HilbertEvaluation
open scoped Classical

variable {K : Type*} [Field K]

def affineForm (p : Fin 3 → K) (w : Fin 2 → K) (hp : p 0 ≠ 0) (hw : w 0 ≠ 0)
    (F : PlaneRing K) : MvPolynomial (Fin 2) K := chartAt 1 (chartCoordinates p w hp hw F)

theorem top_affineForm (p : Fin 3 → K) (w : Fin 2 → K) (hp : p 0 ≠ 0) (hw : w 0 ≠ 0)
    (F : PlaneRing K) (m : ℕ) (hF : F.IsHomogeneous m) :
    homogeneousComponent m (affineForm p w hp hw F) = lineRestriction p w F := by
  rw [affineForm, top_component_chartAt m _ (chartCoordinates_homogeneous p w hp hw F m hF),
    chart_at_zero_coordinates]

theorem affineForm_totalDegree (p : Fin 3 → K) (w : Fin 2 → K) (hp : p 0 ≠ 0) (hw : w 0 ≠ 0)
    (F : PlaneRing K) (m : ℕ) (hF : F.IsHomogeneous m) (hrest : lineRestriction p w F ≠ 0) :
    (affineForm p w hp hw F).totalDegree = m := by
  apply chartAt_one_totalDegree m _ (chartCoordinates_homogeneous p w hp hw F m hF)
  rwa [chart_at_zero_coordinates]

theorem exists_line_nondegenerate [Infinite K]
    (F G : PlaneRing K) (m n : ℕ) (hF : F.IsHomogeneous m) (hG : G.IsHomogeneous n)
    (hF0 : F ≠ 0) (hG0 : G ≠ 0) (hcop : IsRelPrime F G) :
    ∃ p : Fin 3 → K, ∃ w : Fin 2 → K,
      p 0 ≠ 0 ∧ w 0 ≠ 0 ∧ lineRestriction p w F ≠ 0 ∧ lineRestriction p w G ≠ 0 ∧
        IsRelPrime (lineRestriction p w F) (lineRestriction p w G) := by
  obtain ⟨p, hp0, hpFG⟩ := exists_triangular_nonvanishing (F * G) (mul_ne_zero hF0 hG0)
  rw [map_mul, map_mul, mul_ne_zero_iff] at hpFG
  obtain ⟨w, hw0, _havoid, hrest⟩ := exists_coprime_pencil (triangularMap p F) (triangularMap p G)
    m n (triangularMap_homogeneous p F m hF) (triangularMap_homogeneous p G n hG) hpFG.1
    (relPrime_ringEquiv (triangularEquiv p hp0).toRingEquiv hcop) 1 one_ne_zero
  have hFrest : lineRestriction p w F ≠ 0 := by
    intro hz
    apply hpFG.1
    rw [← pencil_eval_infinity w (triangularMap p F)]
    change eval ![1, 0] (lineRestriction p w F) = 0
    rw [hz, map_zero]
  have hGrest : lineRestriction p w G ≠ 0 := by
    intro hz
    apply hpFG.2
    rw [← pencil_eval_infinity w (triangularMap p G)]
    change eval ![1, 0] (lineRestriction p w G) = 0
    rw [hz, map_zero]
  exact ⟨p, w, hp0, hw0, hFrest, hGrest, hrest⟩

theorem exists_affine_chart [Infinite K]
    (F G : PlaneRing K) (m n : ℕ) (hF : F.IsHomogeneous m) (hG : G.IsHomogeneous n)
    (hF0 : F ≠ 0) (hG0 : G ≠ 0) (hcop : IsRelPrime F G) :
    ∃ p : Fin 3 → K, ∃ w : Fin 2 → K, ∃ hp : p 0 ≠ 0, ∃ hw : w 0 ≠ 0,
      (affineForm p w hp hw F).totalDegree = m ∧
      (affineForm p w hp hw G).totalDegree = n ∧
      homogeneousComponent m (affineForm p w hp hw F) ≠ 0 ∧
      homogeneousComponent n (affineForm p w hp hw G) ≠ 0 ∧
      IsRelPrime (homogeneousComponent m (affineForm p w hp hw F))
        (homogeneousComponent n (affineForm p w hp hw G)) := by
  obtain ⟨p, w, hp, hw, hFrest, hGrest, hrest⟩ := exists_line_nondegenerate F G m n hF hG hF0 hG0 hcop
  refine ⟨p, w, hp, hw, affineForm_totalDegree p w hp hw F m hF hFrest,
    affineForm_totalDegree p w hp hw G n hG hGrest, ?_, ?_, ?_⟩
  · rwa [top_affineForm p w hp hw F m hF]
  · rwa [top_affineForm p w hp hw G n hG]
  · rwa [top_affineForm p w hp hw F m hF, top_affineForm p w hp hw G n hG]

/-- Coprime positive-degree binary forms have no common nonzero vector zero.
The proof uses the already proved actual binary ideal generation. -/
theorem binary_common_zero_eq_zero
    (F G : MvPolynomial (Fin 2) K) (m n : ℕ) (hm : 0 < m) (hn : 0 < n)
    (hF : F.IsHomogeneous m) (hG : G.IsHomogeneous n) (hF0 : F ≠ 0) (hG0 : G ≠ 0)
    (hcop : IsRelPrime F G) (u : Fin 2 → K) (huF : eval u F = 0) (huG : eval u G = 0) : u = 0 := by
  funext i
  have hI := CompleteIntersectionFinite.homogeneous_bound_mem_ideal F G m n hm hn hF hG hF0 hG0 hcop
    (X i ^ (m + n - 1)) (isHomogeneous_X_pow i (m + n - 1))
  obtain ⟨A, B, hAB⟩ := Ideal.mem_span_pair.mp hI
  have hz := congrArg (eval u) hAB
  simp only [map_add, map_mul, huF, huG, mul_zero, zero_add, map_pow, eval_X] at hz
  exact eq_zero_of_pow_eq_zero hz.symm

end Cylinder.CompleteIntersectionChart

end
