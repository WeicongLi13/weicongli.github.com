module

public import Cylinder.CompleteIntersectionChart
public import Cylinder.PlanePointModel

/-! Normalizing actual projective common zeros in the constructed affine chart. -/

@[expose] public section
noncomputable section

namespace Cylinder.CompleteIntersectionAffinePoints

open MvPolynomial Cylinder.GenericPlaneLine Cylinder.PlaneLineCoordinates
open Cylinder.HomogeneousAffineChart Cylinder.CompleteIntersectionChart Cylinder.HilbertEvaluation
open scoped Classical LinearAlgebra.Projectivization

variable {K : Type*} [Field K]

theorem affineForm_eq_dehomogenize (p : Fin 3 → K) (w : Fin 2 → K)
    (hp : p 0 ≠ 0) (hw : w 0 ≠ 0) (F : PlaneRing K) :
    affineForm p w hp hw F = CurvePolarLocal.dehomogenize (chartCoordinates p w hp hw F) :=
  chartAt_one _

def chartFunctional (p : Fin 3 → K) (w : Fin 2 → K) (hp : p 0 ≠ 0) (hw : w 0 ≠ 0) :
    Module.Dual K (Fin 3 → K) := (LinearMap.proj 2).comp (coordinateLinearEquiv p w hp hw).symm.toLinearMap

theorem chartFunctional_ne_zero (p : Fin 3 → K) (w : Fin 2 → K) (hp : p 0 ≠ 0) (hw : w 0 ≠ 0) :
    chartFunctional p w hp hw ≠ 0 := by
  intro hz
  have h := LinearMap.congr_fun hz (coordinateLinearEquiv p w hp hw (Pi.single 2 1))
  simp [chartFunctional] at h

def homogeneousVector (x : Fin 3 → K) : Option (Fin 2) → K :=
  fun i => i.elim (x 2) (fun j => x j.castSucc)

def liftVector (a : K) (u : Fin 2 → K) : Fin 3 → K := ![u 0, u 1, a]

theorem eval_chartCoordinates (p : Fin 3 → K) (w : Fin 2 → K) (hp : p 0 ≠ 0) (hw : w 0 ≠ 0)
    (x : Fin 3 → K) (F : PlaneRing K) :
    eval (homogeneousVector x) (chartCoordinates p w hp hw F) =
      eval (coordinateLinearEquiv p w hp hw x) F := by
  change eval (homogeneousVector x) (rename lastEquiv (coordinates p w hp hw F)) = _
  rw [eval_rename]
  have he : homogeneousVector x ∘ lastEquiv = x := by
    funext i
    fin_cases i <;> simp [homogeneousVector]
  rw [he, eval_coordinates]

theorem eval_chart_at_coordinates (p : Fin 3 → K) (w : Fin 2 → K)
    (hp : p 0 ≠ 0) (hw : w 0 ≠ 0) (a : K) (u : Fin 2 → K) (F : PlaneRing K) :
    eval u (chartAt a (chartCoordinates p w hp hw F)) =
      eval (coordinateLinearEquiv p w hp hw (liftVector a u)) F := by
  rw [eval_chartAt]
  have he : (fun i : Option (Fin 2) => i.elim a u) = homogeneousVector (liftVector a u) := by
    funext i
    cases i with
    | none => rfl
    | some i => fin_cases i <;> rfl
  rw [he, eval_chartCoordinates]

theorem chart_coordinate_ne_zero_of_common_zero
    (p : Fin 3 → K) (w : Fin 2 → K) (hp : p 0 ≠ 0) (hw : w 0 ≠ 0)
    (F G : PlaneRing K) (m n : ℕ) (hm : 0 < m) (hn : 0 < n)
    (hF : F.IsHomogeneous m) (hG : G.IsHomogeneous n)
    (hFrest : lineRestriction p w F ≠ 0) (hGrest : lineRestriction p w G ≠ 0)
    (hrest : IsRelPrime (lineRestriction p w F) (lineRestriction p w G))
    (v : Fin 3 → K) (hv : v ≠ 0) (hvF : eval v F = 0) (hvG : eval v G = 0) :
    (coordinateLinearEquiv p w hp hw).symm v 2 ≠ 0 := by
  let g := coordinateLinearEquiv p w hp hw
  let x := g.symm v
  intro hx2
  let u : Fin 2 → K := ![x 0, x 1]
  have he : liftVector 0 u = x := by
    funext i
    fin_cases i <;> simp [liftVector, u]
    exact hx2.symm
  have huF : eval u (lineRestriction p w F) = 0 := by
    rw [← chart_at_zero_coordinates p w hp hw F, eval_chart_at_coordinates, he]
    simpa only [x, g, LinearEquiv.apply_symm_apply] using hvF
  have huG : eval u (lineRestriction p w G) = 0 := by
    rw [← chart_at_zero_coordinates p w hp hw G, eval_chart_at_coordinates, he]
    simpa only [x, g, LinearEquiv.apply_symm_apply] using hvG
  have hu := binary_common_zero_eq_zero _ _ m n hm hn
    (lineRestriction_homogeneous p w F m hF) (lineRestriction_homogeneous p w G n hG)
    hFrest hGrest hrest u huF huG
  have hx : x = 0 := by
    funext i
    fin_cases i
    · exact congrFun hu 0
    · exact congrFun hu 1
    · exact hx2
  apply hv
  calc
    v = g x := (g.apply_symm_apply v).symm
    _ = 0 := by rw [hx, map_zero]

def normalizedAffinePoint (p : Fin 3 → K) (w : Fin 2 → K) (hp : p 0 ≠ 0) (hw : w 0 ≠ 0)
    (v : Fin 3 → K) : Fin 2 → K :=
  fun i => (coordinateLinearEquiv p w hp hw).symm v i.castSucc /
    (coordinateLinearEquiv p w hp hw).symm v 2

theorem normalized_liftVector (p : Fin 3 → K) (w : Fin 2 → K) (hp : p 0 ≠ 0) (hw : w 0 ≠ 0)
    (v : Fin 3 → K) (hchart : (coordinateLinearEquiv p w hp hw).symm v 2 ≠ 0) :
    liftVector 1 (normalizedAffinePoint p w hp hw v) =
      ((coordinateLinearEquiv p w hp hw).symm v 2)⁻¹ • (coordinateLinearEquiv p w hp hw).symm v := by
  funext i
  fin_cases i <;> simp [liftVector, normalizedAffinePoint, div_eq_mul_inv, mul_comm, hchart]

theorem eval_affineForm_normalized (p : Fin 3 → K) (w : Fin 2 → K) (hp : p 0 ≠ 0) (hw : w 0 ≠ 0)
    (v : Fin 3 → K) (hchart : (coordinateLinearEquiv p w hp hw).symm v 2 ≠ 0)
    (F : PlaneRing K) (m : ℕ) (hF : F.IsHomogeneous m) :
    eval (normalizedAffinePoint p w hp hw v) (affineForm p w hp hw F) =
      (((coordinateLinearEquiv p w hp hw).symm v 2)⁻¹) ^ m * eval v F := by
  rw [affineForm, eval_chart_at_coordinates, normalized_liftVector p w hp hw v hchart,
    map_smul, LinearEquiv.apply_symm_apply]
  exact LinearEvaluationTransport.homogeneous_eval_smul F m hF _ v

theorem normalized_points_injective
    (p : Fin 3 → K) (w : Fin 2 → K) (hp : p 0 ≠ 0) (hw : w 0 ≠ 0)
    (P Q : PlanePointModel.Plane K)
    (hP : (coordinateLinearEquiv p w hp hw).symm P.rep 2 ≠ 0)
    (hQ : (coordinateLinearEquiv p w hp hw).symm Q.rep 2 ≠ 0)
    (heq : normalizedAffinePoint p w hp hw P.rep = normalizedAffinePoint p w hp hw Q.rep) : P = Q := by
  let g := coordinateLinearEquiv p w hp hw
  let a := g.symm P.rep 2
  let b := g.symm Q.rep 2
  have hv : a⁻¹ • g.symm P.rep = b⁻¹ • g.symm Q.rep := by
    rw [← normalized_liftVector p w hp hw P.rep hP, ← normalized_liftVector p w hp hw Q.rep hQ, heq]
  have hg : a⁻¹ • P.rep = b⁻¹ • Q.rep := by
    simpa only [map_smul, LinearEquiv.apply_symm_apply] using congrArg g hv
  have hscale : (a * b⁻¹) • Q.rep = P.rep := by
    have ha : a ≠ 0 := hP
    have h := congrArg (fun x => a • x) hg.symm
    simpa only [smul_smul, mul_inv_cancel₀ ha, one_smul] using h
  have hmk := (Projectivization.mk_eq_mk_iff' K P.rep Q.rep P.rep_nonzero Q.rep_nonzero).mpr ⟨a * b⁻¹, hscale⟩
  simpa only [Projectivization.mk_rep] using hmk

theorem exists_affine_chart_avoiding_common_zeros [Infinite K]
    (F G : PlaneRing K) (m n : ℕ) (hm : 0 < m) (hn : 0 < n)
    (hF : F.IsHomogeneous m) (hG : G.IsHomogeneous n)
    (hF0 : F ≠ 0) (hG0 : G ≠ 0) (hcop : IsRelPrime F G) :
    ∃ p : Fin 3 → K, ∃ w : Fin 2 → K, ∃ hp : p 0 ≠ 0, ∃ hw : w 0 ≠ 0,
      (affineForm p w hp hw F).totalDegree = m ∧
      (affineForm p w hp hw G).totalDegree = n ∧
      homogeneousComponent m (affineForm p w hp hw F) ≠ 0 ∧
      homogeneousComponent n (affineForm p w hp hw G) ≠ 0 ∧
      IsRelPrime (homogeneousComponent m (affineForm p w hp hw F))
        (homogeneousComponent n (affineForm p w hp hw G)) ∧
      ∀ v : Fin 3 → K, v ≠ 0 → eval v F = 0 → eval v G = 0 →
        chartFunctional p w hp hw v ≠ 0 := by
  obtain ⟨p, w, hp, hw, hFrest, hGrest, hrest⟩ := exists_line_nondegenerate F G m n hF hG hF0 hG0 hcop
  refine ⟨p, w, hp, hw, affineForm_totalDegree p w hp hw F m hF hFrest,
    affineForm_totalDegree p w hp hw G n hG hGrest, ?_, ?_, ?_, ?_⟩
  · rwa [top_affineForm p w hp hw F m hF]
  · rwa [top_affineForm p w hp hw G n hG]
  · rwa [top_affineForm p w hp hw F m hF, top_affineForm p w hp hw G n hG]
  · intro v hv hvF hvG
    exact chart_coordinate_ne_zero_of_common_zero p w hp hw F G m n hm hn hF hG
      hFrest hGrest hrest v hv hvF hvG

end Cylinder.CompleteIntersectionAffinePoints

end
