module

public import Cylinder.PlaneCoordinateInverse
public import Cylinder.PlaneNumericalCharacter
public import Cylinder.FiniteEvaluationDuality

/-! Actual chart data for the original finite projective complete intersection. -/

@[expose] public section
noncomputable section
open scoped Classical LinearAlgebra.Projectivization

namespace Cylinder.ProjectiveChartData

open MvPolynomial Cylinder.HilbertEvaluation Cylinder.PlaneLineCoordinates
open Cylinder.CompleteIntersectionChart Cylinder.CompleteIntersectionAffinePoints
open Cylinder.CurvePolarLocal Cylinder.FiniteEvaluationDuality

variable {K : Type*} [Field K]

structure Chart (K : Type*) [Field K] where
  a : Fin 3 → K
  b : Fin 2 → K
  ha : a 0 ≠ 0
  hb : b 0 ≠ 0

def Chart.coordinates (c : Chart K) : PlaneRing K ≃ₐ[K] HomogeneousPlanePolynomial (K := K) :=
  chartCoordinates c.a c.b c.ha c.hb

def Chart.line (c : Chart K) : Module.Dual K (Fin 3 → K) := chartFunctional c.a c.b c.ha c.hb

def Chart.affinePoint (c : Chart K) (P : PlanePointModel.Plane K) : Fin 2 → K :=
  normalizedAffinePoint c.a c.b c.ha c.hb P.rep

def Chart.normalizedPoint (c : Chart K) (P : PlanePointModel.Plane K) : Fin 3 → K :=
  (c.line P.rep)⁻¹ • P.rep

theorem line_ne_zero (c : Chart K) : c.line ≠ 0 := chartFunctional_ne_zero c.a c.b c.ha c.hb

theorem normalizedPoint_line (c : Chart K) (P : PlanePointModel.Plane K) (hP : c.line P.rep ≠ 0) :
    c.line (c.normalizedPoint P) = 1 := by
  change c.line ((c.line P.rep)⁻¹ • P.rep) = 1
  rw [map_smul]
  change (c.line P.rep)⁻¹ * c.line P.rep = 1
  exact inv_mul_cancel₀ hP

theorem eval_normalized_coordinates (c : Chart K) (P : PlanePointModel.Plane K)
    (hP : c.line P.rep ≠ 0) (H : PlaneRing K) (n : ℕ) (hH : H.IsHomogeneous n) :
    eval (normalizedPoints (fun _ : Unit => c.affinePoint P) ()) (c.coordinates H) =
      eval (c.normalizedPoint P) H := by
  have h := eval_affineForm_normalized c.a c.b c.ha c.hb P.rep hP H n hH
  rw [affineForm_eq_dehomogenize, eval_dehomogenize] at h
  have hs := LinearEvaluationTransport.homogeneous_eval_smul H n hH (c.line P.rep)⁻¹ P.rep
  exact h.trans hs.symm

structure GoodChart (c : Chart K) (F G : PlaneRing K) (e t : ℕ) : Prop where
  degreeF : (dehomogenize (c.coordinates F)).totalDegree = e
  degreeG : (dehomogenize (c.coordinates G)).totalDegree = t
  topF : homogeneousComponent e (dehomogenize (c.coordinates F)) ≠ 0
  topG : homogeneousComponent t (dehomogenize (c.coordinates G)) ≠ 0
  topcop : IsRelPrime (homogeneousComponent e (dehomogenize (c.coordinates F)))
    (homogeneousComponent t (dehomogenize (c.coordinates G)))
  avoids : ∀ v : Fin 3 → K, v ≠ 0 → eval v F = 0 → eval v G = 0 → c.line v ≠ 0

theorem exists_goodChart [Infinite K] (F G : PlaneRing K) (e t : ℕ)
    (he : 0 < e) (ht : 0 < t) (hF : F.IsHomogeneous e) (hG : G.IsHomogeneous t)
    (hF0 : F ≠ 0) (hG0 : G ≠ 0) (hcop : IsRelPrime F G) :
    ∃ c : Chart K, GoodChart c F G e t := by
  obtain ⟨a, b, ha, hb, hdegF, hdegG, htopF, htopG, htopcop, hav⟩ :=
    exists_affine_chart_avoiding_common_zeros F G e t he ht hF hG hF0 hG0 hcop
  let c : Chart K := ⟨a, b, ha, hb⟩
  have hcf : dehomogenize (c.coordinates F) = affineForm a b ha hb F :=
    (affineForm_eq_dehomogenize a b ha hb F).symm
  have hcg : dehomogenize (c.coordinates G) = affineForm a b ha hb G :=
    (affineForm_eq_dehomogenize a b ha hb G).symm
  refine ⟨c, ⟨?_, ?_, ?_, ?_, ?_, hav⟩⟩
  · rwa [hcf]
  · rwa [hcg]
  · rwa [hcf]
  · rwa [hcg]
  · rwa [hcf, hcg]

theorem point_line_ne_zero (c : Chart K) (F G : PlaneRing K) (e t : ℕ)
    (hgood : GoodChart c F G e t) (D : Finset (PlanePointModel.Plane K))
    (hpoints : ∀ P : D, eval P.val.rep F = 0 ∧ eval P.val.rep G = 0) :
    ∀ P : D, c.line P.val.rep ≠ 0 :=
  fun P => hgood.avoids P.val.rep P.val.rep_nonzero (hpoints P).1 (hpoints P).2

theorem affinePoints_injective (c : Chart K) (D : Finset (PlanePointModel.Plane K))
    (hchart : ∀ P : D, c.line P.val.rep ≠ 0) :
    Function.Injective (fun P : D => c.affinePoint P.val) := by
  intro P Q hPQ
  exact Subtype.ext (normalized_points_injective c.a c.b c.ha c.hb P.val Q.val
    (hchart P) (hchart Q) hPQ)

theorem affinePoints_common_zero (c : Chart K) (F G : PlaneRing K) (e t : ℕ)
    (hF : F.IsHomogeneous e) (hG : G.IsHomogeneous t) (hgood : GoodChart c F G e t)
    (D : Finset (PlanePointModel.Plane K))
    (hpoints : ∀ P : D, eval P.val.rep F = 0 ∧ eval P.val.rep G = 0) :
    (∀ P : D, eval (c.affinePoint P.val) (dehomogenize (c.coordinates F)) = 0) ∧
    (∀ P : D, eval (c.affinePoint P.val) (dehomogenize (c.coordinates G)) = 0) := by
  have hchart := point_line_ne_zero c F G e t hgood D hpoints
  constructor
  · intro P
    change eval (normalizedAffinePoint c.a c.b c.ha c.hb P.val.rep)
      (dehomogenize (chartCoordinates c.a c.b c.ha c.hb F)) = 0
    rw [← affineForm_eq_dehomogenize]
    rw [eval_affineForm_normalized c.a c.b c.ha c.hb P.val.rep (hchart P) F e hF, (hpoints P).1, mul_zero]
  · intro P
    change eval (normalizedAffinePoint c.a c.b c.ha c.hb P.val.rep)
      (dehomogenize (chartCoordinates c.a c.b c.ha c.hb G)) = 0
    rw [← affineForm_eq_dehomogenize]
    rw [eval_affineForm_normalized c.a c.b c.ha c.hb P.val.rep (hchart P) G t hG, (hpoints P).2, mul_zero]

end Cylinder.ProjectiveChartData

end
