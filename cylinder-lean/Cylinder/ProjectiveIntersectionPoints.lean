module

public import Cylinder.AffineIntersectionPoints
public import Cylinder.CompleteIntersectionAffineDimension

/-! Actual projective common zeros correspond to actual affine common
zeros in an avoiding chart, and hence to all maximal ideals of the
intersection algebra. Both directions use the original equations. -/

@[expose] public section
noncomputable section
open scoped Classical
set_option autoImplicit false

namespace Cylinder.ProjectiveIntersectionPoints

open MvPolynomial Module Cylinder.HilbertEvaluation Cylinder.ProjectiveChartData
open Cylinder.CompleteIntersectionAffinePoints Cylinder.PlaneLineCoordinates
open Cylinder.CurvePolarLocal Cylinder.HomogeneousAffineChart
open Cylinder.AffineIntersectionPoints Cylinder.CompleteIntersectionAffineDimension

variable {K : Type*} [Field K]

abbrev ProjectiveCommonZero (F G : PlaneRing K) :=
  {P : PlanePointModel.Plane K // eval P.rep F = 0 ∧ eval P.rep G = 0}

def toAffine (c : Chart K) (F G : PlaneRing K) (e t : ℕ)
    (hF : F.IsHomogeneous e) (hG : G.IsHomogeneous t) (hgood : GoodChart c F G e t)
    (P : ProjectiveCommonZero F G) :
    CommonZero (dehomogenize (c.coordinates F)) (dehomogenize (c.coordinates G)) := by
  have hp : c.line P.val.rep ≠ 0 := hgood.avoids P.val.rep P.val.rep_nonzero P.property.1 P.property.2
  refine ⟨c.affinePoint P.val, ?_, ?_⟩
  · change eval (normalizedAffinePoint c.a c.b c.ha c.hb P.val.rep)
      (dehomogenize (chartCoordinates c.a c.b c.ha c.hb F)) = 0
    rw [← affineForm_eq_dehomogenize, eval_affineForm_normalized c.a c.b c.ha c.hb
      P.val.rep hp F e hF, P.property.1, mul_zero]
  · change eval (normalizedAffinePoint c.a c.b c.ha c.hb P.val.rep)
      (dehomogenize (chartCoordinates c.a c.b c.ha c.hb G)) = 0
    rw [← affineForm_eq_dehomogenize, eval_affineForm_normalized c.a c.b c.ha c.hb
      P.val.rep hp G t hG, P.property.2, mul_zero]

theorem toAffine_injective (c : Chart K) (F G : PlaneRing K) (e t : ℕ)
    (hF : F.IsHomogeneous e) (hG : G.IsHomogeneous t) (hgood : GoodChart c F G e t) :
    Function.Injective (toAffine c F G e t hF hG hgood) := by
  intro P Q hPQ
  apply Subtype.ext
  exact normalized_points_injective c.a c.b c.ha c.hb P.val Q.val
    (hgood.avoids P.val.rep P.val.rep_nonzero P.property.1 P.property.2)
    (hgood.avoids Q.val.rep Q.val.rep_nonzero Q.property.1 Q.property.2)
    (congrArg Subtype.val hPQ)

theorem normalized_scaled_lift (c : Chart K) (u : K) (hu : u ≠ 0) (x : Fin 2 → K) :
    normalizedAffinePoint c.a c.b c.ha c.hb
      (u • coordinateLinearEquiv c.a c.b c.ha c.hb (liftVector 1 x)) = x := by
  funext i
  change ((coordinateLinearEquiv c.a c.b c.ha c.hb).symm
      (u • coordinateLinearEquiv c.a c.b c.ha c.hb (liftVector 1 x))) i.castSucc /
      ((coordinateLinearEquiv c.a c.b c.ha c.hb).symm
      (u • coordinateLinearEquiv c.a c.b c.ha c.hb (liftVector 1 x))) 2 = x i
  simp only [map_smul, LinearEquiv.symm_apply_apply, Pi.smul_apply, smul_eq_mul]
  fin_cases i <;> simp [liftVector, hu]

theorem toAffine_surjective (c : Chart K) (F G : PlaneRing K) (e t : ℕ)
    (hF : F.IsHomogeneous e) (hG : G.IsHomogeneous t) (hgood : GoodChart c F G e t) :
    Function.Surjective (toAffine c F G e t hF hG hgood) := by
  intro x
  let g := coordinateLinearEquiv c.a c.b c.ha c.hb
  let v := g (liftVector 1 x.val)
  have hv : v ≠ 0 := by
    intro hz
    have hz' : liftVector 1 x.val = 0 := g.injective (hz.trans (map_zero g).symm)
    exact one_ne_zero (congrFun hz' 2)
  let P := Projectivization.mk K v hv
  obtain ⟨u, hu⟩ := Projectivization.exists_smul_eq_mk_rep K v hv
  rw [Units.smul_def] at hu
  have hvF : eval v F = 0 := by
    rw [← eval_chart_at_coordinates c.a c.b c.ha c.hb 1 x.val F]
    rw [chartAt_one]
    exact x.property.1
  have hvG : eval v G = 0 := by
    rw [← eval_chart_at_coordinates c.a c.b c.ha c.hb 1 x.val G]
    rw [chartAt_one]
    exact x.property.2
  have hPF : eval P.rep F = 0 := by
    rw [← hu, LinearEvaluationTransport.homogeneous_eval_smul F e hF, hvF, mul_zero]
  have hPG : eval P.rep G = 0 := by
    rw [← hu, LinearEvaluationTransport.homogeneous_eval_smul G t hG, hvG, mul_zero]
  refine ⟨⟨P, hPF, hPG⟩, ?_⟩
  apply Subtype.ext
  change normalizedAffinePoint c.a c.b c.ha c.hb P.rep = x.val
  rw [← hu]
  exact normalized_scaled_lift c u.val u.ne_zero x.val

def projectiveAffineEquiv (c : Chart K) (F G : PlaneRing K) (e t : ℕ)
    (hF : F.IsHomogeneous e) (hG : G.IsHomogeneous t) (hgood : GoodChart c F G e t) :
    ProjectiveCommonZero F G ≃
      CommonZero (dehomogenize (c.coordinates F)) (dehomogenize (c.coordinates G)) :=
  Equiv.ofBijective (toAffine c F G e t hF hG hgood)
    ⟨toAffine_injective c F G e t hF hG hgood, toAffine_surjective c F G e t hF hG hgood⟩

def projectiveCommonZeroEquivMaximalSpectrum [IsAlgClosed K]
    (c : Chart K) (F G : PlaneRing K) (e t : ℕ) (he : 0 < e) (ht : 0 < t)
    (hF : F.IsHomogeneous e) (hG : G.IsHomogeneous t) (hgood : GoodChart c F G e t) :
    ProjectiveCommonZero F G ≃ MaximalSpectrum (ChartAlgebra c F G) := by
  letI := chartAlgebra_finiteDimensional c F G e t he ht hgood
  exact (projectiveAffineEquiv c F G e t hF hG hgood).trans
    (commonZeroEquivMaximalSpectrum (dehomogenize (c.coordinates F)) (dehomogenize (c.coordinates G)))

end Cylinder.ProjectiveIntersectionPoints
end
