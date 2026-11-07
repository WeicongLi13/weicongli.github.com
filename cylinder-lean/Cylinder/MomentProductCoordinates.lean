module

public import Cylinder.ProjectionChart
public import Cylinder.ExactRayMomentsNormalization

/-! The polynomial identities in prescribed projection coordinates are
equivalent to the original plane-product identities for the same residues. -/

@[expose] public section
noncomputable section
open scoped Classical BigOperators
namespace Cylinder.MomentProductCoordinates
open MvPolynomial Cylinder.ProjectiveGeometry Cylinder.ProjectiveBalance
open Cylinder.ProductFrobenius Cylinder.ProductCoordinates Cylinder.ProductRescaling
open Cylinder.BlackProjection Cylinder.ProjectionChart Cylinder.ExactRayMomentsCoordinates
open Cylinder.ExactRayMomentsDirections Cylinder.ExactRayMomentsLow
open Cylinder.DualLineBalance

variable (p : ℕ) [Fact p.Prime] {b : DualPoint p}

def dualChange (C : Chart (coordinatePoint p b)) : DualSpace p ≃ₗ[ZMod p] DualSpace p :=
  ((dualCoordinates p).trans C.g).trans (dualCoordinates p).symm

def polynomialChange (C : Chart (coordinatePoint p b)) : Form p ≃+* Form p :=
  polynomialEquiv p (primalOfDual (dualChange p C))

def coordinateMap (C : Chart (coordinatePoint p b)) :
    Form p ≃+* Polynomial (MvPolynomial (Fin 3) (ZMod p)) :=
  (polynomialChange p C).trans (MvPolynomial.finSuccEquiv (ZMod p) 3).toRingEquiv

@[simp] theorem coordinateMap_C (C : Chart (coordinatePoint p b)) (a : ZMod p) :
    coordinateMap p C (MvPolynomial.C a) = Polynomial.C (MvPolynomial.C a) := by
  simp [coordinateMap, polynomialChange, polynomialEquiv_C, MvPolynomial.finSuccEquiv_apply]

theorem planeForm_image (C : Chart (coordinatePoint p b)) (H : DualPoint p) :
    polynomialChange p C (planeForm p H) = functionalForm p (dualChange p C H.rep) := by
  change polynomialEquiv p (primalOfDual (dualChange p C)) (functionalForm p H.rep) = _
  rw [polynomialEquiv_functionalForm, primalOfDual_dualMap]

theorem transformed_coefficient (C : Chart (coordinatePoint p b)) (H : DualPoint p) (j : Fin 4) :
    dualChange p C H.rep (Pi.single j 1) = C.g (dualCoordinates p H.rep) (finSuccEquiv 3 j) := by
  have hcoord (f : DualSpace p) (o : Option (Fin 3)) :
      dualCoordinates p f o = f (Pi.single ((finSuccEquiv 3).symm o) 1) := rfl
  have hmap : dualCoordinates p (dualChange p C H.rep) = C.g (dualCoordinates p H.rep) := by
    simp [dualChange]
  have hval := congrFun hmap (finSuccEquiv 3 j)
  simpa only [hcoord, Equiv.symm_apply_apply] using hval

theorem plane_factor (C : Chart (coordinatePoint p b)) (H : DualPoint p) :
    coordinateMap p C (planeForm p H) =
      actualFactor (directionForm (fun j => C.g (dualCoordinates p H.rep) (some j)))
        (C.g (dualCoordinates p H.rep) none) := by
  change MvPolynomial.finSuccEquiv (ZMod p) 3 (polynomialChange p C (planeForm p H)) = _
  simp [planeForm_image, functionalForm, linearForm, MvPolynomial.finSuccEquiv_apply,
    Fin.sum_univ_succ, transformed_coefficient, actualFactor, directionForm,
    Cylinder.PowerEvaluationRelation.linearForm]
  rw [add_comm]
  rfl

def factor (C : Chart (coordinatePoint p b)) (a : DualPoint p → ZMod p) (H : DualPoint p) :=
  let v := C.g (a H • dualCoordinates p H.rep)
  actualFactor (directionForm (fun j => v (some j))) (v none)

theorem scaled_factor (C : Chart (coordinatePoint p b)) (a : DualPoint p → ZMod p)
    (H : DualPoint p) : coordinateMap p C (scaledPlaneForm p a H) = factor p C a H := by
  rw [scaledPlaneForm, map_mul, coordinateMap_C, plane_factor]
  simp only [factor, map_smul]
  change Polynomial.C (MvPolynomial.C (a H)) * _ =
    actualFactor (directionForm (a H • (fun j => C.g (dualCoordinates p H.rep) (some j))))
      (a H * C.g (dualCoordinates p H.rep) none)
  rw [ExactRayMomentsNormalization.directionForm_scalar]
  simp only [actualFactor, map_mul, mul_add, MvPolynomial.algebraMap_eq]
  ring

theorem product_identity_iff (S : Finset (Geometry.Point p))
    (C : Chart (coordinatePoint p b)) (a c : DualPoint p → ZMod p) :
    ((∏ H ∈ blackPoints p S, scaledPlaneForm p a H ^ weight p S H) =
      ∑ E ∈ whitePoints p S, MvPolynomial.C (c E) *
        ∏ H ∈ (whitePoints p S).erase E, scaledPlaneForm p a H) ↔
    ((∏ H ∈ blackPoints p S, factor p C a H ^ weight p S H) =
      ∑ E ∈ whitePoints p S, Polynomial.C (MvPolynomial.C (c E)) *
        ∏ H ∈ (whitePoints p S).erase E, factor p C a H) := by
  rw [← (coordinateMap p C).injective.eq_iff]
  simp only [map_prod, map_pow, map_sum, map_mul, coordinateMap_C, scaled_factor]

theorem power_identity_iff (S : Finset (Geometry.Point p))
    (C : Chart (coordinatePoint p b)) (a c : DualPoint p → ZMod p) :
    ((∑ E ∈ whitePoints p S, MvPolynomial.C (c E) * scaledPlaneForm p a E ^ (p - 2)) = 0) ↔
    ((∑ E ∈ whitePoints p S, Polynomial.C (MvPolynomial.C (c E)) *
      factor p C a E ^ (p - 2)) = 0) := by
  rw [← (coordinateMap p C).injective.eq_iff]
  simp only [map_sum, map_mul, map_pow, map_zero, coordinateMap_C, scaled_factor]

end Cylinder.MomentProductCoordinates
end
