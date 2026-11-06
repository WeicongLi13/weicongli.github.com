module

public import Cylinder.ExactRayMomentsCoordinates
public import Cylinder.BlackProjectionVandermonde

/-! Actual plane equations are normalized in the same black-point coordinates.
Every noncentral plane has its actual projective direction as constant part;
the central black plane is exactly the variable `T`. -/

@[expose] public section
noncomputable section
open scoped Classical BigOperators LinearAlgebra.Projectivization
namespace Cylinder.ExactRayMomentsNormalization
open Cylinder.ProjectiveGeometry Cylinder.DualLineBalance Cylinder.BlackProjection
open Cylinder.ProjectiveProjection Cylinder.ExactRayMomentsCoordinates
open Cylinder.ExactRayMomentsDirections Cylinder.ExactRayMomentsLow
open Cylinder.ProductFrobenius Cylinder.ProductCoordinates Cylinder.ProductRescaling
variable (p : ℕ) [Fact p.Prime]

def productCoordinateMap (b : DualPoint p) : Form p →+*
    Polynomial (MvPolynomial (Fin 3) (ZMod p)) :=
  (MvPolynomial.finSuccEquiv (ZMod p) 3).toRingHom.comp (blackPolynomialEquiv p b).toRingHom

@[simp] theorem productCoordinateMap_C (b : DualPoint p) (a : ZMod p) :
    productCoordinateMap p b (MvPolynomial.C a) = Polynomial.C (MvPolynomial.C a) := by
  simp [productCoordinateMap, blackPolynomialEquiv, polynomialEquiv_C,
    MvPolynomial.finSuccEquiv_apply]

@[simp] theorem productCoordinateMap_plane (b H : DualPoint p) :
    productCoordinateMap p b (planeForm p H) = transformedPlanePolynomial p b H := rfl

theorem directionForm_scalar (a : ZMod p) (v : Fin 3 → ZMod p) :
    directionForm (a • v) = MvPolynomial.C a * directionForm v := by
  simp only [directionForm, Cylinder.PowerEvaluationRelation.linearForm, Pi.smul_apply,
    smul_eq_mul, map_mul, Finset.mul_sum, mul_assoc]

theorem productCoordinateMap_scaled_plane (b H : DualPoint p) (a : ZMod p) :
    productCoordinateMap p b (MvPolynomial.C a * planeForm p H) =
      actualFactor (directionForm (a • (fun j => transformedCoordinates p b H (some j))))
        (a * transformedCoordinates p b H none) := by
  rw [map_mul, productCoordinateMap_C, productCoordinateMap_plane,
    transformed_plane_polynomial, directionForm_scalar]
  simp only [actualFactor, map_mul, mul_add, MvPolynomial.algebraMap_eq]
  ring

def actualDirection (b H : DualPoint p) (hHb : H ≠ b) : BlackProjection.Direction p :=
  projectPoint (ZMod p) (Fin 3) (coordinatePoint p b) (coordinatePoint p H)
    (fun h => hHb (coordinatePoint_injective p h))

theorem exists_noncentral_normalization (b H : DualPoint p) (hHb : H ≠ b) :
    ∃ a : ZMod p, a ≠ 0 ∧
      a • (fun j => transformedCoordinates p b H (some j)) = (actualDirection p b H hHb).rep := by
  obtain ⟨q, hq⟩ := exists_coordinate_rep_unit p H
  have htail : (q : ZMod p) • (fun j => transformedCoordinates p b H (some j)) =
      directionVector (ZMod p) (Fin 3) (coordinatePoint p b) (coordinatePoint p H) := by
    funext j
    change (q : ZMod p) * coordinateChange (ZMod p) (Fin 3) (coordinatePoint p b)
      (dualCoordinates p H.rep) (some j) =
      coordinateChange (ZMod p) (Fin 3) (coordinatePoint p b) (coordinatePoint p H).rep (some j)
    rw [← hq, Units.smul_def, map_smul]
    rfl
  obtain ⟨u, hu⟩ := Projectivization.exists_smul_eq_mk_rep (ZMod p)
    (directionVector (ZMod p) (Fin 3) (coordinatePoint p b) (coordinatePoint p H))
    (directionVector_ne_zero (ZMod p) (Fin 3) (coordinatePoint p b) (coordinatePoint p H)
      (fun h => hHb (coordinatePoint_injective p h)))
  refine ⟨(u : ZMod p) * q, mul_ne_zero (Units.ne_zero u) (Units.ne_zero q), ?_⟩
  rw [mul_smul, htail]
  exact hu

def normalizationScale (b H : DualPoint p) : ZMod p :=
  if hHb : H = b then Classical.choose (exists_centre_normalization p b)
  else Classical.choose (exists_noncentral_normalization p b H hHb)

theorem normalizationScale_nonzero (b H : DualPoint p) : normalizationScale p b H ≠ 0 := by
  unfold normalizationScale
  split_ifs with hHb
  · exact (Classical.choose_spec (exists_centre_normalization p b)).1
  · exact (Classical.choose_spec (exists_noncentral_normalization p b H hHb)).1

def normalizedTime (b H : DualPoint p) : ZMod p :=
  normalizationScale p b H * transformedCoordinates p b H none

theorem normalized_centre_factor (b : DualPoint p) :
    productCoordinateMap p b (scaledPlaneForm p (normalizationScale p b) b) = Polynomial.X := by
  change MvPolynomial.finSuccEquiv (ZMod p) 3 (blackPolynomialEquiv p b
    (MvPolynomial.C (normalizationScale p b b) * planeForm p b)) = _
  rw [normalizationScale, dite_eq_left rfl]
  exact (Classical.choose_spec (exists_centre_normalization p b)).2

theorem normalized_noncentral_factor (b H : DualPoint p) (hHb : H ≠ b) :
    productCoordinateMap p b (scaledPlaneForm p (normalizationScale p b) H) =
      actualFactor (directionForm (actualDirection p b H hHb).rep) (normalizedTime p b H) := by
  rw [scaledPlaneForm, productCoordinateMap_scaled_plane]
  have hs : normalizationScale p b H • (fun j => transformedCoordinates p b H (some j)) =
      (actualDirection p b H hHb).rep := by
    unfold normalizationScale
    rw [dite_eq_right hHb]
    exact (Classical.choose_spec (exists_noncentral_normalization p b H hHb)).2
  rw [hs]
  rfl

end Cylinder.ExactRayMomentsNormalization
end
