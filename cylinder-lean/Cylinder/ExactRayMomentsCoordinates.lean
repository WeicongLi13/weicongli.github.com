module

public import Cylinder.ProductCoordinates
public import Cylinder.BlackProjection
public import Cylinder.ExactRayMomentsDirections
public import Cylinder.ProductRescaling
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.Algebra.MvPolynomial.Equiv

/-!
# The actual primal coordinate change induced by black-point dual coordinates

Finite-dimensional duality constructs the primal linear equivalence whose
dual is the chosen black-point coordinate map. The product polynomial
equivalence therefore acts on the actual plane equations by that same map.
-/

@[expose] public section
noncomputable section
namespace Cylinder.ExactRayMomentsCoordinates
section Dual
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

def primalOfDual (e : Module.Dual K V ≃ₗ[K] Module.Dual K V) : V ≃ₗ[K] V :=
  ((Module.evalEquiv K V).trans e.dualMap).trans (Module.evalEquiv K V).symm

theorem primalOfDual_dualMap (e : Module.Dual K V ≃ₗ[K] Module.Dual K V) :
    (primalOfDual e).dualMap = e := by
  apply LinearEquiv.ext
  intro f
  apply LinearMap.ext
  intro x
  change f ((Module.evalEquiv K V).symm (e.dualMap ((Module.evalEquiv K V) x))) = e f x
  rw [Module.apply_evalEquiv_symm_apply]
  rfl

end Dual

open Cylinder.ProjectiveGeometry Cylinder.ProductFrobenius Cylinder.ProductCoordinates
open Cylinder.BlackProjection Cylinder.ProjectiveProjection
open Cylinder.DualLineBalance
open scoped LinearAlgebra.Projectivization
variable (p : ℕ) [Fact p.Prime]

def blackDualChange (b : DualPoint p) : DualSpace p ≃ₗ[ZMod p] DualSpace p :=
  ((dualCoordinates p).trans (coordinateChange (ZMod p) (Fin 3) (coordinatePoint p b))).trans
    (dualCoordinates p).symm

def blackPrimalChange (b : DualPoint p) : Vector p ≃ₗ[ZMod p] Vector p := primalOfDual (blackDualChange p b)

theorem blackPrimalChange_dualMap (b : DualPoint p) :
    (blackPrimalChange p b).dualMap = blackDualChange p b := primalOfDual_dualMap _

def blackPolynomialEquiv (b : DualPoint p) : Form p ≃+* Form p :=
  polynomialEquiv p (blackPrimalChange p b)

theorem actual_planeForm_image (b H : DualPoint p) :
    blackPolynomialEquiv p b (planeForm p H) = functionalForm p (blackDualChange p b H.rep) := by
  change polynomialEquiv p (blackPrimalChange p b) (functionalForm p H.rep) = _
  rw [polynomialEquiv_functionalForm, blackPrimalChange_dualMap]

def transformedCoordinates (b H : DualPoint p) : Option (Fin 3) → ZMod p :=
  coordinateChange (ZMod p) (Fin 3) (coordinatePoint p b) (dualCoordinates p H.rep)

theorem transformed_coefficient (b H : DualPoint p) (j : Fin 4) :
    blackDualChange p b H.rep (Pi.single j 1) = transformedCoordinates p b H (finSuccEquiv 3 j) := by
  have hcoord (f : DualSpace p) (o : Option (Fin 3)) :
      dualCoordinates p f o = f (Pi.single ((finSuccEquiv 3).symm o) 1) := rfl
  have hmap : dualCoordinates p (blackDualChange p b H.rep) = transformedCoordinates p b H := by
    simp [blackDualChange, transformedCoordinates]
  have hval := congrFun hmap (finSuccEquiv 3 j)
  simpa only [hcoord, Equiv.symm_apply_apply] using hval

def transformedPlanePolynomial (b H : DualPoint p) : Polynomial (MvPolynomial (Fin 3) (ZMod p)) :=
  MvPolynomial.finSuccEquiv (ZMod p) 3 (blackPolynomialEquiv p b (planeForm p H))

theorem transformed_plane_polynomial (b H : DualPoint p) :
    transformedPlanePolynomial p b H =
      Cylinder.ExactRayMomentsLow.actualFactor
        (Cylinder.ExactRayMomentsDirections.directionForm (fun j => transformedCoordinates p b H (some j)))
        (transformedCoordinates p b H none) := by
  simp [transformedPlanePolynomial, actual_planeForm_image, functionalForm, linearForm,
    MvPolynomial.finSuccEquiv_apply, Fin.sum_univ_succ, transformed_coefficient,
    Cylinder.ExactRayMomentsLow.actualFactor, Cylinder.ExactRayMomentsDirections.directionForm,
    Cylinder.PowerEvaluationRelation.linearForm]
  rw [add_comm]
  rfl

theorem transformedCoordinates_nonzero (b H : DualPoint p) :
    transformedCoordinates p b H ≠ 0 := by
  intro h
  apply H.rep_nonzero
  apply (dualCoordinates p).injective
  apply (coordinateChange (ZMod p) (Fin 3) (coordinatePoint p b)).injective
  simpa only [transformedCoordinates, map_zero] using h

theorem coordinatePoint_eq_mk (H : DualPoint p) :
    coordinatePoint p H = Projectivization.mk (ZMod p) (dualCoordinates p H.rep)
      (fun h => H.rep_nonzero ((dualCoordinates p).injective (by simpa using h))) := by
  conv_lhs => rw [← Projectivization.mk_rep H]
  rfl

theorem exists_coordinate_rep_unit (H : DualPoint p) :
    ∃ u : (ZMod p)ˣ, u • dualCoordinates p H.rep = (coordinatePoint p H).rep := by
  obtain ⟨u, hu⟩ := Projectivization.exists_smul_eq_mk_rep (ZMod p) (dualCoordinates p H.rep)
    (fun h => H.rep_nonzero ((dualCoordinates p).injective (by simpa using h)))
  exact ⟨u, by simpa only [← coordinatePoint_eq_mk] using hu⟩

theorem exists_centre_scalar (b : DualPoint p) :
    ∃ β : ZMod p, β ≠ 0 ∧ transformedCoordinates p b b = β • centreAxis (ZMod p) (Fin 3) := by
  obtain ⟨u, hu⟩ := exists_coordinate_rep_unit p b
  rw [Units.smul_def] at hu
  have hscale : (u : ZMod p) • transformedCoordinates p b b = centreAxis (ZMod p) (Fin 3) := by
    change (u : ZMod p) • coordinateChange (ZMod p) (Fin 3) (coordinatePoint p b)
      (dualCoordinates p b.rep) = _
    rw [← map_smul, hu, coordinateChange_centre]
  refine ⟨(↑u : ZMod p)⁻¹, inv_ne_zero (Units.ne_zero u), ?_⟩
  rw [← hscale, smul_smul, inv_mul_cancel₀ (Units.ne_zero u), one_smul]

theorem centre_polynomial (b : DualPoint p) :
    ∃ β : ZMod p, β ≠ 0 ∧ transformedPlanePolynomial p b b =
      Polynomial.C (MvPolynomial.C β) * Polynomial.X := by
  obtain ⟨β, hβ, heq⟩ := exists_centre_scalar p b
  refine ⟨β, hβ, ?_⟩
  rw [transformed_plane_polynomial]
  simp [heq, centreAxis, Cylinder.ExactRayMomentsLow.actualFactor,
    Cylinder.ExactRayMomentsDirections.directionForm, Cylinder.PowerEvaluationRelation.linearForm]

theorem exists_centre_normalization (b : DualPoint p) :
    ∃ a : ZMod p, a ≠ 0 ∧
      MvPolynomial.finSuccEquiv (ZMod p) 3
        (blackPolynomialEquiv p b (MvPolynomial.C a * planeForm p b)) = Polynomial.X := by
  obtain ⟨β, hβ, heq⟩ := centre_polynomial p b
  refine ⟨β⁻¹, inv_ne_zero hβ, ?_⟩
  have hC (a : ZMod p) : MvPolynomial.finSuccEquiv (ZMod p) 3
      (blackPolynomialEquiv p b (MvPolynomial.C a)) = Polynomial.C (MvPolynomial.C a) := by
    simp [blackPolynomialEquiv, polynomialEquiv_C, MvPolynomial.finSuccEquiv_apply]
  rw [map_mul, map_mul, hC]
  change Polynomial.C (MvPolynomial.C β⁻¹) * transformedPlanePolynomial p b b = _
  rw [heq, ← mul_assoc, ← map_mul, ← map_mul, inv_mul_cancel₀ hβ, map_one, map_one, one_mul]

end Cylinder.ExactRayMomentsCoordinates
end
