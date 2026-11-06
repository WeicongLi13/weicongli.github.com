module

public import Cylinder.CompleteIntersectionAffinePoints
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! Both directions of the actual selected plane coordinates preserve degrees. -/

@[expose] public section
noncomputable section

namespace Cylinder.PlaneCoordinateInverse

open MvPolynomial Cylinder.HilbertEvaluation Cylinder.PlaneLineCoordinates
open Cylinder.GenericPlaneLine

variable {K : Type*} [Field K]

def coordinatesOnForms (a : Fin 3 → K) (b : Fin 2 → K) (ha : a 0 ≠ 0) (hb : b 0 ≠ 0) (n : ℕ) :
    Forms K n →ₗ[K] Forms K n where
  toFun H := ⟨coordinates a b ha hb H.val, coordinates_homogeneous a b ha hb H.val n H.property⟩
  map_add' H J := by apply Subtype.ext; exact map_add _ _ _
  map_smul' c H := by
    apply Subtype.ext
    exact (coordinates a b ha hb).toLinearEquiv.map_smul c H.val

theorem coordinatesOnForms_injective (a : Fin 3 → K) (b : Fin 2 → K)
    (ha : a 0 ≠ 0) (hb : b 0 ≠ 0) (n : ℕ) :
    Function.Injective (coordinatesOnForms a b ha hb n) := by
  intro H J hHJ
  apply Subtype.ext
  exact (coordinates a b ha hb).injective (congrArg Subtype.val hHJ)

theorem coordinates_symm_homogeneous (a : Fin 3 → K) (b : Fin 2 → K)
    (ha : a 0 ≠ 0) (hb : b 0 ≠ 0) (H : PlaneRing K) (n : ℕ) (hH : H.IsHomogeneous n) :
    ((coordinates a b ha hb).symm H).IsHomogeneous n := by
  have hsurj : Function.Surjective (coordinatesOnForms a b ha hb n) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank rfl).mp
      (coordinatesOnForms_injective a b ha hb n)
  obtain ⟨J, hJ⟩ := hsurj ⟨H, hH⟩
  have hval : coordinates a b ha hb J.val = H := congrArg Subtype.val hJ
  have hjval : J.val = (coordinates a b ha hb).symm H := by
    simpa only [AlgEquiv.symm_apply_apply] using congrArg (coordinates a b ha hb).symm hval
  rw [← hjval]
  exact J.property

theorem chartCoordinates_symm_homogeneous (a : Fin 3 → K) (b : Fin 2 → K)
    (ha : a 0 ≠ 0) (hb : b 0 ≠ 0)
    (H : Cylinder.CurvePolarLocal.HomogeneousPlanePolynomial (K := K))
    (n : ℕ) (hH : H.IsHomogeneous n) :
    ((chartCoordinates a b ha hb).symm H).IsHomogeneous n := by
  change ((coordinates a b ha hb).symm (rename lastEquiv.symm H)).IsHomogeneous n
  exact coordinates_symm_homogeneous a b ha hb _ n hH.rename_isHomogeneous

end Cylinder.PlaneCoordinateInverse

end
