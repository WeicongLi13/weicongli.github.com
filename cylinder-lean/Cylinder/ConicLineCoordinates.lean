module

public import Cylinder.ExactRayMomentsCoordinates
public import Cylinder.BlackProjectionRationalLines
public import Mathlib.Algebra.MvPolynomial.Funext

/-! Genuine invertible coordinates taking a prescribed nonzero linear
functional to the last coordinate. Polynomial pullback is an actual
algebra equivalence and preserves irreducibility. -/

@[expose] public section
noncomputable section
open scoped Classical

namespace Cylinder.ConicLineCoordinates
open MvPolynomial Cylinder.HilbertEvaluation Cylinder.LinearEvaluationTransport
open Cylinder.PlaneLinearForms Cylinder.RationalPlaneLine

variable {K : Type*} [Field K]

theorem exists_functional_coordinates (ell : Module.Dual K (Fin 3 → K)) (hell : ell ≠ 0) :
    ∃ g : (Fin 3 → K) ≃ₗ[K] (Fin 3 → K), ∀ x, ell (g x) = x 2 := by
  let target : Module.Dual K (Fin 3 → K) := LinearMap.proj (2 : Fin 3)
  have ht : target ≠ 0 := by
    intro hz
    have h := congrArg (fun f : Module.Dual K (Fin 3 → K) => f (Pi.single (2 : Fin 3) 1)) hz
    change (1 : K) = 0 at h
    exact one_ne_zero h
  let u : Fin 1 → Module.Dual K (Fin 3 → K) := fun _ => ell
  let w : Fin 1 → Module.Dual K (Fin 3 → K) := fun _ => target
  have hu : LinearIndependent K u := linearIndependent_unique_iff.mpr hell
  have hw : LinearIndependent K w := linearIndependent_unique_iff.mpr ht
  let f : Submodule.span K (Set.range u) ≃ₗ[K] Submodule.span K (Set.range w) :=
    hu.linearCombinationEquiv.symm.trans hw.linearCombinationEquiv
  let _ : FiniteDimensional K (Submodule.span K (Set.range u)) :=
    FiniteDimensional.span_of_finite K (Set.finite_range u)
  obtain ⟨h, hh⟩ := Submodule.exists_linearEquiv_restrict_eq f
  have he : h ell = target := by
    simpa [f, u, w] using (hh (hu.linearCombinationEquiv (Finsupp.single (0 : Fin 1) 1))).symm
  refine ⟨ExactRayMomentsCoordinates.primalOfDual h, ?_⟩
  intro x
  change (ExactRayMomentsCoordinates.primalOfDual h).dualMap ell x = x 2
  rw [ExactRayMomentsCoordinates.primalOfDual_dualMap, he]
  rfl

section Polynomial
variable [Infinite K]

def pullbackEquiv (g : (Fin 3 → K) ≃ₗ[K] (Fin 3 → K)) : PlaneRing K ≃ₐ[K] PlaneRing K where
  toFun := linearPullback g
  invFun := linearPullback g.symm
  left_inv P := by
    apply MvPolynomial.funext
    intro x
    rw [linearPullback_eval, linearPullback_eval, LinearEquiv.apply_symm_apply]
  right_inv P := by
    apply MvPolynomial.funext
    intro x
    rw [linearPullback_eval, linearPullback_eval, LinearEquiv.symm_apply_apply]
  map_mul' := map_mul (aeval (linearCoordinate g))
  map_add' := map_add (aeval (linearCoordinate g))
  commutes' := (aeval (linearCoordinate g)).commutes

theorem pullback_irreducible (g : (Fin 3 → K) ≃ₗ[K] (Fin 3 → K)) (Q : PlaneRing K)
    (hQ : Irreducible Q) : Irreducible (linearPullback g Q) :=
  (MulEquiv.irreducible_iff (f := (pullbackEquiv g).toMulEquiv)).mpr hQ

theorem exists_line_coordinates (ell : PlaneRing K) (hell : ell.IsHomogeneous 1) (hell0 : ell ≠ 0) :
    ∃ g : (Fin 3 → K) ≃ₗ[K] (Fin 3 → K), linearPullback g ell = X 2 := by
  obtain ⟨a, ha⟩ := exists_coefficients ell hell
  have ha0 := coefficients_ne_zero ell a hell0 ha
  let ellMap := BlackProjectionRationalLines.dotMap a
  have hm : ellMap ≠ 0 := by
    intro hz
    obtain ⟨v, hv⟩ := BlackProjectionRationalLines.dotMap_surjective a ha0 1
    have h := congrArg (fun f : Module.Dual K (Fin 3 → K) => f v) hz
    change ellMap v = 0 at h
    rw [hv] at h
    exact one_ne_zero h
  obtain ⟨g, hg⟩ := exists_functional_coordinates ellMap hm
  refine ⟨g, ?_⟩
  apply MvPolynomial.funext
  intro x
  rw [linearPullback_eval, ha, eval_linearForm, eval_X]
  exact hg x

end Polynomial
end Cylinder.ConicLineCoordinates
end
