module
public import Cylinder.LinearEvaluationTransport
@[expose] public section
noncomputable section
open scoped Classical BigOperators
namespace Cylinder.MomentCoordinateTransport
open MvPolynomial Cylinder.LinearEvaluationTransport
variable {K σ : Type*} [Field K] [Fintype σ]
/-- Polynomial substitution composes algebraically, including over finite
fields, where equality of polynomial functions alone would not suffice. -/
theorem linearPullback_linearCoordinate
    (g h : (σ → K) ≃ₗ[K] (σ → K)) (j : σ) :
    linearPullback g (linearCoordinate h j) = linearCoordinate (g.trans h) j := by
  simp only [linearPullback, linearCoordinate, map_sum, map_mul, aeval_C, aeval_X,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  simp only [MvPolynomial.algebraMap_eq, ← mul_assoc, ← map_mul, ← Finset.sum_mul, ← map_sum]
  have hcoord := linearCoordinate_eval h j (g (Pi.single k 1))
  have he : (∑ i, h (Pi.single i 1) j * g (Pi.single k 1) i) =
      h (g (Pi.single k 1)) j := by
    simpa only [linearCoordinate, map_sum, map_mul, eval_C, eval_X] using hcoord
  rw [he]
  rfl

theorem linearPullback_comp (g h : (σ → K) ≃ₗ[K] (σ → K)) (F : MvPolynomial σ K) :
    linearPullback g (linearPullback h F) = linearPullback (g.trans h) F := by
  have heq : (aeval (linearCoordinate g)).comp (aeval (linearCoordinate h)) =
      aeval (linearCoordinate (g.trans h)) := by
    ext j : 1
    simpa only [AlgHom.comp_apply, aeval_X, linearPullback] using
      linearPullback_linearCoordinate g h j
  exact congrArg (fun f : MvPolynomial σ K →ₐ[K] MvPolynomial σ K => f F) heq

@[simp] theorem linearPullback_refl (F : MvPolynomial σ K) :
    linearPullback (LinearEquiv.refl K (σ → K)) F = F := by
  have heq : aeval (linearCoordinate (LinearEquiv.refl K (σ → K))) =
      AlgHom.id K (MvPolynomial σ K) := by
    ext j : 1
    simp [linearCoordinate, Pi.single_apply]
  exact congrArg (fun f : MvPolynomial σ K →ₐ[K] MvPolynomial σ K => f F) heq

@[simp] theorem linearPullback_symm (g : (σ → K) ≃ₗ[K] (σ → K)) (F : MvPolynomial σ K) :
    linearPullback g.symm (linearPullback g F) = F := by
  rw [linearPullback_comp]
  simpa using linearPullback_refl F

theorem linearPullback_injective (g : (σ → K) ≃ₗ[K] (σ → K)) :
    Function.Injective (linearPullback g) := by
  intro F G h
  simpa using congrArg (linearPullback g.symm) h


end Cylinder.MomentCoordinateTransport
end
