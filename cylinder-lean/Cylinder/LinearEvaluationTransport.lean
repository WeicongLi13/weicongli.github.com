module

public import Cylinder.EvaluationProjection
public import Cylinder.PowerEvaluationRelation
public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Tactic.Ring

/-!
# Transporting homogeneous evaluation relations

Linear coordinate changes act by actual polynomial substitution.
Scaling a representative by a nonzero scalar divides its relation
coefficient by the corresponding degree power.
-/

@[expose] public section

noncomputable section

namespace Cylinder.LinearEvaluationTransport

open MvPolynomial
open scoped BigOperators Classical

variable {K σ I : Type*} [Field K] [Fintype σ]

abbrev HomogeneousEvaluationRelation [Fintype I] (x : I → σ → K) (c : I → K) (d : ℕ) : Prop :=
  PowerEvaluationRelation.Relation x c d

theorem vector_eq_sum_single (x : σ → K) : x = ∑ i : σ, x i • Pi.single i 1 := by
  funext j
  simp [Finset.sum_apply, Pi.single_apply]

def linearCoordinate (g : (σ → K) ≃ₗ[K] (σ → K)) (j : σ) : MvPolynomial σ K :=
  ∑ i : σ, C (g (Pi.single i 1) j) * X i

theorem linearCoordinate_homogeneous (g : (σ → K) ≃ₗ[K] (σ → K)) (j : σ) :
    (linearCoordinate g j).IsHomogeneous 1 := by
  apply IsHomogeneous.sum
  intro i _hi
  exact isHomogeneous_C_mul_X _ _

@[simp] theorem linearCoordinate_eval (g : (σ → K) ≃ₗ[K] (σ → K)) (j : σ) (x : σ → K) :
    eval x (linearCoordinate g j) = g x j := by
  have h := congrArg (fun y => g y j) (vector_eq_sum_single x)
  have hexpand : g x j = ∑ i : σ, x i * g (Pi.single i 1) j := by
    simpa [map_sum, map_smul, smul_eq_mul, Finset.sum_apply] using h
  simp only [linearCoordinate, map_sum, map_mul, eval_C, eval_X]
  simpa only [mul_comm] using hexpand.symm

def linearPullback (g : (σ → K) ≃ₗ[K] (σ → K)) (F : MvPolynomial σ K) : MvPolynomial σ K :=
  MvPolynomial.aeval (linearCoordinate g) F

theorem linearPullback_homogeneous (g : (σ → K) ≃ₗ[K] (σ → K))
    (F : MvPolynomial σ K) (d : ℕ) (hF : F.IsHomogeneous d) :
    (linearPullback g F).IsHomogeneous d := by
  simpa only [linearPullback, one_mul] using hF.aeval (linearCoordinate g)
    (linearCoordinate_homogeneous g)

@[simp] theorem linearPullback_eval (g : (σ → K) ≃ₗ[K] (σ → K))
    (F : MvPolynomial σ K) (x : σ → K) : eval x (linearPullback g F) = eval (g x) F := by
  change MvPolynomial.aeval x (MvPolynomial.aeval (linearCoordinate g) F) =
    MvPolynomial.aeval (g x) F
  rw [MvPolynomial.comp_aeval_apply]
  have hvalues : (fun j => MvPolynomial.aeval x (linearCoordinate g j)) = g x := by
    funext j
    exact linearCoordinate_eval g j x
  rw [hvalues]

theorem relation_after_linearEquiv [Fintype I] (x : I → σ → K) (c : I → K) (d : ℕ)
    (g : (σ → K) ≃ₗ[K] (σ → K)) (hrel : HomogeneousEvaluationRelation x c d) :
    HomogeneousEvaluationRelation (fun i => g (x i)) c d := by
  intro F hF
  have h := hrel (linearPullback g F) (linearPullback_homogeneous g F d hF)
  simpa only [linearPullback_eval] using h

theorem homogeneous_eval_smul (F : MvPolynomial σ K) (d : ℕ) (hF : F.IsHomogeneous d)
    (u : K) (x : σ → K) : eval (u • x) F = u ^ d * eval x F := by
  rw [eval_eq', eval_eq', Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro β hβ
  have hdegree : β.degree = d := by
    by_contra hdegree
    exact (MvPolynomial.mem_support_iff.mp hβ) (hF.coeff_eq_zero hdegree)
  have hsum : (∑ i : σ, β i) = d := (Finsupp.degree_eq_sum β).symm.trans hdegree
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow, Finset.prod_mul_distrib]
  rw [Finset.prod_pow_eq_pow_sum, hsum]
  ring

theorem rescaled_coefficient_ne_zero (c u : K) (d : ℕ) (hc : c ≠ 0) (hu : u ≠ 0) :
    c / u ^ d ≠ 0 := div_ne_zero hc (pow_ne_zero d hu)

theorem relation_after_rescaling [Fintype I] (x : I → σ → K) (c u : I → K)
    (hu : ∀ i, u i ≠ 0) (d : ℕ) (hrel : HomogeneousEvaluationRelation x c d) :
    HomogeneousEvaluationRelation (fun i => u i • x i) (fun i => c i / u i ^ d) d := by
  intro F hF
  calc
    (∑ i : I, (c i / u i ^ d) * eval (u i • x i) F) =
        ∑ i : I, c i * eval (x i) F := by
      apply Finset.sum_congr rfl
      intro i _hi
      rw [homogeneous_eval_smul F d hF, ← mul_assoc, div_mul_cancel₀ _ (pow_ne_zero d (hu i))]
    _ = 0 := hrel F hF

end Cylinder.LinearEvaluationTransport

end
