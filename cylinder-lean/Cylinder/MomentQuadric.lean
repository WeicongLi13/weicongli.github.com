module

public import Cylinder.ComponentMomentRelations
public import Cylinder.LocalRepresentativeTransport

/-! The literal monic quadratic determined by the first three actual moments.
Its two-ray roots and the first two moments of the residual coefficients are
derived from the moment identities. -/

@[expose] public section
noncomputable section
open scoped Classical BigOperators

namespace Cylinder.MomentQuadric
open MvPolynomial Cylinder.HilbertEvaluation Cylinder.EvaluationProjection
open Cylinder.TwoRayMoments Cylinder.ComponentMomentRelations

variable {K : Type*} [Field K]

def quadric (f g : PlaneRing K) : MvPolynomial (Option (Fin 3)) K :=
  X none ^ 2 - rename Option.some f * X none + (rename Option.some f) ^ 2 - rename Option.some g

theorem quadric_homogeneous (f g : PlaneRing K) (hf : f.IsHomogeneous 1) (hg : g.IsHomogeneous 2) :
    (quadric f g).IsHomogeneous 2 := by
  have hf' := hf.rename_isHomogeneous (f := Option.some)
  have hg' := hg.rename_isHomogeneous (f := Option.some)
  have hprod : (rename Option.some f * (X none : MvPolynomial (Option (Fin 3)) K)).IsHomogeneous 2 :=
    by simpa only [Nat.reduceAdd] using hf'.mul (isHomogeneous_X K none)
  have hpow : (rename Option.some f ^ 2).IsHomogeneous 2 :=
    by simpa only [Nat.reduceMul] using hf'.pow 2
  exact (((isHomogeneous_X_pow (R := K) none 2).sub hprod).add hpow).sub hg'

theorem quadric_eval_ray (f g : PlaneRing K) (a : Fin 3 → K) (t : K) :
    eval (rayPoint a t) (quadric f g) = t ^ 2 - eval a f * t + (eval a f) ^ 2 - eval a g := by
  simp only [quadric, map_sub, map_add, map_mul, map_pow, eval_X, eval_rename, Function.comp_def, rayPoint]

theorem homogeneous_eval_zero (P : PlaneRing K) (n : ℕ) (hP : P.IsHomogeneous n) (hn : 0 < n) :
    eval (0 : Fin 3 → K) P = 0 := by
  rw [eval_zero]
  exact hP.coeff_eq_zero (by simp; omega)

theorem quadric_nonzero (f g : PlaneRing K) (hf : f.IsHomogeneous 1) (hg : g.IsHomogeneous 2) :
    quadric f g ≠ 0 := by
  have heval : eval (rayPoint (0 : Fin 3 → K) 1) (quadric f g) = 1 := by
    rw [quadric_eval_ray, homogeneous_eval_zero f 1 hf (by decide), homogeneous_eval_zero g 2 hg (by decide)]
    ring
  intro hzero
  rw [hzero, map_zero] at heval
  exact zero_ne_one heval

theorem two_ray_quadratic_root (t c : Fin 2 → K) (ht : Function.Injective t)
    (hc : c 0 ≠ 0) (hzero : twoMoment t c 0 = 0) (F G : K)
    (hM2 : twoMoment t c 2 = F * twoMoment t c 1)
    (hM3 : twoMoment t c 3 = G * twoMoment t c 1) :
    ∀ ν, t ν ^ 2 - F * t ν + F ^ 2 - G = 0 := by
  have hM1 := first_moment_ne_zero t c ht hc hzero
  have hF : F = t 0 + t 1 := by
    have hh := normalized_one t c ht hc hzero
    unfold normalizedMoment at hh
    rw [hM2, mul_div_cancel_right₀ F hM1] at hh
    exact hh
  have hG : G = t 0 ^ 2 + t 0 * t 1 + t 1 ^ 2 := by
    have hh := normalized_two t c ht hc hzero
    unfold normalizedMoment at hh
    rw [hM3, mul_div_cancel_right₀ G hM1] at hh
    exact hh
  intro ν
  fin_cases ν
  · change t 0 ^ 2 - F * t 0 + F ^ 2 - G = 0
    rw [hF, hG]
    ring
  · change t 1 ^ 2 - F * t 1 + F ^ 2 - G = 0
    rw [hF, hG]
    ring

section Rays
variable {I : Type*} (r : I → ℕ) (a : I → Fin 3 → K)
variable (t c : ∀ i, Fin (r i) → K)

def residualCoefficients (f g : PlaneRing K) (i : I) (ν : Fin (r i)) : K :=
  c i ν * eval (rayPoint (a i) (t i ν)) (quadric f g)

theorem residual_moment_formula (f g : PlaneRing K) (i : I) (j : ℕ) :
    rayMoment r t (residualCoefficients r a t c f g) i j =
      rayMoment r t c i (j + 2) - eval (a i) f * rayMoment r t c i (j + 1) +
        ((eval (a i) f) ^ 2 - eval (a i) g) * rayMoment r t c i j := by
  unfold rayMoment residualCoefficients
  simp only [quadric_eval_ray, pow_add, pow_one]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro ν _
  ring

theorem residual_first_two_moments (f g : PlaneRing K) (i : I)
    (hM0 : rayMoment r t c i 0 = 0)
    (hM2 : rayMoment r t c i 2 = eval (a i) f * rayMoment r t c i 1)
    (hM3 : rayMoment r t c i 3 = eval (a i) g * rayMoment r t c i 1) :
    rayMoment r t (residualCoefficients r a t c f g) i 0 = 0 ∧
      rayMoment r t (residualCoefficients r a t c f g) i 1 = 0 := by
  constructor
  · rw [residual_moment_formula, zero_add, zero_add, hM2, hM0]
    ring
  · rw [residual_moment_formula]
    change rayMoment r t c i 3 - eval (a i) f * rayMoment r t c i 2 +
      ((eval (a i) f) ^ 2 - eval (a i) g) * rayMoment r t c i 1 = 0
    rw [hM3, hM2]
    ring

theorem quadric_zero_on_two_ray (f g : PlaneRing K) (i : I) (hr : r i = 2)
    (ht : Function.Injective (t i)) (hc : ∀ ν, c i ν ≠ 0)
    (hM0 : rayMoment r t c i 0 = 0)
    (hM2 : rayMoment r t c i 2 = eval (a i) f * rayMoment r t c i 1)
    (hM3 : rayMoment r t c i 3 = eval (a i) g * rayMoment r t c i 1) :
    ∀ ν, eval (rayPoint (a i) (t i ν)) (quadric f g) = 0 := by
  let e := Equiv.cast (congrArg Fin hr)
  let t' := fun ν : Fin 2 => t i (e.symm ν)
  let c' := fun ν : Fin 2 => c i (e.symm ν)
  have hz : twoMoment t' c' 0 = 0 := by simpa only [rayMoment_fin_two r t c i hr] using hM0
  have h2 : twoMoment t' c' 2 = eval (a i) f * twoMoment t' c' 1 := by
    simpa only [rayMoment_fin_two r t c i hr] using hM2
  have h3 : twoMoment t' c' 3 = eval (a i) g * twoMoment t' c' 1 := by
    simpa only [rayMoment_fin_two r t c i hr] using hM3
  have hroot := two_ray_quadratic_root t' c' (ht.comp e.symm.injective) (hc _) hz _ _ h2 h3
  intro ν
  have hh := hroot (e ν)
  simpa only [t', Equiv.symm_apply_apply, quadric_eval_ray] using hh

end Rays

#print axioms quadric_homogeneous
#print axioms quadric_nonzero
#print axioms two_ray_quadratic_root
#print axioms residual_first_two_moments
#print axioms quadric_zero_on_two_ray

end Cylinder.MomentQuadric
end
