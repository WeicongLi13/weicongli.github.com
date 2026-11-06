module

public import Cylinder.VandermondeMoments
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.Algebra.Module.Submodule.Union
public meta import Lean.Elab.Tactic.Omega

/-!
# Homogeneous evaluation relations after projection

Directions are represented by nonzero vectors `a i`.  A point on ray `i`
is the actual vector `(a i, t i ν)`, with the last coordinate encoded by
`none` and the direction coordinates by `some`.  Independence means
surjectivity of the homogeneous polynomial evaluation map.

Over an infinite field, a linear form avoiding all finitely many
directions is obtained from Mathlib's finite-subspace avoidance theorem.
Multiplication by this form proves persistence of independence in higher
degrees. Testing the original relation against `T^j G` then gives actual
moment equations, to which the Vandermonde theorem applies.
-/

@[expose] public section

noncomputable section

open scoped Classical

namespace Cylinder.EvaluationProjection

open MvPolynomial Finset

variable {K σ I : Type*} [Field K]

/-- Independence of the normalized direction representatives in degree
`a`, expressed using actual homogeneous polynomials and their values. -/
def Independent (v : I → σ → K) (a : ℕ) : Prop :=
  ∀ w : I → K, ∃ G : MvPolynomial σ K,
    G.IsHomogeneous a ∧ ∀ i, eval (v i) G = w i

/-- Evaluation at a point as a linear functional on the polynomial ring. -/
def evaluationDual (v : σ → K) : Module.Dual K (MvPolynomial σ K) where
  toFun := eval v
  map_add' G H := map_add (eval v) G H
  map_smul' c G := by simp only [smul_eval, RingHom.id_apply, smul_eq_mul]

@[simp] theorem evaluationDual_apply (v : σ → K) (G : MvPolynomial σ K) :
    evaluationDual v G = eval v G := rfl

/-- A single homogeneous linear form can avoid a finite collection of
nonzero direction representatives over an infinite field. -/
theorem exists_linear_form_avoiding [Fintype I] [Infinite K]
    (v : I → σ → K) (hv : ∀ i, v i ≠ 0) :
    ∃ L : MvPolynomial σ K, L.IsHomogeneous 1 ∧ ∀ i, eval (v i) L ≠ 0 := by
  apply Module.Dual.exists_forall_mem_ne_zero_of_forall_exists
    (homogeneousSubmodule σ K 1) (fun i => evaluationDual (v i))
  intro i
  obtain ⟨s, hs⟩ : ∃ s, v i s ≠ 0 := by
    by_contra h
    apply hv i
    funext s
    by_contra hs
    exact h ⟨s, hs⟩
  refine ⟨X s, isHomogeneous_X K s, ?_⟩
  simpa only [evaluationDual_apply, eval_X] using hs

/-- Homogeneous evaluation surjectivity persists in every higher degree.
The avoiding linear form is constructed, not assumed. -/
theorem independent_of_le [Fintype I] [Infinite K]
    (v : I → σ → K) (hv : ∀ i, v i ≠ 0)
    (a b : ℕ) (hab : a ≤ b) (hind : Independent v a) : Independent v b := by
  obtain ⟨L, hL, hLval⟩ := exists_linear_form_avoiding v hv
  intro w
  obtain ⟨G, hG, hGval⟩ := hind (fun i => w i / (eval (v i) L) ^ (b - a))
  refine ⟨G * L ^ (b - a), ?_, ?_⟩
  · have hdegree : a + 1 * (b - a) = b := by omega
    have hh := hG.mul (hL.pow (b - a))
    rw [hdegree] at hh
    exact hh
  · intro i
    rw [map_mul, map_pow, hGval]
    exact div_mul_cancel₀ _ (pow_ne_zero (b - a) (hLval i))

/-- The vector representing a point on a projection ray. -/
def rayPoint (v : σ → K) (t : K) : Option σ → K
  | none => t
  | some s => v s

/-- A degree-`d` evaluation relation on the actual normalized points. -/
def EvaluationRelation [Fintype I] (v : I → σ → K) (r : I → ℕ)
    (t c : ∀ i, Fin (r i) → K) (d : ℕ) : Prop :=
  ∀ F : MvPolynomial (Option σ) K, F.IsHomogeneous d →
    (∑ i : I, ∑ ν : Fin (r i), c i ν * eval (rayPoint (v i) (t i ν)) F) = 0

/-- The mixed moment of the normalized coefficients on one ray. -/
def rayMoment (r : I → ℕ) (t c : ∀ i, Fin (r i) → K) (i : I) (j : ℕ) : K :=
  ∑ ν : Fin (r i), c i ν * t i ν ^ j

/-- Testing against `T^j G` is an actual polynomial evaluation identity. -/
theorem moment_evaluation_relation [Fintype I]
    (v : I → σ → K) (r : I → ℕ) (t c : ∀ i, Fin (r i) → K)
    (d j : ℕ) (hj : j ≤ d)
    (hrel : EvaluationRelation v r t c d)
    (G : MvPolynomial σ K) (hG : G.IsHomogeneous (d - j)) :
    (∑ i : I, rayMoment r t c i j * eval (v i) G) = 0 := by
  have htest : (X (none : Option σ) ^ j * rename Option.some G).IsHomogeneous d := by
    have hh := (isHomogeneous_X_pow (R := K) (none : Option σ) j).mul
      (hG.rename_isHomogeneous (f := Option.some))
    have hdegree : j + (d - j) = d := by omega
    exact hdegree ▸ hh
  have h := hrel (X (none : Option σ) ^ j * rename Option.some G) htest
  simp only [map_mul, map_pow, eval_X, eval_rename, Function.comp_def, rayPoint] at h
  simpa only [rayMoment, mul_assoc, Finset.sum_mul] using h

/-- Direction independence forces each of the first `d-a+1` moments
on every ray to vanish. -/
theorem rayMoment_eq_zero [Fintype I] [Infinite K]
    (v : I → σ → K) (hv : ∀ i, v i ≠ 0)
    (r : I → ℕ) (t c : ∀ i, Fin (r i) → K)
    (d a : ℕ) (ha : a ≤ d) (hind : Independent v a)
    (hrel : EvaluationRelation v r t c d)
    (i : I) (j : ℕ) (hj : j ≤ d - a) : rayMoment r t c i j = 0 := by
  have hjd : j ≤ d := by omega
  have hind' : Independent v (d - j) := independent_of_le v hv a (d - j) (by omega) hind
  obtain ⟨G, hG, hGval⟩ := hind' (fun k => if k = i then 1 else 0)
  have h := moment_evaluation_relation v r t c d j hjd hrel G hG
  simpa [hGval] using h

/-- The coordinate form of Lemma `lem:vandermonde`: no moment equations
or persistence of independence are assumed as extra hypotheses. -/
theorem ray_size_lower_bound_of_evaluation_relation [Fintype I] [Infinite K]
    (v : I → σ → K) (hv : ∀ i, v i ≠ 0)
    (r : I → ℕ) (hr : ∀ i, 0 < r i)
    (t c : ∀ i, Fin (r i) → K)
    (ht : ∀ i, Function.Injective (t i)) (hc : ∀ i ν, c i ν ≠ 0)
    (d a : ℕ) (ha : a ≤ d) (hind : Independent v a)
    (hrel : EvaluationRelation v r t c d) :
    ∀ i, d - a + 2 ≤ r i := by
  intro i
  apply VandermondeMoments.ray_size_lower_bound_of_degree
    (t i) (c i) (hr i) (ht i) (hc i) d a
  intro j hj
  exact rayMoment_eq_zero v hv r t c d a ha hind hrel i j hj

end Cylinder.EvaluationProjection
