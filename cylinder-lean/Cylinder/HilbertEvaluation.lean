module

public import Cylinder.EvaluationProjection
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.RingTheory.Ideal.Colon

/-!
# Homogeneous evaluation of a finite set of actual plane points

The Hilbert function here is the rank of evaluation of degree-d forms at
fixed nonzero three-coordinate representatives. No Hilbert-sequence properties
are assumed in its definition.
-/

@[expose] public section
noncomputable section
open scoped Classical BigOperators
namespace Cylinder.HilbertEvaluation
open MvPolynomial Module
variable {K I : Type*} [Field K] [Fintype I]

abbrev PlaneRing (K : Type*) [Field K] := MvPolynomial (Fin 3) K
abbrev Forms (K : Type*) [Field K] (d : ℕ) := homogeneousSubmodule (Fin 3) K d

/-- Distinct projective points, stated on their actual nonzero representatives. -/
def ProjectivelyDistinct (v : I → Fin 3 → K) : Prop :=
  ∀ i j, i ≠ j → ∀ c : K, v j ≠ c • v i

/-- Evaluation of actual homogeneous degree-d forms at the given representatives. -/
def evaluationMap (v : I → Fin 3 → K) (d : ℕ) : Forms K d →ₗ[K] (I → K) where
  toFun P i := eval (v i) P.val
  map_add' P Q := by funext i; exact map_add (eval (v i)) _ _
  map_smul' c P := by funext i; simp only [Submodule.coe_smul_of_tower, smul_eval,
    RingHom.id_apply, Pi.smul_apply, smul_eq_mul]

def evaluationSpace (v : I → Fin 3 → K) (d : ℕ) : Submodule K (I → K) :=
  LinearMap.range (evaluationMap v d)

def hilbert (v : I → Fin 3 → K) (d : ℕ) : ℕ := finrank K (evaluationSpace v d)

instance forms_finiteDimensional (d : ℕ) : FiniteDimensional K (Forms K d) :=
  Module.Finite.iff_fg.mpr (homogeneousSubmodule_fg (Fin 3) K d)

omit [Fintype I] in
theorem mem_evaluationSpace (v : I → Fin 3 → K) (d : ℕ) (w : I → K) :
    w ∈ evaluationSpace v d ↔
      ∃ P : PlaneRing K, P.IsHomogeneous d ∧ ∀ i, eval (v i) P = w i := by
  constructor
  · rintro ⟨P, hP⟩
    exact ⟨P.val, P.property, fun i => congrFun hP i⟩
  · rintro ⟨P, hP, hPw⟩
    exact ⟨⟨P, hP⟩, funext hPw⟩

theorem hilbert_le_card (v : I → Fin 3 → K) (d : ℕ) : hilbert v d ≤ Fintype.card I := by
  simpa [hilbert] using (evaluationSpace v d).finrank_le

/-- Nonzero diagonal rescaling of the evaluation coordinates is an actual linear equivalence. -/
def diagonalEquiv (a : I → K) (ha : ∀ i, a i ≠ 0) : (I → K) ≃ₗ[K] (I → K) where
  toFun w i := a i * w i
  invFun w i := (a i)⁻¹ * w i
  left_inv w := by funext i; simp [ha i]
  right_inv w := by funext i; simp [ha i]
  map_add' w z := by funext i; exact mul_add _ _ _
  map_smul' c w := by funext i; simp [mul_left_comm]

omit [Fintype I] in
theorem rescaled_evaluation_le (v : I → Fin 3 → K) (d : ℕ)
    (L : PlaneRing K) (hL : L.IsHomogeneous 1) (hLv : ∀ i, eval (v i) L ≠ 0) :
    (evaluationSpace v d).map (diagonalEquiv (fun i => eval (v i) L) hLv).toLinearMap ≤
      evaluationSpace v (d + 1) := by
  intro w hw
  obtain ⟨z, hz, rfl⟩ := Submodule.mem_map.mp hw
  obtain ⟨P, hP, hPz⟩ := (mem_evaluationSpace v d z).mp hz
  apply (mem_evaluationSpace v (d + 1) _).mpr
  refine ⟨L * P, ?_, ?_⟩
  · convert hL.mul hP using 1; omega
  · intro i
    change eval (v i) (L * P) = eval (v i) L * z i
    rw [map_mul, hPz]

theorem hilbert_succ_mono_of_avoiding (v : I → Fin 3 → K) (d : ℕ)
    (L : PlaneRing K) (hL : L.IsHomogeneous 1) (hLv : ∀ i, eval (v i) L ≠ 0) :
    hilbert v d ≤ hilbert v (d + 1) := by
  let e := diagonalEquiv (fun i => eval (v i) L) hLv
  have he := (Submodule.equivMapOfInjective e.toLinearMap e.injective (evaluationSpace v d)).finrank_eq
  exact he.trans_le (Submodule.finrank_mono (rescaled_evaluation_le v d L hL hLv))

/-- Monotonicity is derived using a constructed avoiding linear form. -/
theorem hilbert_monotone [Infinite K] (v : I → Fin 3 → K) (hv : ∀ i, v i ≠ 0) :
    Monotone (hilbert v) := by
  obtain ⟨L, hL, hLv⟩ := EvaluationProjection.exists_linear_form_avoiding v hv
  exact monotone_nat_of_le_succ (fun d => hilbert_succ_mono_of_avoiding v d L hL hLv)

omit [Fintype I] in
/-- Actual rank-nullity, identifying the dimension of vanishing degree-d forms. -/
theorem ideal_piece_dimension (v : I → Fin 3 → K) (d : ℕ) :
    hilbert v d + finrank K (LinearMap.ker (evaluationMap v d)) = finrank K (Forms K d) :=
  (evaluationMap v d).finrank_range_add_finrank_ker


omit [Fintype I] in
/-- An actual degree-one form separates two distinct projective representatives. -/
theorem exists_linear_separator (v : I → Fin 3 → K) (hsep : ProjectivelyDistinct v)
    (L : PlaneRing K) (hL : L.IsHomogeneous 1) (hLv : ∀ i, eval (v i) L ≠ 0)
    (i j : I) (hij : i ≠ j) :
    ∃ F : PlaneRing K, F.IsHomogeneous 1 ∧ eval (v i) F ≠ 0 ∧ eval (v j) F = 0 := by
  have he : ∃ a : Fin 3, eval (v j) L * v i a - v j a * eval (v i) L ≠ 0 := by
    by_contra hn
    push Not at hn
    apply hsep i j hij ((eval (v i) L)⁻¹ * eval (v j) L)
    funext a
    change v j a = ((eval (v i) L)⁻¹ * eval (v j) L) * v i a
    have hcross := sub_eq_zero.mp (hn a)
    calc
      v j a = (eval (v i) L)⁻¹ * (eval (v i) L * v j a) := by simp [hLv i]
      _ = (eval (v i) L)⁻¹ * (eval (v j) L * v i a) := by rw [mul_comm _ (v j a), ← hcross]
      _ = _ := by rw [mul_assoc]
  obtain ⟨a, ha⟩ := he
  refine ⟨C (eval (v j) L) * X a - C (v j a) * L, ?_, ?_, ?_⟩
  · exact (isHomogeneous_C_mul_X _ _).sub (hL.C_mul _)
  · simpa only [map_sub, map_mul, eval_C, eval_X] using ha
  · simp only [map_sub, map_mul, eval_C, eval_X, mul_comm (eval (v j) L) (v j a), sub_self]

/-- A product of separating lines isolates a single projective point in degree |D|-1. -/
theorem exists_point_separator (v : I → Fin 3 → K) (hsep : ProjectivelyDistinct v)
    (L : PlaneRing K) (hL : L.IsHomogeneous 1) (hLv : ∀ i, eval (v i) L ≠ 0) (i : I) :
    ∃ G : PlaneRing K, G.IsHomogeneous (Fintype.card I - 1) ∧
      eval (v i) G ≠ 0 ∧ ∀ j, j ≠ i → eval (v j) G = 0 := by
  let J := {j : I // j ≠ i}
  have hex (j : J) := exists_linear_separator v hsep L hL hLv i j.val (Ne.symm j.property)
  choose F hF hFi hFj using hex
  let G : PlaneRing K := ∏ j : J, F j
  refine ⟨G, ?_, ?_, ?_⟩
  · have hh := IsHomogeneous.prod Finset.univ F (fun _ => 1) (fun j _ => hF j)
    simpa [G, J, Fintype.card_subtype_compl] using hh
  · change eval (v i) (∏ j : J, F j) ≠ 0
    rw [map_prod]
    exact Finset.prod_ne_zero_iff.mpr (fun j _ => hFi j)
  · intro j hji
    change eval (v j) (∏ k : J, F k) = 0
    rw [map_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ (⟨j, hji⟩ : J)) (hFj ⟨j, hji⟩)

/-- Surjectivity in degree |D|-1 is proved by actual homogeneous interpolation. -/
theorem independent_card_sub_one [Infinite K]
    (v : I → Fin 3 → K) (hv : ∀ i, v i ≠ 0) (hsep : ProjectivelyDistinct v) :
    EvaluationProjection.Independent v (Fintype.card I - 1) := by
  obtain ⟨L, hL, hLv⟩ := EvaluationProjection.exists_linear_form_avoiding v hv
  choose G hG hGi hGj using exists_point_separator v hsep L hL hLv
  intro w
  let P : PlaneRing K := ∑ j : I, C (w j / eval (v j) (G j)) * G j
  refine ⟨P, ?_, ?_⟩
  · exact IsHomogeneous.sum Finset.univ _ _ (fun j _ => (hG j).C_mul _)
  · intro i
    have ht (j : I) : eval (v i) (C (w j / eval (v j) (G j)) * G j) =
        if j = i then w i else 0 := by
      by_cases hji : j = i
      · subst j
        simp only [map_mul, eval_C]
        exact div_mul_cancel₀ _ (hGi i)
      · simp only [map_mul, eval_C, ite_eq_right hji, hGj j i (Ne.symm hji), mul_zero]
    change eval (v i) (∑ j : I, C (w j / eval (v j) (G j)) * G j) = w i
    rw [map_sum]
    simp only [ht]
    simp

/-- The actual finite-point Hilbert function reaches |D| in degree |D|-1 and stays there. -/
theorem hilbert_eq_card_of_card_sub_one_le [Infinite K]
    (v : I → Fin 3 → K) (hv : ∀ i, v i ≠ 0) (hsep : ProjectivelyDistinct v)
    (d : ℕ) (hd : Fintype.card I - 1 ≤ d) : hilbert v d = Fintype.card I := by
  have hind := EvaluationProjection.independent_of_le v hv (Fintype.card I - 1) d hd
    (independent_card_sub_one v hv hsep)
  have he : evaluationSpace v d = ⊤ := by
    apply top_unique
    intro w _
    exact (mem_evaluationSpace v d w).mpr (hind w)
  change finrank K (evaluationSpace v d) = Fintype.card I
  rw [he]
  simp

/-- Eventual zero first differences are derived from interpolation. -/
theorem hilbert_difference_eventually_zero [Infinite K]
    (v : I → Fin 3 → K) (hv : ∀ i, v i ≠ 0) (hsep : ProjectivelyDistinct v)
    (d : ℕ) (hd : Fintype.card I - 1 ≤ d) : hilbert v (d + 1) - hilbert v d = 0 := by
  rw [hilbert_eq_card_of_card_sub_one_le v hv hsep d hd,
    hilbert_eq_card_of_card_sub_one_le v hv hsep (d + 1) (by omega), Nat.sub_self]

end Cylinder.HilbertEvaluation


