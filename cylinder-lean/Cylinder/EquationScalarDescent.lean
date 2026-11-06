module

public import Cylinder.InitialDegreeExists
public import Cylinder.RationalPlanePointModel
public import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Actual descent of homogeneous vanishing equations

A base-linear coefficient functional preserves evaluation at base-field
vectors. A functional separating one actual nonzero coefficient therefore
descends a nonzero homogeneous equation without changing its degree.
No matrix-rank or equation-descent assumption is needed.
-/

@[expose] public section
noncomputable section

namespace Cylinder.EquationScalarDescent

open MvPolynomial Cylinder.HilbertEvaluation Cylinder.PlaneNumericalCharacter Cylinder.PlaneBinaryReduction
open scoped Classical BigOperators

variable {K L σ I : Type*} [Field K] [Field L] [Algebra K L]

def coefficientProjection (l : L →ₗ[K] K) (F : MvPolynomial σ L) : MvPolynomial σ K :=
  AddMonoidAlgebra.ofCoeff (Finsupp.mapRange l l.map_zero F.coeff)

@[simp] theorem coefficientProjection_coeff (l : L →ₗ[K] K) (F : MvPolynomial σ L) (m : σ →₀ ℕ) :
    (coefficientProjection l F).coeff m = l (F.coeff m) := rfl

theorem coefficientProjection_add (l : L →ₗ[K] K) (F G : MvPolynomial σ L) :
    coefficientProjection l (F + G) = coefficientProjection l F + coefficientProjection l G := by
  ext m
  simp

theorem coefficientProjection_monomial (l : L →ₗ[K] K) (m : σ →₀ ℕ) (a : L) :
    coefficientProjection l (monomial m a) = monomial m (l a) := by
  ext n
  by_cases h : m = n <;> simp [h]

theorem coefficientProjection_homogeneous (l : L →ₗ[K] K) (F : MvPolynomial σ L)
    (d : ℕ) (hF : F.IsHomogeneous d) : (coefficientProjection l F).IsHomogeneous d := by
  intro m hm
  apply hF
  intro hz
  exact hm (by rw [coefficientProjection_coeff, hz, map_zero])

theorem eval_coefficientProjection (l : L →ₗ[K] K) (F : MvPolynomial σ L) (v : σ → K) :
    eval v (coefficientProjection l F) = l (eval (fun j => algebraMap K L (v j)) F) := by
  induction F using MvPolynomial.induction_on' with
  | monomial m a =>
    rw [coefficientProjection_monomial, eval_monomial, eval_monomial]
    have hp : m.prod (fun j k => algebraMap K L (v j) ^ k) =
        algebraMap K L (m.prod (fun j k => v j ^ k)) := by
      simp only [map_finsuppProd, map_pow]
    rw [hp]
    simpa only [Algebra.smul_def, smul_eq_mul, Algebra.algebraMap_self, RingHom.id_apply, mul_comm] using
      (l.map_smul (m.prod (fun j k => v j ^ k)) a).symm
  | add F G hF hG => rw [coefficientProjection_add, map_add, hF, hG, map_add, map_add]

theorem exists_nonzero_coefficientProjection (F : MvPolynomial σ L) (hF : F ≠ 0) :
    ∃ l : L →ₗ[K] K, coefficientProjection l F ≠ 0 := by
  obtain ⟨m, hm⟩ := exists_coeff_ne_zero hF
  obtain ⟨l, hl⟩ := Module.Projective.exists_dual_ne_zero K hm
  refine ⟨l, ?_⟩
  intro hz
  exact hl (by simpa only [coefficientProjection_coeff, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply]
    using congrArg (fun Q => Q.coeff m) hz)

theorem exists_equation_descent (v : I → σ → K) (d : ℕ) (F : MvPolynomial σ L)
    (hF : F.IsHomogeneous d) (hF0 : F ≠ 0)
    (hzero : ∀ i, eval (fun j => algebraMap K L (v i j)) F = 0) :
    ∃ Q : MvPolynomial σ K, Q.IsHomogeneous d ∧ Q ≠ 0 ∧ ∀ i, eval (v i) Q = 0 := by
  obtain ⟨l, hl⟩ := exists_nonzero_coefficientProjection (K := K) F hF0
  refine ⟨coefficientProjection l F, coefficientProjection_homogeneous l F d hF, hl, ?_⟩
  intro i
  rw [eval_coefficientProjection, hzero i, map_zero]

theorem mapped_homogeneous (F : MvPolynomial σ K) (d : ℕ) (hF : F.IsHomogeneous d) :
    (MvPolynomial.map (algebraMap K L) F).IsHomogeneous d := by
  intro m hm
  apply hF
  intro hz
  exact hm (by rw [coeff_map, hz, map_zero])

def HasEquation (v : I → Fin 3 → K) (d : ℕ) : Prop :=
  ∃ F : MvPolynomial (Fin 3) K, F.IsHomogeneous d ∧ F ≠ 0 ∧ ∀ i, eval (v i) F = 0

theorem hasEquation_scalar_extension_iff (v : I → Fin 3 → K) (d : ℕ) :
    HasEquation (fun i j => algebraMap K L (v i j)) d ↔ HasEquation v d := by
  constructor
  · rintro ⟨F, hF, hF0, hzero⟩
    exact exists_equation_descent v d F hF hF0 hzero
  · rintro ⟨F, hF, hF0, hzero⟩
    refine ⟨MvPolynomial.map (algebraMap K L) F, mapped_homogeneous F d hF, ?_, ?_⟩
    · intro hz
      apply hF0
      exact MvPolynomial.map_injective (algebraMap K L) (algebraMap K L).injective
        (by simpa only [map_zero] using hz)
    · intro i
      simpa only [map_eval, Function.comp_def, map_zero] using congrArg (algebraMap K L) (hzero i)

omit [Algebra K L] [Field L] in
theorem idealPiece_ne_bot_iff (v : I → Fin 3 → K) (d : ℕ) :
    idealPiece v d ≠ ⊥ ↔ HasEquation v d := by
  rw [idealPiece_eq_kernel]
  constructor
  · intro h
    obtain ⟨F, hF, hF0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h
    refine ⟨F.val, F.property, fun hz => hF0 (Subtype.ext hz), ?_⟩
    intro i
    exact congrFun hF i
  · rintro ⟨F, hF, hF0, hzero⟩ hbot
    have hmem : (⟨F, hF⟩ : Forms K d) ∈ LinearMap.ker (evaluationMap v d) := funext hzero
    rw [hbot, Submodule.mem_bot] at hmem
    exact hF0 (congrArg Subtype.val hmem)

theorem initialDegree_scalar_extension_iff (v : I → Fin 3 → K) (s : ℕ) :
    InitialDegree (fun i j => algebraMap K L (v i j)) s ↔ InitialDegree v s := by
  have hpiece (d : ℕ) : idealPiece (fun i j => algebraMap K L (v i j)) d ≠ ⊥ ↔ idealPiece v d ≠ ⊥ := by
    rw [idealPiece_ne_bot_iff, idealPiece_ne_bot_iff, hasEquation_scalar_extension_iff]
  constructor
  · rintro ⟨hs, hsmall⟩
    refine ⟨(hpiece s).mp hs, ?_⟩
    intro d hd
    by_contra h
    exact ((hpiece d).mpr h) (hsmall d hd)
  · rintro ⟨hs, hsmall⟩
    refine ⟨(hpiece s).mpr hs, ?_⟩
    intro d hd
    by_contra h
    exact ((hpiece d).mp h) (hsmall d hd)

end Cylinder.EquationScalarDescent

end
