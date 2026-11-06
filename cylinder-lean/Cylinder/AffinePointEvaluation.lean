module

public import Cylinder.AffineFilteredDuality

/-! Evaluation of the actual affine quotient at an actual finite set of
distinct common zeros. Polynomial interpolation proves surjectivity over
any field; no evaluation-surjectivity hypothesis is imposed. -/

@[expose] public section
noncomputable section

namespace Cylinder.AffinePointEvaluation

open MvPolynomial Module Finset
open Cylinder.PlaneBinaryReduction Cylinder.CompleteIntersectionKoszul
open scoped Classical BigOperators

variable {K I : Type*} [Field K] [Fintype I]

theorem exists_separating_coordinate (v : I → Fin 2 → K) (hv : Function.Injective v)
    (i j : I) (hij : i ≠ j) : ∃ k : Fin 2, v i k ≠ v j k := by
  by_contra! h
  exact hij (hv (funext h))

def separationCoordinate (v : I → Fin 2 → K) (hv : Function.Injective v) (i j : I) : Fin 2 :=
  if h : i ≠ j then Classical.choose (exists_separating_coordinate v hv i j h) else 0

theorem separationCoordinate_ne (v : I → Fin 2 → K) (hv : Function.Injective v)
    (i j : I) (hij : i ≠ j) :
    v i (separationCoordinate v hv i j) ≠ v j (separationCoordinate v hv i j) := by
  simp only [separationCoordinate, dif_pos hij]
  exact Classical.choose_spec (exists_separating_coordinate v hv i j hij)

def separator (v : I → Fin 2 → K) (hv : Function.Injective v) (i j : I) : BinaryRing K :=
  let k := separationCoordinate v hv i j
  C (v i k - v j k)⁻¹ * (X k - C (v j k))

theorem separator_eval_self (v : I → Fin 2 → K) (hv : Function.Injective v)
    (i j : I) (hij : i ≠ j) : eval (v i) (separator v hv i j) = 1 := by
  simp only [separator, map_mul, map_sub, eval_C, eval_X]
  exact inv_mul_cancel₀ (sub_ne_zero.mpr (separationCoordinate_ne v hv i j hij))

theorem separator_eval_other (v : I → Fin 2 → K) (hv : Function.Injective v)
    (i j : I) : eval (v j) (separator v hv i j) = 0 := by
  simp [separator]

def indicator (v : I → Fin 2 → K) (hv : Function.Injective v) (i : I) : BinaryRing K :=
  ∏ j ∈ univ.erase i, separator v hv i j

theorem indicator_eval (v : I → Fin 2 → K) (hv : Function.Injective v) (i j : I) :
    eval (v j) (indicator v hv i) = if j = i then 1 else 0 := by
  rw [indicator, map_prod]
  by_cases hji : j = i
  · subst j
    rw [if_pos rfl]
    apply prod_eq_one
    intro k hk
    exact separator_eval_self v hv i k (Ne.symm (mem_erase.mp hk).1)
  · rw [if_neg hji]
    exact prod_eq_zero (mem_erase.mpr ⟨hji, mem_univ j⟩) (separator_eval_other v hv i j)

def polynomialEvaluation (v : I → Fin 2 → K) : BinaryRing K →ₐ[K] (I → K) where
  toFun P i := eval (v i) P
  map_zero' := by funext i; exact map_zero _
  map_one' := by funext i; exact map_one _
  map_add' P Q := by funext i; exact map_add _ _ _
  map_mul' P Q := by funext i; exact map_mul _ _ _
  commutes' k := by funext i; exact eval_C k

theorem polynomialEvaluation_surjective (v : I → Fin 2 → K) (hv : Function.Injective v) :
    Function.Surjective (polynomialEvaluation v) := by
  intro w
  refine ⟨∑ i, C (w i) * indicator v hv i, ?_⟩
  funext j
  change eval (v j) (∑ i, C (w i) * indicator v hv i) = w j
  simp [indicator_eval]

def polynomialPointIdeal (v : I → Fin 2 → K) : Ideal (BinaryRing K) :=
  RingHom.ker (polynomialEvaluation v).toRingHom

theorem mem_polynomialPointIdeal (v : I → Fin 2 → K) (P : BinaryRing K) :
    P ∈ polynomialPointIdeal v ↔ ∀ i, eval (v i) P = 0 := by
  change polynomialEvaluation v P = 0 ↔ _
  exact ⟨fun h i => congrFun h i, fun h => funext h⟩

theorem equations_le_pointIdeal (f g : BinaryRing K) (v : I → Fin 2 → K)
    (hf : ∀ i, eval (v i) f = 0) (hg : ∀ i, eval (v i) g = 0) :
    equationsIdeal f g ≤ polynomialPointIdeal v := by
  apply Ideal.span_le.mpr
  intro P hP
  rcases hP with rfl | hP
  · exact (mem_polynomialPointIdeal v _).mpr hf
  · have hPg := Set.mem_singleton_iff.mp hP
    subst P
    exact (mem_polynomialPointIdeal v g).mpr hg

def evaluation (f g : BinaryRing K) (v : I → Fin 2 → K)
    (hf : ∀ i, eval (v i) f = 0) (hg : ∀ i, eval (v i) g = 0) :
    QuotientRing f g →ₐ[K] (I → K) :=
  Ideal.Quotient.liftₐ (equationsIdeal f g) (polynomialEvaluation v)
    (fun P hP => equations_le_pointIdeal f g v hf hg hP)

theorem evaluation_mk (f g : BinaryRing K) (v : I → Fin 2 → K)
    (hf : ∀ i, eval (v i) f = 0) (hg : ∀ i, eval (v i) g = 0) (P : BinaryRing K) :
    evaluation f g v hf hg (Ideal.Quotient.mk (equationsIdeal f g) P) = polynomialEvaluation v P := rfl

theorem evaluation_surjective (f g : BinaryRing K) (v : I → Fin 2 → K) (hv : Function.Injective v)
    (hf : ∀ i, eval (v i) f = 0) (hg : ∀ i, eval (v i) g = 0) :
    Function.Surjective (evaluation f g v hf hg) := by
  intro w
  obtain ⟨P, hP⟩ := polynomialEvaluation_surjective v hv w
  exact ⟨Ideal.Quotient.mk (equationsIdeal f g) P, hP⟩

def pointIdeal (f g : BinaryRing K) (v : I → Fin 2 → K)
    (hf : ∀ i, eval (v i) f = 0) (hg : ∀ i, eval (v i) g = 0) : Ideal (QuotientRing f g) :=
  RingHom.ker (evaluation f g v hf hg).toRingHom

theorem pointIdeal_restrict_eq_kernel (f g : BinaryRing K) (v : I → Fin 2 → K)
    (hf : ∀ i, eval (v i) f = 0) (hg : ∀ i, eval (v i) g = 0) :
    (pointIdeal f g v hf hg).restrictScalars K = LinearMap.ker (evaluation f g v hf hg).toLinearMap := rfl

#print axioms polynomialEvaluation_surjective
#print axioms evaluation_surjective
#print axioms pointIdeal_restrict_eq_kernel

end Cylinder.AffinePointEvaluation

end
