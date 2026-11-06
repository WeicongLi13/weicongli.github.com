module

public import Cylinder.IntegerResidualDuality

/-! Actual homogeneous multiplication and coefficient multiplication are
intertwined in every integer degree by the same residue-defined duality. -/

@[expose] public section
noncomputable section

namespace Cylinder.IntegerResidualMultiplication

open Module MvPolynomial
open Cylinder.PlaneBinaryReduction Cylinder.CompleteIntersectionKoszul
open Cylinder.FiniteEvaluationDuality Cylinder.CurvePolarLocal Cylinder.PlaneHomogenization
open Cylinder.HomogeneousCompleteIntersection Cylinder.ResidualEvaluation Cylinder.ResidualQuotientPieces
open Cylinder.ResidualIntegerPieces Cylinder.IntegerEvaluationDuality Cylinder.IntegerResidualDuality
open Cylinder.AffinePointEvaluation
open scoped Classical BigOperators

variable {K I : Type*} [Field K] [Fintype I]

theorem integerForms_mul (H Q : HomRing (K := K)) (d m : ℤ) (u : ℕ)
    (hm : d + u = m) (hH : H ∈ integerForms K d) (hQ : Q.IsHomogeneous u) :
    H * Q ∈ integerForms K m := by
  by_cases hd : 0 ≤ d
  · have hHhom : H.IsHomogeneous d.toNat := by
      rw [integerForms, if_pos hd] at hH
      exact (mem_homogeneousSubmodule _ _).mp hH
    have hm0 : 0 ≤ m := by omega
    change H * Q ∈ integerForms K m
    rw [integerForms, if_pos hm0]
    change (H * Q).IsHomogeneous m.toNat
    have heq : d.toNat + u = m.toNat := by omega
    rw [← heq]
    exact hHhom.mul hQ
  · have hHz : H = 0 := by simpa only [integerForms, if_neg hd, Submodule.mem_bot] using hH
    rw [hHz, zero_mul]
    exact Submodule.zero_mem _

def integerPieceMultiplication (F G : HomRing (K := K)) (v : I → Fin 2 → K)
    (d m : ℤ) (u : ℕ) (hm : d + u = m) (Q : HomRing (K := K)) (hQ : Q.IsHomogeneous u) :
    integerResidualPiece F G v d →ₗ[K] integerResidualPiece F G v m where
  toFun H := ⟨H.val * Q, (residualIdeal F G v).mul_mem_right Q H.property.1,
    integerForms_mul H.val Q d m u hm H.property.2 hQ⟩
  map_add' H J := by apply Subtype.ext; exact add_mul _ _ _
  map_smul' k H := by apply Subtype.ext; exact smul_mul_assoc _ _ _

def integerResidualMultiplication (F G : HomRing (K := K)) (v : I → Fin 2 → K)
    (d m : ℤ) (u : ℕ) (hm : d + u = m) (Q : HomRing (K := K)) (hQ : Q.IsHomogeneous u) :
    IntegerResidualQuotient F G v d →ₗ[K] IntegerResidualQuotient F G v m :=
  Submodule.mapQ (R := K) (R₂ := K) (τ₁₂ := RingHom.id K)
    (integerEquationPiece F G v d) (integerEquationPiece F G v m)
    (integerPieceMultiplication F G v d m u hm Q hQ) (by
      intro H hH
      exact (equationsIdeal F G).mul_mem_right Q hH)

theorem integer_multiply_relation (v : I → Fin 2 → K) (j : ℤ) (u : ℕ)
    (Q : HomRing (K := K)) (hQ : Q.IsHomogeneous u) (c : integerCoefficientRelations v j) :
    (fun i => c.val i * eval (normalizedPoints v i) Q) ∈ integerCoefficientRelations v (j - u) := by
  apply (mem_integerCoefficientRelations v (j - u) _).mpr
  intro H hH
  have hproduct : Q * H ∈ integerForms K j := by
    rw [mul_comm]
    exact integerForms_mul H Q (j - u) j u (by ring) hH hQ
  have hz := (mem_integerCoefficientRelations v j c.val).mp c.property (Q * H) hproduct
  simpa only [map_mul, mul_assoc] using hz

def integerCoefficientMultiplication (v : I → Fin 2 → K) (j : ℤ) (u : ℕ)
    (Q : HomRing (K := K)) (hQ : Q.IsHomogeneous u) :
    integerCoefficientRelations v j →ₗ[K] integerCoefficientRelations v (j - u) where
  toFun c := ⟨fun i => c.val i * eval (normalizedPoints v i) Q, integer_multiply_relation v j u Q hQ c⟩
  map_add' c z := by
    apply Subtype.ext
    funext i
    change (c.val i + z.val i) * eval (normalizedPoints v i) Q =
      c.val i * eval (normalizedPoints v i) Q + z.val i * eval (normalizedPoints v i) Q
    ring
  map_smul' k c := by
    apply Subtype.ext
    funext i
    change (k * c.val i) * eval (normalizedPoints v i) Q = k * (c.val i * eval (normalizedPoints v i) Q)
    ring

theorem quotientToAnnihilator_multiply (F G : HomRing (K := K)) (e t : ℕ)
    (v : I → Fin 2 → K) (s : ValidSystem F G e t v)
    (d m : ℤ) (u : ℕ) (hm : d + u = m) (Q : HomRing (K := K)) (hQ : Q.IsHomogeneous u)
    (a : IntegerResidualQuotient F G v d) :
    (quotientToAnnihilator F G e t v s m
      (integerResidualMultiplication F G v d m u hm Q hQ a)).val =
    (quotientToAnnihilator F G e t v s d a).val *
      Ideal.Quotient.mk (equationsIdeal (dehomogenize F) (dehomogenize G)) (dehomogenize Q) := by
  obtain ⟨H, rfl⟩ := Submodule.Quotient.mk_surjective (integerEquationPiece F G v d) a
  rw [integerResidualMultiplication, Submodule.mapQ_apply]
  change Ideal.Quotient.mk (equationsIdeal (dehomogenize F) (dehomogenize G))
    (dehomogenize (H.val * Q)) =
    Ideal.Quotient.mk (equationsIdeal (dehomogenize F) (dehomogenize G)) (dehomogenize H.val) *
      Ideal.Quotient.mk (equationsIdeal (dehomogenize F) (dehomogenize G)) (dehomogenize Q)
  rw [map_mul, map_mul]

/-- The single residue-defined isomorphism respects multiplication in
all integer degrees, including j-u<0. -/
theorem duality_multiply (F G : HomRing (K := K)) (e t : ℕ)
    (v : I → Fin 2 → K) (s : ValidSystem F G e t v) (j : ℤ) (u : ℕ)
    (Q : HomRing (K := K)) (hQ : Q.IsHomogeneous u)
    (a : IntegerResidualQuotient F G v ((e : ℤ) + t - 3 - j)) :
    (IntegerResidualDuality.relationResidualEquiv F G e t v s (j - u)).symm
      (integerResidualMultiplication F G v _ _ u (by ring) Q hQ a) =
    integerCoefficientMultiplication v j u Q hQ
      ((IntegerResidualDuality.relationResidualEquiv F G e t v s j).symm a) := by
  apply Subtype.ext
  apply coefficientDualMap_injective
  apply LinearMap.ext
  intro w
  obtain ⟨b, rfl⟩ := evaluation_surjective (dehomogenize F) (dehomogenize G) v s.hv s.hfv s.hgv w
  change (∑ i, quotientCoefficients F G e t v s _
      (integerResidualMultiplication F G v _ _ u (by ring) Q hQ a) i *
        evaluation (dehomogenize F) (dehomogenize G) v s.hfv s.hgv b i) =
    ∑ i, (quotientCoefficients F G e t v s _ a i * eval (normalizedPoints v i) Q) *
      evaluation (dehomogenize F) (dehomogenize G) v s.hfv s.hgv b i
  rw [← quotient_formula F G e t v s _ _ b, quotientToAnnihilator_multiply,
    mul_assoc, quotient_formula F G e t v s _ a]
  simp only [map_mul, Pi.mul_apply, mul_assoc, evaluation_mk, polynomialEvaluation]
  apply Finset.sum_congr rfl
  intro i hi
  change quotientCoefficients F G e t v s _ a i *
    (eval (v i) (dehomogenize Q) * evaluation (dehomogenize F) (dehomogenize G) v s.hfv s.hgv b i) =
    quotientCoefficients F G e t v s _ a i *
    (eval (normalizedPoints v i) Q * evaluation (dehomogenize F) (dehomogenize G) v s.hfv s.hgv b i)
  rw [eval_dehomogenize]
  rfl

#print axioms integerResidualMultiplication
#print axioms integer_multiply_relation
#print axioms quotientToAnnihilator_multiply
#print axioms duality_multiply

end Cylinder.IntegerResidualMultiplication

end
