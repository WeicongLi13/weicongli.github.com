module

public import Cylinder.ResidualIntegerPieces
public import Cylinder.FullEvaluationDuality

/-! The manuscript's relation/residual duality in every integer degree.
Negative relation degrees are the full coefficient space; negative
residual degrees are the actual zero homogeneous piece. -/

@[expose] public section
noncomputable section

namespace Cylinder.IntegerEvaluationDuality

open Module MvPolynomial
open Cylinder.PlaneBinaryReduction Cylinder.CompleteIntersectionKoszul
open Cylinder.FiniteEvaluationDuality Cylinder.CurvePolarLocal Cylinder.PlaneHomogenization
open Cylinder.HomogeneousCompleteIntersection Cylinder.ResidualEvaluation Cylinder.ResidualQuotientPieces
open Cylinder.ResidualIntegerPieces Cylinder.FullEvaluationDuality
open scoped Classical BigOperators

variable {K I : Type*} [Field K] [Fintype I]

def integerCoefficientRelations (v : I → Fin 2 → K) (j : ℤ) : Submodule K (I → K) :=
  if 0 ≤ j then coefficientRelations v j.toNat else ⊤

theorem mem_integerCoefficientRelations (v : I → Fin 2 → K) (j : ℤ) (c : I → K) :
    c ∈ integerCoefficientRelations v j ↔
      ∀ H : HomRing (K := K), H ∈ integerForms K j →
        ∑ i, c i * eval (normalizedPoints v i) H = 0 := by
  by_cases hj : 0 ≤ j
  · simp only [integerCoefficientRelations, integerForms, if_pos hj]
    exact mem_coefficientRelations_iff_homogeneous v j.toNat c
  · simp only [integerCoefficientRelations, integerForms, if_neg hj, Submodule.mem_top,
      Submodule.mem_bot]
    constructor
    · intro _ H hH
      rw [hH]
      simp
    · intro _
      trivial

/-- All integer degrees, including negative relation degrees, are covered
by actual isomorphisms of actual finite evaluation/residual spaces. -/
def relationResidualEquiv (F G : HomRing (K := K)) (e t : ℕ)
    (he : 0 < e) (ht : 0 < t)
    (hF : F.IsHomogeneous e) (hG : G.IsHomogeneous t)
    (hf : (dehomogenize F).totalDegree = e) (hg : (dehomogenize G).totalDegree = t)
    (hfe : homogeneousComponent e (dehomogenize F) ≠ 0)
    (hge : homogeneousComponent t (dehomogenize G) ≠ 0)
    (hcop : IsRelPrime (homogeneousComponent e (dehomogenize F))
      (homogeneousComponent t (dehomogenize G)))
    (v : I → Fin 2 → K) (hv : Function.Injective v)
    (hfv : ∀ i, eval (v i) (dehomogenize F) = 0)
    (hgv : ∀ i, eval (v i) (dehomogenize G) = 0) (j : ℤ) :
    integerCoefficientRelations v j ≃ₗ[K] IntegerResidualQuotient F G v ((e : ℤ) + t - 3 - j) := by
  by_cases hj : 0 ≤ j
  · have heq : integerCoefficientRelations v j = coefficientRelations v j.toNat := by
      simp only [integerCoefficientRelations, if_pos hj]
    have hd : (e : ℤ) + t - 3 - j = (e : ℤ) + t - 3 - (j.toNat : ℤ) := by
      rw [Int.toNat_of_nonneg hj]
    rw [hd]
    exact (LinearEquiv.ofEq _ _ heq).trans
      (relationResidualIntegerEquiv F G e t he ht hF hG hf hg hfe hge hcop v hv hfv hgv j.toNat)
  · let d : ℤ := (e : ℤ) + t - 3 - j
    have hd : 0 ≤ d := by dsimp [d]; omega
    have hdNat : d = (d.toNat : ℤ) := (Int.toNat_of_nonneg hd).symm
    have hhigh : e + t - 2 ≤ d.toNat := by dsimp [d] at *; omega
    have heq : integerCoefficientRelations v j = ⊤ := by
      simp only [integerCoefficientRelations, if_neg hj]
    exact ((LinearEquiv.ofEq _ _ heq).trans Submodule.topEquiv).trans
      (((highFilteredAnnihilatorEquiv (dehomogenize F) (dehomogenize G) e t he ht hf hg hfe hge hcop
        v hfv hgv d.toNat hhigh).trans
        (fullEvaluationDuality (dehomogenize F) (dehomogenize G) e t he ht hf hg hfe hge hcop
          v hv hfv hgv)).symm.trans
        ((residualQuotientEquiv F G e t d.toNat hF hG hf hg hfe hcop v hfv hgv).symm.trans
          (residualQuotientEquivInteger F G v d.toNat d hdNat)))

#print axioms mem_integerCoefficientRelations
#print axioms relationResidualEquiv

end Cylinder.IntegerEvaluationDuality

end
