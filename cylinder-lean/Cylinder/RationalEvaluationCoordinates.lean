module

public import Cylinder.RationalEvaluationDefect
public import Cylinder.IntegerCharacterFormulas

/-! The actual normalized rational points in the original three-variable
evaluation and numerical-character conventions. -/

@[expose] public section
noncomputable section
open scoped Classical BigOperators
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Cylinder.RationalEvaluationCoordinates

open MvPolynomial Module

universe u
variable (K : Type u) [Field K] {I : Type u} [Fintype I]

def representatives (x : I → Fin 2 → K) : I → Fin 3 → K :=
  fun i j => RationalFractionEvaluation.normalized K (x i) (_root_.finSuccEquiv 2 j)

theorem representatives_nonzero (x : I → Fin 2 → K) (i : I) :
    representatives K x i ≠ 0 := by
  intro h
  have he := congrFun h 0
  exact one_ne_zero (show (1 : K) = 0 from he)

theorem representatives_distinct (x : I → Fin 2 → K) (hx : Function.Injective x) :
    HilbertEvaluation.ProjectivelyDistinct (representatives K x) := by
  intro i j hij c h
  have hc : (1 : K) = c * 1 := congrFun h 0
  have hc1 : c = 1 := by simpa only [mul_one] using hc.symm
  rw [hc1, one_smul] at h
  have he : x j = x i := by
    funext a
    exact congrFun h a.succ
  exact hij (hx he).symm

theorem relations_eq_representatives (v : ℤ) (x : I → Fin 2 → K) :
    IntegerEvaluationDuality.integerCoefficientRelations x v =
      IntegerRepresentativeRelations.integerRelations (representatives K x) v := by
  by_cases hv : 0 ≤ v
  · ext c
    simp only [IntegerEvaluationDuality.integerCoefficientRelations,
      IntegerRepresentativeRelations.integerRelations, ite_eq_left hv]
    rw [FiniteEvaluationDuality.mem_coefficientRelations_iff_homogeneous,
      PlaneRelationSpaces.mem_relationSpace]
    constructor
    · intro h H hH
      have hh := h (rename (_root_.finSuccEquiv 2) H)
        (hH.rename_isHomogeneous (f := _root_.finSuccEquiv 2))
      have hn (i : I) : FiniteEvaluationDuality.normalizedPoints x i ∘
          (_root_.finSuccEquiv 2) = representatives K x i := rfl
      simpa only [eval_rename, hn] using hh
    · intro h H hH
      have hh := h (rename (_root_.finSuccEquiv 2).symm H)
        (hH.rename_isHomogeneous (f := (_root_.finSuccEquiv 2).symm))
      have hn (i : I) : representatives K x i ∘ (_root_.finSuccEquiv 2).symm =
          FiniteEvaluationDuality.normalizedPoints x i := by
        funext a
        change RationalFractionEvaluation.normalized K (x i)
          ((_root_.finSuccEquiv 2) ((_root_.finSuccEquiv 2).symm a)) =
            RationalFractionEvaluation.normalized K (x i) a
        rw [Equiv.apply_symm_apply]
      simpa only [eval_rename, hn] using hh
  · simp only [IntegerEvaluationDuality.integerCoefficientRelations,
      IntegerRepresentativeRelations.integerRelations, ite_eq_right hv]

theorem defect_eq_original (v : ℤ) (x : I → Fin 2 → K) :
    Fintype.card I - RationalEvaluationDefect.hilbert K v x =
      IntegerCharacterFormulas.integerDefect (representatives K x) v := by
  rw [IntegerCharacterFormulas.integerDefect_eq_relations,
    ← relations_eq_representatives K v x,
    ← RationalEvaluationDefect.relations_eq_original K v x]
  exact (RationalEvaluationDefect.relations_finrank K v x).symm

end Cylinder.RationalEvaluationCoordinates
end
