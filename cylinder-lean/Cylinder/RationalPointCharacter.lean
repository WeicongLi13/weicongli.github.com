module

public import Cylinder.RationalPointCohomology
public import Cylinder.RationalEvaluationCoordinates

/-! The numerical-character formulas for actual ideal-sheaf Ext-H¹,
in the manuscript's full integer degree range. -/

@[expose] public section
noncomputable section
open scoped Classical BigOperators Cylinder.SheafCohomologyScalarAction
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Cylinder.RationalPointCharacter

open Module Finset
open Cylinder.RationalPointCohomology Cylinder.RationalEvaluationCoordinates
open Cylinder.HilbertCharacterFormulas Cylinder.PlaneBinaryReduction

attribute [local instance] MvPolynomial.gradedAlgebra

universe u
variable (K : Type u) [Field K] [Infinite K] {I : Type u} [Fintype I]

local instance idealCohomologyModule (v : ℤ) (x : I → Fin 2 → K) :
    Module K (cohomologyOne K v x) :=
  SheafCohomologyScalarAction.cohomologyModule
    (J := _root_.Opens.grothendieckTopology (GlobalTwistLocalFractions.plane K).toTopCat)
    (K := K) (RationalPointIdealSheaf.idealTwist K v x) 1

theorem cohomologyOne_finrank_eq_defect (v : ℤ) (x : I → Fin 2 → K)
    (hx : Function.Injective x) :
    finrank K (cohomologyOne K v x) =
      IntegerCharacterFormulas.integerDefect (representatives K x) v :=
  (cohomologyOne_finrank K v x hx).trans (RationalEvaluationCoordinates.defect_eq_original K v x)

variable [Nonempty I]

theorem cohomologyOne_character_formula (x : I → Fin 2 → K) (hx : Function.Injective x)
    (s : ℕ) (hs : InitialDegree (representatives K x) s) (v : ℤ) :
    finrank K (cohomologyOne K v x) = ∑ i ∈ range s,
      IntegerCharacterFormulas.characterTerm (numericalCharacter (representatives K x) i) i v := by
  rw [cohomologyOne_finrank_eq_defect K v x hx]
  exact IntegerCharacterFormulas.integerDefect_character_formula _
    (representatives_nonzero K x) (representatives_distinct K x hx) s hs v

theorem cohomologyOne_positive_iff (x : I → Fin 2 → K) (hx : Function.Injective x)
    (s : ℕ) (hs : InitialDegree (representatives K x) s) (v : ℤ) :
    0 < finrank K (cohomologyOne K v x) ↔
      v < (numericalCharacter (representatives K x) 0 : ℤ) - 1 := by
  rw [cohomologyOne_finrank_eq_defect K v x hx]
  exact IntegerCharacterFormulas.integerDefect_positive_iff _
    (representatives_nonzero K x) (representatives_distinct K x hx) s hs v

theorem last_positive_cohomology_degree (x : I → Fin 2 → K) (hx : Function.Injective x)
    (s : ℕ) (hs : InitialDegree (representatives K x) s) :
    0 < finrank K (cohomologyOne K ((numericalCharacter (representatives K x) 0 : ℤ) - 2) x) ∧
      ∀ v : ℤ, (numericalCharacter (representatives K x) 0 : ℤ) - 2 < v →
        finrank K (cohomologyOne K v x) = 0 := by
  constructor
  · rw [cohomologyOne_positive_iff K x hx s hs]
    omega
  · intro v hv
    have h := cohomologyOne_positive_iff K x hx s hs v
    omega

theorem isGreatest_positive_cohomology_degree (x : I → Fin 2 → K)
    (hx : Function.Injective x) (s : ℕ) (hs : InitialDegree (representatives K x) s) :
    IsGreatest {v : ℤ | 0 < finrank K (cohomologyOne K v x)}
      ((numericalCharacter (representatives K x) 0 : ℤ) - 2) := by
  constructor
  · change 0 < finrank K (cohomologyOne K _ x)
    rw [cohomologyOne_positive_iff K x hx s hs]
    omega
  · intro v hv
    have h := (cohomologyOne_positive_iff K x hx s hs v).mp hv
    omega

theorem chart_cohomologyOne_character_formula (D : Finset (PlanePointModel.Plane K))
    [Nonempty D] (c : ProjectiveChartData.Chart K)
    (hc : ∀ P : D, c.line P.val.rep ≠ 0) (s : ℕ)
    (hs : InitialDegree (PlanePointModel.representatives D) s) (v : ℤ) :
    finrank K (cohomologyOne K v (fun P : D => c.affinePoint P.val)) = ∑ i ∈ range s,
      IntegerCharacterFormulas.characterTerm
        (numericalCharacter (PlanePointModel.representatives D) i) i v := by
  rw [chart_cohomologyOne_finrank_eq_original_defect K v c D hc]
  exact IntegerCharacterFormulas.integerDefect_character_formula _
    (PlanePointModel.representatives_nonzero D) (PlanePointModel.representatives_distinct D) s hs v

theorem chart_cohomologyOne_positive_iff (D : Finset (PlanePointModel.Plane K))
    [Nonempty D] (c : ProjectiveChartData.Chart K)
    (hc : ∀ P : D, c.line P.val.rep ≠ 0) (s : ℕ)
    (hs : InitialDegree (PlanePointModel.representatives D) s) (v : ℤ) :
    0 < finrank K (cohomologyOne K v (fun P : D => c.affinePoint P.val)) ↔
      v < (numericalCharacter (PlanePointModel.representatives D) 0 : ℤ) - 1 := by
  rw [chart_cohomologyOne_finrank_eq_original_defect K v c D hc]
  exact IntegerCharacterFormulas.integerDefect_positive_iff _
    (PlanePointModel.representatives_nonzero D) (PlanePointModel.representatives_distinct D) s hs v

/-- All conclusions of the manuscript's numerical-character lemma for
an actual nonempty finite projective point set and its actual initial
degree. A common affine chart is constructed rather than assumed. -/
theorem numerical_character (D : Finset (PlanePointModel.Plane K)) [Nonempty D]
    (s : ℕ) (hs : InitialDegree (PlanePointModel.representatives D) s) :
    ∃ c : ProjectiveChartData.Chart K, (∀ P : D, c.line P.val.rep ≠ 0) ∧
      (∀ i < s, s ≤ numericalCharacter (PlanePointModel.representatives D) i) ∧
      Antitone (numericalCharacter (PlanePointModel.representatives D)) ∧
      D.card = ∑ i ∈ range s, (numericalCharacter (PlanePointModel.representatives D) i - i) ∧
      (∀ v : ℤ, finrank K (cohomologyOne K v (fun P : D => c.affinePoint P.val)) =
        ∑ i ∈ range s, IntegerCharacterFormulas.characterTerm
          (numericalCharacter (PlanePointModel.representatives D) i) i v) ∧
      IsGreatest {v : ℤ | 0 < finrank K (cohomologyOne K v (fun P : D => c.affinePoint P.val))}
        ((numericalCharacter (PlanePointModel.representatives D) 0 : ℤ) - 2) ∧
      ∀ d : ℕ, s ≤ d + 1 →
        finrank K (PlaneNumericalCharacter.idealPiece (PlanePointModel.representatives D) d) =
          NumericalIdealFormula.triangular (d + 1 - s) +
            ∑ i ∈ range s, (d + 1 - numericalCharacter (PlanePointModel.representatives D) i) := by
  obtain ⟨c, hc⟩ := RationalPointChartChoice.exists_common_chart K D
  have hdata := ActualIdealCharacter.character_formulas (PlanePointModel.representatives D)
    (PlanePointModel.representatives_nonzero D) (PlanePointModel.representatives_distinct D) s hs
  refine ⟨c, hc, hdata.1, hdata.2.1, ?_,
    fun v => chart_cohomologyOne_character_formula K D c hc s hs v, ?_, ?_⟩
  · simpa only [Fintype.card_coe] using hdata.2.2.1
  · constructor
    · change 0 < finrank K (cohomologyOne K _ _)
      rw [chart_cohomologyOne_positive_iff K D c hc s hs]
      omega
    · intro v hv
      have h := (chart_cohomologyOne_positive_iff K D c hc s hs v).mp hv
      omega
  · intro d hd
    exact ActualIdealCharacter.ideal_dimension (PlanePointModel.representatives D)
      (PlanePointModel.representatives_nonzero D) (PlanePointModel.representatives_distinct D) s hs d hd

end Cylinder.RationalPointCharacter
end
