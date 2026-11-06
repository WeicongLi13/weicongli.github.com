module

public import Cylinder.OriginalPointCohomology
public import Cylinder.RationalPointCharacter

/-! The manuscript's cohomology and character formulas on the original
projective plane. The cohomology groups are Ext-defined groups of the
actual point-evaluation kernel sheaf. -/

@[expose] public section
noncomputable section
open scoped Classical BigOperators Cylinder.SheafCohomologyScalarAction
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Cylinder.OriginalPointCharacter

open Module Finset
open Cylinder.OriginalPointCohomology
open Cylinder.HilbertCharacterFormulas Cylinder.PlaneBinaryReduction

attribute [local instance] MvPolynomial.gradedAlgebra

universe u
variable (K : Type u) [Field K] [Infinite K]

local instance originalCohomologyModule (c : ProjectiveChartData.Chart K)
    (v : ℤ) (D : Finset (PlanePointModel.Plane K)) :
    Module K (cohomologyOne K c v D) :=
  SheafCohomologyScalarAction.cohomologyModule
    (J := _root_.Opens.grothendieckTopology (ProjectiveCoordinateIso.originalPlane K).toTopCat)
    (K := K) (originalIdealTwist K c v D) 1

theorem cohomologyOne_finiteDimensional (c : ProjectiveChartData.Chart K) (v : ℤ)
    (D : Finset (PlanePointModel.Plane K))
    (hc : ∀ P : D, c.line P.val.rep ≠ 0) :
    FiniteDimensional K (cohomologyOne K c v D) := by
  letI := RationalPointCohomology.cohomologyOne_finiteDimensional K v
    (fun P : D => c.affinePoint P.val)
    (ProjectiveChartData.affinePoints_injective c D hc)
  exact Module.Finite.of_injective
    (originalChartCohomologyEquiv K c v D).toLinearMap
    (originalChartCohomologyEquiv K c v D).injective

theorem cohomologyOne_eq_card_sub_hilbert (c : ProjectiveChartData.Chart K)
    (v : ℤ) (D : Finset (PlanePointModel.Plane K))
    (hc : ∀ P : D, c.line P.val.rep ≠ 0) :
    finrank K (cohomologyOne K c v D) =
      D.card - if 0 ≤ v then HilbertEvaluation.hilbert
        (PlanePointModel.representatives D) v.toNat else 0 := by
  rw [original_cohomology_finrank K c v D hc]
  change IntegerCharacterFormulas.integerDefect (PlanePointModel.representatives D) v = _
  by_cases hv : 0 ≤ v
  · simp only [IntegerCharacterFormulas.integerDefect, ite_eq_left hv, Fintype.card_coe]
  · simp only [IntegerCharacterFormulas.integerDefect, ite_eq_right hv,
      Fintype.card_coe, Nat.sub_zero]

theorem cohomologyOne_eq_relations (c : ProjectiveChartData.Chart K)
    (v : ℤ) (D : Finset (PlanePointModel.Plane K))
    (hc : ∀ P : D, c.line P.val.rep ≠ 0) :
    finrank K (cohomologyOne K c v D) =
      finrank K (IntegerRepresentativeRelations.integerRelations
        (PlanePointModel.representatives D) v) :=
  (original_cohomology_finrank K c v D hc).trans
    (IntegerCharacterFormulas.integerDefect_eq_relations _ v)

theorem cohomologyOne_character_formula (D : Finset (PlanePointModel.Plane K))
    [Nonempty D] (c : ProjectiveChartData.Chart K)
    (hc : ∀ P : D, c.line P.val.rep ≠ 0) (s : ℕ)
    (hs : InitialDegree (PlanePointModel.representatives D) s) (v : ℤ) :
    finrank K (cohomologyOne K c v D) = ∑ i ∈ range s,
      IntegerCharacterFormulas.characterTerm
        (numericalCharacter (PlanePointModel.representatives D) i) i v := by
  rw [original_cohomology_finrank K c v D hc]
  exact IntegerCharacterFormulas.integerDefect_character_formula _
    (PlanePointModel.representatives_nonzero D) (PlanePointModel.representatives_distinct D) s hs v

theorem cohomologyOne_positive_iff (D : Finset (PlanePointModel.Plane K))
    [Nonempty D] (c : ProjectiveChartData.Chart K)
    (hc : ∀ P : D, c.line P.val.rep ≠ 0) (s : ℕ)
    (hs : InitialDegree (PlanePointModel.representatives D) s) (v : ℤ) :
    0 < finrank K (cohomologyOne K c v D) ↔
      v < (numericalCharacter (PlanePointModel.representatives D) 0 : ℤ) - 1 := by
  rw [original_cohomology_finrank K c v D hc]
  exact IntegerCharacterFormulas.integerDefect_positive_iff _
    (PlanePointModel.representatives_nonzero D) (PlanePointModel.representatives_distinct D) s hs v

theorem isGreatest_positive_cohomology_degree (D : Finset (PlanePointModel.Plane K))
    [Nonempty D] (c : ProjectiveChartData.Chart K)
    (hc : ∀ P : D, c.line P.val.rep ≠ 0) (s : ℕ)
    (hs : InitialDegree (PlanePointModel.representatives D) s) :
    IsGreatest {v : ℤ | 0 < finrank K (cohomologyOne K c v D)}
      ((numericalCharacter (PlanePointModel.representatives D) 0 : ℤ) - 2) := by
  constructor
  · change 0 < finrank K (cohomologyOne K c _ D)
    rw [cohomologyOne_positive_iff K D c hc s hs]
    omega
  · intro v hv
    have h := (cohomologyOne_positive_iff K D c hc s hs v).mp hv
    omega

/-- The full numerical-character lemma for the original finite point set,
including every integer twist and the actual last nonzero H¹ degree. -/
theorem numerical_character (D : Finset (PlanePointModel.Plane K)) [Nonempty D]
    (s : ℕ) (hs : InitialDegree (PlanePointModel.representatives D) s) :
    ∃ c : ProjectiveChartData.Chart K, (∀ P : D, c.line P.val.rep ≠ 0) ∧
      (∀ i < s, s ≤ numericalCharacter (PlanePointModel.representatives D) i) ∧
      Antitone (numericalCharacter (PlanePointModel.representatives D)) ∧
      D.card = ∑ i ∈ range s, (numericalCharacter (PlanePointModel.representatives D) i - i) ∧
      (∀ v : ℤ, finrank K (cohomologyOne K c v D) =
        ∑ i ∈ range s, IntegerCharacterFormulas.characterTerm
          (numericalCharacter (PlanePointModel.representatives D) i) i v) ∧
      IsGreatest {v : ℤ | 0 < finrank K (cohomologyOne K c v D)}
        ((numericalCharacter (PlanePointModel.representatives D) 0 : ℤ) - 2) ∧
      ∀ d : ℕ, s ≤ d + 1 →
        finrank K (PlaneNumericalCharacter.idealPiece (PlanePointModel.representatives D) d) =
          NumericalIdealFormula.triangular (d + 1 - s) +
            ∑ i ∈ range s, (d + 1 - numericalCharacter (PlanePointModel.representatives D) i) := by
  obtain ⟨c, hc⟩ := RationalPointChartChoice.exists_common_chart K D
  have hdata := ActualIdealCharacter.character_formulas (PlanePointModel.representatives D)
    (PlanePointModel.representatives_nonzero D) (PlanePointModel.representatives_distinct D) s hs
  refine ⟨c, hc, hdata.1, hdata.2.1, ?_,
    fun v => cohomologyOne_character_formula K D c hc s hs v,
    isGreatest_positive_cohomology_degree K D c hc s hs, ?_⟩
  · simpa only [Fintype.card_coe] using hdata.2.2.1
  · intro d hd
    exact ActualIdealCharacter.ideal_dimension (PlanePointModel.representatives D)
      (PlanePointModel.representatives_nonzero D) (PlanePointModel.representatives_distinct D) s hs d hd

end Cylinder.OriginalPointCharacter
end
