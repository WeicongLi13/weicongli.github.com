module

public import Cylinder.RationalDependentSetBounds
public import Cylinder.ResidualRayArithmetic

/-! The actual character and polar estimates for residual direction sets in
degree p-r-3, with the residual threshold rather than the black-ray threshold. -/

@[expose] public section
noncomputable section
open scoped Classical

namespace Cylinder.ResidualDependentDirections
open MvPolynomial Cylinder.RationalPlaneLine Cylinder.RationalPlanePointModel
open Cylinder.HilbertEvaluation Cylinder.PlaneNumericalCharacter Cylinder.PlaneBinaryReduction
open Cylinder.MinimalEvaluationRelation Cylinder.ResidualRayArithmetic

variable {K : Type*} [Field K] [Infinite K]
variable (p : ℕ) [Fact p.Prime] [CharP K p] [IsAlgClosed K]

omit [Fact p.Prime] [CharP K p] [IsAlgClosed K] [Infinite K] in
theorem residual_line_bound_strict (r : ℕ) (hr : 3 ≤ r) (hrp : r ≤ (p - 1) / 2) :
    (p - 1) / r < p - r - 1 := by
  have hstrict : p - 1 < 3 * (p - r - 1) := by omega
  have hmul := Nat.mul_le_mul_right (p - r - 1) hr
  by_contra hn
  have hbad := Nat.mul_le_mul_right r (le_of_not_gt hn)
  have hdiv := Nat.div_mul_le_self (p - 1) r
  nlinarith

theorem initial_degree_lower (f : ZMod p →+* K)
    (D W : Finset (PlanePoint (ZMod p))) (hWD : W ⊆ D) (r s : ℕ)
    (hr : 3 ≤ r) (hrp : r ≤ (p - 1) / 2) (hcap : LineCap D ((p - 1) / r))
    (hmin : MinimallyDependent (representatives f W) (p - r - 3))
    (hs : InitialDegree (representatives f W) s) : residualThreshold p r ≤ s := by
  let : Nonempty W := minimally_dependent_nonempty _ _ hmin
  have hs0 := initialDegree_pos (representatives f W) s hs
  obtain ⟨_hchar, _hsum, _hmax, htrunc⟩ :=
    ActualCharacterBounds.minimally_dependent_character_bounds (representatives f W)
      (representatives_nonzero f W) (representatives_distinct f W) s hs _ hmin
  have hd : p - r - 3 + 3 = p - r := by omega
  obtain ⟨F, hF, hF0, hzero⟩ := RationalDependentSetBounds.initial_degree_curve p f W s hs
  have hsubset : W ⊆ zeroSet f D F := by
    intro P hP
    exact Finset.mem_filter.mpr ⟨hWD hP, hzero P hP⟩
  have hcard : W.card ≤ (zeroSet f D F).card := Finset.card_le_card hsubset
  by_cases hs1 : s = 1
  · have hlin := linear_factor_card_bound f D ((p - 1) / r)
      ((Nat.le_div_iff_mul_le (by omega : 0 < r)).mpr (by omega : 1 * r ≤ p - 1))
      hcap F (by simpa only [hs1] using hF) hF0
    have hlo := htrunc 1 (by omega)
    simp only [Fintype.card_coe, hd, one_mul] at hlo
    have hstrict := residual_line_bound_strict p r hr hrp
    omega
  have hs2 : 2 ≤ s := by omega
  apply max_le hs2
  by_contra hnot
  have hsmall : 3 * s < p - 2 * r + 1 := by omega
  have hsp : s < p := by omega
  have hhalf : (p - 1) / r ≤ (p - 1) / 2 := Nat.div_le_div_left (by omega : 2 ≤ r) (by decide)
  have hpolar := FrobeniusPolarBound.twice_card_le p f D
    (RationalDependentSetBounds.lineCap_mono D _ _ hcap hhalf) F s hF hF0 hsp
  have hlo := htrunc s (le_refl s)
  simp only [Fintype.card_coe, hd] at hlo
  have hinner : s + p - 1 < 2 * (p - r - s) := by omega
  have hstrict := Nat.mul_lt_mul_of_pos_left hinner (by omega : 0 < s)
  nlinarith

theorem dependent_subset_lower (f : ZMod p →+* K)
    (D W : Finset (PlanePoint (ZMod p))) (hWD : W ⊆ D) (r : ℕ)
    (hr : 3 ≤ r) (hrp : r ≤ (p - 1) / 2) (hcap : LineCap D ((p - 1) / r))
    (hmin : MinimallyDependent (representatives f W) (p - r - 3)) :
    residualThreshold p r * (p - r - residualThreshold p r) ≤ W.card := by
  obtain ⟨s, hs⟩ := InitialDegreeExists.exists_initialDegree (representatives f W)
  have ht := initial_degree_lower p f D W hWD r s hr hrp hcap hmin hs
  obtain ⟨_hchar, _hsum, _hmax, htrunc⟩ :=
    ActualCharacterBounds.minimally_dependent_character_bounds (representatives f W)
      (representatives_nonzero f W) (representatives_distinct f W) s hs _ hmin
  have hd : p - r - 3 + 3 = p - r := by omega
  simpa only [hd, Fintype.card_coe] using htrunc (residualThreshold p r) ht

theorem dependent_set_lower (f : ZMod p →+* K) (D : Finset (PlanePoint (ZMod p))) (r : ℕ)
    (hr : 3 ≤ r) (hrp : r ≤ (p - 1) / 2) (hcap : LineCap D ((p - 1) / r))
    (hdep : ¬EvaluationProjection.Independent (representatives f D) (p - r - 3)) :
    residualThreshold p r * (p - r - residualThreshold p r) ≤ D.card := by
  have hbad : ¬Function.Surjective (evaluationMap (representatives f D) (p - r - 3)) :=
    fun h => hdep ((InitialDegreeExists.independent_iff_surjective _ _).mpr h)
  obtain ⟨W, hWD, hmin⟩ := MinimalDependentSubset.exists_minimally_dependent_subset
    (fun P : PlanePoint (ZMod p) => fun j => f (P.rep j)) D (p - r - 3) hbad
  exact (dependent_subset_lower p f D W hWD r hr hrp hcap hmin).trans (Finset.card_le_card hWD)

#print axioms initial_degree_lower
#print axioms dependent_subset_lower
#print axioms dependent_set_lower

end Cylinder.ResidualDependentDirections
end
