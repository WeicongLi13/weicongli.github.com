module

public import Cylinder.MinimalDependentSubset
public import Cylinder.InitialDegreeExists
public import Cylinder.ActualCharacterBounds
public import Cylinder.FrobeniusPolarBound
public import Cylinder.BlackRayArithmetic

/-! Initial-degree and length bounds for genuine dependent rational point sets. -/

@[expose] public section
noncomputable section
open scoped Classical

namespace Cylinder.RationalDependentSetBounds

open MvPolynomial Cylinder.RationalPlaneLine Cylinder.RationalPlanePointModel
open Cylinder.HilbertEvaluation Cylinder.PlaneNumericalCharacter
open Cylinder.PlaneBinaryReduction Cylinder.MinimalEvaluationRelation
open Cylinder.BlackRayArithmetic

variable {K : Type*} [Field K] [Infinite K]

omit [Infinite K] in
theorem initial_degree_curve (p : ℕ) [Fact p.Prime] (f : ZMod p →+* K)
    (W : Finset (PlanePoint (ZMod p))) (s : ℕ) (hs : InitialDegree (representatives f W) s) :
    ∃ F : PlaneRing K, F.IsHomogeneous s ∧ F ≠ 0 ∧
      ∀ P ∈ W, eval (fun j => f (P.rep j)) F = 0 := by
  obtain ⟨F, hFI, hF0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hs.1
  have hFval : F.val ≠ 0 := fun hz => hF0 (Subtype.ext hz)
  have hker : evaluationMap (representatives f W) s F = 0 := by
    rw [← LinearMap.mem_ker, ← idealPiece_eq_kernel]
    exact hFI
  exact ⟨F.val, F.property, hFval, fun P hP => congrFun hker ⟨P, hP⟩⟩

theorem lineCap_mono {L : Type*} [Field L] (D : Finset (PlanePoint L))
    (a b : ℕ) (hcap : LineCap D a) (hab : a ≤ b) : LineCap D b :=
  fun c hc => (hcap c hc).trans hab

variable (p : ℕ) [Fact p.Prime] [CharP K p] [IsAlgClosed K]

/-- A minimal dependent subset in degree p-r-1 cannot have a smaller
initial degree than the actual rounded threshold in the manuscript. -/
theorem initial_degree_lower (f : ZMod p →+* K)
    (D W : Finset (PlanePoint (ZMod p))) (hWD : W ⊆ D) (r s : ℕ)
    (hr : 2 ≤ r) (hrp : r ≤ (p - 1) / 2)
    (hcap : LineCap D ((p - 1) / r))
    (hmin : MinimallyDependent (representatives f W) (p - r - 1))
    (hs : InitialDegree (representatives f W) s) : rayCeiling p r ≤ s := by
  let : Nonempty W := minimally_dependent_nonempty _ _ hmin
  have hs0 := initialDegree_pos (representatives f W) s hs
  obtain ⟨_hchar, _hsum, _hmax, htrunc⟩ :=
    ActualCharacterBounds.minimally_dependent_character_bounds (representatives f W)
      (representatives_nonzero f W) (representatives_distinct f W) s hs _ hmin
  have hd : p - r - 1 + 3 = p - r + 2 := by omega
  obtain ⟨F, hF, hF0, hzero⟩ := initial_degree_curve p f W s hs
  have hsubset : W ⊆ zeroSet f D F := by
    intro P hP
    exact Finset.mem_filter.mpr ⟨hWD hP, hzero P hP⟩
  have hcard : W.card ≤ (zeroSet f D F).card := Finset.card_le_card hsubset
  have hp : 5 ≤ p := by omega
  have hpr : r ≤ p := by omega
  by_cases hs1 : s = 1
  · have hlin := linear_factor_card_bound f D ((p - 1) / r)
      ((Nat.le_div_iff_mul_le (by omega : 0 < r)).mpr (by omega : 1 * r ≤ p - 1))
      hcap F (by simpa only [hs1] using hF) hF0
    have hlo := htrunc 1 (by omega)
    simp only [Fintype.card_coe, hd, one_mul] at hlo
    have hstrict := line_bound_strict p r hr hrp
    omega
  have hs2 : 2 ≤ s := by omega
  apply rayCeiling_le_of_not_small
  by_contra hsmall
  have hsmall' : 3 * s < p - 2 * r + 5 := by omega
  have hsp := small_degree_lt_prime p r s hr hs2 hsmall'
  have hhalf : (p - 1) / r ≤ (p - 1) / 2 := Nat.div_le_div_left hr (by decide)
  have hpolar := FrobeniusPolarBound.twice_card_le p f D
    (lineCap_mono D _ _ hcap hhalf) F s hF hF0 hsp
  have hlo := htrunc s (le_refl s)
  simp only [Fintype.card_coe, hd] at hlo
  have hstrict := small_degree_polar_strict p r s hs2 hsmall'
  nlinarith

/-- The characteristic lower bound at the rounded threshold is derived
from actual minimal dependence, not supplied as a numerical hypothesis. -/
theorem dependent_subset_lower (f : ZMod p →+* K)
    (D W : Finset (PlanePoint (ZMod p))) (hWD : W ⊆ D) (r : ℕ)
    (hr : 2 ≤ r) (hrp : r ≤ (p - 1) / 2)
    (hcap : LineCap D ((p - 1) / r))
    (hmin : MinimallyDependent (representatives f W) (p - r - 1)) :
    rayCeiling p r * (p - r + 2 - rayCeiling p r) ≤ W.card := by
  obtain ⟨s, hs⟩ := InitialDegreeExists.exists_initialDegree (representatives f W)
  have ht := initial_degree_lower p f D W hWD r s hr hrp hcap hmin hs
  obtain ⟨_hchar, _hsum, _hmax, htrunc⟩ :=
    ActualCharacterBounds.minimally_dependent_character_bounds (representatives f W)
      (representatives_nonzero f W) (representatives_distinct f W) s hs _ hmin
  have hd : p - r - 1 + 3 = p - r + 2 := by omega
  simpa only [hd, Fintype.card_coe] using htrunc (rayCeiling p r) ht

/-- The direction-set lower bound follows by choosing a genuine minimal
dependent subset of the given finite rational point set. -/
theorem dependent_set_lower (f : ZMod p →+* K)
    (D : Finset (PlanePoint (ZMod p))) (r : ℕ)
    (hr : 2 ≤ r) (hrp : r ≤ (p - 1) / 2)
    (hcap : LineCap D ((p - 1) / r))
    (hdep : ¬Cylinder.EvaluationProjection.Independent (representatives f D) (p - r - 1)) :
    rayCeiling p r * (p - r + 2 - rayCeiling p r) ≤ D.card := by
  have hbad : ¬Function.Surjective (evaluationMap (representatives f D) (p - r - 1)) :=
    fun h => hdep ((InitialDegreeExists.independent_iff_surjective _ _).mpr h)
  obtain ⟨W, hWD, hmin⟩ := MinimalDependentSubset.exists_minimally_dependent_subset
    (fun P : PlanePoint (ZMod p) => fun j => f (P.rep j)) D (p - r - 1) hbad
  exact (dependent_subset_lower p f D W hWD r hr hrp hcap hmin).trans (Finset.card_le_card hWD)

end Cylinder.RationalDependentSetBounds

end
