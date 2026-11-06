module

public import Cylinder.IrreduciblePolarPointBound
public import Cylinder.CurvePointAggregation
public import Cylinder.RationalPlanePointModel

/-! The complete curve bound of Lemma `lem:polar`, on actual prime-field points. -/

@[expose] public section
noncomputable section
open scoped Classical

namespace Cylinder.FrobeniusPolarBound

open MvPolynomial Cylinder.RationalPlaneLine Cylinder.PlaneCurveFactors
open Cylinder.CurvePointAggregation Cylinder.FrobeniusPolar

theorem eval_map_at_mapped_point {L : Type*} [Field L] {K : Type*} [Field K]
    (f : L →+* K) (v : Fin 3 → L) (F : MvPolynomial (Fin 3) L) :
    eval (fun j => f (v j)) (MvPolynomial.map f F) = f (eval v F) := by
  induction F using MvPolynomial.induction_on with
  | C a => simp
  | add F G hF hG => simp [hF, hG]
  | mul_X F j hF => simp [hF]

variable (p : ℕ) [Fact p.Prime]
variable {K : Type*} [Field K] [CharP K p] [IsAlgClosed K]

/-- The original polar bound for every curve, including reducible curves
and nonrational geometric factors. All component estimates are derived. -/
theorem twice_card_le (f : ZMod p →+* K) (D : Finset (PlanePoint (ZMod p)))
    (hcap : LineCap D ((p - 1) / 2)) (F : MvPolynomial (Fin 3) K) (s : ℕ)
    (hF : F.IsHomogeneous s) (hF0 : F ≠ 0) (hs : s < p) :
    2 * (zeroSet f D F).card ≤ s * (s + p - 1) := by
  by_cases hp2 : p = 2
  · have hcap0 : LineCap D 0 := by simpa only [hp2] using hcap
    have hD := lineCap_zero_implies_empty D hcap0
    simp [zeroSet, hD]
  have hp : 3 ≤ p := by have hprime := (Fact.out : p.Prime).two_le; omega
  have hdegree : F.totalDegree = s := hF.totalDegree hF0
  apply curve_bound_of_factor_bounds f D F hF0 s p (by omega) hdegree.le
  intro G hG
  have hhom := factor_homogeneous F s hF hF0 G hG
  have hirr := factor_irreducible F G hG
  have hpos := positive_degree_of_irreducible G hirr
  have hdeg : G.totalDegree < p :=
    lt_of_le_of_lt (by
      have h := totalDegree_le_of_dvd_of_isDomain (factor_dvd F G hG) hF0
      rwa [hdegree] at h) hs
  by_cases hline : G.totalDegree = 1
  · have hb : 1 ≤ (p - 1) / 2 := by omega
    have hcard := linear_factor_card_bound f D ((p - 1) / 2) hb hcap G
      (by simpa only [hline] using hhom) hirr.ne_zero
    rw [hline]
    have heq : 1 + p - 1 = p := by omega
    rw [heq, one_mul]
    omega
  · have hn : 2 ≤ G.totalDegree := by omega
    let T := zeroSet f D G
    have hzero : ∀ P : T, eval (RationalPlanePointModel.representatives f T P) G = 0 := by
      intro P
      exact (Finset.mem_filter.mp P.property).2
    have hbound := IrreduciblePolarPointBound.rational_point_bound p G.totalDegree G hhom
      hirr hn hdeg (RationalPlanePointModel.representatives f T)
      (RationalPlanePointModel.representatives_nonzero f T)
      (RationalPlanePointModel.representatives_distinct f T)
      (RationalPlanePointModel.representatives_frobeniusFixed p f T) hzero
    simpa only [Fintype.card_coe] using hbound

/-- The integer cardinality bound is the exact counterpart of the fraction
in the manuscript; no rounding hypothesis is required. -/
theorem card_le_half (f : ZMod p →+* K) (D : Finset (PlanePoint (ZMod p)))
    (hcap : LineCap D ((p - 1) / 2)) (F : MvPolynomial (Fin 3) K) (s : ℕ)
    (hF : F.IsHomogeneous s) (hF0 : F ≠ 0) (hs : s < p) :
    (zeroSet f D F).card ≤ s * (s + p - 1) / 2 := by
  apply (Nat.le_div_iff_mul_le (by decide : 0 < 2)).mpr
  simpa only [mul_comm] using twice_card_le p f D hcap F s hF hF0 hs

/-- The literal prime-field curve statement uses its original equation and
its original actual projective zero set. Extension of the field is verified. -/
theorem prime_field_card_le_half (f : ZMod p →+* K) (D : Finset (PlanePoint (ZMod p)))
    (hcap : LineCap D ((p - 1) / 2)) (F : MvPolynomial (Fin 3) (ZMod p)) (s : ℕ)
    (hF : F.IsHomogeneous s) (hF0 : F ≠ 0) (hs : s < p) :
    (D.filter (fun P => eval P.rep F = 0)).card ≤ s * (s + p - 1) / 2 := by
  have hmap0 : MvPolynomial.map f F ≠ 0 := by
    intro hz
    exact hF0 (MvPolynomial.map_injective f f.injective (by simpa only [map_zero] using hz))
  have hmaphom : (MvPolynomial.map f F).IsHomogeneous s := hF.map f
  have hzset : zeroSet f D (MvPolynomial.map f F) = D.filter (fun P => eval P.rep F = 0) := by
    ext P
    simp only [zeroSet, Finset.mem_filter, eval_map_at_mapped_point]
    rw [map_eq_zero_iff f f.injective]
  rw [← hzset]
  exact card_le_half p f D hcap (MvPolynomial.map f F) s hmaphom hmap0 hs

end Cylinder.FrobeniusPolarBound

end
