module

public import Cylinder.ProjectionPolynomial
public import Cylinder.AffineProjection
public import Cylinder.LineFactors
public import Cylinder.FactorDegreeBound
public import Mathlib.Tactic.FieldSimp

/-!
# Empty lines in an affine quotient plane

The line parameters cover the horizontal and graph forms of affine
lines. An empty line is defined by the actual projection-fibre counts,
not by a postulated polynomial factor. The projection lemma gives a
nonzero low-degree polynomial. Each empty line yields a distinct prime
linear factor, and the total-degree bound counts these lines.
-/

@[expose] public section

noncomputable section

namespace Cylinder.EmptyLineBound

open Cylinder.Geometry Cylinder.CoordinateProjection Cylinder.ProjectionPolynomial
open scoped Classical

variable (p : ℕ) [Fact p.Prime]

theorem mem_linePoints_iff (L : LineFactors.Line (ZMod p)) (q : QuotientPoint p) :
    q ∈ LineFactors.linePoints L ↔ MvPolynomial.eval q (LineFactors.equation L) = 0 := by
  simp only [LineFactors.linePoints, Finset.mem_image, Finset.mem_univ, true_and]
  rcases L with c | ⟨α, β⟩
  · simp only [LineFactors.equation, map_sub, MvPolynomial.eval_X, MvPolynomial.eval_C,
      sub_eq_zero]
    constructor
    · rintro ⟨t, ht⟩
      simpa only [LineFactors.point, Matrix.cons_val_one, Matrix.cons_val_zero] using
        (congrFun ht 1).symm
    · intro hq
      refine ⟨q 0, ?_⟩
      funext i
      fin_cases i <;> simp [LineFactors.point, hq]
  · simp only [LineFactors.equation, LineDivisibility.graphEquation, map_sub, map_add,
      map_mul, MvPolynomial.eval_X, MvPolynomial.eval_C, sub_eq_zero]
    constructor
    · rintro ⟨t, ht⟩
      have hx := congrFun ht 0
      have hy := congrFun ht 1
      simp only [LineFactors.point, Matrix.cons_val_zero, Matrix.cons_val_one] at hx hy
      rw [← hx, ← hy]
      ring
    · intro hq
      refine ⟨q 1, ?_⟩
      funext i
      fin_cases i
      · change α + q 1 * β = q 0
        rw [mul_comm]
        exact hq.symm
      · rfl

/-- Every affine quotient line with a nonzero normal has one of the
normalized horizontal or graph forms. -/
theorem quotientLine_eq_normalized {n : QuotientPoint p} (hn : n ≠ 0) (b : ZMod p) :
    ∃ L : LineFactors.Line (ZMod p), quotientLine p n b = LineFactors.linePoints L := by
  by_cases h0 : n 0 = 0
  · have h1 : n 1 ≠ 0 := by
      intro h
      apply hn
      funext i
      fin_cases i <;> simp_all
    refine ⟨Sum.inl (b / n 1), ?_⟩
    ext q
    rw [mem_quotientLine, mem_linePoints_iff]
    simp only [quotientPairing, Fin.sum_univ_two, h0, zero_mul, zero_add,
      LineFactors.equation, map_sub, MvPolynomial.eval_X, MvPolynomial.eval_C,
      sub_eq_zero]
    rw [eq_div_iff h1]
    rw [mul_comm (q 1) (n 1)]
  · refine ⟨Sum.inr (b / n 0, -n 1 / n 0), ?_⟩
    ext q
    rw [mem_quotientLine, mem_linePoints_iff]
    simp only [quotientPairing, Fin.sum_univ_two, LineFactors.equation,
      LineDivisibility.graphEquation, map_sub, map_add, map_mul,
      MvPolynomial.eval_X, MvPolynomial.eval_C]
    have heq : q 0 - (b / n 0 + (-n 1 / n 0) * q 1) =
        (n 0 * q 0 + n 1 * q 1 - b) / n 0 := by
      field_simp
      ring
    rw [heq, div_eq_zero_iff]
    simp only [h0, or_false, sub_eq_zero]

def emptyLines (S : Finset (Point p)) : Finset (LineFactors.Line (ZMod p)) :=
  Finset.univ.filter (fun L => ∀ t : ZMod p, fibreSize p S (LineFactors.point L t) = 0)

def emptyQuotientLines (S : Finset (Point p)) : Finset (Finset (QuotientPoint p)) :=
  (emptyLines p S).image LineFactors.linePoints

theorem empty_quotientLine_mem {S : Finset (Point p)}
    {n : QuotientPoint p} (hn : n ≠ 0) (b : ZMod p)
    (hempty : ∀ q ∈ quotientLine p n b, fibreSize p S q = 0) :
    quotientLine p n b ∈ emptyQuotientLines p S := by
  obtain ⟨L, hL⟩ := quotientLine_eq_normalized p hn b
  apply Finset.mem_image.mpr
  refine ⟨L, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, hL.symm⟩
  intro t
  apply hempty
  rw [hL]
  exact (mem_linePoints_iff p L _).mpr (LineFactors.equation_eval_point L t)

theorem empty_line_polynomial_vanishes {S : Finset (Point p)}
    {L : LineFactors.Line (ZMod p)} (hL : L ∈ emptyLines p S) :
    LineFactors.VanishesOn (countPolynomial p S) L := by
  intro t
  rw [eval_countPolynomial, (Finset.mem_filter.mp hL).2 t, Nat.cast_zero]

/-- The affine quotient-plane assertion of Lemma `lem:planecap`. -/
theorem emptyLines_card_le {S : Finset (Point p)} (hcard : S.card = p ^ 2)
    (hS : PDivisible p S) (hnon : ¬ IsCylinder p S) :
    (emptyLines p S).card ≤ p - 2 := by
  have hp := (Fact.out : p.Prime).two_le
  have hdegree := countPolynomial_totalDegree_le p hS
  have hsmall : (countPolynomial p S).totalDegree < Fintype.card (ZMod p) := by
    rw [ZMod.card]
    omega
  apply le_trans (FactorDegreeBound.linear_factor_count_le_totalDegree
    (emptyLines p S) LineFactors.equation (countPolynomial p S)
    (countPolynomial_ne_zero_of_not_isCylinder p hcard hnon) ?_ ?_ ?_) hdegree
  · intro L _ M _ hLM
    exact LineFactors.equation_isRelPrime L M hLM
  · intro L hL
    exact LineFactors.equation_dvd_of_vanishing _ L hsmall
      (empty_line_polynomial_vanishes p hL)
  · intro L _
    exact LineFactors.equation_totalDegree L

theorem emptyQuotientLines_card_le {S : Finset (Point p)} (hcard : S.card = p ^ 2)
    (hS : PDivisible p S) (hnon : ¬ IsCylinder p S) :
    (emptyQuotientLines p S).card ≤ p - 2 := by
  exact (Finset.card_image_le).trans (emptyLines_card_le p hcard hS hnon)

/-- The bound holds in every affine coordinate system, including
translations of the original point set. -/
theorem emptyQuotientLines_card_le_in_affine_coordinates
    (e : Point p ≃ᵃ[ZMod p] Point p) {S : Finset (Point p)}
    (hcard : S.card = p ^ 2) (hS : PDivisible p S) (hnon : ¬ IsCylinder p S) :
    (emptyQuotientLines p (S.image e)).card ≤ p - 2 := by
  apply emptyQuotientLines_card_le p
  · simpa only [AffineTransport.image_card] using hcard
  · exact AffineTransport.pDivisible_image p e hS
  · intro h
    exact hnon ((AffineTransport.isCylinder_image_iff p e S).mp h)

end Cylinder.EmptyLineBound

end
