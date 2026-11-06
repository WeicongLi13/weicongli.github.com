module

public import Cylinder.FrobeniusPolarBound
public import Cylinder.PolynomialDivisibilityDescent
public import Cylinder.PowerRelationScalarExtension
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.LinearAlgebra.Projectivization.Cardinality

/-! The standalone reducible-curve bound in Proposition 4.6 of finalfinal.tex.
The hypothesis excludes base-field line factors; no line-cap assumption is used. -/

@[expose] public section
noncomputable section
open scoped Classical BigOperators

namespace Cylinder.FinalCurvePointBound

open MvPolynomial Cylinder.RationalPlaneLine Cylinder.PlaneCurveFactors
open Cylinder.PowerEvaluationRelation Cylinder.CurvePointAggregation

variable (p : ℕ) [Fact p.Prime]
variable {K : Type*} [Field K] [CharP K p] [IsAlgClosed K] [Algebra (ZMod p) K]

local instance : Fintype (PlanePoint (ZMod p)) := Fintype.ofFinite _

theorem linear_geometric_factor_card_le_one
    (D : Finset (PlanePoint (ZMod p))) (F : MvPolynomial (Fin 3) (ZMod p))
    (hline : ∀ c : Fin 3 → ZMod p, c ≠ 0 → ¬linearForm c ∣ F)
    (G : MvPolynomial (Fin 3) K) (hG : G.IsHomogeneous 1) (hG0 : G ≠ 0)
    (hdiv : G ∣ MvPolynomial.map (algebraMap (ZMod p) K) F) :
    (zeroSet (algebraMap (ZMod p) K) D G).card ≤ 1 := by
  by_contra hn
  have htwo : 1 < (zeroSet (algebraMap (ZMod p) K) D G).card := by omega
  obtain ⟨P, hP, Q, hQ, hPQ⟩ := Finset.one_lt_card.mp htwo
  obtain ⟨c, hc, u, hu, hGu⟩ := line_equation_descends (algebraMap (ZMod p) K)
    G hG hG0 P.rep Q.rep P.rep_nonzero (representatives_not_proportional P Q hPQ)
    (Finset.mem_filter.mp hP).2 (Finset.mem_filter.mp hQ).2
  have hGmul : G = C u * MvPolynomial.map (algebraMap (ZMod p) K) (linearForm c) := by
    rw [hGu, Cylinder.PowerRelationScalarExtension.map_linearForm]
    simp [linearForm, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]
  have hbase : MvPolynomial.map (algebraMap (ZMod p) K) (linearForm c) ∣ G := by
    rw [hGmul]
    exact dvd_mul_left _ _
  exact hline c hc (Cylinder.PolynomialDivisibilityDescent.dvd_of_mapped_dvd
    (linearForm c) F (hbase.trans hdiv))

include K in
theorem twice_card_le
    (D : Finset (PlanePoint (ZMod p))) (F : MvPolynomial (Fin 3) (ZMod p)) (d : ℕ)
    (hF : F.IsHomogeneous d) (hF0 : F ≠ 0) (hd : d < p)
    (hline : ∀ c : Fin 3 → ZMod p, c ≠ 0 → ¬linearForm c ∣ F) :
    2 * (D.filter (fun P => eval P.rep F = 0)).card ≤ d * (d + p - 1) := by
  let f := algebraMap (ZMod p) K
  let E := MvPolynomial.map f F
  have hE0 : E ≠ 0 := by
    intro hz
    exact hF0 (MvPolynomial.map_injective f f.injective (by simpa only [map_zero] using hz))
  have hEhom : E.IsHomogeneous d := hF.map f
  have hdegree : E.totalDegree = d := hEhom.totalDegree hE0
  have hzset : zeroSet f D E = D.filter (fun P => eval P.rep F = 0) := by
    ext P
    simp only [zeroSet, Finset.mem_filter, E, Cylinder.FrobeniusPolarBound.eval_map_at_mapped_point]
    rw [map_eq_zero_iff f f.injective]
  rw [← hzset]
  apply curve_bound_of_factor_bounds f D E hE0 d p (Fact.out : p.Prime).pos hdegree.le
  intro G hG
  have hhom := factor_homogeneous E d hEhom hE0 G hG
  have hirr := factor_irreducible E G hG
  have hpos := positive_degree_of_irreducible G hirr
  have hdeg : G.totalDegree < p :=
    lt_of_le_of_lt (by
      have h := totalDegree_le_of_dvd_of_isDomain (factor_dvd E G hG) hE0
      rwa [hdegree] at h) hd
  by_cases hlinear : G.totalDegree = 1
  · have hcard := linear_geometric_factor_card_le_one p D F hline G
      (by simpa only [hlinear] using hhom) hirr.ne_zero (factor_dvd E G hG)
    change (zeroSet f D G).card ≤ 1 at hcard
    rw [hlinear]
    have hp := (Fact.out : p.Prime).two_le
    omega
  · have hn : 2 ≤ G.totalDegree := by omega
    let T := zeroSet f D G
    have hzero : ∀ P : T, eval (Cylinder.RationalPlanePointModel.representatives f T P) G = 0 := by
      intro P
      exact (Finset.mem_filter.mp P.property).2
    have hbound := Cylinder.IrreduciblePolarPointBound.rational_point_bound p G.totalDegree G
      hhom hirr hn hdeg (Cylinder.RationalPlanePointModel.representatives f T)
      (Cylinder.RationalPlanePointModel.representatives_nonzero f T)
      (Cylinder.RationalPlanePointModel.representatives_distinct f T)
      (Cylinder.RationalPlanePointModel.representatives_frobeniusFixed p f T) hzero
    simpa only [Fintype.card_coe] using hbound

include K in
theorem card_le_half
    (D : Finset (PlanePoint (ZMod p))) (F : MvPolynomial (Fin 3) (ZMod p)) (d : ℕ)
    (hF : F.IsHomogeneous d) (hF0 : F ≠ 0) (hd : d < p)
    (hline : ∀ c : Fin 3 → ZMod p, c ≠ 0 → ¬linearForm c ∣ F) :
    (D.filter (fun P => eval P.rep F = 0)).card ≤ d * (d + p - 1) / 2 := by
  apply (Nat.le_div_iff_mul_le (by decide : 0 < 2)).mpr
  simpa only [mul_comm] using twice_card_le p (K := K) D F d hF hF0 hd hline

/-- The full finite-field curve, with no auxiliary choice of extension field. -/
theorem carlin_voloch (F : MvPolynomial (Fin 3) (ZMod p)) (d : ℕ)
    (hF : F.IsHomogeneous d) (hF0 : F ≠ 0) (hd : d < p)
    (hline : ∀ c : Fin 3 → ZMod p, c ≠ 0 → ¬linearForm c ∣ F) :
    (Finset.univ.filter (fun P : PlanePoint (ZMod p) => eval P.rep F = 0)).card ≤
      d * (d + p - 1) / 2 :=
  card_le_half p (K := AlgebraicClosure (ZMod p)) Finset.univ F d hF hF0 hd hline

#print axioms carlin_voloch

end Cylinder.FinalCurvePointBound

end
