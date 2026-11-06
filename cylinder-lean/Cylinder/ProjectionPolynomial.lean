module

public import Cylinder.CoordinateProjection
public import Cylinder.FiniteGrid
public import Cylinder.ProjectionDegree
public import Cylinder.IntegerLift
public import Cylinder.DirectionCylinder
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# The reduced polynomial of the actual projection fibres

The interpolation data are the fibre cardinalities of a subset of the
actual affine three-space. Plane divisibility gives the line-sum
conditions, and hence the total-degree bound in Lemma `lem:projectionpoly`.
-/

@[expose] public section

noncomputable section

namespace Cylinder.ProjectionPolynomial

open Cylinder.Geometry Cylinder.CoordinateProjection MvPolynomial
open scoped BigOperators Classical

variable (p : ℕ) [Fact p.Prime]

def planeEquiv : (ZMod p × ZMod p) ≃ QuotientPoint p where
  toFun z := ![z.1, z.2]
  invFun q := (q 0, q 1)
  left_inv _ := rfl
  right_inv q := by
    funext i
    fin_cases i <;> rfl

omit [Fact p.Prime] in
@[simp] theorem planeEquiv_apply (z : ZMod p × ZMod p) :
    planeEquiv p z = ![z.1, z.2] := rfl

theorem double_sum_eq_sum (f : QuotientPoint p → ℕ) :
    (∑ x : ZMod p, ∑ y : ZMod p, f ![x, y]) = ∑ q, f q := by
  simpa only [planeEquiv_apply, Fintype.sum_prod_type] using (planeEquiv p).sum_comp f

def countPolynomial (S : Finset (Point p)) : MvPolynomial (Fin 2) (ZMod p) :=
  FiniteGrid.binaryInterpolation (fun x y => (fibreSize p S ![x, y] : ZMod p))

@[simp] theorem eval_countPolynomial (S : Finset (Point p)) (q : QuotientPoint p) :
    eval q (countPolynomial p S) = (fibreSize p S q : ZMod p) := by
  have hq : ![q 0, q 1] = q := (planeEquiv p).right_inv q
  rw [← hq]
  exact FiniteGrid.eval_binaryInterpolation _ _ _

theorem countPolynomial_degreeOf_lt (S : Finset (Point p)) (i : Fin 2) :
    (countPolynomial p S).degreeOf i < p := by
  have hp := (Fact.out : p.Prime).two_le
  have h := FiniteGrid.zmod_binaryInterpolation_degreeOf_le
    (fun x y => (fibreSize p S ![x, y] : ZMod p)) i
  change (countPolynomial p S).degreeOf i ≤ p - 1 at h
  omega

theorem count_lineSumsZero {S : Finset (Point p)} (hS : PDivisible p S) :
    ProjectionMoments.LineSumsZero p
      (fun z => (fibreSize p S ![z.1, z.2] : ZMod p)) := by
  intro a b hab c
  let n : QuotientPoint p := ![a, b]
  have hn : n ≠ 0 := by
    intro hz
    apply hab
    apply Prod.ext
    · simpa [n] using congrFun hz 0
    · simpa [n] using congrFun hz 1
  have hcast : (∑ q ∈ quotientLine p n c, (fibreSize p S q : ZMod p)) = 0 := by
    have h := (ZMod.natCast_eq_zero_iff _ p).mpr (quotientLine_sum_dvd p hS hn c)
    simpa only [Nat.cast_sum] using h
  simp only [quotientLine, Finset.sum_filter] at hcast
  rw [Finset.sum_filter]
  calc
    (∑ z : ZMod p × ZMod p,
        if a * z.1 + b * z.2 = c then (fibreSize p S ![z.1, z.2] : ZMod p) else 0) =
      ∑ q : QuotientPoint p,
        if quotientPairing p n q = c then (fibreSize p S q : ZMod p) else 0 := by
      apply Fintype.sum_equiv (planeEquiv p)
      intro z
      simp [quotientPairing, n, Fin.sum_univ_two]
    _ = 0 := hcast

theorem countPolynomial_totalDegree_le {S : Finset (Point p)} (hS : PDivisible p S) :
    (countPolynomial p S).totalDegree ≤ p - 2 := by
  apply ProjectionDegree.totalDegree_le_of_lineSumsZero p _
    (countPolynomial_degreeOf_lt p S)
  simpa only [eval_countPolynomial] using count_lineSumsZero p hS

theorem isCylinder_of_countPolynomial_eq_zero {S : Finset (Point p)}
    (hcard : S.card = p ^ 2) (hzero : countPolynomial p S = 0) : IsCylinder p S := by
  apply isCylinder_of_fibreSize_dvd p hcard
  intro q
  apply (ZMod.natCast_eq_zero_iff _ p).mp
  rw [← eval_countPolynomial, hzero, map_zero]

theorem countPolynomial_ne_zero_of_not_isCylinder {S : Finset (Point p)}
    (hcard : S.card = p ^ 2) (hnon : ¬ IsCylinder p S) : countPolynomial p S ≠ 0 := by
  intro hz
  exact hnon (isCylinder_of_countPolynomial_eq_zero p hcard hz)

/-- Reducing an actual full fibre modulo `p` strictly decreases the
integer total of the fibre counts. -/
theorem representative_total_lt_of_full_fibre {S : Finset (Point p)}
    {q : QuotientPoint p} (hfull : fibreSize p S q = p) :
    (∑ x : ZMod p, ∑ y : ZMod p, (eval ![x, y] (countPolynomial p S)).val) < S.card := by
  simp only [eval_countPolynomial]
  rw [double_sum_eq_sum p (fun r => (fibreSize p S r : ZMod p).val),
    ← sum_fibreSize p S]
  apply Finset.sum_lt_sum
  · intro r _
    rw [ZMod.val_natCast]
    exact Nat.mod_le _ _
  · refine ⟨q, Finset.mem_univ _, ?_⟩
    rw [hfull, ZMod.val_natCast, Nat.mod_self]
    exact (Fact.out : p.Prime).pos

theorem countPolynomial_eq_zero_of_full_fibre {S : Finset (Point p)}
    (hcard : S.card = p ^ 2) (hS : PDivisible p S)
    {q : QuotientPoint p} (hfull : fibreSize p S q = p) :
    countPolynomial p S = 0 := by
  by_contra hnonzero
  have hlow := IntegerLift.integer_lift_lower_bound (countPolynomial p S) hnonzero
    (countPolynomial_totalDegree_le p hS)
  have hhigh := representative_total_lt_of_full_fibre p hfull
  rw [hcard] at hhigh
  exact (not_lt_of_ge hlow) hhigh

theorem fibreSize_dvd_of_countPolynomial_eq_zero {S : Finset (Point p)}
    (hzero : countPolynomial p S = 0) (q : QuotientPoint p) :
    p ∣ fibreSize p S q := by
  apply (ZMod.natCast_eq_zero_iff _ p).mp
  rw [← eval_countPolynomial, hzero, map_zero]

/-- A full coordinate fibre gives a cylinder in precisely that direction. -/
theorem inVerticalDirection_of_full_fibre {S : Finset (Point p)}
    (hcard : S.card = p ^ 2) (hS : PDivisible p S)
    {q : QuotientPoint p} (hfull : fibreSize p S q = p) :
    IsCylinderInDirection p S (verticalDirection p) := by
  apply DirectionCylinder.inVerticalDirection_of_fibreSize_dvd p hcard
  exact fibreSize_dvd_of_countPolynomial_eq_zero p
    (countPolynomial_eq_zero_of_full_fibre p hcard hS hfull)

/-- The first assertion of Lemma `lem:projectionpoly`, in an arbitrary
specified nonzero direction. -/
theorem inDirection_of_affineLine_subset {S : Finset (Point p)}
    (hcard : S.card = p ^ 2) (hS : PDivisible p S)
    {base direction : Point p} (hdirection : direction ≠ 0)
    (hline : affineLine p base direction ⊆ S) :
    IsCylinderInDirection p S direction := by
  obtain ⟨g, hgv⟩ := LinearTransport.exists_linearEquiv_to_vertical p hdirection
  have hcard' : (S.image g).card = p ^ 2 := by
    simpa only [LinearTransport.image_card] using hcard
  have hS' := LinearTransport.pDivisible_image p g hS
  have hfull := DirectionCylinder.fibreSize_image_eq_p_of_affineLine_subset p g hgv hline
  apply DirectionCylinder.inDirection_of_image_fibreSize_dvd p g hgv hcard
  exact fibreSize_dvd_of_countPolynomial_eq_zero p
    (countPolynomial_eq_zero_of_full_fibre p hcard' hS' hfull)

theorem fibreSize_lt_of_not_isCylinder {S : Finset (Point p)}
    (hcard : S.card = p ^ 2) (hS : PDivisible p S) (hnon : ¬ IsCylinder p S)
    (q : QuotientPoint p) : fibreSize p S q < p := by
  have hle := fibreSize_le p S q
  by_contra hnot
  have hfull : fibreSize p S q = p := by omega
  exact hnon (isCylinder_of_inDirection p
    (inVerticalDirection_of_full_fibre p hcard hS hfull))

/-- The second assertion of Lemma `lem:projectionpoly`. Coordinates can
be changed by any invertible linear map; all conclusions are derived
from the original point set and plane divisibility. -/
theorem noncylinder_projection (g : Point p ≃ₗ[ZMod p] Point p)
    {S : Finset (Point p)} (hcard : S.card = p ^ 2)
    (hS : PDivisible p S) (hnon : ¬ IsCylinder p S) :
    (∀ q : QuotientPoint p, fibreSize p (S.image g) q < p) ∧
    countPolynomial p (S.image g) ≠ 0 ∧
    (countPolynomial p (S.image g)).totalDegree ≤ p - 2 := by
  have hcard' : (S.image g).card = p ^ 2 := by
    simpa only [LinearTransport.image_card] using hcard
  have hS' := LinearTransport.pDivisible_image p g hS
  have hnon' : ¬ IsCylinder p (S.image g) := by
    intro h
    exact hnon ((LinearTransport.isCylinder_image_iff p g S).mp h)
  exact ⟨fibreSize_lt_of_not_isCylinder p hcard' hS' hnon',
    countPolynomial_ne_zero_of_not_isCylinder p hcard' hnon',
    countPolynomial_totalDegree_le p hS'⟩

end Cylinder.ProjectionPolynomial

end
