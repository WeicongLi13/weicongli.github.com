module

public import Cylinder.FiniteGrid
public import Cylinder.AffineLinePolynomial
public import Cylinder.PowerSums
public import Mathlib.Algebra.Polynomial.Eval.Degree
public import Mathlib.Algebra.Polynomial.Roots

/-!
# Integer representatives of a low-degree plane polynomial

For a nonzero polynomial of total degree at most `p - 2` over `ZMod p`,
the sum of the ordinary representatives of its values on the affine
plane is at least `p^2`.  A nonzero highest homogeneous component gives
a direction in which every line restriction is nonzero.  Each line has
a positive sum divisible by `p`. Explicit coordinate equivalences prove
that the parallel lines partition the plane.
-/

@[expose] public section

noncomputable section

open scoped Classical

namespace Cylinder.IntegerLift

open Finset MvPolynomial

variable {p : ℕ} [Fact p.Prime]

/-- Every polynomial of degree below `p - 1` has zero field-valued sum
over the prime field. -/
theorem univariate_sum_eq_zero (Q : Polynomial (ZMod p))
    (hdegree : Q.natDegree < p - 1) : (∑ t : ZMod p, Q.eval t) = 0 := by
  simp_rw [Polynomial.eval_eq_sum_range' hdegree]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro i hi
  rw [← Finset.mul_sum, PowerSums.prime_sum_pow_low p i (Finset.mem_range.mp hi), mul_zero]

/-- Nonzero, low-degree line polynomials have positive integer sums
divisible by `p`, so each sum is at least `p`. -/
theorem univariate_integer_sum_lower (Q : Polynomial (ZMod p))
    (hQ : Q ≠ 0) (hdegree : Q.natDegree < p - 1) :
    p ≤ ∑ t : ZMod p, (Q.eval t).val := by
  have hroot : ∃ t : ZMod p, Q.eval t ≠ 0 := by
    by_contra h
    apply hQ
    apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero Q Function.injective_id
    · intro t
      by_contra ht
      exact h ⟨t, ht⟩
    · have hcard : Q.natDegree < p := by omega
      simpa only [ZMod.card] using hcard
  obtain ⟨t, ht⟩ := hroot
  have hle : (Q.eval t).val ≤ ∑ x : ZMod p, (Q.eval x).val :=
    Finset.single_le_sum (f := fun x : ZMod p => (Q.eval x).val)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ t)
  have hpos : 0 < ∑ x : ZMod p, (Q.eval x).val := (ZMod.val_pos.mpr ht).trans_le hle
  have hcast : ((∑ x : ZMod p, (Q.eval x).val : ℕ) : ZMod p) = 0 := by
    rw [Nat.cast_sum]
    simp only [ZMod.natCast_zmod_val]
    exact univariate_sum_eq_zero Q hdegree
  exact Nat.le_of_dvd hpos ((ZMod.natCast_eq_zero_iff _ p).mp hcast)

section Coordinates

variable {K : Type*} [Field K]

/-- Parallel lines with a nonzero first direction coordinate partition
the plane. The first parameter selects the line, the second its point. -/
def horizontalCoordinates (v₀ v₁ : K) (hv₀ : v₀ ≠ 0) : K × K ≃ K × K where
  toFun ct := (ct.2 * v₀, ct.1 + ct.2 * v₁)
  invFun xy := (xy.2 - (xy.1 / v₀) * v₁, xy.1 / v₀)
  left_inv ct := by
    rcases ct with ⟨c, t⟩
    apply Prod.ext <;> simp [hv₀]
  right_inv xy := by
    rcases xy with ⟨x, y⟩
    apply Prod.ext <;> simp [hv₀]

/-- The corresponding partition when only the second coordinate of the
direction is nonzero. -/
def verticalCoordinates (v₁ : K) (hv₁ : v₁ ≠ 0) : K × K ≃ K × K where
  toFun ct := (ct.1, ct.2 * v₁)
  invFun xy := (xy.1, xy.2 / v₁)
  left_inv ct := by
    rcases ct with ⟨c, t⟩
    apply Prod.ext <;> simp [hv₁]
  right_inv xy := by
    rcases xy with ⟨x, y⟩
    apply Prod.ext <;> simp [hv₁]

theorem sum_horizontalCoordinates [Fintype K] (W : K → K → ℕ)
    (v₀ v₁ : K) (hv₀ : v₀ ≠ 0) :
    (∑ c : K, ∑ t : K, W (t * v₀) (c + t * v₁)) =
      ∑ x : K, ∑ y : K, W x y := by
  have h := Fintype.sum_equiv (horizontalCoordinates v₀ v₁ hv₀)
    (fun ct : K × K => W (ct.2 * v₀) (ct.1 + ct.2 * v₁))
    (fun xy : K × K => W xy.1 xy.2) (fun _ => rfl)
  simpa only [Fintype.sum_prod_type] using h

theorem sum_verticalCoordinates [Fintype K] (W : K → K → ℕ)
    (v₁ : K) (hv₁ : v₁ ≠ 0) :
    (∑ c : K, ∑ t : K, W c (t * v₁)) = ∑ x : K, ∑ y : K, W x y := by
  have h := Fintype.sum_equiv (verticalCoordinates v₁ hv₁)
    (fun ct : K × K => W ct.1 (ct.2 * v₁))
    (fun xy : K × K => W xy.1 xy.2) (fun _ => rfl)
  simpa only [Fintype.sum_prod_type] using h

end Coordinates

/-- The integer lift bound used in Lemma `lem:projectionpoly`. All
direction, line nonvanishing, and partition conditions are derived. -/
theorem integer_lift_lower_bound (P : MvPolynomial (Fin 2) (ZMod p))
    (hP : P ≠ 0) (hdegree : P.totalDegree ≤ p - 2) :
    p ^ 2 ≤ ∑ x : ZMod p, ∑ y : ZMod p, (eval ![x, y] P).val := by
  obtain ⟨v, hv, htop⟩ := FiniteGrid.zmod_top_component_has_nonzero_direction P hP hdegree
  have hp : 2 ≤ p := (Fact.out : p.Prime).two_le
  have line_lower (a : Fin 2 → ZMod p) :
      p ≤ ∑ t : ZMod p, (eval (fun i => a i + t * v i) P).val := by
    have hQ := AffineLinePolynomial.linePolynomial_ne_zero P a v htop
    have hQdegree : (AffineLinePolynomial.linePolynomial P a v).natDegree < p - 1 := by
      have h := AffineLinePolynomial.linePolynomial_degree_le P a v
      omega
    simpa only [AffineLinePolynomial.linePolynomial_eval] using
      univariate_integer_sum_lower (AffineLinePolynomial.linePolynomial P a v) hQ hQdegree
  rw [pow_two]
  by_cases hv₀ : v 0 = 0
  · have hv₁ : v 1 ≠ 0 := by
      intro h
      apply hv
      funext i
      fin_cases i <;> simp_all
    calc
      p * p = ∑ _c : ZMod p, p := by simp [ZMod.card]
      _ ≤ ∑ c : ZMod p, ∑ t : ZMod p, (eval ![c, t * v 1] P).val := by
        apply Finset.sum_le_sum
        intro c _
        have he (t : ZMod p) :
            (fun i => ![c, 0] i + t * v i) = ![c, t * v 1] := by
          funext i
          fin_cases i <;> simp [hv₀]
        simpa only [he] using line_lower ![c, 0]
      _ = _ := sum_verticalCoordinates (fun x y => (eval ![x, y] P).val) (v 1) hv₁
  · calc
      p * p = ∑ _c : ZMod p, p := by simp [ZMod.card]
      _ ≤ ∑ c : ZMod p, ∑ t : ZMod p,
          (eval ![t * v 0, c + t * v 1] P).val := by
        apply Finset.sum_le_sum
        intro c _
        have he (t : ZMod p) :
            (fun i => ![0, c] i + t * v i) = ![t * v 0, c + t * v 1] := by
          funext i
          fin_cases i <;> simp
        simpa only [he] using line_lower ![0, c]
      _ = _ := sum_horizontalCoordinates (fun x y => (eval ![x, y] P).val)
        (v 0) (v 1) hv₀

end Cylinder.IntegerLift
