module

public import Cylinder.ProjectiveCover
public import Cylinder.IncidenceRestricted

/-!
# Incidence consequences needed by the product proposition

The intersection sum through a point is computed both inside and outside
the point set. Its quotient sum is divisible by `p`. The elementary
intersection cap also proves the manuscript's `|E| ≥ p` bound.
-/

@[expose] public section

noncomputable section

namespace Cylinder.ProductIntersection

open Cylinder.ProjectiveGeometry Cylinder.ProjectivePointSet Cylinder.ProjectiveBalance
open Cylinder.ProjectiveCover
open scoped BigOperators Classical

variable (p : ℕ) [Fact p.Prime]

theorem sum_intersection_through_point (S : Finset (Geometry.Point p)) (x : PG3 p) :
    (∑ H ∈ IncidenceDoubleCount.through (Incident p) x, (intersection p S H).card) =
      S.card * (p + 1) + if x ∈ pointSet p S then p ^ 2 else 0 := by
  change (∑ H ∈ IncidenceDoubleCount.through (Incident p) x,
    ((pointSet p S).filter (fun y => Incident p y H)).card) = _
  rw [IncidenceRestricted.sum_card_on]
  have hpoint (y : PG3 p) :
      ((IncidenceDoubleCount.through (Incident p) x).filter (fun H => Incident p y H)).card =
        (p + 1) + if y = x then p ^ 2 else 0 := by
    by_cases hyx : y = x
    · subst y
      simpa [IncidenceDoubleCount.through, Finset.filter_filter, Nat.add_comm,
        Nat.add_left_comm, Nat.add_assoc] using point_plane_count p x
    · have heq :
          (IncidenceDoubleCount.through (Incident p) x).filter (fun H => Incident p y H) =
            IncidenceDoubleCount.through (fun z H => Incident p z.1 H ∧ Incident p z.2 H) (x, y) := by
        ext H
        simp [IncidenceDoubleCount.through]
      rw [heq, pair_plane_count p x y (Ne.symm hyx)]
      simp [hyx]
  simp_rw [hpoint]
  simp [Finset.sum_add_distrib, pointSet_card, Nat.mul_comm]

theorem sum_quotient_through_dvd {S : Finset (Geometry.Point p)}
    (hcard : S.card = p ^ 2) (hS : Geometry.PDivisible p S) (x : PG3 p) :
    p ∣ ∑ H ∈ IncidenceDoubleCount.through (Incident p) x, quotient p S H := by
  refine ⟨p + 1 + (if x ∈ pointSet p S then 1 else 0), ?_⟩
  apply Nat.eq_of_mul_eq_mul_left (Fact.out : p.Prime).pos
  rw [Finset.mul_sum]
  simp_rw [p_mul_quotient p hS]
  rw [sum_intersection_through_point, hcard]
  split_ifs <;> ring

theorem quotient_le_prime {S : Finset (Geometry.Point p)} (hcard : S.card = p ^ 2)
    (hS : Geometry.PDivisible p S) (H : DualPoint p) : quotient p S H ≤ p := by
  have hle : (intersection p S H).card ≤ S.card := by
    calc
      (intersection p S H).card ≤ (pointSet p S).card :=
        Finset.card_le_card (Finset.filter_subset _ _)
      _ = S.card := pointSet_card p S
  have hmul : p * quotient p S H ≤ p * p := by
    rw [p_mul_quotient p hS H]
    simpa only [hcard, pow_two] using hle
  exact le_of_mul_le_mul_left hmul (Fact.out : p.Prime).pos

/-- The actual white configuration has at least `p` points, as used in the product proof. -/
theorem white_card_lower_bound {S : Finset (Geometry.Point p)} (hcard : S.card = p ^ 2)
    (hS : Geometry.PDivisible p S) : p ≤ (whitePoints p S).card := by
  have henergy : p * (p - 1) ≤ p * ((whitePoints p S).card - 1) := by
    calc
      p * (p - 1) = ∑ H ∈ blackPoints p S, weight p S H * (weight p S H + 1) :=
        (sum_black_energy p hcard hS).symm
      _ ≤ p * (∑ H ∈ blackPoints p S, weight p S H) := by
        rw [Finset.mul_sum]
        apply Finset.sum_le_sum
        intro H hH
        have hq : 2 ≤ quotient p S H := (Finset.mem_filter.mp hH).2
        have hw : weight p S H + 1 = quotient p S H := by unfold weight; omega
        rw [hw]
        exact (Nat.mul_le_mul_left _ (quotient_le_prime p hcard hS H)).trans_eq (mul_comm _ _)
      _ = p * ((whitePoints p S).card - 1) := by rw [sum_black_weight p hcard hS]
  have hle := le_of_mul_le_mul_left henergy (Fact.out : p.Prime).pos
  have hp := (Fact.out : p.Prime).two_le
  have hn : 0 < (whitePoints p S).card :=
    Finset.card_pos.mpr ⟨infinity p, infinity_mem_whitePoints p S⟩
  omega

#print axioms sum_intersection_through_point
#print axioms sum_quotient_through_dvd
#print axioms white_card_lower_bound

end Cylinder.ProductIntersection

end
