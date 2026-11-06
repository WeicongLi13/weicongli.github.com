module

public import Cylinder.ProjectivePointSet
public import Cylinder.ProjectiveIncidence
public import Cylinder.WhiteBlackWeights
public import Mathlib.Tactic.Ring
public meta import Lean.Elab.Tactic.Omega

/-!
# The energy identities of the dual configuration

White and black points are actual dual projective points whose planes
have intersection quotient zero or at least two. The incidence sums
come from the actual point and pair counts in PG(3,p). This proves the
energy assertions of Lemma `lem:balance`; its pencil assertion is a
separate geometric step.
-/

@[expose] public section

noncomputable section

namespace Cylinder.ProjectiveBalance

open Cylinder.ProjectiveGeometry Cylinder.ProjectivePointSet
open scoped BigOperators Classical

variable (p : ℕ) [Fact p.Prime]

def quotient (S : Finset (Geometry.Point p)) (H : DualPoint p) : ℕ :=
  (intersection p S H).card / p

def whitePoints (S : Finset (Geometry.Point p)) : Finset (DualPoint p) :=
  WhiteBlackWeights.white Finset.univ (quotient p S)

def blackPoints (S : Finset (Geometry.Point p)) : Finset (DualPoint p) :=
  WhiteBlackWeights.black Finset.univ (quotient p S)

def weight (S : Finset (Geometry.Point p)) (H : DualPoint p) : ℕ := quotient p S H - 1

theorem point_plane_count (x : PG3 p) :
    (IncidenceDoubleCount.through (Incident p) x).card = p ^ 2 + p + 1 := by
  simpa only [Nat.card_eq_fintype_card, Fintype.card_subtype,
    IncidenceDoubleCount.through] using ProjectiveIncidence.card_planesThrough p x

theorem pair_plane_count (x y : PG3 p) (hxy : x ≠ y) :
    (IncidenceDoubleCount.through (fun z H => Incident p z.1 H ∧ Incident p z.2 H) (x, y)).card =
      p + 1 := by
  simpa only [Nat.card_eq_fintype_card, Fintype.card_subtype,
    IncidenceDoubleCount.through] using ProjectiveIncidence.card_planesThroughPair p x y hxy

theorem sum_intersection_card (S : Finset (Geometry.Point p)) :
    (∑ H : DualPoint p, (intersection p S H).card) = S.card * (p ^ 2 + p + 1) := by
  have h := IncidenceDoubleCount.first_moment (Incident p) (pointSet p S) (p ^ 2 + p + 1)
    (fun x _ => point_plane_count p x)
  simpa only [pointSet_card, intersection] using h

theorem sum_intersection_pairs (S : Finset (Geometry.Point p)) :
    (∑ H : DualPoint p, (intersection p S H).card * ((intersection p S H).card - 1)) =
      S.card * (S.card - 1) * (p + 1) := by
  have h := IncidenceDoubleCount.second_moment (Incident p) (pointSet p S) (p + 1) (by
    intro z hz
    exact pair_plane_count p z.1 z.2 (Finset.mem_offDiag.mp hz).2.2)
  simpa only [pointSet_card, intersection] using h

theorem p_mul_quotient {S : Finset (Geometry.Point p)} (hS : Geometry.PDivisible p S)
    (H : DualPoint p) : p * quotient p S H = (intersection p S H).card := by
  exact Nat.mul_div_cancel' (intersection_card_dvd p hS H)

theorem sum_quotient {S : Finset (Geometry.Point p)} (hcard : S.card = p ^ 2)
    (hS : Geometry.PDivisible p S) :
    (∑ H : DualPoint p, quotient p S H) = p ^ 3 + p ^ 2 + p := by
  apply Nat.eq_of_mul_eq_mul_left (Nat.Prime.pos (Fact.out : p.Prime))
  rw [Finset.mul_sum]
  simp_rw [p_mul_quotient p hS]
  rw [sum_intersection_card, hcard]
  ring

theorem falling_pair_identity (p r : ℕ) (hp : 1 ≤ p) :
    (p * r) * (p * r - 1) = p ^ 2 * (r * (r - 1)) + (p - 1) * (p * r) := by
  cases r with
  | zero => simp
  | succ r =>
      simp only [Nat.add_sub_cancel]
      rw [mul_add, mul_one, Nat.add_sub_assoc hp]
      ring

theorem polynomial_count_identity (p : ℕ) :
    (p ^ 2 - 1) * (p + 1) = (p - 1) * (p ^ 2 + p + 1) + p * (p - 1) := by
  cases p with
  | zero => simp
  | succ p =>
      simp only [Nat.add_sub_cancel]
      have heq : (p + 1) ^ 2 - 1 = p ^ 2 + 2 * p := by
        have h : (p + 1) ^ 2 = p ^ 2 + 2 * p + 1 := by ring
        rw [h, Nat.add_sub_cancel]
      rw [heq]
      ring

theorem sum_quotient_pairs {S : Finset (Geometry.Point p)} (hcard : S.card = p ^ 2)
    (hS : Geometry.PDivisible p S) :
    (∑ H : DualPoint p, quotient p S H * (quotient p S H - 1)) = p * (p - 1) := by
  have hp : 1 ≤ p := (Fact.out : p.Prime).one_lt.le
  have hpoint (H : DualPoint p) :
      (intersection p S H).card * ((intersection p S H).card - 1) =
        p ^ 2 * (quotient p S H * (quotient p S H - 1)) +
          (p - 1) * (intersection p S H).card := by
    rw [← p_mul_quotient p hS H]
    exact falling_pair_identity p _ hp
  have hsum := Finset.sum_congr rfl (fun H (_ : H ∈ (Finset.univ : Finset (DualPoint p))) => hpoint H)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    sum_intersection_pairs, sum_intersection_card, hcard] at hsum
  have hrhs : p ^ 2 * (p ^ 2 - 1) * (p + 1) =
      p ^ 2 * (p * (p - 1)) + (p - 1) * (p ^ 2 * (p ^ 2 + p + 1)) := by
    rw [mul_assoc, polynomial_count_identity]
    ring
  rw [hrhs] at hsum
  have heq : p ^ 2 * (p * (p - 1)) =
      p ^ 2 * (∑ H : DualPoint p, quotient p S H * (quotient p S H - 1)) :=
    Nat.add_right_cancel hsum
  exact Nat.eq_of_mul_eq_mul_left (pow_pos (Fact.out : p.Prime).pos 2) heq.symm

theorem quotient_total (S : Finset (Geometry.Point p)) (hcard : S.card = p ^ 2)
    (hS : Geometry.PDivisible p S) :
    (∑ H : DualPoint p, quotient p S H) + 1 = (Finset.univ : Finset (DualPoint p)).card := by
  rw [sum_quotient p hcard hS, Finset.card_univ, card_dualPoint]

theorem sum_black_weight {S : Finset (Geometry.Point p)} (hcard : S.card = p ^ 2)
    (hS : Geometry.PDivisible p S) :
    (∑ H ∈ blackPoints p S, weight p S H) = (whitePoints p S).card - 1 := by
  exact WhiteBlackWeights.sum_black_weight_eq_white_sub_one _ _ (quotient_total p S hcard hS)

theorem sum_black_energy {S : Finset (Geometry.Point p)} (hcard : S.card = p ^ 2)
    (hS : Geometry.PDivisible p S) :
    (∑ H ∈ blackPoints p S, weight p S H * (weight p S H + 1)) = p * (p - 1) := by
  exact (WhiteBlackWeights.energy_identity _ _).trans (sum_quotient_pairs p hcard hS)

theorem black_nonempty {S : Finset (Geometry.Point p)} (hcard : S.card = p ^ 2)
    (hS : Geometry.PDivisible p S) : (blackPoints p S).Nonempty := by
  exact WhiteBlackWeights.black_nonempty _ _ p (Fact.out : p.Prime).two_le
    (sum_quotient_pairs p hcard hS)

theorem white_card_upper_bound {S : Finset (Geometry.Point p)} (hcard : S.card = p ^ 2)
    (hS : Geometry.PDivisible p S) : (whitePoints p S).card ≤ 1 + p * (p - 1) / 2 := by
  exact WhiteBlackWeights.white_card_upper_bound _ _ p (quotient_total p S hcard hS)
    (sum_quotient_pairs p hcard hS)

end Cylinder.ProjectiveBalance

end
