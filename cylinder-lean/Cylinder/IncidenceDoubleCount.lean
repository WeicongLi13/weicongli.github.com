module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Data.Finset.Prod

/-!
# Counting incidences with points and distinct ordered pairs

Both identities are derived from actual filtered finite sets. No
incidence total is postulated. Uniform point and pair incidence counts
can subsequently be supplied by the finite projective geometry module.
-/

@[expose] public section

noncomputable section

namespace Cylinder.IncidenceDoubleCount

open scoped BigOperators Classical

variable {A B : Type*} [Fintype B]

def intersection (R : A → B → Prop) (S : Finset A) (H : B) : Finset A :=
  S.filter (fun x => R x H)

def through (R : A → B → Prop) (x : A) : Finset B :=
  Finset.univ.filter (R x)

theorem sum_intersection_card (R : A → B → Prop) (S : Finset A) :
    (∑ H : B, (intersection R S H).card) = ∑ x ∈ S, (through R x).card := by
  have hcard (H : B) : (intersection R S H).card =
      ∑ x ∈ S, if R x H then 1 else 0 := by
    simp only [intersection, Finset.sum_boole, Nat.cast_id]
  simp_rw [hcard]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  simp only [through, Finset.sum_boole, Nat.cast_id]

omit [Fintype B] in
theorem intersection_offDiag (R : A → B → Prop) (S : Finset A) (H : B) :
    (intersection R S H).offDiag =
      S.offDiag.filter (fun z => R z.1 H ∧ R z.2 H) := by
  ext z
  simp only [intersection, Finset.mem_offDiag, Finset.mem_filter]
  aesop

theorem card_offDiag (S : Finset A) : S.offDiag.card = S.card * (S.card - 1) := by
  rw [Finset.offDiag_card, Nat.mul_sub_left_distrib, mul_one]

theorem sum_intersection_pairs (R : A → B → Prop) (S : Finset A) :
    (∑ H : B, (intersection R S H).card * ((intersection R S H).card - 1)) =
      ∑ z ∈ S.offDiag, (through (fun z H => R z.1 H ∧ R z.2 H) z).card := by
  calc
    (∑ H : B, (intersection R S H).card * ((intersection R S H).card - 1)) =
        ∑ H : B, (intersection R S H).offDiag.card := by
      apply Finset.sum_congr rfl
      intro H _
      exact (card_offDiag _).symm
    _ = ∑ H : B, (intersection (fun z H => R z.1 H ∧ R z.2 H) S.offDiag H).card := by
      simp_rw [intersection_offDiag]
      apply Finset.sum_congr rfl
      intro H _
      congr 1
      ext z
      simp only [intersection, Finset.mem_filter]
    _ = _ := sum_intersection_card _ _

theorem first_moment (R : A → B → Prop) (S : Finset A) (c : ℕ)
    (hcount : ∀ x ∈ S, (through R x).card = c) :
    (∑ H : B, (intersection R S H).card) = S.card * c := by
  rw [sum_intersection_card]
  exact Finset.sum_const_nat hcount

theorem second_moment (R : A → B → Prop) (S : Finset A) (c : ℕ)
    (hcount : ∀ z ∈ S.offDiag,
      (through (fun z H => R z.1 H ∧ R z.2 H) z).card = c) :
    (∑ H : B, (intersection R S H).card * ((intersection R S H).card - 1)) =
      S.card * (S.card - 1) * c := by
  rw [sum_intersection_pairs, ← card_offDiag S]
  exact Finset.sum_const_nat hcount

end Cylinder.IncidenceDoubleCount

end
