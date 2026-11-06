import Cylinder.Geometry
import Mathlib.GroupTheory.Complement
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.FieldTheory.Finiteness
import Mathlib.Tactic.IntervalCases

/-! Cardinality and spanning reductions for normalized factorizations of the
additive group of three-dimensional prime vector space. -/
namespace Cylinder.Redei

open Geometry

variable {p : ℕ} [Fact p.Prime]

/-- Interchanging the factors preserves unique additive representations. -/
theorem swapFactors {G : Type*} [AddCommGroup G] {A B : Set G}
    (h : AddSubgroup.IsComplement A B) : AddSubgroup.IsComplement B A := by
  change Function.Bijective (fun x : B × A => (x.1 : G) + x.2)
  have hs := h.comp (Equiv.prodComm B A).bijective
  simpa only [Function.comp_def, Equiv.prodComm_apply, Prod.fst_swap, Prod.snd_swap, add_comm]
    using hs

theorem factorSizes {A B : Finset (Point p)}
    (h : AddSubgroup.IsComplement (A : Set (Point p)) B) :
    A.card = 1 ∨ B.card = 1 ∨
      (A.card = p ∧ B.card = p ^ 2) ∨ (A.card = p ^ 2 ∧ B.card = p) := by
  have hp : p.Prime := Fact.out
  have hp0 : 0 < p := hp.pos
  have hmul : A.card * B.card = p ^ 3 := by
    simpa [Nat.card_eq_fintype_card, Geometry.Point] using h.card_mul_card
  obtain ⟨k, hk, hA⟩ := (Nat.dvd_prime_pow hp).mp (Dvd.intro B.card hmul)
  interval_cases k
  · exact Or.inl (by simpa using hA)
  · right; right; left
    have hA' : A.card = p := by simpa using hA
    refine ⟨hA', ?_⟩
    apply Nat.eq_of_mul_eq_mul_left hp.pos
    simpa [hA', pow_succ, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hmul
  · right; right; right
    refine ⟨hA, ?_⟩
    apply Nat.eq_of_mul_eq_mul_left (show 0 < p ^ 2 by positivity)
    simpa only [hA, pow_succ] using hmul
  · right; left
    apply Nat.eq_of_mul_eq_mul_left (show 0 < p ^ 3 by positivity)
    simpa only [hA, Nat.mul_one] using hmul

/-- A normalized set of at most three points in three-space cannot span. -/
theorem span_ne_top_of_card_le_three {A : Finset (Point p)}
    (h0 : 0 ∈ A) (hA : A.card ≤ 3) :
    Submodule.span (ZMod p) (A : Set (Point p)) ≠ ⊤ := by
  classical
  intro ht
  have hspan : Submodule.span (ZMod p) (↑(A.erase 0) : Set (Point p)) = ⊤ := by
    calc
      _ = Submodule.span (ZMod p) (↑(insert 0 (A.erase 0)) : Set (Point p)) := by
        rw [Finset.coe_insert, Submodule.span_insert_zero]
      _ = ⊤ := by simpa [Finset.insert_erase h0] using ht
  have hr := finrank_span_finset_le_card (R := ZMod p) (A.erase 0)
  change Module.finrank (ZMod p) (Submodule.span (ZMod p) (↑(A.erase 0) : Set (Point p))) ≤ _ at hr
  rw [hspan, finrank_top] at hr
  simp [Geometry.Point] at hr
  have hn := Finset.card_erase_of_mem h0
  omega

/-- It suffices to treat a spanning factor of size p, in either order. -/
theorem of_spanning_prime_factor
    (hprime : ∀ (A B : Finset (Point p)),
      0 ∈ A → 0 ∈ B → AddSubgroup.IsComplement (A : Set (Point p)) B →
      A.card = p → B.card = p ^ 2 → Submodule.span (ZMod p) (A : Set (Point p)) = ⊤ →
      Submodule.span (ZMod p) (B : Set (Point p)) ≠ ⊤)
    (A B : Finset (Point p)) (hA : 0 ∈ A) (hB : 0 ∈ B)
    (h : AddSubgroup.IsComplement (A : Set (Point p)) B) :
    Submodule.span (ZMod p) (A : Set (Point p)) ≠ ⊤ ∨
    Submodule.span (ZMod p) (B : Set (Point p)) ≠ ⊤ := by
  classical
  rcases factorSizes h with h1 | h1 | ⟨ha, hb⟩ | ⟨ha, hb⟩
  · exact Or.inl (span_ne_top_of_card_le_three hA (by omega))
  · exact Or.inr (span_ne_top_of_card_le_three hB (by omega))
  · by_cases htop : Submodule.span (ZMod p) (A : Set (Point p)) = ⊤
    · exact Or.inr (hprime A B hA hB h ha hb htop)
    · exact Or.inl htop
  · by_cases htop : Submodule.span (ZMod p) (B : Set (Point p)) = ⊤
    · exact Or.inl (hprime B A hB hA (swapFactors h) hb ha htop)
    · exact Or.inr htop

/-- The normalized factorization theorem for p=2 and p=3. -/
theorem small_prime_factorization (hp : p ≤ 3) (A B : Finset (Point p))
    (hA : 0 ∈ A) (hB : 0 ∈ B)
    (h : AddSubgroup.IsComplement (A : Set (Point p)) B) :
    Submodule.span (ZMod p) (A : Set (Point p)) ≠ ⊤ ∨
    Submodule.span (ZMod p) (B : Set (Point p)) ≠ ⊤ := by
  apply of_spanning_prime_factor _ A B hA hB h
  intro A B ha _ _ hcard _ hspan
  exact False.elim (span_ne_top_of_card_le_three ha (hcard.le.trans hp) hspan)

end Cylinder.Redei
