module

public import Cylinder.RedeiDivisibility
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! The standalone first-moment lemma for every normalized spanning
p-point set. No tiling or bijective projection is assumed. -/

@[expose] public section
noncomputable section
open scoped Classical BigOperators

namespace Cylinder.FinalFirstMoment

open MvPolynomial Cylinder.Geometry Cylinder.Redei Module

variable (p : ℕ) [Fact p.Prime]

theorem plane_counts_constant_of_low_moments (A : Finset (Point p))
    (hcard : A.card = p) (hzero : ∀ j < p - 1, moment p A j = 0)
    (u : Point p) (t : ZMod p) :
    ((A.filter fun x => pairing p u x = t).card : ZMod p) =
      -eval u (moment p A (p - 1)) := by
  have hp := (Fact.out : p.Prime).two_le
  rw [plane_count_eq_moments, hcard, ZMod.natCast_self, zero_sub]
  congr 1
  rw [Finset.sum_eq_single (p - 1)]
  · simp
  · intro j hj hne
    have hjlt : j < p - 1 := by
      have := Finset.mem_range.mp hj
      omega
    rw [hzero j hjlt, map_zero, zero_mul, zero_mul]
  · intro h
    exact False.elim (h (Finset.mem_range.mpr (by omega)))

theorem pairing_coordinates (l : Point p →ₗ[ZMod p] ZMod p) (x : Point p) :
    pairing p (fun i => l (Pi.single i 1)) x = l x := by
  have hx : (∑ i : Fin 3, x i • (Pi.single i (1 : ZMod p) : Point p)) = x := by
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  conv_rhs => rw [← hx, map_sum]
  simp [pairing, mul_comm]

/- Lemma 7.2: a positive formal moment of degree at most p−2 is nonzero. -/
set_option maxHeartbeats 500000 in
theorem exists_nonzero_moment (A : Finset (Point p)) (hcard : A.card = p)
    (h0 : 0 ∈ A) (hspan : Submodule.span (ZMod p) (A : Set (Point p)) = ⊤) :
    ∃ r, 1 ≤ r ∧ r ≤ p - 2 ∧ moment p A r ≠ 0 := by
  have hp := (Fact.out : p.Prime).two_le
  by_contra! hnone
  have hz : ∀ j < p - 1, moment p A j = 0 := by
    intro j hj
    by_cases hj0 : j = 0
    · subst j
      simp [moment, hcard]
    · exact hnone j (by omega) (by omega)
  have hne : (A.erase 0).Nonempty := Finset.card_pos.mp (by
    rw [Finset.card_erase_of_mem h0, hcard]
    omega)
  obtain ⟨b, hb⟩ := hne
  obtain ⟨hb0, hbA⟩ := Finset.mem_erase.mp hb
  let W : Submodule (ZMod p) (Point p) := Submodule.span (ZMod p) {b}
  have hdim : finrank (ZMod p) W ≤ 1 := by
    simpa [W] using (finrank_span_le_card (R := ZMod p) ({b} : Set (Point p)))
  have hproper : W < ⊤ := lt_top_iff_ne_top.mpr (by
    intro heq
    rw [heq, finrank_top, Module.finrank_fin_fun] at hdim
    omega)
  obtain ⟨l, hl, hW⟩ := W.exists_dual_map_eq_bot_of_lt_top hproper inferInstance
  have hlb : l b = 0 := by
    have hmem : l b ∈ W.map l := Submodule.mem_map.mpr
      ⟨b, Submodule.subset_span (by simp), rfl⟩
    simpa only [hW, Submodule.mem_bot] using hmem
  have hnonzero : ∃ c ∈ A, l c ≠ 0 := by
    by_contra! hn
    have hle : Submodule.span (ZMod p) (A : Set (Point p)) ≤ LinearMap.ker l :=
      Submodule.span_le.mpr hn
    rw [hspan] at hle
    exact hl (LinearMap.ker_eq_top.mp (top_unique hle))
  obtain ⟨c, hcA, hlc⟩ := hnonzero
  have hinj : ¬ Function.Injective (fun a : A => l a) := by
    intro h
    have hab : (⟨b, hbA⟩ : A) = ⟨0, h0⟩ := h (by simpa using hlb)
    exact hb0 (congrArg Subtype.val hab)
  have hsurj : ¬ Function.Surjective (fun a : A => l a) := by
    intro h
    exact hinj ((Fintype.bijective_iff_surjective_and_card _).mpr
      ⟨h, by simpa using hcard⟩).1
  simp only [Function.Surjective] at hsurj
  push Not at hsurj
  obtain ⟨t, ht⟩ := hsurj
  let u : Point p := fun i => l (Pi.single i 1)
  have hpair (x : Point p) : pairing p u x = l x := pairing_coordinates p l x
  have hempty : (A.filter fun x => pairing p u x = t) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro x hx
    obtain ⟨hxA, hxt⟩ := Finset.mem_filter.mp hx
    exact ht ⟨x, hxA⟩ (by simpa only [hpair] using hxt)
  have hcast : ((A.filter fun x => pairing p u x = 0).card : ZMod p) = 0 := by
    calc
      _ = -eval u (moment p A (p - 1)) := plane_counts_constant_of_low_moments p A hcard hz u 0
      _ = ((A.filter fun x => pairing p u x = t).card : ZMod p) :=
        (plane_counts_constant_of_low_moments p A hcard hz u t).symm
      _ = 0 := by rw [hempty]; simp
  have hpos : 0 < (A.filter fun x => pairing p u x = 0).card :=
    Finset.card_pos.mpr ⟨0, Finset.mem_filter.mpr ⟨h0, pairing_zero p u⟩⟩
  have hlt : (A.filter fun x => pairing p u x = 0).card < p := by
    calc
      _ < A.card := Finset.card_lt_card
        (Finset.filter_ssubset.mpr ⟨c, hcA, by simpa only [hpair] using hlc⟩)
      _ = p := hcard
  have hdvd := (ZMod.natCast_eq_zero_iff _ p).mp hcast
  exact (Nat.not_le_of_gt hlt) (Nat.le_of_dvd hpos hdvd)

#print axioms exists_nonzero_moment

end Cylinder.FinalFirstMoment
end
