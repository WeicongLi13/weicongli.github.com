module

public import Cylinder.Geometry
public import Mathlib.Tactic.Ring

/-!
# Necessary conditions for a cylinder

These results establish the elementary direction of the conjecture: an exact
union of `p` disjoint parallel lines has `p²` points and is `p`-divisible.
They do not establish the difficult converse asserted in the article.
-/

@[expose] public section

namespace Cylinder.Geometry

variable (p : ℕ) [Fact p.Prime]

theorem affineLine_filter_parallel (base direction a : Point p) (b : ZMod p)
    (hparallel : pairing p a direction = 0) :
    (affineLine p base direction).filter (fun x => pairing p a x = b) =
      if pairing p a base = b then affineLine p base direction else ∅ := by
  by_cases hb : pairing p a base = b
  · rw [ite_eq_left hb]
    ext x
    constructor
    · intro hx
      exact (Finset.mem_filter.mp hx).1
    · intro hx
      refine Finset.mem_filter.mpr ⟨hx, ?_⟩
      obtain ⟨t, rfl⟩ := (mem_affineLine p base direction x).mp hx
      simpa [pairing_on_line, hparallel] using hb
  · rw [ite_eq_right hb]
    ext x
    constructor
    · intro hx
      obtain ⟨hline, hplane⟩ := Finset.mem_filter.mp hx
      obtain ⟨t, rfl⟩ := (mem_affineLine p base direction x).mp hline
      have : pairing p a base = b := by
        simpa [pairing_on_line, hparallel] using hplane
      exact False.elim (hb this)
    · simp

theorem affineLine_filter_transverse (base direction a : Point p) (b : ZMod p)
    (htransverse : pairing p a direction ≠ 0) :
    (affineLine p base direction).filter (fun x => pairing p a x = b) =
      {base + ((b - pairing p a base) / pairing p a direction) • direction} := by
  let t₀ := (b - pairing p a base) / pairing p a direction
  have ht₀ : pairing p a base + t₀ * pairing p a direction = b := by
    dsimp [t₀]
    rw [div_mul_cancel₀ _ htransverse]
    ring
  ext x
  constructor
  · intro hx
    obtain ⟨hline, hplane⟩ := Finset.mem_filter.mp hx
    obtain ⟨t, htx⟩ := (mem_affineLine p base direction x).mp hline
    rw [← htx, pairing_on_line] at hplane
    have ht : t = t₀ := by
      apply mul_right_cancel₀ htransverse
      exact add_left_cancel (hplane.trans ht₀.symm)
    apply Finset.mem_singleton.mpr
    exact htx.symm.trans (congrArg (fun u => base + u • direction) ht)
  · intro hx
    have hx' := Finset.mem_singleton.mp hx
    subst x
    refine Finset.mem_filter.mpr ⟨?_, ?_⟩
    · exact (mem_affineLine p _ _ _).mpr ⟨t₀, rfl⟩
    · rw [pairing_on_line]
      exact ht₀

theorem cylinder_card {S : Finset (Point p)} (hS : IsCylinder p S) :
    S.card = p ^ 2 := by
  obtain ⟨direction, hd, base, hdisjoint, hUnion⟩ := hS
  rw [hUnion, Finset.card_biUnion]
  · simp [affineLine_card p _ hd, pow_two]
  · intro i _ j _ hij
    exact hdisjoint hij

theorem cylinder_pDivisible {S : Finset (Point p)} (hS : IsCylinder p S) :
    PDivisible p S := by
  obtain ⟨direction, hd, base, hdisjoint, hUnion⟩ := hS
  intro a _ b
  have hfilter :
      S.filter (fun x => pairing p a x = b) =
        Finset.univ.biUnion (fun i =>
          (affineLine p (base i) direction).filter (fun x => pairing p a x = b)) := by
    rw [hUnion]
    ext x
    simp only [Finset.mem_filter, Finset.mem_biUnion, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨⟨i, hi⟩, hb⟩
      exact ⟨i, hi, hb⟩
    · rintro ⟨i, hi, hb⟩
      exact ⟨⟨i, hi⟩, hb⟩
  rw [hfilter, Finset.card_biUnion]
  · by_cases hparallel : pairing p a direction = 0
    · apply Finset.dvd_sum
      intro i _
      rw [affineLine_filter_parallel p (base i) direction a b hparallel]
      split_ifs <;> simp [affineLine_card p (base i) hd]
    · simp_rw [affineLine_filter_transverse p _ direction a b hparallel,
        Finset.card_singleton]
      simp
  · intro i _ j _ hij
    exact (hdisjoint hij).mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)

end Cylinder.Geometry
