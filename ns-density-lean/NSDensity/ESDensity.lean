import NSDensity.ESFixed
import NSDensity.SquareTails

namespace NSDensity

/-- A witness length belongs to a fixed prime-power valuation slice, with
valuation at least two. -/
theorem ESWitness.exists_fixed_decomposition {q n l : ℕ} (hq : 1 < q)
    (h : ESWitness q n l) :
    ∃ a : ℕ, 2 ≤ a ∧ ∃ v : ℕ, ¬l ∣ v ∧ n = l ^ a * v := by
  have hn : n ≠ 0 := h.1.ne'
  have hl : l.Prime := h.2.2.1
  have hsquare : l ^ 2 ∣ n := ESWitness.square_dvd hq.le h
  have ha : 2 ≤ n.factorization l := (hl.pow_dvd_iff_le_factorization hn).mp hsquare
  refine ⟨n.factorization l, ha, n / l ^ n.factorization l, ?_, ?_⟩
  · exact Nat.not_dvd_ordCompl hl hn
  · exact (Nat.mul_div_cancel' (Nat.ordProj_dvd n l)).symm

private def ESGrid (q : ℕ) (p : ℕ × ℕ) : Set ℕ :=
  if (p.1 + 2).Prime then ESFixed q (p.1 + 2) (p.2 + 2) else ∅

private theorem densityZero_ESGrid (hWM : WiertelakMoreeInput) {q : ℕ}
    (hq : 1 < q) (p : ℕ × ℕ) : DensityZero (ESGrid q p) := by
  unfold ESGrid
  split_ifs with hp
  · exact densityZero_ESFixed hWM hq hp (by omega)
  · exact densityZero_empty

private theorem ESGrid_subset_multiples (q : ℕ) (p : ℕ × ℕ) :
    ESGrid q p ⊆ {n | (p.1 + 2) ^ (p.2 + 2) ∣ n} := by
  unfold ESGrid
  split_ifs
  · intro n hn
    obtain ⟨_, v, _, hnrel⟩ := hn
    exact ⟨v, hnrel⟩
  · exact Set.empty_subset _

/-- The complete equally-spaced density argument, including all prime witnesses
and all their exact valuations. The entire two-parameter tail is controlled by
the proved power-grid reciprocal estimate. -/
theorem densityZero_equallySpaced (hWM : WiertelakMoreeInput) {q : ℕ}
    (hq : 1 < q) : DensityZero {n | EquallySpaced q n} := by
  have hgrid : DensityZero (⋃ p : ℕ × ℕ, ESGrid q p) :=
    densityZero_iUnion_of_reciprocalTails (ESGrid q)
      (fun p => (p.1 + 2) ^ (p.2 + 2)) (fun p => by positivity)
      (ESGrid_subset_multiples q) (densityZero_ESGrid hWM hq)
      reciprocalTails_powerGrid
  apply hgrid.mono
  intro n hn
  obtain ⟨l, hW⟩ := hn.exists_witness
  have hl : l.Prime := hW.2.2.1
  obtain ⟨a, ha, v, hv, hnrel⟩ := hW.exists_fixed_decomposition hq
  have hl2 : l - 2 + 2 = l := Nat.sub_add_cancel hl.two_le
  have ha2 : a - 2 + 2 = a := Nat.sub_add_cancel ha
  apply Set.mem_iUnion.mpr
  refine ⟨(l - 2, a - 2), ?_⟩
  simpa only [ESGrid, hl2, ha2, ite_eq_left hl] using
    (show n ∈ ESFixed q l a from ⟨hW, v, hv, hnrel⟩)

end NSDensity
