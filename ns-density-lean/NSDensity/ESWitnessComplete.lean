import NSDensity.ESArithmetic

namespace NSDensity

/-- A prime order witness also gives the factorization in the definition of
equally-spaced pairs. The square-divisibility theorem ensures that the
remaining factor is at least two. -/
theorem ESWitness.equallySpaced {q n l : ℕ} (hq : 1 ≤ q)
    (h : ESWitness q n l) : EquallySpaced q n := by
  have hsquare := h.square_dvd hq
  obtain ⟨hn, hcop, hl, hln, hord⟩ := h
  have hlquot : l ≤ n / l :=
    (Nat.le_div_iff_mul_le hl.pos).2
      (by simpa [pow_two] using Nat.le_of_dvd hn hsquare)
  exact ⟨hn, hcop, n / l, l, hl.two_le.trans hlquot, hl.two_le,
    (Nat.div_mul_cancel hln).symm, hord⟩

/-- The prime-witness criterion for an equally-spaced pair. -/
theorem equallySpaced_iff_exists_witness {q n : ℕ} (hq : 1 ≤ q) :
    EquallySpaced q n ↔ ∃ l, ESWitness q n l := by
  constructor
  · exact EquallySpaced.exists_witness
  · rintro ⟨l, h⟩
    exact h.equallySpaced hq

#print axioms ESWitness.equallySpaced
#print axioms equallySpaced_iff_exists_witness

end NSDensity
