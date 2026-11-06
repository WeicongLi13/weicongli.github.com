import NSDensity

/-!
Standalone submission audit for the manuscript dated 31 October 2026.

The two theorems below make Corollary 3.7 explicit: the exact set of
derived lengths is `NormalLengths n (p ^ e)`, and every such length is
realized at both the original alphabet exponent and exponent one.
Only the existing arithmetic normal form is used; neither external
classification nor analytic input is required for this corollary.
The arithmetic statement does not need the manuscript's extra coprimality
hypothesis on the initial pair. The original proof sources are unchanged.
-/

namespace NSDensity

/-- Every exact normal-form length is realized over the original alphabet
and over the prime alphabet. This is the last claim of Corollary 3.7. -/
theorem submission_normalLengths_realized {p n e N : ℕ}
    (hp : p.Prime) (hn : 0 < n) (he : 0 < e)
    (hN : N ∈ NormalLengths n (p ^ e)) :
    Derived p (n, e) (N, e) ∧ Derived p (n, e) (N, 1) := by
  obtain ⟨u, ⟨t, ht, hcop, hdiv⟩, hlength⟩ := hN
  have hpow : 1 < (p ^ e) ^ t := by
    have h := Nat.pow_lt_pow_right hp.one_lt (Nat.mul_pos he ht)
    simpa only [pow_zero, pow_mul] using h
  have hu : 0 < u := Nat.pos_of_dvd_of_pos
    (dvd_trans hdiv (Nat.div_dvd_of_dvd (Nat.gcd_dvd_right n ((p ^ e) ^ t - 1))))
    (Nat.sub_pos_of_lt hpow)
  have hcop' : Nat.Coprime t (orderOf (p ^ e : ZMod n)) := by
    simpa only [Nat.cast_pow] using hcop
  have hdiv' : u ∣ (p ^ (e * t) - 1) / Nat.gcd n (p ^ (e * t) - 1) := by
    simpa only [pow_mul] using hdiv
  have hform : ∀ f : ℕ, f ∣ e * t → NormalForm p (n, e) (N, f) := by
    intro f hf
    exact ⟨t, u, ht, hu, hlength, hcop', hdiv', hf⟩
  exact ⟨(derived_iff_normalForm hp.one_lt.le hn he).2
      (hform e (Nat.dvd_mul_right e t)),
    (derived_iff_normalForm hp.one_lt.le hn he).2 (hform 1 (one_dvd _))⟩

/-- The exact derived-length equivalence in Corollary 3.7. The final
alphabet exponent is positive and otherwise unrestricted. -/
theorem submission_derived_length_iff {p n e N : ℕ}
    (hp : p.Prime) (hn : 0 < n) (he : 0 < e) :
    (∃ f : ℕ, 0 < f ∧ Derived p (n, e) (N, f)) ↔
      N ∈ NormalLengths n (p ^ e) := by
  constructor
  · rintro ⟨f, _, hderived⟩
    exact ((derived_iff_normalForm hp.one_lt.le hn he).1 hderived).mem_normalLengths
  · intro hN
    exact ⟨e, he, (submission_normalLengths_realized hp hn he hN).1⟩

#check @submission_derived_length_iff
#check @submission_normalLengths_realized
#check @abstract_density_main
#check @abstractRatio_sup_eq
#check @abstractRatio_sup_tendsto_zero

#print axioms submission_derived_length_iff
#print axioms submission_normalLengths_realized
#print axioms abstract_density_main
#print axioms abstractRatio_sup_eq
#print axioms abstractRatio_sup_tendsto_zero

end NSDensity
