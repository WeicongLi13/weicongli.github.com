import NSDensity.Classification
import NSDensity.FixedPair

namespace NSDensity

/-- Reading the lift-extension part of the normal form gives a permitted
multiplier, independently of the final alphabet exponent. -/
theorem NormalForm.mem_normalLengths {p a e n f : ℕ}
    (h : NormalForm p (a, e) (n, f)) : n ∈ NormalLengths a (p ^ e) := by
  obtain ⟨t, u, ht, hu, hnu, hcop, hdiv, hfe⟩ := h
  refine ⟨u, ⟨t, ht, ?_, ?_⟩, hnu⟩
  · simpa only [Nat.cast_pow] using hcop
  · simpa only [pow_mul] using hdiv

end NSDensity
