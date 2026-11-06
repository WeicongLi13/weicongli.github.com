import NSDensity.Reduction
import NSDensity.FourFamilies

namespace NSDensity

def OtherLengths (p : ℕ) : Set ℕ :=
  DualRepetitionLengths p ∪ (PrimitiveLengths p ∪ (OvoidLengths p ∪ GolayLengths))

theorem densityZero_otherLengths (hWM : WiertelakMoreeInput)
    {p : ℕ} (hp : 1 < p) : DensityZero (OtherLengths p) :=
  (densityZero_dualRepetitionLengths hWM hp).union
    ((densityZero_primitiveLengths hWM hp).union
      ((densityZero_ovoidLengths hWM hp).union (densityZero_golayLengths hWM)))

/-- Equally-spaced initial pairs remain equally spaced at the prime alphabet.
The final alphabet exponent may be arbitrary. -/
theorem EquallySpaced.of_normalForm {p a e n f : ℕ} (hp : 1 < p) (he : 0 < e)
    (hcopFinal : Nat.Coprime p n) (hES : EquallySpaced (p ^ e) a)
    (hNF : NormalForm p (a, e) (n, f)) : EquallySpaced p n := by
  obtain ⟨t, u, ht, hu, hnu, hcop, hdiv, hfe⟩ := hNF
  dsimp only at hnu hcop hdiv hfe
  have hEt : 0 < e * t := Nat.mul_pos he ht
  have hbase : 1 < p ^ (e * t) := by
    simpa only [pow_zero] using Nat.pow_lt_pow_right hp hEt
  have hLift : EquallySpaced (p ^ (e * t)) a := by
    simpa only [pow_mul] using
      hES.lift (by simpa only [Nat.cast_pow] using hcop)
  have hExt : EquallySpaced (p ^ (e * t)) n := by
    rw [hnu]
    exact hLift.extension hbase hdiv
  exact EquallySpaced.descent hEt hcopFinal hExt

theorem initial_normalForm_covered {p a e n f : ℕ} (hp : 1 < p)
    (hcopFinal : Nat.Coprime p n) (hInitial : Initial p a e)
    (hNF : NormalForm p (a, e) (n, f)) :
    n ∈ OtherLengths p ∨ EquallySpaced p n := by
  obtain ⟨ha, he, hcop, hFamily⟩ := hInitial
  have hmem := hNF.mem_normalLengths
  cases hFamily with
  | dual heq hprime ha5 hord =>
    left
    left
    refine ⟨a, hprime, ha5, hord, ?_⟩
    simpa only [heq, pow_one] using hmem
  | primitive m hm hae =>
    left
    right
    left
    apply Set.mem_iUnion.mpr
    refine ⟨(e - 1, m - 2), ?_⟩
    change n ∈ NormalLengths (p ^ ((e - 1 + 1) * (m - 2 + 2)) - 1)
      (p ^ (e - 1 + 1))
    rw [Nat.sub_add_cancel (by omega : 1 ≤ e), Nat.sub_add_cancel hm, ← hae]
    exact hmem
  | ovoid hae =>
    left
    right
    right
    left
    apply Set.mem_iUnion.mpr
    refine ⟨e - 1, ?_⟩
    change n ∈ NormalLengths ((p ^ (e - 1 + 1) - 1) *
      (p ^ (2 * (e - 1 + 1)) + 1)) (p ^ (e - 1 + 1))
    rw [Nat.sub_add_cancel (by omega : 1 ≤ e), ← hae]
    exact hmem
  | golay_binary hpe hae heq =>
    left
    right
    right
    right
    left
    simpa only [hpe, hae, heq, pow_one] using hmem
  | golay_ternary hpe hae heq =>
    left
    right
    right
    right
    right
    simpa only [hpe, hae, heq, pow_one] using hmem
  | equally_spaced hES =>
    exact Or.inr (hES.of_normalForm hp he hcopFinal hNF)

/-- FHLX's entire four-construction closure is bounded by the five counted sets. -/
theorem exceptionalLengths_subset {NS : ℕ → ℕ → Prop} (hFHLX : FHLXInput NS)
    {p : ℕ} (hp : p.Prime) :
    ExceptionalLengths NS p ⊆ OtherLengths p ∪ {n | EquallySpaced p n} := by
  rintro n ⟨hn, hcop, f, hf, hNS⟩
  obtain ⟨a, e, hInitial, hPath⟩ := hFHLX p hp n f hn hcop hf hNS
  have hNF := classification_normalForm hp.one_lt.le hInitial.1 hPath
  exact initial_normalForm_covered hp.one_lt hcop hInitial hNF

end NSDensity
