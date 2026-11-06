module

public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.PowerSeries.Order

/-!
# The completeness of actual power series for the `X`-adic filtration

The limit of a Cauchy sequence is constructed coefficient by coefficient.
No completeness or Henselian assumption on the power series ring is used.
-/

@[expose] public section

noncomputable section

namespace Cylinder.PowerSeriesAdicComplete

open PowerSeries
open scoped Classical

variable (R : Type*) [CommRing R]

def xIdeal : Ideal R⟦X⟧ := Ideal.span {X}

theorem mem_xIdeal_pow_iff (f : R⟦X⟧) (n : ℕ) :
    f ∈ xIdeal R ^ n ↔ ∀ j < n, coeff j f = 0 := by
  rw [xIdeal, Ideal.span_singleton_pow, Ideal.mem_span_singleton, X_pow_dvd_iff]

theorem smodEq_xIdeal_pow_iff (f g : R⟦X⟧) (n : ℕ) :
    f ≡ g [SMOD (xIdeal R ^ n • ⊤ : Ideal R⟦X⟧)] ↔
      ∀ j < n, coeff j f = coeff j g := by
  rw [← Ideal.one_eq_top, Ideal.smul_eq_mul, mul_one, SModEq.sub_mem,
    mem_xIdeal_pow_iff]
  simp only [map_sub, sub_eq_zero]

instance isAdicComplete : IsAdicComplete (xIdeal R) R⟦X⟧ where
  haus' f hf := by
    ext j
    have h := (smodEq_xIdeal_pow_iff R f 0 (j + 1)).mp (hf (j + 1)) j (by omega)
    simpa using h
  prec' f hf := by
    let L : R⟦X⟧ := PowerSeries.mk fun j => coeff j (f (j + 1))
    refine ⟨L, fun n => (smodEq_xIdeal_pow_iff R (f n) L n).mpr ?_⟩
    intro j hj
    have h := (smodEq_xIdeal_pow_iff R (f (j + 1)) (f n) (j + 1)).mp
      (hf (show j + 1 ≤ n by omega)) j (by omega)
    simpa only [L, coeff_mk] using h.symm

theorem mem_xIdeal_iff_constantCoeff_eq_zero (f : R⟦X⟧) :
    f ∈ xIdeal R ↔ f.constantCoeff = 0 := by
  rw [xIdeal, Ideal.mem_span_singleton, X_dvd_iff]

end Cylinder.PowerSeriesAdicComplete

end
