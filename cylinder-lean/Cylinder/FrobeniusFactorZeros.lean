module

public import Cylinder.FrobeniusPolynomialPeriod
public import Cylinder.PlaneCurveFactors

/-!
# Rational zeros lie on every nonunit geometric divisor of an irreducible prime-field equation

The actual finite Frobenius orbit product descends to the prime field and
divides a power of the original equation. Irreducibility forces the original
equation to divide this nonunit norm. Evaluation at a rational zero then
forces the chosen factor itself to vanish, by injectivity of Frobenius.
-/

@[expose] public section
noncomputable section

namespace Cylinder.FrobeniusFactorZeros

open MvPolynomial Cylinder.EquationScalarDescent Cylinder.PolynomialDivisibilityDescent
open Cylinder.FrobeniusPolynomialPeriod
open scoped Classical BigOperators

variable (p : ℕ) [Fact p.Prime]
variable {L : Type*} [Field L] [Algebra (ZMod p) L] [CharP L p]

theorem exists_base_of_twist_fixed {σ : Type*} (N : MvPolynomial σ L) (hN : twist p 1 N = N) :
    ∃ Q : MvPolynomial σ (ZMod p), MvPolynomial.map (algebraMap (ZMod p) L) Q = N := by
  obtain ⟨l, hl⟩ := Module.Projective.exists_dual_eq_one (ZMod p) (one_ne_zero : (1 : L) ≠ 0)
  refine ⟨coefficientProjection l N, ?_⟩
  ext m
  have hm := congrArg (fun F : MvPolynomial σ L => F.coeff m) hN
  simp only [twist, coeff_map, iterateFrobenius_def, pow_one] at hm
  obtain ⟨a, ha⟩ := fixed_scalar_in_base p (N.coeff m) hm
  rw [coeff_map, coefficientProjection_coeff, ← ha, projection_algebraMap l hl]

theorem eval_twist_at_base {σ : Type*} (n : ℕ) (H : MvPolynomial σ L) (v : σ → ZMod p) :
    eval (fun j => algebraMap (ZMod p) L (v j)) (twist p n H) =
      iterateFrobenius L p n (eval (fun j => algebraMap (ZMod p) L (v j)) H) := by
  have h := MvPolynomial.map_eval (iterateFrobenius L p n)
    (fun j => algebraMap (ZMod p) L (v j)) H
  have hv : iterateFrobenius L p n ∘ (fun j => algebraMap (ZMod p) L (v j)) =
      fun j => algebraMap (ZMod p) L (v j) := by
    funext j
    simp only [Function.comp_def, iterateFrobenius_def, ← map_pow, ZMod.pow_card_pow]
  rw [hv] at h
  exact h.symm

theorem orbitProduct_dvd_power {σ : Type*} (G : MvPolynomial σ (ZMod p)) (H : MvPolynomial σ L)
    (hH : H ∣ MvPolynomial.map (algebraMap (ZMod p) L) G) (n : ℕ) :
    orbitProduct p n H ∣ MvPolynomial.map (algebraMap (ZMod p) L) (G ^ n) := by
  have hi (i : ℕ) : twist p i H ∣ MvPolynomial.map (algebraMap (ZMod p) L) G := by
    have h := map_dvd (MvPolynomial.map (iterateFrobenius L p i)) hH
    change twist p i H ∣ twist p i (MvPolynomial.map (algebraMap (ZMod p) L) G) at h
    rwa [twist_mapped_base] at h
  have hprod := Finset.prod_dvd_prod_of_dvd (s := Finset.range n)
    (fun i => twist p i H) (fun _ => MvPolynomial.map (algebraMap (ZMod p) L) G) (fun i _ => hi i)
  simpa only [orbitProduct, Finset.prod_const, Finset.card_range, map_pow] using hprod

theorem eval_divisor_zero_of_base_irreducible [Algebra.IsAlgebraic (ZMod p) L]
    (G : MvPolynomial (Fin 3) (ZMod p)) (hG : Irreducible G) (H : MvPolynomial (Fin 3) L)
    (hHunit : ¬ IsUnit H) (hdiv : H ∣ MvPolynomial.map (algebraMap (ZMod p) L) G)
    (v : Fin 3 → ZMod p) (hv : eval v G = 0) :
    eval (fun j => algebraMap (ZMod p) L (v j)) H = 0 := by
  have hmapG : MvPolynomial.map (algebraMap (ZMod p) L) G ≠ 0 := by
    intro hz
    exact hG.ne_zero (MvPolynomial.map_injective (algebraMap (ZMod p) L)
      (algebraMap (ZMod p) L).injective (by simpa only [map_zero] using hz))
  have hH0 : H ≠ 0 := ne_zero_of_dvd_ne_zero hmapG hdiv
  obtain ⟨n, hn, hperiod⟩ := exists_twist_period p H
  obtain ⟨Q, hQ⟩ := exists_base_of_twist_fixed p (orbitProduct p n H)
    (orbitProduct_fixed p n H hH0 hperiod)
  have hHnorm : H ∣ orbitProduct p n H := by
    have h := Finset.dvd_prod_of_mem (fun i => twist p i H) (Finset.mem_range.mpr hn)
    simpa only [twist_zero, orbitProduct] using h
  have hQunit : ¬ IsUnit Q := by
    intro hu
    have huN := hu.map (MvPolynomial.map (algebraMap (ZMod p) L))
    rw [hQ] at huN
    exact hHunit (isUnit_iff_dvd_one.mpr (hHnorm.trans huN.dvd))
  have hQdvd : Q ∣ G ^ n := by
    apply PolynomialDivisibilityDescent.dvd_of_mapped_dvd (L := L) Q (G ^ n)
    rw [hQ]
    exact orbitProduct_dvd_power p G H hdiv n
  have hGQ : G ∣ Q := by
    by_contra hnot
    have hc : IsRelPrime G Q := hG.isRelPrime_iff_not_dvd.mpr hnot
    have hcp : IsRelPrime Q (G ^ n) := hc.symm.pow_right
    exact hQunit (hcp dvd_rfl hQdvd)
  obtain ⟨R, hR⟩ := hGQ
  have hQzero : eval v Q = 0 := by rw [hR, map_mul, hv, zero_mul]
  have hnormzero : eval (fun j => algebraMap (ZMod p) L (v j)) (orbitProduct p n H) = 0 := by
    rw [← hQ]
    simpa only [map_eval, Function.comp_def, map_zero] using congrArg (algebraMap (ZMod p) L) hQzero
  rw [orbitProduct, map_prod] at hnormzero
  obtain ⟨i, _hi, hzero⟩ := Finset.prod_eq_zero_iff.mp hnormzero
  rw [eval_twist_at_base] at hzero
  exact (iterateFrobenius L p i).injective (by simpa only [map_zero] using hzero)

end Cylinder.FrobeniusFactorZeros

end
