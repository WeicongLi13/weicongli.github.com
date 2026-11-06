import NSDensity.Arithmetic
import Mathlib.Logic.Relation

/-! Arithmetic construction paths and their lift-extension-descent normal form. -/

namespace NSDensity

abbrev Pair := ℕ × ℕ

/-- The three elementary operations, with positive length and field exponents. -/
inductive Step (p : ℕ) : Pair → Pair → Prop
  | lift {n e t : ℕ} (hn : 0 < n) (he : 0 < e) (ht : 0 < t)
      (hcop : Nat.Coprime t (orderOf (p ^ e : ZMod n))) :
      Step p (n, e) (n, e * t)
  | extension {n e u : ℕ} (hn : 0 < n) (he : 0 < e) (hu : 0 < u)
      (hdiv : u ∣ (p ^ e - 1) / Nat.gcd n (p ^ e - 1)) :
      Step p (n, e) (n * u, e)
  | descent {n e r : ℕ} (hn : 0 < n) (he : 0 < e) (hr : 0 < r) :
      Step p (n, e * r) (n, e)

abbrev Derived (p : ℕ) : Pair → Pair → Prop := Relation.ReflTransGen (Step p)

/-- The tensor operation as stated in the classification. -/
inductive TensorStep (p : ℕ) : Pair → Pair → Prop
  | tensor {n e s : ℕ} (hn : 0 < n) (he : 0 < e) (hs : 0 < s)
      (ht : 1 < orderOf (p ^ e : ZMod s))
      (hcop : Nat.Coprime (orderOf (p ^ e : ZMod s)) (orderOf (p ^ e : ZMod n))) :
      TensorStep p (n, e) (Nat.lcm n s, e)

def ClassificationStep (p : ℕ) (x y : Pair) : Prop := Step p x y ∨ TensorStep p x y

/-- The arithmetic normal form with explicit positive lift and extension factors. -/
def NormalForm (p : ℕ) (x y : Pair) : Prop :=
  ∃ t u : ℕ, 0 < t ∧ 0 < u ∧ y.1 = x.1 * u ∧
    Nat.Coprime t (orderOf (p ^ x.2 : ZMod x.1)) ∧
    u ∣ (p ^ (x.2 * t) - 1) / Nat.gcd x.1 (p ^ (x.2 * t) - 1) ∧
    y.2 ∣ x.2 * t

/-- Divisibility of exponents gives divisibility of the corresponding powers minus one. -/
theorem pow_sub_one_dvd_of_exponent_dvd {p e f : ℕ} (hp : 1 ≤ p) (hef : e ∣ f) :
    p ^ e - 1 ∣ p ^ f - 1 := by
  obtain ⟨k, rfl⟩ := hef
  rw [pow_mul]
  exact sub_one_dvd_pow_sub_one (one_le_pow₀ hp)

/-- The initial degree divides the degree at every normal-form endpoint. -/
theorem normalForm_initial_order_dvd {p a e n f : ℕ}
    (h : NormalForm p (a, e) (n, f)) :
    orderOf (p ^ e : ZMod a) ∣ orderOf (p ^ f : ZMod n) := by
  obtain ⟨t, u, ht, hu, hn, hcop, hdiv, hfe⟩ := h
  dsimp only at hn hcop hdiv hfe
  have htop : orderOf (p ^ e : ZMod a) = orderOf (p ^ (e * t) : ZMod a) := by
    simpa only [Nat.cast_pow, pow_mul] using
      (order_lift (n := a) (q := p ^ e) (t := t)
        (by simpa only [Nat.cast_pow] using hcop)).symm
  calc
    orderOf (p ^ e : ZMod a) = orderOf (p ^ (e * t) : ZMod a) := htop
    _ ∣ orderOf (p ^ f : ZMod a) := by
      obtain ⟨k, hk⟩ := hfe
      rw [hk, pow_mul]
      exact orderOf_pow_dvd k
    _ ∣ orderOf (p ^ f : ZMod n) := by
      have had : a ∣ n := by rw [hn]; exact Nat.dvd_mul_right a u
      simpa only [Nat.cast_pow] using order_dvd_of_modulus_dvd (q := p ^ f) had

/-- The empty path has the normal form with both factors equal to one. -/
theorem normalForm_refl (p a e : ℕ) : NormalForm p (a, e) (a, e) := by
  refine ⟨1, 1, Nat.one_pos, Nat.one_pos, ?_, ?_, ?_, ?_⟩ <;> simp

/-- Each further elementary operation preserves the normal-form invariant. -/
theorem NormalForm.step {p a e : ℕ} {x y : Pair} (hp : 1 ≤ p) (ha : 0 < a)
    (h : NormalForm p (a, e) x) (hs : Step p x y) : NormalForm p (a, e) y := by
  cases hs with
  | @lift n f r hn hf hr hrcop =>
    have hord := normalForm_initial_order_dvd h
    obtain ⟨t, u, ht, hu, hna, hcop, hdiv, hfe⟩ := h
    dsimp only at hna hcop hdiv hfe
    have hrcop' : Nat.Coprime r (orderOf (p ^ e : ZMod a)) :=
      Nat.Coprime.of_dvd_right hord hrcop
    refine ⟨t * r, u, Nat.mul_pos ht hr, hu, hna, hcop.mul_left hrcop', ?_, ?_⟩
    · have hAA : p ^ (e * t) - 1 ∣ p ^ (e * (t * r)) - 1 := by
        simpa only [Nat.mul_assoc] using
          pow_sub_one_dvd_of_exponent_dvd hp (Nat.dvd_mul_right (e * t) r)
      exact dvd_trans hdiv (div_gcd_dvd_div_gcd ha hAA)
    · simpa only [Nat.mul_assoc] using Nat.mul_dvd_mul hfe (dvd_refl r)
  | @extension n f v hn hf hv hvdiv =>
    obtain ⟨t, u, ht, hu, hna, hcop, hdiv, hfe⟩ := h
    dsimp only at hna hcop hdiv hfe
    refine ⟨t, u * v, ht, Nat.mul_pos hu hv, ?_, hcop, ?_, hfe⟩
    · simp only [hna, Nat.mul_assoc]
    · have hAA : p ^ f - 1 ∣ p ^ (e * t) - 1 :=
        pow_sub_one_dvd_of_exponent_dvd hp hfe
      have hvtop : v ∣ (p ^ (e * t) - 1) / Nat.gcd n (p ^ (e * t) - 1) :=
        dvd_trans hvdiv (div_gcd_dvd_div_gcd hn hAA)
      apply (extension_iff_mul_dvd_lcm ha).mpr
      have hnlcm : n ∣ Nat.lcm a (p ^ (e * t) - 1) := by
        rw [hna]
        exact (extension_iff_mul_dvd_lcm ha).mp hdiv
      have hlcm : Nat.lcm n (p ^ (e * t) - 1) ∣ Nat.lcm a (p ^ (e * t) - 1) :=
        Nat.lcm_dvd hnlcm (Nat.dvd_lcm_right _ _)
      have hnv := dvd_trans ((extension_iff_mul_dvd_lcm hn).mp hvtop) hlcm
      simpa only [hna, Nat.mul_assoc] using hnv
  | @descent n f r hn hf hr =>
    obtain ⟨t, u, ht, hu, hna, hcop, hdiv, hfe⟩ := h
    dsimp only at hna hcop hdiv hfe
    exact ⟨t, u, ht, hu, hna, hcop, hdiv,
      dvd_trans (Nat.dvd_mul_right f r) hfe⟩

/-- Every finite path has one lift, one extension, and one descent as a normal form. -/
theorem derived_normalForm {p a e : ℕ} {y : Pair} (hp : 1 ≤ p) (ha : 0 < a)
    (h : Derived p (a, e) y) : NormalForm p (a, e) y := by
  induction h with
  | refl => exact normalForm_refl p a e
  | tail hpath hstep ih => exact ih.step hp ha hstep

/-- The explicit normal-form conditions realize a path of precisely three operations. -/
theorem normalForm_derived {p a e n f : ℕ} (ha : 0 < a) (he : 0 < e)
    (h : NormalForm p (a, e) (n, f)) : Derived p (a, e) (n, f) := by
  obtain ⟨t, u, ht, hu, hna, hcop, hdiv, hfe⟩ := h
  dsimp only at hna hcop hdiv hfe
  have het : 0 < e * t := Nat.mul_pos he ht
  have hn : 0 < n := by rw [hna]; exact Nat.mul_pos ha hu
  have hf : 0 < f := Nat.pos_of_dvd_of_pos hfe het
  obtain ⟨r, hr⟩ := hfe
  have hrpos : 0 < r := by
    apply Nat.pos_of_ne_zero
    intro hrzero
    rw [hrzero, Nat.mul_zero] at hr
    exact Nat.ne_of_gt het hr
  have h₁ : Derived p (a, e) (a, e * t) :=
    Relation.ReflTransGen.single (Step.lift ha he ht hcop)
  have h₂ : Derived p (a, e * t) (n, e * t) := by
    rw [hna]
    exact Relation.ReflTransGen.single (Step.extension ha het hu hdiv)
  have h₃ : Derived p (n, e * t) (n, f) := by
    rw [hr]
    exact Relation.ReflTransGen.single (Step.descent hn hf hrpos)
  exact h₁.trans (h₂.trans h₃)

/-- Powers at their multiplicative order are congruent to one at the original modulus. -/
theorem modulus_dvd_pow_order_sub_one {n q : ℕ} (hq : 1 ≤ q) :
    n ∣ q ^ orderOf (q : ZMod n) - 1 := by
  apply (Nat.modEq_iff_dvd' (one_le_pow₀ hq)).mp
  apply (ZMod.natCast_eq_natCast_iff 1 (q ^ orderOf (q : ZMod n)) n).mp
  simpa only [Nat.cast_one, Nat.cast_pow] using (pow_orderOf_eq_one (q : ZMod n)).symm

/-- Every tensor operation is a lift, an extension, and a descent. -/
theorem tensor_derived {p : ℕ} (hp : 1 ≤ p) {x y : Pair}
    (h : TensorStep p x y) : Derived p x y := by
  cases h with
  | @tensor n e s hn he hs ht hcop =>
    let t := orderOf (p ^ e : ZMod s)
    let u := Nat.lcm n s / n
    have htpos : 0 < t := Nat.lt_trans Nat.zero_lt_one ht
    have hL : 0 < Nat.lcm n s := Nat.lcm_pos hn hs
    have hu : 0 < u := Nat.div_pos (Nat.le_of_dvd hL (Nat.dvd_lcm_left n s)) hn
    have hmul : n * u = Nat.lcm n s := Nat.mul_div_cancel' (Nat.dvd_lcm_left n s)
    have hsdiv : s ∣ p ^ (e * t) - 1 := by
      simpa only [Nat.cast_pow, pow_mul] using
        modulus_dvd_pow_order_sub_one (n := s) (q := p ^ e) (one_le_pow₀ hp)
    have hdiv : u ∣ (p ^ (e * t) - 1) / Nat.gcd n (p ^ (e * t) - 1) := by
      apply (extension_iff_mul_dvd_lcm hn).mpr
      rw [hmul]
      exact Nat.lcm_dvd (Nat.dvd_lcm_left _ _) (dvd_trans hsdiv (Nat.dvd_lcm_right _ _))
    have h₁ : Derived p (n, e) (n, e * t) :=
      Relation.ReflTransGen.single (Step.lift hn he htpos hcop)
    have h₂ : Derived p (n, e * t) (Nat.lcm n s, e * t) := by
      have h₂' := Relation.ReflTransGen.single
        (Step.extension hn (Nat.mul_pos he htpos) hu hdiv)
      simpa only [hmul] using h₂'
    have h₃ : Derived p (Nat.lcm n s, e * t) (Nat.lcm n s, e) :=
      Relation.ReflTransGen.single (Step.descent hL he htpos)
    exact h₁.trans (h₂.trans h₃)

/-- A single construction from the classification lies in the elementary closure. -/
theorem classificationStep_derived {p : ℕ} (hp : 1 ≤ p) {x y : Pair}
    (h : ClassificationStep p x y) : Derived p x y := by
  rcases h with h | h
  · exact Relation.ReflTransGen.single h
  · exact tensor_derived hp h

/-- Every finite sequence of all four classification constructions reduces to the three operations. -/
theorem classification_derived {p : ℕ} (hp : 1 ≤ p) {x y : Pair}
    (h : Relation.ReflTransGen (ClassificationStep p) x y) : Derived p x y := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail hpath hstep ih => exact ih.trans (classificationStep_derived hp hstep)

/-- Consequently the original four construction operations have the same normal form. -/
theorem classification_normalForm {p a e : ℕ} {y : Pair} (hp : 1 ≤ p) (ha : 0 < a)
    (h : Relation.ReflTransGen (ClassificationStep p) (a, e) y) :
    NormalForm p (a, e) y :=
  derived_normalForm hp ha (classification_derived hp h)

/-- For a positive initial pair, the explicit arithmetic conditions characterize the closure. -/
theorem derived_iff_normalForm {p a e n f : ℕ} (hp : 1 ≤ p) (ha : 0 < a) (he : 0 < e) :
    Derived p (a, e) (n, f) ↔ NormalForm p (a, e) (n, f) :=
  ⟨derived_normalForm hp ha, normalForm_derived ha he⟩

end NSDensity
