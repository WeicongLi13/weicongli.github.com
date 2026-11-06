module

public import Mathlib.RingTheory.Valuation.Basic
public import Mathlib.Data.Nat.Init
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith.Frontend
public import Lean.Elab.Tactic.Omega

/-!
# The second-order recurrence in Proposition `prop:poles`

These results concern an arbitrary field and a genuine additive valuation.
The valuation pole bounds below are algebraic ingredients of the proposition;
they do not yet identify the valuation with the order at an irreducible
multivariate polynomial, or prove the polynomial/homogeneity conclusions.
-/

@[expose] public section

namespace Cylinder.Recurrence

variable {R : Type*} [CommRing R]

/-- The recurrence, without divisions or restrictions on characteristic. -/
def moment (f q : R) : ℕ → R
  | 0 => 1
  | 1 => f
  | n + 2 => f * moment f q (n + 1) - q * moment f q n

@[simp] theorem moment_zero (f q : R) : moment f q 0 = 1 := rfl
@[simp] theorem moment_one (f q : R) : moment f q 1 = f := rfl
theorem moment_step (f q : R) (n : ℕ) :
    moment f q (n + 2) = f * moment f q (n + 1) - q * moment f q n := rfl

theorem moment_two (f q : R) : moment f q 2 = f ^ 2 - q := by
  simp [moment, pow_two]

/-- Initial values and the recurrence determine every term. -/
theorem moment_unique (f q : R) (h : ℕ → R)
    (h0 : h 0 = 1) (h1 : h 1 = f)
    (hs : ∀ n, h (n + 2) = f * h (n + 1) - q * h n) :
    ∀ n, h n = moment f q n := by
  intro n
  induction n using Nat.twoStepInduction with
  | zero => exact h0
  | one => exact h1
  | more n ih0 ih1 => rw [hs, moment_step, ih0, ih1]

/-- The same uniqueness result for a recurrence given only through a
finite upper index, as in the proposition. -/
theorem moment_unique_to (f q : R) (h : ℕ → R) (N : ℕ)
    (h0 : h 0 = 1) (h1 : h 1 = f)
    (hs : ∀ n, n + 2 ≤ N → h (n + 2) = f * h (n + 1) - q * h n) :
    ∀ n, n ≤ N → h n = moment f q n := by
  intro n
  induction n using Nat.twoStepInduction with
  | zero => intro _; exact h0
  | one => intro _; exact h1
  | more n ih0 ih1 =>
      intro hn
      rw [hs n hn, moment_step, ih0 (by omega), ih1 (by omega)]

/-- The normalization used in the proof of the pole bound. -/
theorem moment_scaling (f w : R) (n : ℕ) :
    moment f (f ^ 2 * w) n = f ^ n * moment 1 w n := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => simp
  | more n ih0 ih1 =>
      rw [moment_step, moment_step, ih0, ih1]
      simp only [one_mul, pow_succ]
      ring

section Domain

variable [IsDomain R]

/-- With nonzero second coefficient, consecutive zero terms would force
the first term to be zero by backward induction. -/
theorem moment_no_consecutive_zero (f q : R) (hq : q ≠ 0) (n : ℕ) :
    ¬ (moment f q n = 0 ∧ moment f q (n + 1) = 0) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rintro ⟨hn1, hn2⟩
      have hp : q * moment f q n = 0 := by
        have hs := moment_step f q n
        rw [hn1, hn2, mul_zero, zero_sub] at hs
        exact neg_eq_zero.mp hs.symm
      exact ih ⟨(mul_eq_zero.mp hp).resolve_left hq, hn1⟩

end Domain

section Valuation

variable {K : Type*} [Field K] (v : AddValuation K (WithTop ℤ))

/-- The positive-valuation case for the normalized recurrence: every term
has valuation zero. This includes `w = 0`. -/
theorem normalized_positive (w : K) (hw : 0 < v w) (n : ℕ) :
    v (moment 1 w n) = 0 := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => simp
  | more n ih0 ih1 =>
      rw [moment_step, one_mul]
      have hs : v (moment 1 w (n + 1)) < v (w * moment 1 w n) := by
        simpa only [v.map_mul, ih0, ih1, add_zero] using hw
      rw [v.map_sub_eq_of_lt_left hs, ih1]

/-- If the second coefficient is a valuation unit, two consecutive
normalized terms cannot both have positive valuation. -/
theorem normalized_unit_no_consecutive_positive (w : K) (hw : v w = 0)
    (n : ℕ) :
    ¬ (0 < v (moment 1 w n) ∧ 0 < v (moment 1 w (n + 1))) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rintro ⟨hn1, hn2⟩
      have hb : w * moment 1 w n =
          moment 1 w (n + 1) - moment 1 w (n + 2) := by
        rw [moment_step, one_mul]
        ring
      have hp : 0 < v (w * moment 1 w n) := by
        rw [hb, sub_eq_add_neg]
        exact v.map_lt_add hn1 (by simpa only [v.map_neg] using hn2)
      rw [v.map_mul, hw, zero_add] at hp
      exact ih ⟨hp, hn1⟩

/-- A unit second coefficient keeps all normalized terms in the valuation
ring; cancellation may increase their valuations. -/
theorem normalized_unit_nonnegative (w : K) (hw : v w = 0) (n : ℕ) :
    0 ≤ v (moment 1 w n) := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => simp
  | more n ih0 ih1 =>
      rw [moment_step, one_mul]
      exact v.map_le_sub ih1 (by simpa only [v.map_mul, hw, zero_add] using ih0)

/-- The residue-unit case: at least one term of every consecutive pair is
a valuation unit. -/
theorem normalized_unit_pair (w : K) (hw : v w = 0) (n : ℕ) :
    v (moment 1 w n) = 0 ∨ v (moment 1 w (n + 1)) = 0 := by
  have h0 := normalized_unit_nonnegative v w hw n
  have h1 := normalized_unit_nonnegative v w hw (n + 1)
  have hn := normalized_unit_no_consecutive_positive v w hw n
  by_cases hz : v (moment 1 w n) = 0
  · exact Or.inl hz
  · exact Or.inr (le_antisymm
      (not_lt.mp (fun hp => hn ⟨lt_of_le_of_ne h0 (fun he => hz he.symm), hp⟩)) h1)

/-- The dominant-`q` case is proved directly by two-term induction, avoiding
the binomial closed form. At even indices no cancellation is possible. -/
theorem dominant_even_odd (f q : K) (b c : ℤ)
    (hf : (b : WithTop ℤ) ≤ v f) (hq : v q = (c : WithTop ℤ))
    (hdom : c < 2 * b) (j : ℕ) :
    v (moment f q (2 * j)) = (((j : ℤ) * c : ℤ) : WithTop ℤ) ∧
    (((j : ℤ) * c + b : ℤ) : WithTop ℤ) ≤ v (moment f q (2 * j + 1)) := by
  induction j with
  | zero => simpa using hf
  | succ j ih =>
      have hleft : (((j : ℤ) * c + 2 * b : ℤ) : WithTop ℤ) ≤
          v (f * moment f q (2 * j + 1)) := by
        rw [v.map_mul]
        calc
          (((j : ℤ) * c + 2 * b : ℤ) : WithTop ℤ) =
              (b : WithTop ℤ) + (((j : ℤ) * c + b : ℤ) : WithTop ℤ) := by
                exact_mod_cast (by ring : (j : ℤ) * c + 2 * b = b + ((j : ℤ) * c + b))
          _ ≤ _ := add_le_add hf ih.2
      have hright : v (q * moment f q (2 * j)) =
          ((((j : ℤ) + 1) * c : ℤ) : WithTop ℤ) := by
        rw [v.map_mul, hq, ih.1]
        exact_mod_cast (by ring : c + (j : ℤ) * c = ((j : ℤ) + 1) * c)
      have hstrict : v (q * moment f q (2 * j)) <
          v (f * moment f q (2 * j + 1)) := by
        rw [hright]
        apply lt_of_lt_of_le _ hleft
        exact_mod_cast (by nlinarith : ((j : ℤ) + 1) * c < (j : ℤ) * c + 2 * b)
      have heven : v (moment f q (2 * (j + 1))) =
          ((((j : ℤ) + 1) * c : ℤ) : WithTop ℤ) := by
        rw [show 2 * (j + 1) = 2 * j + 2 by omega, moment_step,
          v.map_sub_eq_of_lt_right hstrict, hright]
      constructor
      · simpa only [Nat.cast_add, Nat.cast_one] using heven
      · rw [show 2 * (j + 1) + 1 = (2 * j + 1) + 2 by omega, moment_step]
        apply v.map_le_sub
        · rw [show 2 * j + 1 + 1 = 2 * (j + 1) by omega, v.map_mul, heven]
          calc
            ((((j + 1 : ℕ) : ℤ) * c + b : ℤ) : WithTop ℤ) =
                (b : WithTop ℤ) + ((((j : ℤ) + 1) * c : ℤ) : WithTop ℤ) := by
                  exact_mod_cast (by push_cast; ring :
                    (((j + 1 : ℕ) : ℤ) * c + b) = b + ((j : ℤ) + 1) * c)
            _ ≤ _ := add_le_add_left hf _
        · rw [v.map_mul, hq]
          calc
            ((((j + 1 : ℕ) : ℤ) * c + b : ℤ) : WithTop ℤ) =
                (c : WithTop ℤ) + (((j : ℤ) * c + b : ℤ) : WithTop ℤ) := by
                  exact_mod_cast (by push_cast; ring :
                    (((j + 1 : ℕ) : ℤ) * c + b) = c + ((j : ℤ) * c + b))
            _ ≤ _ := add_le_add_right ih.2 _

/-- The second pole bound in its valuation form. The hypotheses are exactly
the lower bound on the common-denominator sequence, together with the
already established absence of poles in `f`. -/
theorem quadratic_pole_bound (f q : K) (a : ℕ)
    (hf : 0 ≤ v f)
    (hbound : ∀ n ≤ 2 * a + 2, ((-(a : ℤ) : ℤ) : WithTop ℤ) ≤ v (moment f q n)) :
    0 ≤ v q := by
  by_contra hn
  have hneg : v q < 0 := lt_of_not_ge hn
  cases hq : v q using WithTop.recTopCoe with
  | top => simp [hq] at hneg
  | coe c =>
      have hc : c < 0 := by
        rw [hq] at hneg
        exact WithTop.coe_lt_coe.mp hneg
      have hvq : v q = (c : WithTop ℤ) := hq
      have he := (dominant_even_odd v f q 0 c hf hvq (by omega) (a + 1)).1
      have hb := hbound (2 * (a + 1)) (by omega)
      rw [he] at hb
      have hi : -(a : ℤ) ≤ ((a + 1 : ℕ) : ℤ) * c := by exact_mod_cast hb
      have hproduct := mul_le_mul_of_nonneg_left (show c ≤ -1 by omega)
        (Int.natCast_nonneg (a + 1))
      push_cast at hi
      push_cast at hproduct
      nlinarith only [hi, hproduct]

/-- The first pole bound in its valuation form. The three branches are the
positive, zero, and negative valuations of the normalized coefficient. -/
theorem linear_pole_bound (f q : K) (a : ℕ)
    (hbound : ∀ n ≤ a + 2, ((-(a : ℤ) : ℤ) : WithTop ℤ) ≤ v (moment f q n)) :
    0 ≤ v f := by
  by_contra hn
  have hneg : v f < 0 := lt_of_not_ge hn
  cases hf : v f using WithTop.recTopCoe with
  | top => simp [hf] at hneg
  | coe b =>
      have hb : b < 0 := by
        rw [hf] at hneg
        exact WithTop.coe_lt_coe.mp hneg
      have hvf : v f = (b : WithTop ℤ) := hf
      have hf0 : f ≠ 0 := by
        intro hz
        simp [hz] at hneg
      let w := q / f ^ 2
      have hq : q = f ^ 2 * w := by dsimp [w]; field_simp [hf0]
      have hscale (n : ℕ) : moment f q n = f ^ n * moment 1 w n := by
        rw [hq]
        exact moment_scaling f w n
      have hunit_bound (n : ℕ) (hn : a + 1 ≤ n) (hn' : n ≤ a + 2)
          (hunit : v (moment 1 w n) = 0) : False := by
        have hlow := hbound n hn'
        rw [hscale, v.map_mul, v.map_pow, hvf, hunit, add_zero] at hlow
        have hlow' : -(a : ℤ) ≤ (n : ℤ) * b := by
          simpa only [nsmul_eq_mul] using (show -(a : ℤ) ≤ n • b by exact_mod_cast hlow)
        have hnInt : (a : ℤ) + 1 ≤ (n : ℤ) := by exact_mod_cast hn
        have hproduct := mul_le_mul_of_nonneg_left (show b ≤ -1 by omega)
          (Int.natCast_nonneg n)
        nlinarith only [hlow', hnInt, hproduct]
      rcases lt_trichotomy 0 (v w) with hw | hw | hw
      · exact hunit_bound (a + 1) (by omega) (by omega)
          (normalized_positive v w hw (a + 1))
      · rcases normalized_unit_pair v w hw.symm (a + 1) with h0 | h1
        · exact hunit_bound (a + 1) (by omega) (by omega) h0
        · exact hunit_bound (a + 2) (by omega) (by omega) h1
      · cases hwval : v w using WithTop.recTopCoe with
        | top => simp [hwval] at hw
        | coe c =>
            have hc : c < 0 := by
              rw [hwval] at hw
              exact WithTop.coe_lt_coe.mp hw
            have hvq : v q = ((2 * b + c : ℤ) : WithTop ℤ) := by
              rw [hq, v.map_mul, v.map_pow, hvf, hwval]
              exact_mod_cast (by simp : 2 • b + c = 2 * b + c)
            let j := a / 2 + 1
            have hidx : 2 * j ≤ a + 2 := by dsimp [j]; omega
            have hj : a + 1 ≤ 2 * j := by dsimp [j]; omega
            have he := (dominant_even_odd v f q b (2 * b + c) hvf.ge hvq (by omega) j).1
            have hl := hbound (2 * j) hidx
            rw [he] at hl
            have hl' : -(a : ℤ) ≤ (j : ℤ) * (2 * b + c) := by exact_mod_cast hl
            have hj' : (a : ℤ) + 1 ≤ 2 * (j : ℤ) := by exact_mod_cast hj
            have hjnonneg : 0 ≤ (j : ℤ) := Int.natCast_nonneg j
            have hproduct := mul_le_mul_of_nonneg_left (show 2 * b + c ≤ -3 by omega)
              hjnonneg
            nlinarith only [hl', hj', hjnonneg, hproduct]

/-- Dividing an integral numerator by an element of valuation `a` gives
the precise common-denominator lower bound used in the paper. -/
theorem denominator_lower_bound (A B : K) (a : ℤ)
    (hA : v A = (a : WithTop ℤ)) (hB : 0 ≤ v B) :
    ((-a : ℤ) : WithTop ℤ) ≤ v (B / A) := by
  simpa only [v.map_div, hA, sub_eq_add_neg, zero_add,
    WithTop.LinearOrderedAddCommGroup.coe_neg] using
    add_le_add hB (le_refl (-(a : WithTop ℤ)))

/-- Both recurrence lengths, with a possibly larger upper index. This is
the local valuation conclusion of `prop:poles`; the factor degree and
polynomial-ring membership steps are separate obligations. -/
theorem common_denominator_pole_bounds (f q : K) (a N : ℕ)
    (hbound : ∀ n ≤ N, ((-(a : ℤ) : ℤ) : WithTop ℤ) ≤ v (moment f q n)) :
    (a + 2 ≤ N → 0 ≤ v f) ∧
    (2 * a + 2 ≤ N → 0 ≤ v q) := by
  constructor
  · intro hN
    exact linear_pole_bound v f q a (fun n hn => hbound n (le_trans hn hN))
  · intro hN
    have hf := linear_pole_bound v f q a (fun n hn => hbound n (by omega))
    exact quadratic_pole_bound v f q a hf (fun n hn => hbound n (le_trans hn hN))

/-- The finite common-denominator formulation. A numerator is integral at
the chosen valuation; the conclusion is derived from the recurrence,
without a pole-removal assumption. -/
theorem finite_common_denominator_pole_bounds
    (A f q : K) (num h : ℕ → K) (a N : ℕ)
    (hA : v A = ((a : ℤ) : WithTop ℤ))
    (hnum : ∀ n ≤ N, 0 ≤ v (num n))
    (hcommon : ∀ n ≤ N, h n = num n / A)
    (h0 : h 0 = 1) (h1 : h 1 = f)
    (hs : ∀ n, n + 2 ≤ N → h (n + 2) = f * h (n + 1) - q * h n) :
    (a + 2 ≤ N → 0 ≤ v f) ∧
    (2 * a + 2 ≤ N → 0 ≤ v q) := by
  apply common_denominator_pole_bounds v f q a N
  intro n hn
  rw [← moment_unique_to f q h N h0 h1 hs n hn, hcommon n hn]
  exact denominator_lower_bound v A (num n) (a : ℤ) hA (hnum n hn)

end Valuation

end Cylinder.Recurrence
