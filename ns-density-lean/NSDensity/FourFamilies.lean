import NSDensity.FixedPair

/-! The primitive, ovoid, and Golay families and all their normal-form lengths. -/

namespace NSDensity

def PrimitiveInitialLength (p : ℕ) (ij : ℕ × ℕ) : ℕ :=
  p ^ ((ij.1 + 1) * (ij.2 + 2)) - 1

def PrimitiveLengths (p : ℕ) : Set ℕ :=
  ⋃ ij : ℕ × ℕ, NormalLengths (PrimitiveInitialLength p ij) (p ^ (ij.1 + 1))

def OvoidInitialLength (p i : ℕ) : ℕ :=
  (p ^ (i + 1) - 1) * (p ^ (2 * (i + 1)) + 1)

def OvoidLengths (p : ℕ) : Set ℕ :=
  ⋃ i : ℕ, NormalLengths (OvoidInitialLength p i) (p ^ (i + 1))

def GolayLengths : Set ℕ := NormalLengths 23 2 ∪ NormalLengths 11 3

/-- Every positive field exponent has alphabet size greater than one. -/
theorem characteristic_power_gt_one {p : ℕ} (hp : 1 < p) (i : ℕ) : 1 < p ^ (i + 1) := by
  have hpow := Nat.pow_lt_pow_right hp (by omega : 0 < i + 1)
  simpa only [pow_zero] using hpow

/-- Degrees at least two give an initial length strictly larger than b-1. -/
theorem power_sub_one_gt_base_sub_one {b k : ℕ} (hb : 1 < b) (hk : 2 ≤ k) :
    b - 1 < b ^ k - 1 := by
  have hpow := Nat.pow_lt_pow_right hb (by omega : 1 < k)
  simp only [pow_one] at hpow
  omega

/-- A dyadic lower bound gives a summable primitive initial-length family. -/
theorem primitiveInitialLength_dyadic {p : ℕ} (hp : 1 < p) (ij : ℕ × ℕ) :
    2 ^ (ij.1 + ij.2) ≤ PrimitiveInitialLength p ij := by
  have hexp : ij.1 + ij.2 + 1 ≤ (ij.1 + 1) * (ij.2 + 2) := by nlinarith
  have h₁ := Nat.pow_le_pow_right (by decide : 0 < 2) hexp
  have h₂ := Nat.pow_le_pow_left (by omega : 2 ≤ p) ((ij.1 + 1) * (ij.2 + 2))
  have hpow : 0 < 2 ^ (ij.1 + ij.2) := Nat.pow_pos (by decide)
  rw [pow_succ] at h₁
  dsimp [PrimitiveInitialLength]
  omega

theorem primitiveInitialLength_pos {p : ℕ} (hp : 1 < p) (ij : ℕ × ℕ) :
    0 < PrimitiveInitialLength p ij :=
  lt_of_lt_of_le (Nat.pow_pos (by decide : 0 < 2)) (primitiveInitialLength_dyadic hp ij)

theorem primitiveInitial_order_gt_one {p : ℕ} (hp : 1 < p) (ij : ℕ × ℕ) :
    1 < orderOf (p ^ (ij.1 + 1) : ZMod (PrimitiveInitialLength p ij)) := by
  have hb := characteristic_power_gt_one hp ij.1
  have hlarge := power_sub_one_gt_base_sub_one hb (by omega : 2 ≤ ij.2 + 2)
  have hlen : PrimitiveInitialLength p ij = (p ^ (ij.1 + 1)) ^ (ij.2 + 2) - 1 := by
    simp only [PrimitiveInitialLength, pow_mul]
  have hm := order_gt_one_of_large_divisor hb (by omega : 0 < ij.2 + 2)
    (show PrimitiveInitialLength p ij ∣ (p ^ (ij.1 + 1)) ^ (ij.2 + 2) - 1 by rw [hlen])
    (by simpa only [hlen] using hlarge)
  simpa only [Nat.cast_pow] using hm

theorem densityZero_primitiveLengths (hWM : WiertelakMoreeInput)
    {p : ℕ} (hp : 1 < p) : DensityZero (PrimitiveLengths p) := by
  apply densityZero_iUnion_of_reciprocalTails
    (fun ij => NormalLengths (PrimitiveInitialLength p ij) (p ^ (ij.1 + 1)))
    (PrimitiveInitialLength p)
  · exact primitiveInitialLength_pos hp
  · intro ij
    exact normalLengths_subset_multiples _ _
  · intro ij
    apply densityZero_normalLengths hWM (primitiveInitialLength_pos hp ij)
      (characteristic_power_gt_one hp ij.1)
    simpa only [Nat.cast_pow] using primitiveInitial_order_gt_one hp ij
  · exact reciprocalTails_of_two_pow_add_le _ (primitiveInitialLength_dyadic hp)

/-- The ovoid length is a divisor of b^4-1. -/
theorem ovoid_factorization (b : ℕ) :
    b ^ 4 - 1 = ((b - 1) * (b ^ 2 + 1)) * (b + 1) := by
  have hsq : b ^ 2 - 1 = (b + 1) * (b - 1) := by
    simpa only [one_pow] using Nat.sq_sub_sq b 1
  have hpow : (b ^ 2) ^ 2 = b ^ 4 := by rw [← pow_mul]
  have hfour : b ^ 4 - 1 = (b ^ 2 + 1) * (b ^ 2 - 1) := by
    calc
      b ^ 4 - 1 = (b ^ 2) ^ 2 - 1 ^ 2 := by rw [hpow, one_pow]
      _ = (b ^ 2 + 1) * (b ^ 2 - 1) := Nat.sq_sub_sq (b ^ 2) 1
  rw [hfour, hsq]
  ac_rfl

theorem ovoidInitialLength_as_base (p i : ℕ) :
    OvoidInitialLength p i = (p ^ (i + 1) - 1) * ((p ^ (i + 1)) ^ 2 + 1) := by
  simp only [OvoidInitialLength, ← pow_mul, Nat.mul_comm 2 (i + 1)]

theorem ovoidInitialLength_dyadic {p : ℕ} (hp : 1 < p) (i : ℕ) :
    2 ^ i ≤ OvoidInitialLength p i := by
  have hbase := Nat.pow_le_pow_left (by omega : 2 ≤ p) (i + 1)
  have hpow : 0 < 2 ^ i := Nat.pow_pos (by decide)
  rw [pow_succ] at hbase
  have hscalar : 2 ^ i ≤ p ^ (i + 1) - 1 := by omega
  exact hscalar.trans (Nat.le_mul_of_pos_right _ (by omega : 0 < p ^ (2 * (i + 1)) + 1))

theorem ovoidInitialLength_pos {p : ℕ} (hp : 1 < p) (i : ℕ) :
    0 < OvoidInitialLength p i :=
  lt_of_lt_of_le (Nat.pow_pos (by decide : 0 < 2)) (ovoidInitialLength_dyadic hp i)

theorem ovoidInitial_order_gt_one {p : ℕ} (hp : 1 < p) (i : ℕ) :
    1 < orderOf (p ^ (i + 1) : ZMod (OvoidInitialLength p i)) := by
  let b := p ^ (i + 1)
  have hb : 1 < b := characteristic_power_gt_one hp i
  have hlen : OvoidInitialLength p i = (b - 1) * (b ^ 2 + 1) :=
    ovoidInitialLength_as_base p i
  have hdiv : OvoidInitialLength p i ∣ b ^ 4 - 1 := by
    rw [hlen, ovoid_factorization]
    exact Nat.dvd_mul_right _ _
  have hlarge : b - 1 < OvoidInitialLength p i := by
    rw [hlen]
    have hbsub : 0 < b - 1 := Nat.sub_pos_of_lt hb
    have hbsq : 0 < b ^ 2 := Nat.pow_pos (by omega)
    nlinarith
  have hm := order_gt_one_of_large_divisor hb (by decide : 0 < 4) hdiv hlarge
  simpa only [b, Nat.cast_pow] using hm

theorem densityZero_ovoidLengths (hWM : WiertelakMoreeInput)
    {p : ℕ} (hp : 1 < p) : DensityZero (OvoidLengths p) := by
  apply densityZero_iUnion_of_reciprocalTails
    (fun i => NormalLengths (OvoidInitialLength p i) (p ^ (i + 1)))
    (OvoidInitialLength p)
  · exact ovoidInitialLength_pos hp
  · intro i
    exact normalLengths_subset_multiples _ _
  · intro i
    apply densityZero_normalLengths hWM (ovoidInitialLength_pos hp i)
      (characteristic_power_gt_one hp i)
    simpa only [Nat.cast_pow] using ovoidInitial_order_gt_one hp i
  · exact reciprocalTails_of_two_pow_le _ (ovoidInitialLength_dyadic hp)

theorem golay23_order_gt_one : 1 < orderOf (2 : ZMod 23) := by
  exact order_gt_one_of_large_divisor (by decide : 1 < 2) (by decide : 0 < 11)
    (by norm_num : 23 ∣ 2 ^ 11 - 1) (by decide)

theorem golay11_order_gt_one : 1 < orderOf (3 : ZMod 11) := by
  exact order_gt_one_of_large_divisor (by decide : 1 < 3) (by decide : 0 < 5)
    (by norm_num : 11 ∣ 3 ^ 5 - 1) (by decide)

theorem densityZero_golayLengths (hWM : WiertelakMoreeInput) : DensityZero GolayLengths :=
  (densityZero_normalLengths hWM (by decide : 0 < 23) (by decide : 1 < 2)
    golay23_order_gt_one).union
  (densityZero_normalLengths hWM (by decide : 0 < 11) (by decide : 1 < 3)
    golay11_order_gt_one)

end NSDensity
