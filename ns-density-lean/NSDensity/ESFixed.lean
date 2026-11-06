import NSDensity.ESArithmetic
import NSDensity.Tails

namespace NSDensity

/-- A fixed prime witness and exact exponent, described without valuation notation. -/
def ESFixed (q l a : ℕ) : Set ℕ :=
  {n | ESWitness q n l ∧ ∃ v, ¬ l ∣ v ∧ n = l ^ a * v}

theorem witness_order_not_dvd_cofactor {q n l a v : ℕ} (hq : 1 < q)
    (ha : 1 ≤ a) (h : ESWitness q n l) (hv : ¬ l ∣ v)
    (hnrel : n = l ^ a * v) :
    ¬ orderOf (q : ZMod (l ^ a)) ∣ orderOf (q : ZMod v) := by
  obtain ⟨hn, hcop, hl, hln, hord⟩ := h
  have hvpos : 0 < v := by
    by_contra hpos
    have hz : v = 0 := by omega
    simp [hz] at hv
  have hcoplv : Nat.Coprime l v := hl.coprime_iff_not_dvd.mpr hv
  have hpow : l ^ a = l ^ (a - 1) * l := by
    rw [← pow_succ]
    congr 1
    omega
  have hnquot : n / l = l ^ (a - 1) * v := by
    rw [hnrel, hpow, mul_assoc, mul_comm l v, ← mul_assoc, Nat.mul_div_cancel _ hl.pos]
  have hnlcm : Nat.lcm (l ^ a) v = n := by
    rw [(hcoplv.pow_left a).lcm_eq_mul, ← hnrel]
  have hdlcm : Nat.lcm (l ^ (a - 1)) v = n / l := by
    rw [(hcoplv.pow_left (a - 1)).lcm_eq_mul, ← hnquot]
  have hBAdvd : orderOf (q : ZMod (l ^ (a - 1))) ∣ orderOf (q : ZMod (l ^ a)) :=
    order_dvd_of_modulus_dvd (pow_dvd_pow l (by omega))
  have hTpos : 0 < orderOf (q : ZMod v) := order_pos hvpos
    (hcop.of_dvd_right (hnrel ▸ Nat.dvd_mul_left v (l ^ a)))
  intro hAT
  have hBT := dvd_trans hBAdvd hAT
  have htop := order_lcm (n := l ^ a) (d := v) hq.le
  have hbot := order_lcm (n := l ^ (a - 1)) (d := v) hq.le
  rw [hnlcm, Nat.lcm_eq_right hAT] at htop
  rw [hdlcm, Nat.lcm_eq_right hBT] at hbot
  rw [htop, hbot] at hord
  have hl1 := hl.one_lt
  nlinarith

theorem witness_cofactor_avoids {q n l a v : ℕ} (hq : 1 < q)
    (ha : 1 ≤ a) (h : ESWitness q n l) (hv : ¬ l ∣ v)
    (hnrel : n = l ^ a * v) :
    v ∈ avoids (OrderPrimes q (orderOf (q : ZMod (l ^ a)))) := by
  intro r hr hrv
  exact witness_order_not_dvd_cofactor hq ha h hv hnrel
    (dvd_trans hr.2.2 (order_dvd_of_modulus_dvd hrv))
theorem densityZero_ESFixed (hWM : WiertelakMoreeInput) {q l a : ℕ}
    (hq : 1 < q) (hl : l.Prime) (ha : 2 ≤ a) : DensityZero (ESFixed q l a) := by
  let A := orderOf (q : ZMod (l ^ a))
  by_cases hA : 1 < A
  · apply (densityZero_avoids_orderPrimes hWM hq hA).scaled
      (l ^ a) (pow_pos hl.pos a) |>.mono
    intro n hn
    obtain ⟨hW, v, hv, hnrel⟩ := hn
    exact ⟨v, witness_cofactor_avoids hq (by omega) hW hv hnrel, hnrel⟩
  · have hemp : ESFixed q l a = ∅ := by
      apply Set.Subset.antisymm ?_ (Set.empty_subset _)
      intro n hn
      obtain ⟨hW, v, hv, hnrel⟩ := hn
      have hcopqa : Nat.Coprime q (l ^ a) := hW.2.1.of_dvd_right
        (hnrel ▸ Nat.dvd_mul_right (l ^ a) v)
      have hApos : 0 < A := order_pos (pow_pos hl.pos a) hcopqa
      have hAeq : A = 1 := by omega
      apply witness_order_not_dvd_cofactor hq (by omega) hW hv hnrel
      rw [show orderOf (q : ZMod (l ^ a)) = 1 from hAeq]
      exact one_dvd _
    rw [hemp]
    exact densityZero_empty

end NSDensity

