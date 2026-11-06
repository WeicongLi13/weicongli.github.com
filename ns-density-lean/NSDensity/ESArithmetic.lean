import NSDensity.Inputs
import Mathlib.FieldTheory.Finite.Basic

namespace NSDensity

/-- The elementary order bound under reduction of a positive modulus. -/
theorem order_le_quotient_mul {d n q : ℕ} (hd : 0 < d) (hn : 0 < n)
    (hdn : d ∣ n) (hcop : Nat.Coprime q n) :
    orderOf (q : ZMod n) ≤ (n / d) * orderOf (q : ZMod d) := by
  classical
  let : NeZero n := ⟨hn.ne'⟩
  let : NeZero d := ⟨hd.ne'⟩
  let D := orderOf (q : ZMod d)
  let x : ZMod n := (q : ZMod n) ^ D
  have hD : 0 < D := order_pos hd (hcop.of_dvd_right hdn)
  have hDM : D ∣ orderOf (q : ZMod n) := order_dvd_of_modulus_dvd hdn
  have hxord : orderOf x = orderOf (q : ZMod n) / D :=
    orderOf_pow_of_dvd hD.ne' hDM
  let f : ℕ → ℕ := fun i => (x ^ i).val / d
  have hrem (i : ℕ) : (x ^ i).val % d = 1 % d := by
    apply (ZMod.natCast_eq_natCast_iff _ _ d).mp
    have hx : ZMod.castHom hdn (ZMod d) x = 1 := by
      change ZMod.castHom hdn (ZMod d) ((q : ZMod n) ^ D) = 1
      rw [map_pow, map_natCast]
      exact pow_orderOf_eq_one _
    rw [← ZMod.cast_eq_val, ← ZMod.castHom_apply, map_pow, hx, one_pow, Nat.cast_one]
    exact hdn
  have hflt (i : ℕ) : f i < n / d := by
    apply (Nat.div_lt_iff_lt_mul hd).mpr
    simpa [Nat.div_mul_cancel hdn] using (ZMod.val_lt (x ^ i))
  have hfinj : Set.InjOn f (Set.Iio (orderOf x)) := by
    intro i hi j hj hij
    apply pow_injOn_Iio_orderOf hi hj
    apply ZMod.val_injective
    have hi' := Nat.mod_add_div (x ^ i).val d
    have hj' := Nat.mod_add_div (x ^ j).val d
    rw [hrem i] at hi'
    rw [hrem j] at hj'
    dsimp [f] at hij
    exact (hi'.symm.trans (by rw [hij])).trans hj'
  have hle : orderOf x ≤ n / d := by
    simpa using Finset.le_card_of_inj_on_range f
      (fun i _ => Finset.mem_range.mpr (hflt i)) hfinj
  rw [hxord] at hle
  have hmul := Nat.mul_le_mul_right D hle
  simpa [Nat.div_mul_cancel hDM] using hmul

theorem order_lcm {n d q : ℕ} (hq : 1 ≤ q) :
    orderOf (q : ZMod (Nat.lcm n d)) =
      Nat.lcm (orderOf (q : ZMod n)) (orderOf (q : ZMod d)) := by
  apply Nat.dvd_antisymm
  · apply order_dvd_of_dvd_pow_sub_one hq
    apply Nat.lcm_dvd
    · apply (Nat.modEq_iff_dvd' (one_le_pow₀ hq)).mp
      apply (ZMod.natCast_eq_natCast_iff _ _ n).mp
      simpa using (orderOf_dvd_iff_pow_eq_one.mp
        (Nat.dvd_lcm_left (orderOf (q : ZMod n)) (orderOf (q : ZMod d)))).symm
    · apply (Nat.modEq_iff_dvd' (one_le_pow₀ hq)).mp
      apply (ZMod.natCast_eq_natCast_iff _ _ d).mp
      simpa using (orderOf_dvd_iff_pow_eq_one.mp
        (Nat.dvd_lcm_right (orderOf (q : ZMod n)) (orderOf (q : ZMod d)))).symm
  · exact Nat.lcm_dvd
      (order_dvd_of_modulus_dvd (Nat.dvd_lcm_left n d))
      (order_dvd_of_modulus_dvd (Nat.dvd_lcm_right n d))

def EquallySpaced (q n : ℕ) : Prop :=
  0 < n ∧ Nat.Coprime q n ∧ ∃ d s : ℕ,
    2 ≤ d ∧ 2 ≤ s ∧ n = d * s ∧
      orderOf (q : ZMod n) = s * orderOf (q : ZMod d)

def ESWitness (q n l : ℕ) : Prop :=
  0 < n ∧ Nat.Coprime q n ∧ l.Prime ∧ l ∣ n ∧
    orderOf (q : ZMod n) = l * orderOf (q : ZMod (n / l))

theorem EquallySpaced.exists_witness {q n : ℕ} (h : EquallySpaced q n) :
    ∃ l, ESWitness q n l := by
  obtain ⟨hn, hcop, d, s, hd, hs, hnrel, hord⟩ := h
  obtain ⟨l, hl, hls⟩ := Nat.exists_prime_and_dvd (by omega : s ≠ 1)
  have hln : l ∣ n := hnrel ▸ dvd_mul_of_dvd_right hls d
  have hdquot : d ∣ n / l := by
    rw [hnrel, Nat.mul_div_assoc _ hls]
    exact Nat.dvd_mul_right _ _
  have hquotpos : 0 < n / l := Nat.div_pos (Nat.le_of_dvd hn hln) hl.pos
  have hdpos : 0 < d := by omega
  have hDpos : 0 < orderOf (q : ZMod d) :=
    order_pos hdpos (hcop.of_dvd_right (hnrel ▸ Nat.dvd_mul_right d s))
  have htop := order_le_quotient_mul hquotpos hn (Nat.div_dvd_of_dvd hln) hcop
  have hbot := order_le_quotient_mul hdpos hquotpos hdquot
    (hcop.of_dvd_right (Nat.div_dvd_of_dvd hln))
  have hdivide : n / (n / l) = l := Nat.div_div_self hln hn.ne'
  rw [hdivide] at htop
  have hquot : n / l / d = s / l := by
    rw [Nat.div_div_eq_div_mul, mul_comm l d, ← Nat.div_div_eq_div_mul, hnrel,
      Nat.mul_div_cancel_left _ hdpos]
  rw [hquot] at hbot
  have hlprod : l * (s / l) = s := Nat.mul_div_cancel' hls
  have hbound : l * orderOf (q : ZMod (n / l)) ≤ s * orderOf (q : ZMod d) := by
    calc
      _ ≤ l * ((s / l) * orderOf (q : ZMod d)) := Nat.mul_le_mul_left l hbot
      _ = _ := by rw [← mul_assoc, hlprod]
  refine ⟨l, hn, hcop, hl, hln, ?_⟩
  exact le_antisymm htop (hord ▸ hbound)

theorem EquallySpaced.lift {q n t : ℕ} (h : EquallySpaced q n)
    (ht : Nat.Coprime t (orderOf (q : ZMod n))) : EquallySpaced (q ^ t) n := by
  obtain ⟨hn, hcop, d, s, hd, hs, hnrel, hord⟩ := h
  have hdord : orderOf (q : ZMod d) ∣ orderOf (q : ZMod n) :=
    order_dvd_of_modulus_dvd (hnrel ▸ Nat.dvd_mul_right d s)
  refine ⟨hn, hcop.pow_left t, d, s, hd, hs, hnrel, ?_⟩
  simp only [Nat.cast_pow]
  rw [order_lift ht, order_lift (ht.of_dvd_right hdord), hord]

theorem EquallySpaced.descent {q n t : ℕ} (ht : 0 < t)
    (hcop : Nat.Coprime q n) (h : EquallySpaced (q ^ t) n) : EquallySpaced q n := by
  obtain ⟨hn, _, d, s, hd, hs, hnrel, hord⟩ := h
  have hdn : d ∣ n := hnrel ▸ Nat.dvd_mul_right d s
  have hdpos : 0 < d := by omega
  have hDpos := order_pos hdpos (hcop.of_dvd_right hdn)
  have hMpos := order_pos hn hcop
  have hDM := order_dvd_of_modulus_dvd (q := q) hdn
  have hbound := order_le_quotient_mul hdpos hn hdn hcop
  have hquotnd : n / d = s := by rw [hnrel, Nat.mul_div_cancel_left _ hdpos]
  rw [hquotnd] at hbound
  have hgdvd : Nat.gcd (orderOf (q : ZMod d)) t ∣
      Nat.gcd (orderOf (q : ZMod n)) t := Nat.gcd_dvd_gcd_of_dvd_left t hDM
  have hgMpos := Nat.gcd_pos_of_pos_left t hMpos
  have hgle := Nat.le_of_dvd hgMpos hgdvd
  simp only [Nat.cast_pow] at hord
  rw [order_power ht, order_power ht] at hord
  have hDdiv := Nat.div_mul_cancel (Nat.gcd_dvd_left (orderOf (q : ZMod d)) t)
  have hMdiv := Nat.div_mul_cancel (Nat.gcd_dvd_left (orderOf (q : ZMod n)) t)
  have hstep := Nat.mul_le_mul_left
    (s * (orderOf (q : ZMod d) / Nat.gcd (orderOf (q : ZMod d)) t)) hgle
  have hreverse : s * orderOf (q : ZMod d) ≤ orderOf (q : ZMod n) := by
    calc
      _ = (s * (orderOf (q : ZMod d) /
        Nat.gcd (orderOf (q : ZMod d)) t)) *
          Nat.gcd (orderOf (q : ZMod d)) t := by rw [mul_assoc, hDdiv]
      _ ≤ _ := hstep
      _ = _ := by rw [← hord, hMdiv]
  exact ⟨hn, hcop, d, s, hd, hs, hnrel, le_antisymm hbound hreverse⟩

theorem es_scalar_intersection {q n d s : ℕ} (hq : 1 < q)
    (hn : 0 < n) (hcop : Nat.Coprime q n) (hd : 0 < d) (hs : 0 < s)
    (hnrel : n = d * s)
    (hord : orderOf (q : ZMod n) = s * orderOf (q : ZMod d)) :
    Nat.gcd n (q - 1) = Nat.gcd d (q - 1) := by
  let e := Nat.gcd n (q - 1)
  let m := Nat.lcm d e
  have hdn : d ∣ n := hnrel ▸ Nat.dvd_mul_right d s
  have hepos : 0 < e := Nat.gcd_pos_of_pos_left _ hn
  have hmn : m ∣ n := Nat.lcm_dvd hdn (Nat.gcd_dvd_left n (q - 1))
  have hmpos : 0 < m := Nat.lcm_pos hd hepos
  have hdm : d ∣ m := Nat.dvd_lcm_left d e
  have hqeq : (q : ZMod e) = 1 := by
    have hm : q ≡ 1 [MOD e] :=
      ((Nat.modEq_iff_dvd' hq.le).mpr (Nat.gcd_dvd_right n (q - 1))).symm
    simpa only [Nat.cast_one] using (ZMod.natCast_eq_natCast_iff q 1 e).mpr hm
  have heord : orderOf (q : ZMod e) = 1 := by rw [hqeq, orderOf_one]
  have hmord : orderOf (q : ZMod m) = orderOf (q : ZMod d) := by
    rw [order_lcm hq.le, heord, Nat.lcm_one_right]
  have hDpos : 0 < orderOf (q : ZMod d) := order_pos hd (hcop.of_dvd_right hdn)
  have hbound := order_le_quotient_mul hmpos hn hmn hcop
  rw [hmord, hord] at hbound
  have hsle : s ≤ n / m := by nlinarith
  have hmsn : m * s ≤ n := by
    simpa [mul_comm] using (Nat.le_div_iff_mul_le hmpos).mp hsle
  have hdlem : d ≤ m := Nat.le_of_dvd hmpos hdm
  have hmd : m = d := by
    rw [hnrel] at hmsn
    have hmled : m ≤ d := by nlinarith
    exact le_antisymm hmled hdlem
  apply Nat.dvd_antisymm
  · exact Nat.dvd_gcd (hmd ▸ Nat.dvd_lcm_right d e)
      (Nat.gcd_dvd_right n (q - 1))
  · exact Nat.gcd_dvd_gcd_of_dvd_left (q - 1) hdn

theorem EquallySpaced.extension {q n u : ℕ} (hq : 1 < q)
    (h : EquallySpaced q n) (hu : u ∣ (q - 1) / Nat.gcd n (q - 1)) :
    EquallySpaced q (n * u) := by
  obtain ⟨hn, hcop, d, s, hd, hs, hnrel, hord⟩ := h
  have hdpos : 0 < d := by omega
  have hspos : 0 < s := by omega
  have hgcd := es_scalar_intersection hq hn hcop hdpos hspos hnrel hord
  have hu' : u ∣ (q - 1) / Nat.gcd d (q - 1) := hgcd ▸ hu
  have hquotpos : 0 < (q - 1) / Nat.gcd n (q - 1) :=
    Nat.div_pos (Nat.le_of_dvd (by omega) (Nat.gcd_dvd_right n (q - 1)))
      (Nat.gcd_pos_of_pos_left _ hn)
  have hupos : 0 < u := Nat.pos_of_dvd_of_pos hu hquotpos
  have huA : u ∣ q - 1 := dvd_trans hu (Nat.div_dvd_of_dvd (Nat.gcd_dvd_right n (q - 1)))
  have hucop : Nat.Coprime q u :=
    ((Nat.coprime_self_sub_right hq.le).mpr (Nat.coprime_one_right q)).of_dvd_right huA
  refine ⟨Nat.mul_pos hn hupos, hcop.mul_right hucop, d * u, s, ?_, hs, ?_, ?_⟩
  · exact hd.trans (Nat.le_mul_of_pos_right d hupos)
  · rw [hnrel]; ac_rfl
  · rw [order_extension hn hq.le hu, order_extension hdpos hq.le hu', hord]

theorem order_prime_dvd_sub_one {q l : ℕ} (hl : l.Prime) (hcop : Nat.Coprime q l) :
    orderOf (q : ZMod l) ∣ l - 1 := by
  apply orderOf_dvd_of_pow_eq_one
  have hm := Nat.ModEq.pow_totient hcop
  rw [Nat.totient_prime hl] at hm
  have hcast := (ZMod.natCast_eq_natCast_iff (q ^ (l - 1)) 1 l).mpr hm
  simpa only [Nat.cast_pow, Nat.cast_one] using hcast

theorem ESWitness.square_dvd {q n l : ℕ} (hq : 1 ≤ q) (h : ESWitness q n l) :
    l ^ 2 ∣ n := by
  obtain ⟨hn, hcop, hl, hln, hord⟩ := h
  have hl1 := hl.one_lt
  by_contra hsq
  have hlv : ¬ l ∣ n / l := by
    intro hdiv
    have hprod := Nat.mul_dvd_mul_left l hdiv
    rw [Nat.mul_div_cancel' hln] at hprod
    exact hsq (by simpa [pow_two] using hprod)
  have hcoplv : Nat.Coprime l (n / l) := hl.coprime_iff_not_dvd.mpr hlv
  have hnrel : Nat.lcm l (n / l) = n := by
    rw [hcoplv.lcm_eq_mul, Nat.mul_div_cancel' hln]
  have horder := order_lcm (n := l) (d := n / l) hq
  rw [hnrel, hord] at horder
  have hpdiv := order_prime_dvd_sub_one hl (hcop.of_dvd_right hln)
  have hlcmdiv : Nat.lcm (orderOf (q : ZMod l)) (orderOf (q : ZMod (n / l))) ∣
      (l - 1) * orderOf (q : ZMod (n / l)) :=
    Nat.lcm_dvd (dvd_mul_of_dvd_left hpdiv _) (Nat.dvd_mul_left _ _)
  have hTpos := order_pos (Nat.div_pos (Nat.le_of_dvd hn hln) hl.pos)
    (hcop.of_dvd_right (Nat.div_dvd_of_dvd hln))
  rw [← horder] at hlcmdiv
  have hle := Nat.le_of_dvd (Nat.mul_pos (by omega : 0 < l - 1) hTpos) hlcmdiv
  have hbad : l ≤ l - 1 := by nlinarith
  omega

end NSDensity
