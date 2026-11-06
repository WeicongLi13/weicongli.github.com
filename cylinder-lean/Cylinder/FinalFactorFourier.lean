import Cylinder.RedeiProjection

/-! The uniform-projection dichotomy for arbitrary factors in prime-field
coordinate spaces (Lemma 7.1), proved by averaging scalar dilations. -/

namespace Cylinder.FinalFactorFourier

open scoped BigOperators

variable {p m : ℕ} [hp : Fact p.Prime]

private theorem scalar_dilation (A B : Finset (Fin m → ZMod p))
    (tile : AddSubgroup.IsComplement (A : Set (Fin m → ZMod p)) B)
    (k : ZMod p) (hk : k ≠ 0) :
    Function.Bijective (fun ab : A × B => k • (ab.1 : Fin m → ZMod p) + ab.2) := by
  have hn : k.val ≠ 0 := by
    intro h
    apply hk
    rw [← ZMod.natCast_zmod_val k, h, Nat.cast_zero]
  have hcard := Fintype.card_of_bijective tile
  change Fintype.card (A × B) = Fintype.card (Fin m → ZMod p) at hcard
  have hcard' : Fintype.card A * Fintype.card B = p ^ m := by
    simpa [Fintype.card_prod, Fintype.card_fun] using hcard
  have hAdvd : Fintype.card A ∣ p ^ m := ⟨Fintype.card B, hcard'.symm⟩
  have hcp : k.val.Coprime p := by
    rw [Nat.coprime_comm, hp.out.coprime_iff_not_dvd]
    exact Nat.not_dvd_of_pos_of_lt (Nat.pos_of_ne_zero hn) (ZMod.val_lt k)
  have hc := Nat.Coprime.of_dvd_right hAdvd (hcp.pow_right m)
  have h := Cylinder.RedeiPlane.dilation_bijective (Subtype.val : A → Fin m → ZMod p)
    (Subtype.val : B → Fin m → ZMod p) tile k.val hn hc
  simpa only [← Nat.cast_smul_eq_nsmul (ZMod p), ZMod.natCast_zmod_val] using h

private theorem sum_linear_zero
    (L : (Fin m → ZMod p) →ₗ[ZMod p] ZMod p) (hL : L ≠ 0)
    (h : ZMod p → ℚ) (hh : ∑ t, h t = 0) (u : ZMod p) :
    (∑ x : Fin m → ZMod p, h (L x + u)) = 0 := by
  classical
  have hc (t : ZMod p) : (∑ x, h (L x + t)) = ∑ x, h (L x) := by
    obtain ⟨w, rfl⟩ := LinearMap.surjective hL t
    simpa [map_add] using Equiv.sum_comp (Equiv.addRight w) (fun x => h (L x))
  have hz : (∑ t : ZMod p, ∑ x, h (L x + t)) = 0 := by
    rw [Finset.sum_comm]
    exact Finset.sum_eq_zero (fun x _ => (Equiv.sum_comp (Equiv.addLeft (L x)) h).trans hh)
  simp_rw [hc] at hz
  have hmul : (p : ℚ) * (∑ x, h (L x)) = 0 := by simpa [nsmul_eq_mul] using hz
  rw [hc]
  exact (mul_eq_zero.mp hmul).resolve_left (by exact_mod_cast hp.out.ne_zero)

theorem uniform_projection_dichotomy (A B : Finset (Fin m → ZMod p))
    (tile : AddSubgroup.IsComplement (A : Set (Fin m → ZMod p)) B)
    (L : (Fin m → ZMod p) →ₗ[ZMod p] ZMod p) (hL : L ≠ 0) :
    (∀ t : ZMod p, p * (A.filter fun a => L a = t).card = A.card) ∨
    (∀ t : ZMod p, p * (B.filter fun b => L b = t).card = B.card) := by
  classical
  by_cases hA : ∀ t : ZMod p, p * (A.filter fun a => L a = t).card = A.card
  · exact Or.inl hA
  right
  push Not at hA
  obtain ⟨u, hu⟩ := hA
  have htest (h : ZMod p → ℚ) (hh : ∑ t, h t = 0) : (∑ b : B, h (L b)) = 0 := by
    let f (k : ZMod p) (ab : A × B) := h (k * (L ab.1 - u) + L ab.2)
    have hinner (ab : A × B) : (∑ k, f k ab) =
        if L ab.1 = u then (p : ℚ) * h (L ab.2) else 0 := by
      by_cases he : L ab.1 = u
      · simp [f, he, nsmul_eq_mul]
      · let e := (Equiv.mulRight₀ (L ab.1 - u) (sub_ne_zero.mpr he)).trans
          (Equiv.addRight (L ab.2))
        rw [if_neg he]
        change (∑ k, h (e k)) = 0
        exact (Equiv.sum_comp e h).trans hh
    have houter (k : ZMod p) (hk : k ≠ 0) : (∑ ab, f k ab) = 0 := by
      let e := Equiv.ofBijective _ (scalar_dilation A B tile k hk)
      calc
        ∑ ab, f k ab = ∑ ab, h (L (e ab) + (-(k * u))) := by
          apply Finset.sum_congr rfl
          intro ab _
          apply congrArg h
          change k * (L ab.1 - u) + L ab.2 = L (k • (ab.1 : Fin m → ZMod p) + ab.2) + (-(k*u))
          simp [map_add, map_smul]
          ring
        _ = ∑ x, h (L x + (-(k*u))) := Equiv.sum_comp e (fun x => h (L x + (-(k*u))))
        _ = 0 := sum_linear_zero L hL h hh _
    have he : (∑ k, ∑ ab, f k ab) = ∑ ab, ∑ k, f k ab := Finset.sum_comm
    rw [Finset.sum_eq_single (0 : ZMod p) (fun k _ hk => houter k hk) (by simp)] at he
    simp_rw [hinner] at he
    have hsum : (∑ ab : A × B, if L ab.1 = u then (p : ℚ) * h (L ab.2) else 0) =
        (A.filter fun a => L a = u).card * (p : ℚ) * (∑ b : B, h (L b)) := by
      rw [Fintype.sum_prod_type]
      have hby (a : A) :
          (∑ b : B, if L a = u then (p : ℚ) * h (L b) else 0) =
            (if L a = u then (p : ℚ) else 0) * (∑ b : B, h (L b)) := by
        by_cases ha : L a = u <;> simp [ha, Finset.mul_sum]
      simp_rw [hby]
      rw [← Finset.sum_mul]
      have hcount : (∑ a : A, if L a = u then (p : ℚ) else 0) =
          (A.filter fun a => L a = u).card * (p : ℚ) := by
        rw [Finset.sum_coe_sort A (fun a => if L a = u then (p : ℚ) else 0)]
        simp [← Finset.sum_filter, nsmul_eq_mul]
      rw [hcount]
    rw [hsum] at he
    have he' : (A.card : ℚ) * (∑ b : B, h (L b)) =
        (p : ℚ) * (A.filter fun a => L a = u).card * (∑ b : B, h (L b)) := by
      simpa [f, Fintype.sum_prod_type, nsmul_eq_mul, mul_assoc, mul_comm, mul_left_comm] using he
    have hne : (A.card : ℚ) ≠ (p : ℚ) * (A.filter fun a => L a = u).card := by
      intro heq
      apply hu
      exact_mod_cast heq.symm
    exact (mul_eq_mul_right_iff.mp he').resolve_left hne
  intro v
  let h (t : ZMod p) : ℚ := (if t = v then (p : ℚ) else 0) - 1
  have hh : ∑ t, h t = 0 := by simp [h, Finset.sum_sub_distrib, nsmul_eq_mul]
  have hz := htest h hh
  rw [Finset.sum_coe_sort B (fun b => h (L b))] at hz
  have he : ((B.filter fun b => L b = v).card : ℚ) * p - B.card = 0 := by
    simpa [h, Finset.sum_sub_distrib, ← Finset.sum_filter, nsmul_eq_mul] using hz
  exact_mod_cast (mul_comm _ _).trans (sub_eq_zero.mp he)

end Cylinder.FinalFactorFourier
