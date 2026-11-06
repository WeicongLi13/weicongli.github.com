module

public import Cylinder.FiniteFieldHyperplaneDivisibility
public import Cylinder.PowerSums
public import Cylinder.LinearFormFactors
public import Mathlib.Algebra.BigOperators.Ring.Finset

/-! The weighted plane-sum statement of Lemma 3.1, including the degree
bound for the actual reduced polynomial in three variables. -/

@[expose] public section
noncomputable section
open scoped Classical BigOperators

namespace Cylinder.FinalPlaneSums

open MvPolynomial Cylinder.PowerEvaluationRelation

variable (p : ℕ) [Fact p.Prime]

abbrev V := Fin 3 → ZMod p

def PlaneSumsZero (f : V p → ZMod p) : Prop :=
  ∀ u : V p, u ≠ 0 → ∀ t : ZMod p,
    ∑ x ∈ Finset.univ.filter (fun x => ∑ i, u i * x i = t), f x = 0

theorem weighted_linear_sum (f : V p → ZMod p) (hf : PlaneSumsZero p f)
    (u : V p) (hu : u ≠ 0) (φ : ZMod p → ZMod p) :
    ∑ x, f x * φ (∑ i, u i * x i) = 0 := by
  rw [← Finset.sum_fiberwise Finset.univ (fun x : V p => ∑ i, u i * x i)
    (fun x => f x * φ (∑ i, u i * x i))]
  apply Finset.sum_eq_zero
  intro t _
  calc
    _ = ∑ x ∈ Finset.univ.filter (fun x : V p => ∑ i, u i * x i = t), f x * φ t := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [(Finset.mem_filter.mp hx).2]
    _ = 0 := by rw [← Finset.sum_mul, hf u hu t, zero_mul]

theorem total_weight_zero (f : V p → ZMod p) (hf : PlaneSumsZero p f) : ∑ x, f x = 0 := by
  have hu : (Pi.single (0 : Fin 3) (1 : ZMod p) : V p) ≠ 0 := by
    intro h
    have := congrFun h 0
    simp at this
  simpa using weighted_linear_sum p f hf _ hu (fun _ => 1)

theorem powerSum_zero (f : V p → ZMod p) (hf : PlaneSumsZero p f)
    (d : ℕ) (hd : d < p) : powerSum (fun x : V p => x) f d = 0 := by
  apply Cylinder.FiniteGrid.eq_zero_of_degreeOf_lt_card
  · intro i
    have hh : (powerSum (fun x : V p => x) f d).IsHomogeneous d := by
      apply IsHomogeneous.sum
      intro x _
      simpa only [one_mul] using
        ((Cylinder.LinearFormFactors.linearForm_homogeneous x).pow d).C_mul (f x)
    exact (degreeOf_le_totalDegree _ _).trans_lt (by simpa only [ZMod.card] using hh.totalDegree_le.trans_lt hd)
  · intro u
    change eval u (∑ x, C (f x) * linearForm x ^ d) = 0
    simp only [map_sum, map_mul, eval_C, map_pow, Cylinder.FiniteFieldHyperplaneDivisibility.eval_linearForm]
    by_cases hu : u = 0
    · subst u
      simp only [Pi.zero_apply, mul_zero, Finset.sum_const_zero]
      rw [← Finset.sum_mul, total_weight_zero p f hf, zero_mul]
    · simpa only [mul_comm] using weighted_linear_sum p f hf u hu (fun t => t ^ d)

theorem weighted_polynomial_sum (f : V p → ZMod p) (hf : PlaneSumsZero p f)
    (G : MvPolynomial (Fin 3) (ZMod p)) (hG : G.totalDegree < p) :
    ∑ x, f x * eval x G = 0 := by
  conv_lhs => rw [G.as_sum]
  simp only [map_sum, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro n hn
  have hd : n.sum (fun _ a => a) < p := (le_totalDegree hn).trans_lt hG
  have hrel := relation_of_powerSum_eq_zero p (fun x : V p => x) f _ hd
    (powerSum_zero p f hf _ hd)
  exact hrel (monomial n (G.coeff n))
    (isHomogeneous_monomial _ (by simp only [Finsupp.degree_apply, Finsupp.sum]))

private theorem exponent_degree (n : Fin 3 →₀ ℕ) :
    n.sum (fun _ a => a) = n 0 + n 1 + n 2 := by
  rw [Finsupp.sum_fintype _ _ (fun _ => rfl)]
  simp [Fin.sum_univ_succ, add_assoc]

private theorem weighted_monomial_sum (a n : Fin 3 →₀ ℕ) (c : ZMod p) :
    (∑ x : V p, eval x (monomial a c) * ∏ i, x i ^ (p - 1 - n i)) =
      c * ∏ i : Fin 3, ∑ t : ZMod p, t ^ (a i + (p - 1 - n i)) := by
  simp only [eval_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _),
    mul_assoc, ← Finset.prod_mul_distrib, ← pow_add]
  rw [← Finset.mul_sum]
  exact congrArg (c * ·) (Fintype.prod_sum
    (fun (i : Fin 3) (t : ZMod p) => t ^ (a i + (p - 1 - n i)))).symm

theorem top_coefficient_extraction (F : MvPolynomial (Fin 3) (ZMod p))
    (n : Fin 3 →₀ ℕ) (hn : ∀ i, n i < p)
    (hdeg : F.totalDegree ≤ n.sum (fun _ a => a)) :
    (∑ x : V p, eval x F * ∏ i, x i ^ (p - 1 - n i)) = -(F.coeff n) := by
  conv_lhs => rw [F.as_sum]
  simp only [map_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  have ht (a : Fin 3 →₀ ℕ) (ha : a ∈ F.support) :
      (∑ x : V p, eval x (monomial a (F.coeff a)) * ∏ i, x i ^ (p - 1 - n i)) =
        if a = n then -(F.coeff a) else 0 := by
    rw [weighted_monomial_sum]
    by_cases he : a = n
    · subst a
      have heq (i : Fin 3) : n i + (p - 1 - n i) = p - 1 := by have := hn i; omega
      simp only [heq, Cylinder.PowerSums.prime_sum_pow_boundary]
      simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ite_true]
      ring
    · rw [ite_eq_right he]
      have hlow : ∃ i, a i < n i := by
        have hh := (le_totalDegree ha).trans hdeg
        rw [exponent_degree, exponent_degree] at hh
        by_contra! hno
        have h0 := hno 0
        have h1 := hno 1
        have h2 := hno 2
        apply he
        ext i
        fin_cases i
        · change a 0 = n 0
          omega
        · change a 1 = n 1
          omega
        · change a 2 = n 2
          omega
      obtain ⟨i, hi⟩ := hlow
      have hz : (∑ t : ZMod p, t ^ (a i + (p - 1 - n i))) = 0 :=
        Cylinder.PowerSums.prime_sum_pow_low p _ (by have := hn i; omega)
      rw [Finset.prod_eq_zero (Finset.mem_univ i) hz, mul_zero]
  rw [Finset.sum_congr rfl ht]
  by_cases hz : F.coeff n = 0 <;> simp [mem_support_iff, hz]

theorem reduced_totalDegree_le (f : V p → ZMod p) (hf : PlaneSumsZero p f)
    (F : MvPolynomial (Fin 3) (ZMod p)) (hF : ∀ x, eval x F = f x)
    (hred : ∀ i, F.degreeOf i < p) : F.totalDegree ≤ 2 * p - 3 := by
  have hp : 2 ≤ p := (Fact.out : p.Prime).two_le
  by_contra hbad
  have hF0 : F ≠ 0 := by intro hz; simp [hz] at hbad
  obtain ⟨n, hn, hmax⟩ := Finset.exists_mem_eq_sup F.support (support_nonempty.mpr hF0)
    (fun n => n.sum (fun _ a => a))
  have hdeg : F.totalDegree = n.sum (fun _ a => a) := hmax
  have hnr (i : Fin 3) : n i < p := (monomial_le_degreeOf i hn).trans_lt (hred i)
  let a : Fin 3 →₀ ℕ := Finsupp.equivFunOnFinite.symm (fun i => p - 1 - n i)
  have ha : a.sum (fun _ k => k) < p := by
    rw [exponent_degree]
    have h0 := hnr 0
    have h1 := hnr 1
    have h2 := hnr 2
    rw [exponent_degree] at hdeg
    change (p - 1 - n 0) + (p - 1 - n 1) + (p - 1 - n 2) < p
    omega
  have hmono : (monomial a (1 : ZMod p)).totalDegree < p :=
    (totalDegree_monomial_le _ _).trans_lt ha
  have he := weighted_polynomial_sum p f hf (monomial a 1) hmono
  have hex := top_coefficient_extraction p F n hnr hdeg.le
  have hh : (∑ x : V p, eval x F * ∏ i, x i ^ (p - 1 - n i)) = 0 := by
    simpa only [hF, eval_monomial, one_mul,
      Finsupp.prod_fintype _ _ (fun _ => pow_zero _), a, Finsupp.equivFunOnFinite_symm_apply_apply] using he
  rw [hh] at hex
  exact (mem_support_iff.mp hn) (neg_eq_zero.mp hex.symm)

end Cylinder.FinalPlaneSums

end
