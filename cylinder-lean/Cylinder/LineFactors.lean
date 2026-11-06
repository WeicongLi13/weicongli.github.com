module

public import Cylinder.LineDivisibility
public import Mathlib.Algebra.Polynomial.RingDivision
public import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
public import Mathlib.Algebra.Prime.Lemmas
public import Mathlib.Tactic.Ring.Basic
public import Lean.Elab.Tactic.Omega

/-!
# Normalized affine line equations and their factors

Every line is represented either by `x₁ = c` or by
`x₀ = α + β*x₁`. The normalized equations are prime, have total
degree one, and distinct parameters give relatively prime equations.
-/

@[expose] public section

namespace Cylinder.LineFactors

open Cylinder.LineDivisibility

variable {K : Type*} [Field K]

abbrev Line (K : Type*) := K ⊕ (K × K)

noncomputable def equation : Line K → MvPolynomial (Fin 2) K
  | Sum.inl c => MvPolynomial.X 1 - MvPolynomial.C c
  | Sum.inr (α, β) => graphEquation α β

def point : Line K → K → (Fin 2 → K)
  | Sum.inl c, t => ![t, c]
  | Sum.inr (α, β), t => ![α + t * β, t]

noncomputable def linePoints [Fintype K] (L : Line K) : Finset (Fin 2 → K) := by
  classical
  exact Finset.univ.image (point L)

def VanishesOn (P : MvPolynomial (Fin 2) K) (L : Line K) : Prop :=
  ∀ t : K, MvPolynomial.eval (point L t) P = 0

noncomputable def swapVars : MvPolynomial (Fin 2) K ≃ₐ[K] MvPolynomial (Fin 2) K :=
  MvPolynomial.renameEquiv K (Equiv.swap (0 : Fin 2) 1)

theorem swapVars_horizontal (c : K) :
    swapVars (equation (Sum.inl c)) = graphEquation c 0 := by
  simp [swapVars, equation, graphEquation, MvPolynomial.renameEquiv_apply]

theorem swapVars_eval (P : MvPolynomial (Fin 2) K) (x : Fin 2 → K) :
    MvPolynomial.eval x (swapVars P) = MvPolynomial.eval ![x 1, x 0] P := by
  rw [swapVars, MvPolynomial.renameEquiv_apply, MvPolynomial.eval_rename]
  have he : x ∘ Equiv.swap (0 : Fin 2) 1 = ![x 1, x 0] := by
    funext i
    fin_cases i <;> simp
  rw [he]

theorem graphEquation_prime (α β : K) : Prime (graphEquation α β) := by
  apply (MulEquiv.prime_iff (MvPolynomial.finSuccEquiv K 1)).mp
  rw [graphEquation_image]
  exact Polynomial.prime_X_sub_C _

theorem equation_prime (L : Line K) : Prime (equation L) := by
  rcases L with c | ⟨α, β⟩
  · apply (MulEquiv.prime_iff (swapVars (K := K))).mp
    rw [swapVars_horizontal]
    exact graphEquation_prime c 0
  · exact graphEquation_prime α β

theorem equation_eval_point (L : Line K) (t : K) :
    MvPolynomial.eval (point L t) (equation L) = 0 := by
  rcases L with c | ⟨α, β⟩
  · simp [point, equation]
  · simp only [point, equation, graphEquation, map_sub, map_add, map_mul,
      MvPolynomial.eval_X, MvPolynomial.eval_C]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    ring

theorem equation_eval_zero_of_dvd (L : Line K) (P : MvPolynomial (Fin 2) K)
    (hdiv : equation L ∣ P) (t : K) : MvPolynomial.eval (point L t) P = 0 := by
  obtain ⟨Q, rfl⟩ := hdiv
  rw [map_mul, equation_eval_point, zero_mul]

/-- Distinct normalized parameters cannot describe scalar multiples of
the same line equation. The divisibility statement is proved by evaluating
at two actual points on the first line. -/
theorem equation_dvd_iff_eq (L M : Line K) : equation L ∣ equation M ↔ L = M := by
  constructor
  · intro hdiv
    have h0 := equation_eval_zero_of_dvd L (equation M) hdiv 0
    have h1 := equation_eval_zero_of_dvd L (equation M) hdiv 1
    rcases L with c | ⟨α, β⟩ <;> rcases M with d | ⟨γ, δ⟩
    · simp only [point, equation, map_sub, MvPolynomial.eval_X, MvPolynomial.eval_C,
        Matrix.cons_val_zero, Matrix.cons_val_one] at h0
      exact congrArg Sum.inl (sub_eq_zero.mp h0)
    · simp only [point, equation, graphEquation, map_sub, map_add, map_mul,
        MvPolynomial.eval_X, MvPolynomial.eval_C, Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1
      have hs : γ + δ * c = 0 := neg_eq_zero.mp (by simpa only [zero_sub] using h0)
      have hh : (1 : K) = 0 := by rw [hs, sub_zero] at h1; exact h1
      exact False.elim (one_ne_zero hh)
    · simp only [point, equation, map_sub, MvPolynomial.eval_X, MvPolynomial.eval_C,
        Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1
      have hc : d = 0 := neg_eq_zero.mp (by simpa only [zero_sub] using h0)
      rw [hc, sub_zero] at h1
      exact False.elim (one_ne_zero h1)
    · simp only [point, equation, graphEquation, map_sub, map_add, map_mul,
        MvPolynomial.eval_X, MvPolynomial.eval_C, Matrix.cons_val_zero, Matrix.cons_val_one,
        zero_mul, mul_zero, one_mul, mul_one, add_zero] at h0 h1
      have ha : α = γ := sub_eq_zero.mp h0
      have hb : β = δ := by rw [ha] at h1; exact add_left_cancel (sub_eq_zero.mp h1)
      exact congrArg Sum.inr (Prod.ext ha hb)
  · rintro rfl
    exact dvd_rfl

theorem equation_isRelPrime (L M : Line K) (hLM : L ≠ M) :
    IsRelPrime (equation L) (equation M) := by
  apply (equation_prime L).irreducible.isRelPrime_iff_not_dvd.mpr
  intro hdiv
  exact hLM ((equation_dvd_iff_eq L M).mp hdiv)

theorem equation_degree_le_one (L : Line K) : (equation L).totalDegree ≤ 1 := by
  rcases L with c | ⟨α, β⟩
  · simpa [equation] using MvPolynomial.totalDegree_sub_C_le
      (MvPolynomial.X (1 : Fin 2) : MvPolynomial (Fin 2) K) c
  · have hg : (MvPolynomial.C α + MvPolynomial.C β * MvPolynomial.X 1 :
        MvPolynomial (Fin 2) K).totalDegree ≤ 1 := by
      apply le_trans (MvPolynomial.totalDegree_add _ _)
      apply max_le
      · simp
      · exact le_trans (MvPolynomial.totalDegree_mul _ _) (by simp)
    apply le_trans (MvPolynomial.totalDegree_sub _ _)
    exact max_le (by simp) hg

theorem equation_totalDegree (L : Line K) : (equation L).totalDegree = 1 := by
  apply Nat.le_antisymm (equation_degree_le_one L)
  by_contra hn
  have hz : (equation L).totalDegree = 0 := Nat.eq_zero_of_not_pos (by omega)
  have he := MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp hz
  have hc : (equation L).coeff 0 ≠ 0 := by
    intro hzero
    apply (equation_prime L).ne_zero
    rw [he, hzero, map_zero]
  apply (equation_prime L).not_isUnit
  rw [he]
  exact (isUnit_iff_ne_zero.mpr hc).map MvPolynomial.C

/-- Low-degree finite-field vanishing gives a factor for either form of
normalized affine line. -/
theorem equation_dvd_of_vanishing [Fintype K]
    (P : MvPolynomial (Fin 2) K) (L : Line K)
    (hdegree : P.totalDegree < Fintype.card K) (hvanish : VanishesOn P L) :
    equation L ∣ P := by
  rcases L with c | ⟨α, β⟩
  · have hdegree' : (swapVars P).totalDegree < Fintype.card K := by
      simpa only [swapVars, MvPolynomial.totalDegree_renameEquiv] using hdegree
    have hv : ∀ t : K, MvPolynomial.eval ![c + t * 0, t] (swapVars P) = 0 := by
      intro t
      rw [swapVars_eval]
      simpa [VanishesOn, point] using hvanish t
    have hdiv := graphEquation_dvd_of_vanishing (swapVars P) c 0 hdegree' hv
    rw [← swapVars_horizontal] at hdiv
    exact (map_dvd_iff (swapVars (K := K))).mp hdiv
  · exact graphEquation_dvd_of_vanishing P α β hdegree hvanish

end Cylinder.LineFactors
