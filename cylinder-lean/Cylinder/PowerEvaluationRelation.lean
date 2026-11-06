module

public import Cylinder.EvaluationProjection
public import Mathlib.Algebra.MvPolynomial.Coeff
public import Mathlib.Algebra.CharP.Basic
public import Mathlib.Data.Nat.Prime.Factorial
public import Mathlib.Tactic.Ring

/-!
The coefficient comparison in `prop:product`.
For degree less than the characteristic, all relevant multinomial coefficients
are nonzero. A power identity therefore gives a relation on actual homogeneous
evaluation functionals. The converse is proved by testing against monomials.
-/

@[expose] public section
noncomputable section
open scoped Classical

namespace Cylinder.PowerEvaluationRelation

open MvPolynomial Finset

variable {K σ I : Type*} [Field K] [Fintype σ] [Fintype I]

def linearForm (a : σ → K) : MvPolynomial σ K := ∑ j, C (a j) * X j

def powerSum (v : I → σ → K) (c : I → K) (d : ℕ) : MvPolynomial σ K :=
  ∑ i, C (c i) * linearForm (v i) ^ d

/-- A relation on the true homogeneous degree-d evaluation map. -/
def Relation (v : I → σ → K) (c : I → K) (d : ℕ) : Prop :=
  ∀ F : MvPolynomial σ K, F.IsHomogeneous d → ∑ i, c i * eval (v i) F = 0

theorem coeff_linearForm_pow (a : σ → K) (m : σ →₀ ℕ) (d : ℕ) :
    (linearForm a ^ d).coeff m =
      if m.sum (fun _ n => n) = d then
        (m.multinomial : K) * m.prod (fun j n => a j ^ n) else 0 := by
  have heq : linearForm a = ∑ j, a j • (X j : MvPolynomial σ K) := by
    simp only [linearForm, smul_eq_C_mul]
  rw [heq, coeff_linearCombination_X_pow_of_fintype]

theorem coeff_powerSum (v : I → σ → K) (c : I → K) (d : ℕ) (m : σ →₀ ℕ)
    (hm : m.sum (fun _ n => n) = d) :
    (powerSum v c d).coeff m =
      (m.multinomial : K) * ∑ i, c i * m.prod (fun j n => v i j ^ n) := by
  simp only [powerSum, coeff_sum, coeff_C_mul, coeff_linearForm_pow, hm, ite_true]
  rw [mul_sum]
  apply sum_congr rfl
  intro i _
  ring

omit [Fintype σ] in
theorem multinomial_cast_ne_zero (p : ℕ) [Fact p.Prime] [CharP K p]
    (m : σ →₀ ℕ) (d : ℕ) (hm : m.sum (fun _ n => n) = d) (hd : d < p) :
    (m.multinomial : K) ≠ 0 := by
  intro hz
  have hmult : m.multinomial ∣ Nat.factorial d := by
    have hspec := Nat.multinomial_spec m.support m
    change (∏ j ∈ m.support, Nat.factorial (m j)) * m.multinomial =
      Nat.factorial (m.sum (fun _ n => n)) at hspec
    rw [hm] at hspec
    refine ⟨∏ j ∈ m.support, Nat.factorial (m j), ?_⟩
    simpa only [mul_comm] using hspec.symm
  have hpdvd := (CharP.cast_eq_zero_iff K p m.multinomial).mp hz
  have hpfact : p ∣ Nat.factorial d := dvd_trans hpdvd hmult
  have hp_le := ((Fact.out : p.Prime).dvd_factorial).mp hpfact
  omega

/-- The forward coefficient comparison, with the degree restriction checked. -/
theorem relation_of_powerSum_eq_zero (p : ℕ) [Fact p.Prime] [CharP K p]
    (v : I → σ → K) (c : I → K) (d : ℕ) (hd : d < p)
    (hzero : powerSum v c d = 0) : Relation v c d := by
  have hmom : ∀ m : σ →₀ ℕ, m.sum (fun _ n => n) = d →
      (∑ i, c i * m.prod (fun j n => v i j ^ n)) = 0 := by
    intro m hm
    have hcoef := congrArg (fun P : MvPolynomial σ K => P.coeff m) hzero
    rw [coeff_powerSum v c d m hm] at hcoef
    have hcoef' : (m.multinomial : K) *
        (∑ i, c i * m.prod (fun j n => v i j ^ n)) = 0 := by simpa using hcoef
    exact (mul_eq_zero.mp hcoef').resolve_left (multinomial_cast_ne_zero p m d hm hd)
  intro F hF
  have heval : ∀ i, eval (v i) F =
      ∑ m ∈ F.support, F.coeff m * m.prod (fun j n => v i j ^ n) := by
    intro i
    calc
      eval (v i) F = eval (v i) (∑ m ∈ F.support, monomial m (F.coeff m)) :=
        congrArg (eval (v i)) F.as_sum
      _ = _ := by simp only [map_sum, eval_monomial]
  calc
    ∑ i, c i * eval (v i) F =
        ∑ i, ∑ m ∈ F.support, c i * (F.coeff m * m.prod (fun j n => v i j ^ n)) := by
      simp only [heval, mul_sum]
    _ = ∑ m ∈ F.support, ∑ i, c i * (F.coeff m * m.prod (fun j n => v i j ^ n)) :=
      sum_comm
    _ = 0 := by
      apply sum_eq_zero
      intro m hm
      have hdeg : m.sum (fun _ n => n) = d := by
        simpa only [Finsupp.sum] using (hF.degree_eq_sum_deg_support hm).symm
      calc
        ∑ i, c i * (F.coeff m * m.prod (fun j n => v i j ^ n)) =
            F.coeff m * ∑ i, c i * m.prod (fun j n => v i j ^ n) := by
          rw [mul_sum]
          apply sum_congr rfl
          intro i _
          ring
        _ = 0 := by rw [hmom m hdeg, mul_zero]

theorem powerSum_eq_zero_of_relation (v : I → σ → K) (c : I → K) (d : ℕ)
    (hrel : Relation v c d) : powerSum v c d = 0 := by
  apply MvPolynomial.ext
  intro m
  by_cases hm : m.sum (fun _ n => n) = d
  · have hmon : (monomial m (1 : K)).IsHomogeneous d :=
      isHomogeneous_monomial 1 (by simpa only [Finsupp.degree_apply, Finsupp.sum] using hm)
    have hmoment := hrel _ hmon
    simp only [eval_monomial, one_mul] at hmoment
    rw [coeff_powerSum v c d m hm, hmoment, mul_zero]
    simp
  · simp [powerSum, coeff_C_mul, coeff_linearForm_pow, hm]

theorem powerSum_eq_zero_iff_relation (p : ℕ) [Fact p.Prime] [CharP K p]
    (v : I → σ → K) (c : I → K) (d : ℕ) (hd : d < p) :
    powerSum v c d = 0 ↔ Relation v c d :=
  ⟨relation_of_powerSum_eq_zero p v c d hd, powerSum_eq_zero_of_relation v c d⟩

end Cylinder.PowerEvaluationRelation

end
