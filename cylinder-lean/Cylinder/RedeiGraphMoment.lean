module

public import Cylinder.RedeiDivisibility
public import Cylinder.PowerSums
public import Mathlib.Algebra.Polynomial.Eval.Degree
public import Mathlib.Tactic.Linarith

/-! The first nonzero moment of a nonlinear polynomial graph, as used for
the small factor in the three-dimensional Rédei argument. -/

@[expose] public section
noncomputable section
namespace Cylinder.Redei
open scoped BigOperators Classical
open PowerEvaluationRelation Geometry

variable (p : ℕ) [Fact p.Prime]

/-- A polynomial of degree exactly p-1 has nonzero sum over the prime field. -/
theorem sum_eval_boundary (f : Polynomial (ZMod p)) (hf : f.natDegree = p-1) :
    (∑ x : ZMod p, f.eval x) = - f.leadingCoeff := by
  simp_rw [Polynomial.eval_eq_sum_range, hf]
  rw [Finset.sum_comm, Finset.sum_range_succ]
  have hlow : ∑ i ∈ Finset.range (p-1), ∑ x : ZMod p, f.coeff i * x^i = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    rw [← Finset.mul_sum, PowerSums.prime_sum_pow_low p i (Finset.mem_range.mp hi), mul_zero]
  rw [hlow, zero_add, ← Finset.mul_sum, PowerSums.prime_sum_pow_boundary]
  simp [Polynomial.leadingCoeff, hf]

/-- Euclidean division gives a low total exponent touching degree p-1. -/
theorem low_exponents (d : ℕ) (hd : 2 ≤ d) (hdp : d < p) :
    ∃ a b : ℕ, 0 < b ∧ a + b*d = p-1 ∧ 2*(a+b) ≤ p-1 := by
  let a := (p-1) % d
  let b := (p-1) / d
  have hdpos : 0 < d := by omega
  have hb : 0 < b := Nat.div_pos (by omega) hdpos
  have ha : a < d := Nat.mod_lt _ hdpos
  have heq : a + b*d = p-1 := by
    simpa only [a,b,Nat.mul_comm] using Nat.mod_add_div (p-1) d
  have hgap : a ≤ d-2 := by
    by_contra! h
    have had : d = a+1 := by omega
    have hdvd : d ∣ p := by
      refine ⟨b+1, ?_⟩
      rw [Nat.mul_add, Nat.mul_one, Nat.mul_comm d b]
      omega
    rcases (Fact.out : p.Prime).eq_one_or_self_of_dvd d hdvd with h1 | hp <;> omega
  have hm : a ≤ b*(d-2) := hgap.trans (Nat.le_mul_of_pos_left _ hb)
  have hprod : b*d = b*(d-2) + b*2 := by
    rw [← Nat.mul_add]
    congr 1
    omega
  exact ⟨a,b,hb,heq,by omega⟩

theorem graph_mixed_moment (f : Polynomial (ZMod p))
    (hf : 2 ≤ f.natDegree) (hfp : f.natDegree < p) :
    ∃ a b : ℕ, 0 < a+b ∧ 2*(a+b) ≤ p-1 ∧ (∑ x : ZMod p, x^a*(f.eval x)^b) ≠ 0 := by
  obtain ⟨a,b,hb,ht,hr⟩ := low_exponents p f.natDegree hf hfp
  refine ⟨a,b,by omega,hr,?_⟩
  intro hsum
  let P : Polynomial (ZMod p) := Polynomial.X ^ a * f ^ b
  have hfn : f ≠ 0 := by
    intro h
    simp [h] at hf
  have hPn : P ≠ 0 := mul_ne_zero (pow_ne_zero _ Polynomial.X_ne_zero) (pow_ne_zero _ hfn)
  have hPdeg : P.natDegree = p-1 := by
    dsimp only [P]
    rw [Polynomial.natDegree_mul (pow_ne_zero _ Polynomial.X_ne_zero) (pow_ne_zero _ hfn),
      Polynomial.natDegree_X_pow, Polynomial.natDegree_pow, ht]
  have hsum' : (∑ x : ZMod p, P.eval x) = 0 := by simpa [P] using hsum
  rw [sum_eval_boundary p P hPdeg, neg_eq_zero] at hsum'
  exact (Polynomial.leadingCoeff_ne_zero.mpr hPn) hsum'

/-- The graph coordinates in §7.1. The first coordinate makes the parameter injective. -/
def polynomialGraph (f : Polynomial (ZMod p)) (g : ZMod p → ZMod p) :
    Finset (Point p) := Finset.univ.image fun x => ![x,f.eval x,g x]

theorem graph_has_low_nonzero_moment (f : Polynomial (ZMod p)) (g : ZMod p → ZMod p)
    (hf : 2 ≤ f.natDegree) (hfp : f.natDegree < p) :
    ∃ r, 0 < r ∧ r ≤ (p-1)/2 ∧ moment p (polynomialGraph p f g) r ≠ 0 := by
  obtain ⟨a, b, hpos, hr, hnonzero⟩ := graph_mixed_moment p f hf hfp
  let V : ZMod p → Point p := fun x => ![x, f.eval x, g x]
  have hV : Function.Injective V := by
    intro x y he
    simpa [V] using congrFun he 0
  refine ⟨a+b, by omega, by omega, ?_⟩
  intro hz
  have hpower : powerSum V (fun _ => 1) (a+b) = 0 := by
    simpa [powerSum, moment, polynomialGraph, V, Finset.sum_image
      (fun x _ y _ he => hV he)] using hz
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have hrel := relation_of_powerSum_eq_zero p V (fun _ => 1) (a+b) (by omega) hpower
  have hhom :
      ((MvPolynomial.X (0 : Fin 3) : MvPolynomial (Fin 3) (ZMod p))^a *
        MvPolynomial.X 1 ^ b).IsHomogeneous (a+b) := by
    simpa only [one_mul] using
      ((MvPolynomial.isHomogeneous_X (ZMod p) (0 : Fin 3)).pow a).mul
      ((MvPolynomial.isHomogeneous_X (ZMod p) (1 : Fin 3)).pow b)
  have hzero := hrel _ hhom
  have hsum : (∑ x : ZMod p, x^a*(f.eval x)^b) = 0 := by simpa [V] using hzero
  exact hnonzero hsum

end Cylinder.Redei
end