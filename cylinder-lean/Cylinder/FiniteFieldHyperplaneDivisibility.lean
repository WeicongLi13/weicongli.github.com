module

public import Cylinder.FiniteGrid
public import Cylinder.PowerEvaluationRelation

/-! Vanishing on an actual finite-field hyperplane forces its linear
equation to divide a polynomial of degree below the field size. -/

@[expose] public section
noncomputable section
open scoped Classical BigOperators

namespace Cylinder.FiniteFieldHyperplaneDivisibility

open MvPolynomial Cylinder.PowerEvaluationRelation

variable {K σ τ : Type} [Field K] [Fintype σ]

theorem eval_linearForm (l x : σ → K) : eval x (linearForm l) = ∑ j, l j * x j := by
  simp [linearForm]

theorem totalDegree_linearForm_le (l : σ → K) : (linearForm l).totalDegree ≤ 1 := by
  apply totalDegree_finsetSum_le
  intro i _
  exact (totalDegree_mul _ _).trans (by simp)

theorem totalDegree_substitution_le (f : σ → MvPolynomial τ K)
    (hf : ∀ i, (f i).totalDegree ≤ 1) (P : MvPolynomial σ K) :
    (aeval f P).totalDegree ≤ P.totalDegree := by
  change (eval₂ C f P).totalDegree ≤ P.totalDegree
  rw [eval₂_eq']
  apply totalDegree_finsetSum_le
  intro m hm
  have hpows : ∀ i, (f i ^ m i).totalDegree ≤ m i := fun i =>
    (totalDegree_pow _ _).trans (by simpa only [mul_one] using Nat.mul_le_mul_left (m i) (hf i))
  have hprod : (∏ i, f i ^ m i).totalDegree ≤ ∑ i, m i :=
    (totalDegree_finsetProd _ _).trans (Finset.sum_le_sum (fun i _ => hpows i))
  have hsum : (∑ i, m i) ≤ P.totalDegree := by
    have h := le_totalDegree hm
    change m.degree ≤ P.totalDegree at h
    simpa only [Finsupp.degree_eq_sum] using h
  have hmul := totalDegree_mul (C (P.coeff m)) (∏ i, f i ^ m i)
  rw [totalDegree_C, zero_add] at hmul
  exact hmul.trans (hprod.trans hsum)

def projectionVariable (l : σ → K) (i j : σ) : MvPolynomial σ K :=
  X j - C ((l i)⁻¹ * (Pi.single i 1 : σ → K) j) * linearForm l

def projectionSubstitution (l : σ → K) (i : σ) : MvPolynomial σ K →ₐ[K] MvPolynomial σ K :=
  aeval (projectionVariable l i)

def projectionVector (l : σ → K) (i : σ) (x : σ → K) : σ → K :=
  x - ((l i)⁻¹ * eval x (linearForm l)) • Pi.single i 1

theorem projectionVariable_degree (l : σ → K) (i j : σ) :
    (projectionVariable l i j).totalDegree ≤ 1 := by
  apply (totalDegree_sub _ _).trans
  apply max_le
  · simp
  · exact (totalDegree_mul _ _).trans (by
      rw [totalDegree_C, zero_add]
      exact totalDegree_linearForm_le l)

theorem projectionSubstitution_degree (l : σ → K) (i : σ) (P : MvPolynomial σ K) :
    (projectionSubstitution l i P).totalDegree ≤ P.totalDegree :=
  totalDegree_substitution_le _ (projectionVariable_degree l i) P

theorem eval_projectionSubstitution (l : σ → K) (i : σ) (x : σ → K) (P : MvPolynomial σ K) :
    eval x (projectionSubstitution l i P) = eval (projectionVector l i x) P := by
  induction P using MvPolynomial.induction_on with
  | C c => simp [projectionSubstitution]
  | add P Q hP hQ => simpa only [map_add] using congrArg₂ (· + ·) hP hQ
  | mul_X P j hP =>
      rw [map_mul, map_mul, hP]
      simp [projectionSubstitution, projectionVariable, projectionVector, Pi.single_apply]

theorem projectionVector_on_hyperplane (l : σ → K) (i : σ) (hi : l i ≠ 0) (x : σ → K) :
    eval (projectionVector l i x) (linearForm l) = 0 := by
  rw [eval_linearForm]
  simp only [projectionVector, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, mul_sub,
    Finset.sum_sub_distrib]
  have hs : ∑ j, l j * (((l i)⁻¹ * eval x (linearForm l)) * (Pi.single i 1 : σ → K) j) =
      eval x (linearForm l) := by
    calc
      _ = ((l i)⁻¹ * eval x (linearForm l)) * ∑ j, l j * (Pi.single i 1 : σ → K) j := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = ((l i)⁻¹ * eval x (linearForm l)) * l i := by simp [Pi.single_apply]
      _ = eval x (linearForm l) := by field_simp
  rw [hs, ← eval_linearForm, sub_self]

theorem linearForm_dvd_sub_projection (l : σ → K) (i : σ) (P : MvPolynomial σ K) :
    linearForm l ∣ P - projectionSubstitution l i P := by
  induction P using MvPolynomial.induction_on with
  | C c => simp [projectionSubstitution]
  | add P Q hP hQ =>
      rw [map_add]
      convert dvd_add hP hQ using 1
      ring
  | mul_X P j hP =>
      have hX : linearForm l ∣ X j - projectionSubstitution l i (X j) := by
        refine ⟨C ((l i)⁻¹ * (Pi.single i 1 : σ → K) j), ?_⟩
        simp only [projectionSubstitution, aeval_X, projectionVariable]
        ring
      rw [map_mul]
      convert dvd_add (dvd_mul_of_dvd_left hP (X j))
        (dvd_mul_of_dvd_right hX (projectionSubstitution l i P)) using 1
      ring

theorem linearForm_dvd_of_vanishing [Fintype K] (l : σ → K) (hl : l ≠ 0)
    (H : MvPolynomial σ K) (hdegree : H.totalDegree < Fintype.card K)
    (hvanish : ∀ x : σ → K, eval x (linearForm l) = 0 → eval x H = 0) :
    linearForm l ∣ H := by
  obtain ⟨i, hi⟩ : ∃ i, l i ≠ 0 := by
    by_contra h
    apply hl
    funext j
    exact not_not.mp (fun hj => h ⟨j, hj⟩)
  have hz : projectionSubstitution l i H = 0 := by
    apply FiniteGrid.eq_zero_of_degreeOf_lt_card
    · intro j
      exact (degreeOf_le_totalDegree _ _).trans_lt
        ((projectionSubstitution_degree l i H).trans_lt hdegree)
    · intro x
      rw [eval_projectionSubstitution]
      exact hvanish _ (projectionVector_on_hyperplane l i hi x)
  simpa only [hz, sub_zero] using linearForm_dvd_sub_projection l i H

theorem zmod_linearForm_dvd_of_vanishing (p : ℕ) [Fact p.Prime]
    (l : σ → ZMod p) (hl : l ≠ 0) (H : MvPolynomial σ (ZMod p))
    (hdegree : H.totalDegree ≤ p - 1)
    (hvanish : ∀ x : σ → ZMod p, eval x (linearForm l) = 0 → eval x H = 0) :
    linearForm l ∣ H := by
  apply linearForm_dvd_of_vanishing l hl H _ hvanish
  rw [ZMod.card]
  have hp := (Fact.out : p.Prime).pos
  omega

end Cylinder.FiniteFieldHyperplaneDivisibility

end
