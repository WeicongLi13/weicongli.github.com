module

public import Cylinder.LocalCurveInterpolation

/-! Point recurrences on actual curve points force genuine cleared
polynomial identities. No polynomial recurrence is assumed. -/

@[expose] public section
noncomputable section

namespace Cylinder.LocalRecurrenceClearing

open MvPolynomial Cylinder.HilbertEvaluation Cylinder.LocalCurveInterpolation
open scoped Classical BigOperators

variable {K I : Type*} [Field K] [Infinite K] [Fintype I]

def firstCleared (A : PlaneRing K) (num : ℕ → PlaneRing K) (n : ℕ) : PlaneRing K :=
  A ^ 2 * num (n + 2) - A * num 1 * num (n + 1) + (num 1 ^ 2 - A * num 2) * num n

theorem firstCleared_homogeneous (A : PlaneRing K) (num : ℕ → PlaneRing K) (m N n : ℕ)
    (hA : A.IsHomogeneous m) (hnum : ∀ i ≤ N, (num i).IsHomogeneous (m + i))
    (hn : n + 2 ≤ N) : (firstCleared A num n).IsHomogeneous (3 * m + n + 2) := by
  have hfirst : (A ^ 2 * num (n + 2)).IsHomogeneous (3 * m + n + 2) := by
    convert (hA.pow 2).mul (hnum (n + 2) hn) using 1 <;> omega
  have hsecond : (A * num 1 * num (n + 1)).IsHomogeneous (3 * m + n + 2) := by
    convert (hA.mul (hnum 1 (by omega))).mul (hnum (n + 1) (by omega)) using 1 <;> omega
  have hcoefficient : (num 1 ^ 2 - A * num 2).IsHomogeneous (2 * m + 2) := by
    apply IsHomogeneous.sub
    · convert (hnum 1 (by omega)).pow 2 using 1 <;> omega
    · convert hA.mul (hnum 2 (by omega)) using 1 <;> omega
  have hthird : ((num 1 ^ 2 - A * num 2) * num n).IsHomogeneous (3 * m + n + 2) := by
    convert hcoefficient.mul (hnum n (by omega)) using 1 <;> omega
  exact (hfirst.sub hsecond).add hthird

theorem firstCleared_eval_zero (A : PlaneRing K) (num : ℕ → PlaneRing K) (x : Fin 3 → K)
    (h : ℕ → K) (N n : ℕ) (hn : n + 2 ≤ N)
    (hcommon : ∀ i ≤ N, eval x (num i) = eval x A * h i)
    (hrec : h (n + 2) = h 1 * h (n + 1) - (h 1 ^ 2 - h 2) * h n) :
    eval x (firstCleared A num n) = 0 := by
  simp only [firstCleared, map_add, map_sub, map_mul, map_pow]
  rw [hcommon (n + 2) hn, hcommon 1 (by omega), hcommon (n + 1) (by omega),
    hcommon 2 (by omega), hcommon n (by omega), hrec]
  ring

/-- Actual pointwise common numerators and recurrences force the first
cleared identities through the true pole threshold m+2. -/
theorem firstCleared_eq_zero (F A : PlaneRing K) (num : ℕ → PlaneRing K) (e m : ℕ)
    (hF : F.IsHomogeneous e) (hirr : Irreducible F) (hA : A.IsHomogeneous m)
    (hnum : ∀ i ≤ 2 * m + 2, (num i).IsHomogeneous (m + i))
    (hsmall : 4 * m + 2 < e)
    (v : I → Fin 3 → K) (hv : ∀ i, v i ≠ 0) (hsep : ProjectivelyDistinct v)
    (hFzero : ∀ i, eval (v i) F = 0) (T : Finset I) (h : I → ℕ → K)
    (hcommon : ∀ i ∈ T, ∀ n ≤ 2 * m + 2, eval (v i) (num n) = eval (v i) A * h i n)
    (hrec : ∀ i ∈ T, ∀ n, n + 2 ≤ 2 * m + 2 →
      h i (n + 2) = h i 1 * h i (n + 1) - (h i 1 ^ 2 - h i 2) * h i n)
    (hcard : e * (5 * m + 2) < T.card) (n : ℕ) (hn : n ≤ m) : firstCleared A num n = 0 := by
  apply polynomial_eq_zero_of_many_points F _ e (3 * m + n + 2) hF hirr
    (firstCleared_homogeneous A num m (2 * m + 2) n hA hnum (by omega)) (by omega)
    (fun i : T => v i.val) (fun i => hv i.val)
    (by intro i j hij c; exact hsep i.val j.val (fun heq => hij (Subtype.ext heq)) c)
  · intro i
    exact ⟨hFzero i.val, firstCleared_eval_zero A num (v i.val) (h i.val) (2 * m + 2) n
      (by omega) (hcommon i.val i.property) (hrec i.val i.property n (by omega))⟩
  · have hbound : e * (3 * m + n + 2) ≤ e * (5 * m + 2) := Nat.mul_le_mul_left e (by omega)
    simpa only [Fintype.card_coe] using lt_of_le_of_lt hbound hcard

def secondCleared (A f : PlaneRing K) (num : ℕ → PlaneRing K) (n : ℕ) : PlaneRing K :=
  A * num (n + 2) - A * f * num (n + 1) + (A * f ^ 2 - num 2) * num n

theorem secondCleared_homogeneous (A f : PlaneRing K) (num : ℕ → PlaneRing K) (m N n : ℕ)
    (hA : A.IsHomogeneous m) (hf : f.IsHomogeneous 1)
    (hnum : ∀ i ≤ N, (num i).IsHomogeneous (m + i)) (hn : n + 2 ≤ N) :
    (secondCleared A f num n).IsHomogeneous (2 * m + n + 2) := by
  have hfirst : (A * num (n + 2)).IsHomogeneous (2 * m + n + 2) := by
    convert hA.mul (hnum (n + 2) hn) using 1 <;> omega
  have hsecond : (A * f * num (n + 1)).IsHomogeneous (2 * m + n + 2) := by
    convert (hA.mul hf).mul (hnum (n + 1) (by omega)) using 1 <;> omega
  have hcoefficient : (A * f ^ 2 - num 2).IsHomogeneous (m + 2) := by
    apply IsHomogeneous.sub
    · convert hA.mul (hf.pow 2) using 1 <;> omega
    · exact hnum 2 (by omega)
  have hthird : ((A * f ^ 2 - num 2) * num n).IsHomogeneous (2 * m + n + 2) := by
    convert hcoefficient.mul (hnum n (by omega)) using 1 <;> omega
  exact (hfirst.sub hsecond).add hthird

theorem secondCleared_eval_zero (A f : PlaneRing K) (num : ℕ → PlaneRing K) (x : Fin 3 → K)
    (h : ℕ → K) (N n : ℕ) (hn : n + 2 ≤ N) (hfirst : num 1 = A * f)
    (hcommon : ∀ i ≤ N, eval x (num i) = eval x A * h i)
    (hrec : h (n + 2) = h 1 * h (n + 1) - (h 1 ^ 2 - h 2) * h n) :
    eval x (secondCleared A f num n) = 0 := by
  by_cases hAz : eval x A = 0
  · simp only [secondCleared, map_add, map_sub, map_mul, map_pow]
    rw [hcommon (n + 2) hn, hcommon (n + 1) (by omega), hcommon 2 (by omega), hcommon n (by omega), hAz]
    ring
  · have hfval : eval x f = h 1 := by
      apply mul_left_cancel₀ hAz
      have hh := hcommon 1 (by omega)
      rw [hfirst, map_mul] at hh
      exact hh
    simp only [secondCleared, map_add, map_sub, map_mul, map_pow]
    rw [hcommon (n + 2) hn, hcommon (n + 1) (by omega), hcommon 2 (by omega),
      hcommon n (by omega), hfval, hrec]
    ring

/-- Once the first numerator is actually A*f, point recurrences force
the second cleared identities through the true quadratic pole threshold. -/
theorem secondCleared_eq_zero (F A f : PlaneRing K) (num : ℕ → PlaneRing K) (e m : ℕ)
    (hF : F.IsHomogeneous e) (hirr : Irreducible F) (hA : A.IsHomogeneous m) (hf : f.IsHomogeneous 1)
    (hnum : ∀ i ≤ 2 * m + 2, (num i).IsHomogeneous (m + i)) (hfirst : num 1 = A * f)
    (hsmall : 4 * m + 2 < e)
    (v : I → Fin 3 → K) (hv : ∀ i, v i ≠ 0) (hsep : ProjectivelyDistinct v)
    (hFzero : ∀ i, eval (v i) F = 0) (T : Finset I) (h : I → ℕ → K)
    (hcommon : ∀ i ∈ T, ∀ n ≤ 2 * m + 2, eval (v i) (num n) = eval (v i) A * h i n)
    (hrec : ∀ i ∈ T, ∀ n, n + 2 ≤ 2 * m + 2 →
      h i (n + 2) = h i 1 * h i (n + 1) - (h i 1 ^ 2 - h i 2) * h i n)
    (hcard : e * (5 * m + 2) < T.card) (n : ℕ) (hn : n ≤ 2 * m) : secondCleared A f num n = 0 := by
  apply polynomial_eq_zero_of_many_points F _ e (2 * m + n + 2) hF hirr
    (secondCleared_homogeneous A f num m (2 * m + 2) n hA hf hnum (by omega)) (by omega)
    (fun i : T => v i.val) (fun i => hv i.val)
    (by intro i j hij c; exact hsep i.val j.val (fun heq => hij (Subtype.ext heq)) c)
  · intro i
    exact ⟨hFzero i.val, secondCleared_eval_zero A f num (v i.val) (h i.val) (2 * m + 2) n
      (by omega) hfirst (hcommon i.val i.property) (hrec i.val i.property n (by omega))⟩
  · have hbound : e * (2 * m + n + 2) ≤ e * (5 * m + 2) := Nat.mul_le_mul_left e (by omega)
    simpa only [Fintype.card_coe] using lt_of_le_of_lt hbound hcard

#print axioms firstCleared_eq_zero
#print axioms secondCleared_eq_zero

end Cylinder.LocalRecurrenceClearing

end
