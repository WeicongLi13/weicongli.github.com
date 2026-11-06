module

public import Cylinder.PlaneLaurentFractionPieces

/-! Every Laurent piece on a pair of distinct coordinate opens has
an actual homogeneous-polynomial numerator after a finite common
coordinate denominator is chosen. -/

@[expose] public section
noncomputable section
open scoped Classical

namespace Cylinder.PlaneLaurentFractionNormalForm

open Cylinder.PlaneLaurentPieces Cylinder.PlaneLaurentDenominatorClearing
open Cylinder.PlaneLaurentFractionPieces Cylinder.PlaneLaurentHomogeneous

set_option autoImplicit false

variable {K : Type*} [CommRing K]

theorem shift_add (b c : Exponent) (f : Laurent K) : shift b (shift c f) = shift (b + c) f := by
  apply Finsupp.ext
  intro a
  simp only [shift_coeff]
  congr 1
  abel

theorem shift_neg_cancel (b : Exponent) (f : Laurent K) : shift (-b) (shift b f) = f := by
  apply Finsupp.ext
  intro a
  simp only [shift_coeff]
  congr 1
  abel

theorem denominator_pair_degree (i j : Fin 3) (hij : i ≠ j) (n : ℕ) :
    totalDegree (denominatorShift {i, j} n) = 2 * (n : ℤ) := by
  fin_cases i <;> fin_cases j <;> simp_all [totalDegree, denominatorShift] <;> omega

theorem negativeDenominator_eq (i j : Fin 3) (hij : i ≠ j) (n : ℕ) :
    negativeDenominator i j n n = -denominatorShift {i, j} n := by
  funext k
  by_cases hi : k = i
  · subst k
    simp [negativeDenominator, denominatorShift, hij]
  · by_cases hj : k = j
    · subst k
      simp [negativeDenominator, denominatorShift, hi]
    · simp [negativeDenominator, denominatorShift, hi, hj]

theorem shift_clears_poles_ge (v : ℤ) (I : Finset (Fin 3))
    (f : piece (K := K) v I) (n : ℕ) (hn : poleBound f.val ≤ n) :
    shift (denominatorShift I n) f.val ∈ piece (K := K) (v + totalDegree (denominatorShift I n)) ∅ := by
  let b := denominatorShift I n
  apply (mem_piece_iff _ _ _).mpr
  intro a ha
  have ha' : f.val (a - b) ≠ 0 := by simpa only [shift_coeff] using ha
  have hAllowed := (mem_piece_iff v I f.val).mp f.property (a - b) ha'
  constructor
  · have hsum := totalDegree_add (a - b) b
    rw [sub_add_cancel, hAllowed.1] at hsum
    exact hsum
  · intro i _
    by_cases hi : i ∈ I
    · have hbound := (poleBound_le f.val (a - b) (Finsupp.mem_support_iff.mpr ha') i).trans hn
      have hbi : b i = (n : ℤ) := by simp [b, denominatorShift, hi]
      have hb : (((-(a - b) i).toNat : ℕ) : ℤ) ≤ (n : ℤ) := by exact_mod_cast hbound
      have hself : -(a - b) i ≤ ((-(a - b) i).toNat : ℤ) := by omega
      change 0 ≤ a i
      change -(a i - b i) ≤ _ at hself
      omega
    · have hnonneg := hAllowed.2 i hi
      have hbi : b i = 0 := by simp [b, denominatorShift, hi]
      change 0 ≤ a i - b i at hnonneg
      simpa only [hbi, sub_zero] using hnonneg

theorem exists_fraction_normal_form (v : ℤ) (i j : Fin 3) (hij : i ≠ j)
    (f : piece (K := K) v {i, j}) :
    ∃ (w : ℤ) (_hw : 0 ≤ w) (a b : ℕ) (H : integerForms K w),
      w - a - b = v ∧
        f.val = shift (negativeDenominator i j a b) ((globalPieceEquivForms K w).symm H).val := by
  let n := poleBound f.val + (-v).toNat
  let w : ℤ := v + 2 * (n : ℤ)
  have hw : 0 ≤ w := by
    have hp : -v ≤ ((-v).toNat : ℤ) := by omega
    dsimp [w, n]
    omega
  have hc : shift (denominatorShift {i, j} n) f.val ∈ piece (K := K) w ∅ := by
    have h := shift_clears_poles_ge v {i, j} f n (by dsimp [n]; omega)
    simpa only [denominator_pair_degree i j hij] using h
  let g : piece (K := K) w ∅ := ⟨_, hc⟩
  refine ⟨w, hw, n, n, globalPieceEquivForms K w g, ?_, ?_⟩
  · dsimp [w]
    omega
  · rw [LinearEquiv.symm_apply_apply]
    change f.val = shift (negativeDenominator i j n n)
      (shift (denominatorShift {i, j} n) f.val)
    rw [negativeDenominator_eq i j hij, shift_neg_cancel]

end Cylinder.PlaneLaurentFractionNormalForm

end
