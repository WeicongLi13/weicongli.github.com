module

public import Cylinder.PlaneLaurentPermutation

/-! Finite Laurent support gives an actual common coordinate
denominator. Translating by that denominator leaves no negative
exponents and preserves the literal coefficient functions. -/

@[expose] public section
noncomputable section
open scoped Classical

namespace Cylinder.PlaneLaurentDenominatorClearing

open Cylinder.PlaneLaurentPieces

set_option autoImplicit false

def translation (b : Exponent) : Exponent ≃ Exponent where
  toFun a := a + b
  invFun a := a - b
  left_inv a := by simp
  right_inv a := by simp

variable {K : Type*} [CommRing K]

def shift (b : Exponent) : Laurent K ≃ₗ[K] Laurent K := Finsupp.domLCongr (translation b)

theorem shift_coeff (b : Exponent) (f : Laurent K) (a : Exponent) :
    shift b f a = f (a - b) := rfl

def poleBound (f : Laurent K) : ℕ :=
  f.support.sup (fun a => Finset.univ.sup (fun i : Fin 3 => (-a i).toNat))

theorem poleBound_le (f : Laurent K) (a : Exponent) (ha : a ∈ f.support) (i : Fin 3) :
    (-a i).toNat ≤ poleBound f := by
  unfold poleBound
  exact (Finset.le_sup (s := Finset.univ) (f := fun i : Fin 3 => (-a i).toNat)
    (Finset.mem_univ i)).trans
      (Finset.le_sup (f := fun a : Exponent => Finset.univ.sup (fun i : Fin 3 => (-a i).toNat)) ha)

def denominatorShift (I : Finset (Fin 3)) (n : ℕ) : Exponent :=
  fun i => if i ∈ I then (n : ℤ) else 0

theorem totalDegree_add (a b : Exponent) :
    totalDegree (a + b) = totalDegree a + totalDegree b := by
  dsimp [totalDegree]
  abel

theorem shift_clears_poles (v : ℤ) (I : Finset (Fin 3)) (f : piece (K := K) v I) :
    shift (denominatorShift I (poleBound f.val)) f.val ∈
      piece (K := K) (v + totalDegree (denominatorShift I (poleBound f.val))) ∅ := by
  let b := denominatorShift I (poleBound f.val)
  apply (mem_piece_iff _ _ _).mpr
  intro a ha
  have ha' : f.val (a - b) ≠ 0 := by simpa only [shift_coeff] using ha
  have hAllowed := (mem_piece_iff v I f.val).mp f.property (a - b) ha'
  constructor
  · change totalDegree a = v + totalDegree b
    have hsum := totalDegree_add (a - b) b
    rw [sub_add_cancel] at hsum
    rw [hAllowed.1] at hsum
    exact hsum
  · intro i _
    by_cases hi : i ∈ I
    · have hbound := poleBound_le f.val (a - b) (Finsupp.mem_support_iff.mpr ha') i
      have hbi : b i = (poleBound f.val : ℤ) := by simp [b, denominatorShift, hi]
      have hn : -(a - b) i ≤ ((-(a - b) i).toNat : ℤ) := by omega
      have hb : (((-(a - b) i).toNat : ℕ) : ℤ) ≤ (poleBound f.val : ℤ) := by exact_mod_cast hbound
      change 0 ≤ a i
      change -(a i - b i) ≤ _ at hn
      omega
    · have hnonneg := hAllowed.2 i hi
      have hbi : b i = 0 := by simp [b, denominatorShift, hi]
      change 0 ≤ a i - b i at hnonneg
      simpa only [hbi, sub_zero] using hnonneg

end Cylinder.PlaneLaurentDenominatorClearing

end
