module

public import Cylinder.PlaneLaurentDenominatorClearing
public import Cylinder.PlaneLaurentHomogeneous

/-! Dividing an actual homogeneous polynomial by powers of two
coordinates gives the corresponding Laurent piece with precisely
those possible poles. All exponent operations are literal translations. -/

@[expose] public section
noncomputable section
open scoped Classical

namespace Cylinder.PlaneLaurentFractionPieces

open Cylinder.PlaneLaurentPieces Cylinder.PlaneLaurentDenominatorClearing
open Cylinder.PlaneLaurentHomogeneous

set_option autoImplicit false

variable {K : Type*} [CommRing K]

theorem shift_mem_piece (v : ℤ) (I J : Finset (Fin 3)) (b : Exponent)
    (hIJ : I ⊆ J) (hb : ∀ i, i ∉ J → 0 ≤ b i) (f : piece (K := K) v I) :
    shift b f.val ∈ piece (K := K) (v + totalDegree b) J := by
  apply (mem_piece_iff _ _ _).mpr
  intro a ha
  have ha' : f.val (a - b) ≠ 0 := by simpa only [shift_coeff] using ha
  have hAllowed := (mem_piece_iff v I f.val).mp f.property (a - b) ha'
  constructor
  · have hsum := totalDegree_add (a - b) b
    rw [sub_add_cancel, hAllowed.1] at hsum
    exact hsum
  · intro i hi
    have hiI : i ∉ I := fun h => hi (hIJ h)
    have hn := hAllowed.2 i hiI
    have hp := hb i hi
    change 0 ≤ a i - b i at hn
    omega

def negativeDenominator (i j : Fin 3) (a b : ℕ) : Exponent :=
  fun k => -(if k = i then (a : ℤ) else 0) - (if k = j then (b : ℤ) else 0)

theorem negativeDenominator_degree (i j : Fin 3) (a b : ℕ) :
    totalDegree (negativeDenominator i j a b) = -(a : ℤ) - b := by
  fin_cases i <;> fin_cases j <;> simp [totalDegree, negativeDenominator] <;> ring

theorem negativeDenominator_outside (i j k : Fin 3) (a b : ℕ) (hk : k ∉ ({i, j} : Finset (Fin 3))) :
    negativeDenominator i j a b k = 0 := by
  have hi : k ≠ i := by simpa using fun h : k = i => hk (by simp [h])
  have hj : k ≠ j := by simpa using fun h : k = j => hk (by simp [h])
  simp [negativeDenominator, hi, hj]

def fractionPiece (d : ℤ) (i j : Fin 3) (a b : ℕ) :
    piece (K := K) d ∅ →ₗ[K] piece (K := K) (d - a - b) {i, j} where
  toFun f := ⟨shift (negativeDenominator i j a b) f.val, by
    have h := shift_mem_piece d ∅ {i, j} (negativeDenominator i j a b)
      (by simp) (fun k hk => by rw [negativeDenominator_outside i j k a b hk]) f
    simpa only [negativeDenominator_degree, sub_eq_add_neg, add_assoc] using h⟩
  map_add' f g := Subtype.ext ((shift (negativeDenominator i j a b)).map_add f.val g.val)
  map_smul' c f := Subtype.ext ((shift (negativeDenominator i j a b)).map_smul c f.val)

def polynomialPiece (d : ℕ) (H : MvPolynomial (Option (Fin 2)) K) (hH : H.IsHomogeneous d) :
    piece (K := K) (d : ℤ) ∅ :=
  (globalPieceEquivForms K (d : ℤ)).symm ⟨H, by
    rw [integerForms, ite_eq_left (Int.natCast_nonneg d)]
    simpa only [Int.toNat_natCast, MvPolynomial.mem_homogeneousSubmodule] using hH⟩

def polynomialFractionPiece (d a b : ℕ) (i j : Fin 3)
    (H : MvPolynomial (Option (Fin 2)) K) (hH : H.IsHomogeneous d) :
    piece (K := K) ((d : ℤ) - a - b) {i, j} :=
  fractionPiece (d : ℤ) i j a b (polynomialPiece d H hH)

theorem fractionPiece_coeff (d : ℤ) (i j : Fin 3) (a b : ℕ)
    (f : piece (K := K) d ∅) (e : Exponent) :
    (fractionPiece d i j a b f).val e = f.val (e - negativeDenominator i j a b) := rfl

end Cylinder.PlaneLaurentFractionPieces

end
