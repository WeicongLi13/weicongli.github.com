module

public import Cylinder.BMMTriangleBlockers

/-! Products of the actual white and black coordinate ratios. The black
complement through a triangle vertex is the off-triangle black set plus
the opposite side blocker. -/

@[expose] public section
noncomputable section
open scoped Classical BigOperators

namespace Cylinder.BMMTriangleProducts

open Cylinder.BMMTriangleBlockers Cylinder.BMMFrameRatios

variable {K : Type*} [Field K]

def whiteRatio (T : Triangle K) (R : T.W) (i : Fin 3) : K :=
  whiteCoordinates T R (next i) / whiteCoordinates T R (previous i)

def blackRatio (T : Triangle K) (R : T.B) (i : Fin 3) : K :=
  blackCoordinates T R (next i) / blackCoordinates T R (previous i)

def whiteProduct (T : Triangle K) (i : Fin 3) : K := ∏ R ∈ offTriangleWhites T, whiteRatio T R i

def blackProduct (T : Triangle K) (i : Fin 3) : K := ∏ R ∈ offTriangleBlacks T, blackRatio T R i

def blackComplementAt (T : Triangle K) (i : Fin 3) : Finset T.B :=
  Finset.univ.filter (fun R => R ≠ sideBlocker T (next i) ∧ R ≠ sideBlocker T (previous i))

theorem index_trichotomy (i j : Fin 3) : j = i ∨ j = next i ∨ j = previous i := by
  fin_cases i <;> fin_cases j <;> simp [next, previous]

theorem coordinate_ratio_cycle (x : Fin 3 → K) (hx : ∀ i, x i ≠ 0) :
    (∏ i : Fin 3, x (next i) / x (previous i)) = 1 := by
  simp [Fin.prod_univ_succ, next, previous]
  field_simp [hx 0, hx 1, hx 2]

theorem white_product_cycle (T : Triangle K) : (∏ i : Fin 3, whiteProduct T i) = 1 := by
  unfold whiteProduct
  rw [Finset.prod_comm]
  apply Finset.prod_eq_one
  intro R hR
  exact coordinate_ratio_cycle (whiteCoordinates T R) (offTriangle_white_coordinates_nonzero T R hR)

theorem black_product_cycle (T : Triangle K) : (∏ i : Fin 3, blackProduct T i) = 1 := by
  unfold blackProduct
  rw [Finset.prod_comm]
  apply Finset.prod_eq_one
  intro R hR
  exact coordinate_ratio_cycle (blackCoordinates T R) (offTriangle_black_coordinates_nonzero T R hR)

theorem white_product_ne_zero (T : Triangle K) (i : Fin 3) : whiteProduct T i ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro R hR
  exact div_ne_zero (offTriangle_white_coordinates_nonzero T R hR (next i))
    (offTriangle_white_coordinates_nonzero T R hR (previous i))

theorem black_product_ne_zero (T : Triangle K) (i : Fin 3) : blackProduct T i ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro R hR
  exact div_ne_zero (offTriangle_black_coordinates_nonzero T R hR (next i))
    (offTriangle_black_coordinates_nonzero T R hR (previous i))

theorem side_ratio_ne_zero (T : Triangle K) (i : Fin 3) : blackRatio T (sideBlocker T i) i ≠ 0 := by
  have h := black_two_coordinates_not_zero T (sideBlocker T i) i (side_coordinate_zero T i)
  exact div_ne_zero h.1 h.2

theorem side_not_offTriangle (T : Triangle K) (i : Fin 3) : sideBlocker T i ∉ offTriangleBlacks T := by
  intro h
  exact (Finset.mem_filter.mp h).2 i rfl

theorem blackComplementAt_eq_insert_side (T : Triangle K) (i : Fin 3) :
    blackComplementAt T i = insert (sideBlocker T i) (offTriangleBlacks T) := by
  ext R
  simp only [blackComplementAt, offTriangleBlacks, Finset.mem_filter, Finset.mem_univ,
    true_and, Finset.mem_insert]
  constructor
  · intro h
    by_cases hRi : R = sideBlocker T i
    · exact Or.inl hRi
    · refine Or.inr (fun j => ?_)
      rcases index_trichotomy i j with hji | hji | hji
      · exact hji ▸ hRi
      · exact hji ▸ h.1
      · exact hji ▸ h.2
  · rintro (rfl | h)
    · exact ⟨fun h => next_ne i ((sideBlocker_injective T h).symm),
        fun h => previous_ne i ((sideBlocker_injective T h).symm)⟩
    · exact ⟨h (next i), h (previous i)⟩

theorem black_complement_ratio_product (T : Triangle K) (i : Fin 3) :
    (∏ R ∈ blackComplementAt T i, blackRatio T R i) =
      blackRatio T (sideBlocker T i) i * blackProduct T i := by
  rw [blackComplementAt_eq_insert_side, Finset.prod_insert (side_not_offTriangle T i)]
  rfl

end Cylinder.BMMTriangleProducts

end
