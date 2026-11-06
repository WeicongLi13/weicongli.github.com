module

public import Cylinder.BMMBlackLineBlocks

/-! The coordinate fibers of an actual normalized system are the
genuine height fibers for the corresponding row of a linear equivalence. -/

@[expose] public section
noncomputable section
open scoped Classical BigOperators

namespace Cylinder.BMMCoordinateFibers

open Cylinder.RationalPlaneLine Cylinder.PlaneCrossProduct Cylinder.BMMBlackLineBlocks

variable {K : Type*} [Field K]

def coordinateRow (g : (Fin 3 → K) ≃ₗ[K] (Fin 3 → K)) (i : Fin 3) : Fin 3 → K :=
  fun j => g (Pi.single j 1) i

theorem coordinateRow_apply (g : (Fin 3 → K) ≃ₗ[K] (Fin 3 → K)) (i : Fin 3) (x : Fin 3 → K) :
    dot (coordinateRow g i) x = g x i := by
  have hx : x = x 0 • (Pi.single 0 1 : Fin 3 → K) +
      x 1 • (Pi.single 1 1 : Fin 3 → K) + x 2 • (Pi.single 2 1 : Fin 3 → K) := by
    ext j
    fin_cases j <;> simp [Pi.single_apply, Pi.smul_apply, smul_eq_mul]
  conv_rhs => rw [hx, map_add, map_add, map_smul, map_smul, map_smul]
  simp [coordinateRow, dot, Fin.sum_univ_succ, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem coordinateRow_nonzero (g : (Fin 3 → K) ≃ₗ[K] (Fin 3 → K)) (i : Fin 3) :
    coordinateRow g i ≠ 0 := by
  intro hz
  have h := coordinateRow_apply g i (g.symm (Pi.single i 1))
  rw [hz, LinearEquiv.apply_symm_apply] at h
  have h01 : (0 : K) = 1 := by simpa [dot, Pi.single_apply] using h
  exact zero_ne_one h01

def coordinateBlacks (A : NormalizedSystem K) (g : (Fin 3 → K) ≃ₗ[K] (Fin 3 → K))
    (i : Fin 3) : Finset A.B := Finset.univ.filter (fun R => g R.val.rep i = 0)

def coordinateFiber (A : NormalizedSystem K) (g : (Fin 3 → K) ≃ₗ[K] (Fin 3 → K))
    (i : Fin 3) (a : K) : Finset A.W := Finset.univ.filter (fun P => g (A.E P) i = a)

theorem coordinateBlacks_eq (A : NormalizedSystem K) (g : (Fin 3 → K) ≃ₗ[K] (Fin 3 → K)) (i : Fin 3) :
    coordinateBlacks A g i = lineBlacks A (coordinateRow g i) := by
  ext R
  simp only [coordinateBlacks, lineBlacks, Finset.mem_filter, coordinateRow_apply]

theorem coordinateFiber_eq (A : NormalizedSystem K) (g : (Fin 3 → K) ≃ₗ[K] (Fin 3 → K))
    (i : Fin 3) (a : K) : coordinateFiber A g i a = whiteFiber A (coordinateRow g i) a := by
  ext P
  simp only [coordinateFiber, whiteFiber, height, Finset.mem_filter, coordinateRow_apply]

theorem coordinateFiber_card (A : NormalizedSystem K) (g : (Fin 3 → K) ≃ₗ[K] (Fin 3 → K))
    (i : Fin 3) (htwo : (2 : K) ≠ 0) (hm : 2 ≤ (coordinateBlacks A g i).card) (P : A.W) :
    (coordinateFiber A g i (g (A.E P) i)).card = (coordinateBlacks A g i).card := by
  rw [coordinateBlacks_eq] at hm ⊢
  rw [coordinateFiber_eq]
  have h := positive_fiber_card A (coordinateRow g i) (coordinateRow_nonzero g i) htwo hm P
  simpa only [height, coordinateRow_apply] using h

theorem negative_coordinateFiber_card (A : NormalizedSystem K) (g : (Fin 3 → K) ≃ₗ[K] (Fin 3 → K))
    (i : Fin 3) (htwo : (2 : K) ≠ 0) (hm : 2 ≤ (coordinateBlacks A g i).card) (P : A.W) :
    (coordinateFiber A g i (-g (A.E P) i)).card = (coordinateBlacks A g i).card := by
  rw [coordinateBlacks_eq] at hm ⊢
  rw [coordinateFiber_eq]
  have h := negative_fiber_card A (coordinateRow g i) P htwo
    (white_height_ne_zero A (coordinateRow g i) (coordinateRow_nonzero g i) hm P)
  simpa only [height, coordinateRow_apply] using h

theorem partner_coordinate_flip (A : NormalizedSystem K) (g : (Fin 3 → K) ≃ₗ[K] (Fin 3 → K))
    (i : Fin 3) (R : A.B) (hR : R ∈ coordinateBlacks A g i) (P : A.W) :
    g (A.E (partner A R P)) i = -g (A.E P) i := by
  rw [coordinateBlacks_eq] at hR
  simpa only [height, coordinateRow_apply] using partner_height_flip A (coordinateRow g i) R hR P

theorem unique_third_of_card_three {I : Type*} (F : Finset I) (hF : F.card = 3)
    (P Q X Y : I) (hP : P ∈ F) (hQ : Q ∈ F) (hPQ : P ≠ Q)
    (hX : X ∈ F) (hXP : X ≠ P) (hXQ : X ≠ Q)
    (hY : Y ∈ F) (hYP : Y ≠ P) (hYQ : Y ≠ Q) : X = Y := by
  have hQ' : Q ∈ F.erase P := Finset.mem_erase.mpr ⟨hPQ.symm, hQ⟩
  have hc : ((F.erase P).erase Q).card ≤ 1 := by
    rw [Finset.card_erase_of_mem hQ', Finset.card_erase_of_mem hP, hF]
  apply Finset.card_le_one.mp hc
  · exact Finset.mem_erase.mpr ⟨hXQ, Finset.mem_erase.mpr ⟨hXP, hX⟩⟩
  · exact Finset.mem_erase.mpr ⟨hYQ, Finset.mem_erase.mpr ⟨hYP, hY⟩⟩

end Cylinder.BMMCoordinateFibers

end
