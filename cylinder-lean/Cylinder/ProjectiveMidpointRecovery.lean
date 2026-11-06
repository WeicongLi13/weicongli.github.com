module

public import Cylinder.ProjectiveSecantCounting
public import Cylinder.LineAffineCoordinates

/-! Recovery of the midpoint and the unordered other pair among the
three finite points on a genuine four-point projective line. The
characteristic-three exception is explicit. -/

@[expose] public section
noncomputable section
open scoped Classical BigOperators

namespace Cylinder.ProjectiveMidpointRecovery

open Cylinder.RationalPlaneLine Cylinder.PlaneCrossProduct Cylinder.LineAffineCoordinates

variable {K : Type*} [Field K]

theorem midpoint_unique {I : Type*} (C : Finset I) (τ : I → K)
    (hτ : Function.Injective (fun P : C => τ P.val)) (hthree : (3 : K) ≠ 0)
    (D D' : C) (hD : (∑ P ∈ C.erase D.val, τ P) = 2 * τ D.val)
    (hD' : (∑ P ∈ C.erase D'.val, τ P) = 2 * τ D'.val) : D = D' := by
  apply hτ
  apply mul_left_cancel₀ hthree
  calc
    3 * τ D.val = τ D.val + 2 * τ D.val := by ring
    _ = ∑ P ∈ C, τ P := by rw [← hD, Finset.add_sum_erase C τ D.property]
    _ = τ D'.val + 2 * τ D'.val := by rw [← hD', Finset.add_sum_erase C τ D'.property]
    _ = 3 * τ D'.val := by ring

theorem second_coordinate_nonzero_off_infinity
    (g : (Fin 3 → K) ≃ₗ[K] (Fin 3 → K)) (B : Finset (PlanePoint K)) (R : PlanePoint K)
    (hR : R ∈ B) (hline : ∀ P ∈ B, g P.rep 0 = 0) (hRone : g R.rep 1 = 0) :
    ∀ P ∈ B.erase R, g P.rep 1 ≠ 0 := by
  have hRtwo : g R.rep 2 ≠ 0 := by
    intro hz
    apply R.rep_nonzero
    apply g.injective
    rw [map_zero]
    funext i
    fin_cases i
    · exact hline R hR
    · exact hRone
    · exact hz
  intro P hP hPone
  obtain ⟨hPR, hPB⟩ := Finset.mem_erase.mp hP
  let a := g P.rep 2 / g R.rep 2
  have hp : g P.rep = a • g R.rep := by
    funext i
    fin_cases i
    · change g P.rep 0 = a * g R.rep 0
      rw [hline P hPB, hline R hR, mul_zero]
    · change g P.rep 1 = a * g R.rep 1
      rw [hPone, hRone, mul_zero]
    · change g P.rep 2 = (g P.rep 2 / g R.rep 2) * g R.rep 2
      rw [div_mul_cancel₀ _ hRtwo]
  exact representatives_not_proportional R P hPR.symm a (g.injective (by rw [map_smul]; exact hp))

theorem line_parameter_injective_off_infinity
    (g : (Fin 3 → K) ≃ₗ[K] (Fin 3 → K)) (B : Finset (PlanePoint K)) (R : PlanePoint K)
    (hR : R ∈ B) (hline : ∀ P ∈ B, g P.rep 0 = 0) (hRone : g R.rep 1 = 0) :
    Function.Injective (fun P : B.erase R => lineParameter g P.val) :=
  lineParameter_injective g (B.erase R) (fun P hP => hline P (Finset.mem_erase.mp hP).2)
    (second_coordinate_nonzero_off_infinity g B R hR hline hRone)

theorem four_point_midpoint_pair_unique
    (g : (Fin 3 → K) ≃ₗ[K] (Fin 3 → K)) (B : Finset (PlanePoint K)) (R : PlanePoint K)
    (hR : R ∈ B) (hB : B.card = 4) (hline : ∀ P ∈ B, g P.rep 0 = 0)
    (hRone : g R.rep 1 = 0) (hthree : (3 : K) ≠ 0)
    (D D' : B.erase R)
    (hD : (∑ P ∈ (B.erase R).erase D.val, lineParameter g P) = 2 * lineParameter g D.val)
    (hD' : (∑ P ∈ (B.erase R).erase D'.val, lineParameter g P) = 2 * lineParameter g D'.val) :
    D = D' ∧ (B.erase R).erase D.val = (B.erase R).erase D'.val ∧
      ((B.erase R).erase D.val).card = 2 := by
  have heq := midpoint_unique (B.erase R) (lineParameter g)
    (line_parameter_injective_off_infinity g B R hR hline hRone) hthree D D' hD hD'
  refine ⟨heq, by rw [heq], ?_⟩
  rw [Finset.card_erase_of_mem D.property, Finset.card_erase_of_mem hR, hB]

end Cylinder.ProjectiveMidpointRecovery

end
