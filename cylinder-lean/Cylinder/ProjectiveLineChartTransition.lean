module

public import Cylinder.ProjectiveMidpointRecovery

/-! The finite parameters in two genuine charts of the same projective
line, with the same point at infinity, differ by an invertible affine
map. Midpoint recovery is therefore independent of the chosen chart. -/

@[expose] public section
noncomputable section
open scoped Classical BigOperators

namespace Cylinder.ProjectiveLineChartTransition

open Cylinder.RationalPlaneLine Cylinder.LineAffineCoordinates Cylinder.ProjectiveMidpointRecovery

variable {K : Type*} [Field K]

theorem last_two_expansion (x : Fin 3 → K) (hx : x 0 = 0) :
    x = x 1 • Pi.single (1 : Fin 3) 1 + x 2 • Pi.single (2 : Fin 3) 1 := by
  ext i
  fin_cases i
  · simpa using hx
  · simp
  · simp

theorem last_coordinate_nonzero (g : (Fin 3 → K) ≃ₗ[K] (Fin 3 → K)) (R : PlanePoint K)
    (hR0 : g R.rep 0 = 0) (hR1 : g R.rep 1 = 0) : g R.rep 2 ≠ 0 := by
  intro hz
  apply R.rep_nonzero
  apply g.injective
  rw [map_zero]
  funext i
  fin_cases i
  · exact hR0
  · exact hR1
  · exact hz

theorem exists_affine_parameter_transition
    (g g' : (Fin 3 → K) ≃ₗ[K] (Fin 3 → K)) (B : Finset (PlanePoint K)) (R : PlanePoint K)
    (hR : R ∈ B) (hcard : 2 ≤ B.card)
    (hline : ∀ P ∈ B, g P.rep 0 = 0) (hline' : ∀ P ∈ B, g' P.rep 0 = 0)
    (hRone : g R.rep 1 = 0) (hRone' : g' R.rep 1 = 0) :
    ∃ a : K, a ≠ 0 ∧ ∃ b : K,
      ∀ P ∈ B.erase R, lineParameter g' P = a * lineParameter g P + b := by
  let e1 : Fin 3 → K := Pi.single 1 1
  let e2 : Fin 3 → K := Pi.single 2 1
  let q := g.symm.trans g'
  have hRtwo := last_coordinate_nonzero g R (hline R hR) hRone
  have hRtwo' := last_coordinate_nonzero g' R (hline' R hR) hRone'
  have hRexp : g R.rep = g R.rep 2 • e2 := by
    calc
      g R.rep = g R.rep 1 • e1 + g R.rep 2 • e2 := last_two_expansion _ (hline R hR)
      _ = _ := by rw [hRone, zero_smul, zero_add]
  have hscaled : g R.rep 2 • q e2 = g' R.rep := by
    rw [← map_smul, ← hRexp]
    simp only [q, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
  have hqe2 : q e2 = (g R.rep 2)⁻¹ • g' R.rep := by
    calc
      q e2 = (g R.rep 2)⁻¹ • (g R.rep 2 • q e2) := by
        rw [smul_smul, inv_mul_cancel₀ hRtwo, one_smul]
      _ = _ := congrArg (fun z : Fin 3 → K => (g R.rep 2)⁻¹ • z) hscaled
  have hq21 : q e2 1 = 0 := by
    rw [hqe2]
    change (g R.rep 2)⁻¹ * g' R.rep 1 = 0
    rw [hRone', mul_zero]
  have hq22 : q e2 2 ≠ 0 := by
    rw [hqe2]
    exact mul_ne_zero (inv_ne_zero hRtwo) hRtwo'
  have hchange (P : PlanePoint K) (hP : P ∈ B) :
      g' P.rep = g P.rep 1 • q e1 + g P.rep 2 • q e2 := by
    calc
      g' P.rep = q (g P.rep) := by
        simp only [q, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
      _ = _ := by
        simpa only [map_add, map_smul] using congrArg q (last_two_expansion (g P.rep) (hline P hP))
  let α := q e1 1
  let β := q e1 2
  let γ := q e2 2
  have hone (P : PlanePoint K) (hP : P ∈ B) : g' P.rep 1 = g P.rep 1 * α := by
    have hh := congrFun (hchange P hP) (1 : Fin 3)
    simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hq21, mul_zero, add_zero] using hh
  have htwo (P : PlanePoint K) (hP : P ∈ B) :
      g' P.rep 2 = g P.rep 1 * β + g P.rep 2 * γ := congrFun (hchange P hP) (2 : Fin 3)
  have hpunctured : (B.erase R).Nonempty := Finset.card_pos.mp (by
    rw [Finset.card_erase_of_mem hR]
    omega)
  obtain ⟨S, hS⟩ := hpunctured
  have hα : α ≠ 0 := by
    intro hz
    have hSone := second_coordinate_nonzero_off_infinity g' B R hR hline' hRone' S hS
    apply hSone
    rw [hone S (Finset.mem_erase.mp hS).2, hz, mul_zero]
  refine ⟨γ / α, div_ne_zero hq22 hα, -β / α, ?_⟩
  intro P hP
  have hPone := second_coordinate_nonzero_off_infinity g B R hR hline hRone P hP
  simp only [lineParameter]
  rw [hone P (Finset.mem_erase.mp hP).2, htwo P (Finset.mem_erase.mp hP).2]
  field_simp
  ring

theorem four_point_midpoint_chart_iff
    (g g' : (Fin 3 → K) ≃ₗ[K] (Fin 3 → K)) (B : Finset (PlanePoint K)) (R : PlanePoint K)
    (hR : R ∈ B) (hcard : B.card = 4)
    (hline : ∀ P ∈ B, g P.rep 0 = 0) (hline' : ∀ P ∈ B, g' P.rep 0 = 0)
    (hRone : g R.rep 1 = 0) (hRone' : g' R.rep 1 = 0) (D : B.erase R) :
    ((∑ P ∈ (B.erase R).erase D.val, lineParameter g' P) = 2 * lineParameter g' D.val) ↔
      ((∑ P ∈ (B.erase R).erase D.val, lineParameter g P) = 2 * lineParameter g D.val) := by
  obtain ⟨a, ha, b, hchange⟩ := exists_affine_parameter_transition g g' B R hR (by omega)
    hline hline' hRone hRone'
  have hpaircard : ((B.erase R).erase D.val).card = 2 := by
    rw [Finset.card_erase_of_mem D.property, Finset.card_erase_of_mem hR, hcard]
  have hsum : (∑ P ∈ (B.erase R).erase D.val, lineParameter g' P) =
      a * (∑ P ∈ (B.erase R).erase D.val, lineParameter g P) + 2 * b := by
    calc
      _ = ∑ P ∈ (B.erase R).erase D.val, (a * lineParameter g P + b) :=
        Finset.sum_congr rfl (fun P hP => hchange P (Finset.mem_erase.mp hP).2)
      _ = _ := by simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
        nsmul_eq_mul, hpaircard, Nat.cast_ofNat]
  rw [hsum, hchange D.val D.property]
  constructor
  · intro h
    have hz : a * ((∑ P ∈ (B.erase R).erase D.val, lineParameter g P) -
        2 * lineParameter g D.val) = 0 := by linear_combination h
    exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left ha)
  · intro h
    rw [h]
    ring

theorem four_point_midpoint_pair_unique_across_charts
    (g g' : (Fin 3 → K) ≃ₗ[K] (Fin 3 → K)) (B : Finset (PlanePoint K)) (R : PlanePoint K)
    (hR : R ∈ B) (hcard : B.card = 4)
    (hline : ∀ P ∈ B, g P.rep 0 = 0) (hline' : ∀ P ∈ B, g' P.rep 0 = 0)
    (hRone : g R.rep 1 = 0) (hRone' : g' R.rep 1 = 0) (hthree : (3 : K) ≠ 0)
    (D D' : B.erase R)
    (hD : (∑ P ∈ (B.erase R).erase D.val, lineParameter g P) = 2 * lineParameter g D.val)
    (hD' : (∑ P ∈ (B.erase R).erase D'.val, lineParameter g' P) = 2 * lineParameter g' D'.val) :
    D = D' ∧ (B.erase R).erase D.val = (B.erase R).erase D'.val ∧
      ((B.erase R).erase D.val).card = 2 :=
  four_point_midpoint_pair_unique g B R hR hcard hline hRone hthree D D' hD
    ((four_point_midpoint_chart_iff g g' B R hR hcard hline hline' hRone hRone' D').mp hD')

end Cylinder.ProjectiveLineChartTransition

end
