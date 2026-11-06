module

public import Cylinder.BMMActualCoefficients
public import Cylinder.BMMTriangleMatching
public import Cylinder.BMMCocycleNormalization

/-! Segre's product identity for the actual black secants, followed by
one simultaneous normalization of all white representatives. -/

@[expose] public section
noncomputable section
open scoped Classical BigOperators

namespace Cylinder.BMMSegreLemma

open Cylinder.RationalPlaneLine Cylinder.BMMArcGeometry Cylinder.BMMFrameRatios
open Cylinder.BMMTriangleBlockers Cylinder.BMMTriangleProducts
open Cylinder.BMMTriangleMatching Cylinder.BMMActualCoefficients
open Cylinder.BMMCocycleNormalization

variable {K : Type*} [Field K]

theorem side_coefficient_inverse_ratio (T : Triangle K) (i : Fin 3) :
    secantCoefficient (triangleConfiguration T) (T.P (next i)) (T.P (previous i)) =
      (blackRatio T (sideBlocker T i) i)⁻¹ := by
  rw [side_coefficient_ratio]
  simp only [blackRatio, inv_div]

theorem side_coefficient_cycle (T : Triangle K) :
    (∏ i : Fin 3,
      secantCoefficient (triangleConfiguration T) (T.P (next i)) (T.P (previous i))) = 1 := by
  simp_rw [side_coefficient_inverse_ratio]
  rw [Finset.prod_inv_distrib, side_ratio_cycle, inv_one]

theorem actual_secant_cocycle (A : Configuration K) (P Q R : A.W)
    (hPQ : P ≠ Q) (hQR : Q ≠ R) (hRP : R ≠ P) :
    secantCoefficient A P Q * secantCoefficient A Q R * secantCoefficient A R P = 1 := by
  let T : Triangle K := {
    W := A.W, B := A.B, arc := A.arc, disjoint := A.disjoint,
    blocks := A.blocks, card := A.card, P := ![P, Q, R],
    injective := by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all }
  have h := side_coefficient_cycle T
  change (∏ i : Fin 3, secantCoefficient A (![P, Q, R] (next i))
    (![P, Q, R] (previous i))) = 1 at h
  simpa [Fin.prod_univ_succ, next, previous, mul_comm, mul_left_comm, mul_assoc] using h

theorem actual_normalizing_weights (A : Configuration K) (anchor : A.W) :
    ∃ α : A.W → K, α anchor = 1 ∧ (∀ P, α P ≠ 0) ∧
      ∀ P Q, secantCoefficient A P Q = α Q / α P := by
  exact exists_normalizing_weights (secantCoefficient A) anchor (coefficient_diagonal A)
    (coefficient_reverse_product A) (actual_secant_cocycle A)

theorem actual_normalized_secants (A : Configuration K) (anchor : A.W) :
    ∃ α : A.W → K, α anchor = 1 ∧ (∀ P, α P ≠ 0) ∧
      ∀ (P Q : A.W) (hPQ : P ≠ Q), ∃ a : K, a ≠ 0 ∧
        (blocker A P Q hPQ).val.rep = a • (α P • P.val.rep + α Q • Q.val.rep) := by
  obtain ⟨α, hanchor, hα, hc⟩ := actual_normalizing_weights A anchor
  refine ⟨α, hanchor, hα, fun P Q hPQ => ?_⟩
  obtain ⟨_hb, a, ha, hrep⟩ := coefficient_spec A P Q hPQ
  refine ⟨a * (α P)⁻¹, mul_ne_zero ha (inv_ne_zero (hα P)), ?_⟩
  rw [hrep, normalized_secant_formula (fun X : A.W => X.val.rep) α hα
    (secantCoefficient A) hc P Q, smul_smul]

theorem actual_normalized_representatives (A : Configuration K) (anchor : A.W) :
    ∃ E : A.W → Fin 3 → K, E anchor = anchor.val.rep ∧
      ∃ hE : ∀ P, E P ≠ 0,
      (∀ P, Projectivization.mk K (E P) (hE P) = P.val) ∧
      ∀ (P Q : A.W) (hPQ : P ≠ Q), ∃ hsum : E P + E Q ≠ 0,
        Projectivization.mk K (E P + E Q) hsum = (blocker A P Q hPQ).val := by
  obtain ⟨α, hanchor, hα, hsec⟩ := actual_normalized_secants A anchor
  let E : A.W → Fin 3 → K := fun P => α P • P.val.rep
  have hE : ∀ P, E P ≠ 0 := fun P => smul_ne_zero (hα P) P.val.rep_nonzero
  refine ⟨E, ?_, hE, ?_, ?_⟩
  · simp only [E, hanchor, one_smul]
  · intro P
    rw [← Projectivization.mk_rep P.val]
    apply (Projectivization.mk_eq_mk_iff' K _ _ (hE P) P.val.rep_nonzero).mpr
    exact ⟨α P, rfl⟩
  · intro P Q hPQ
    obtain ⟨a, _ha, hrep⟩ := hsec P Q hPQ
    have hsum : E P + E Q ≠ 0 := by
      intro hzero
      apply (blocker A P Q hPQ).val.rep_nonzero
      rw [hrep]
      change a • (E P + E Q) = 0
      rw [hzero, smul_zero]
    refine ⟨hsum, ?_⟩
    rw [← Projectivization.mk_rep (blocker A P Q hPQ).val]
    apply ((Projectivization.mk_eq_mk_iff' K _ _
      (blocker A P Q hPQ).val.rep_nonzero hsum).mpr ?_).symm
    exact ⟨a, hrep.symm⟩

theorem actual_normalized_vector_data (A : Configuration K) (anchor : A.W) :
    ∃ E : A.W → Fin 3 → K,
      (∀ P, ∃ α : K, α ≠ 0 ∧ E P = α • P.val.rep) ∧
      ∀ (P Q : A.W) (hPQ : P ≠ Q), ∃ β : K, β ≠ 0 ∧
        E P + E Q = β • (blocker A P Q hPQ).val.rep := by
  obtain ⟨α, _hanchor, hα, hsec⟩ := actual_normalized_secants A anchor
  refine ⟨fun P => α P • P.val.rep, (fun P => ⟨α P, hα P, rfl⟩), ?_⟩
  intro P Q hPQ
  obtain ⟨a, ha, hrep⟩ := hsec P Q hPQ
  refine ⟨a⁻¹, inv_ne_zero ha, ?_⟩
  rw [hrep, smul_smul, inv_mul_cancel₀ ha, one_smul]

end Cylinder.BMMSegreLemma

end
