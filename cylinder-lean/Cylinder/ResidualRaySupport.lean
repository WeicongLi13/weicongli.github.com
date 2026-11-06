module

public import Cylinder.MomentQuadric
public import Cylinder.VandermondeMoments

/-! The actual points outside the moment quadric have full-support residual
relations; every nonempty residual ray has at least three points, and their
total cardinality is bounded by three times the ray excess. -/

@[expose] public section
noncomputable section
open scoped Classical BigOperators

namespace Cylinder.ResidualRaySupport
open MvPolynomial Cylinder.HilbertEvaluation Cylinder.EvaluationProjection Cylinder.MomentQuadric

variable {K I : Type*} [Field K]

abbrev RayRemaining (r : I → ℕ) (a : I → Fin 3 → K) (t : ∀ i, Fin (r i) → K)
    (f g : PlaneRing K) (i : I) :=
  {ν : Fin (r i) // eval (rayPoint (a i) (t i ν)) (quadric f g) ≠ 0}

abbrev Remaining (r : I → ℕ) (a : I → Fin 3 → K) (t : ∀ i, Fin (r i) → K)
    (f g : PlaneRing K) :=
  {x : Σ i, Fin (r i) // eval (rayPoint (a x.1) (t x.1 x.2)) (quadric f g) ≠ 0}

def remainingEquivSigma (r : I → ℕ) (a : I → Fin 3 → K) (t : ∀ i, Fin (r i) → K)
    (f g : PlaneRing K) : Remaining r a t f g ≃ Σ i, RayRemaining r a t f g i where
  toFun x := ⟨x.val.1, ⟨x.val.2, x.property⟩⟩
  invFun x := ⟨⟨x.1, x.2.val⟩, x.2.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem remaining_card [Fintype I] (r : I → ℕ) (a : I → Fin 3 → K) (t : ∀ i, Fin (r i) → K)
    (f g : PlaneRing K) :
    Fintype.card (Remaining r a t f g) = ∑ i, Fintype.card (RayRemaining r a t f g i) := by
  rw [Fintype.card_congr (remainingEquivSigma r a t f g), Fintype.card_sigma]

theorem moment_on_ray_remaining (r : I → ℕ) (a : I → Fin 3 → K)
    (t c : ∀ i, Fin (r i) → K) (f g : PlaneRing K) (i : I) (j : ℕ) :
    (∑ ν : RayRemaining r a t f g i,
      residualCoefficients r a t c f g i ν.val * t i ν.val ^ j) =
        rayMoment r t (residualCoefficients r a t c f g) i j := by
  have hsplit := Fintype.sum_subtype_add_sum_subtype
    (fun ν : Fin (r i) => eval (rayPoint (a i) (t i ν)) (quadric f g) ≠ 0)
    (fun ν => residualCoefficients r a t c f g i ν * t i ν ^ j)
  have hout : (∑ ν : {ν : Fin (r i) // ¬eval (rayPoint (a i) (t i ν)) (quadric f g) ≠ 0},
      residualCoefficients r a t c f g i ν.val * t i ν.val ^ j) = 0 := by
    apply Finset.sum_eq_zero
    intro ν _
    have hz : eval (rayPoint (a i) (t i ν.val)) (quadric f g) = 0 := not_not.mp ν.property
    simp only [residualCoefficients, hz, mul_zero, zero_mul]
  rw [hout, add_zero] at hsplit
  exact hsplit

theorem finite_two_moments_card {J : Type*} [Fintype J] [Nonempty J]
    (t c : J → K) (ht : Function.Injective t) (hc : ∀ i, c i ≠ 0)
    (hM0 : (∑ i, c i) = 0) (hM1 : (∑ i, c i * t i) = 0) : 3 ≤ Fintype.card J := by
  let e := Fintype.equivFin J
  let t' := fun ν : Fin (Fintype.card J) => t (e.symm ν)
  let c' := fun ν : Fin (Fintype.card J) => c (e.symm ν)
  have hm (j : ℕ) (hj : j ≤ 1) : (∑ ν : Fin (Fintype.card J), c' ν * t' ν ^ j) = 0 := by
    have hsum : (∑ ν : Fin (Fintype.card J), c' ν * t' ν ^ j) = ∑ i : J, c i * t i ^ j := by
      rw [← Fintype.sum_equiv e]
      intro i
      simp only [c', t', Equiv.symm_apply_apply]
    rw [hsum]
    have hcases : j = 0 ∨ j = 1 := by omega
    rcases hcases with rfl | rfl
    · simpa only [pow_zero, mul_one] using hM0
    · simpa only [pow_one] using hM1
  exact Cylinder.VandermondeMoments.ray_size_lower_bound t' c' Fintype.card_pos
    (ht.comp e.symm.injective) (fun ν => hc _) 1 hm

theorem ray_remaining_card_ge_three (r : I → ℕ) (a : I → Fin 3 → K)
    (t c : ∀ i, Fin (r i) → K) (f g : PlaneRing K) (i : I)
    (ht : Function.Injective (t i)) (hc : ∀ ν, c i ν ≠ 0)
    (hM0 : rayMoment r t c i 0 = 0)
    (hM2 : rayMoment r t c i 2 = eval (a i) f * rayMoment r t c i 1)
    (hM3 : rayMoment r t c i 3 = eval (a i) g * rayMoment r t c i 1)
    [Nonempty (RayRemaining r a t f g i)] : 3 ≤ Fintype.card (RayRemaining r a t f g i) := by
  obtain ⟨h₀, h₁⟩ := residual_first_two_moments r a t c f g i hM0 hM2 hM3
  have hzero := moment_on_ray_remaining r a t c f g i 0
  have hone := moment_on_ray_remaining r a t c f g i 1
  rw [h₀] at hzero
  rw [h₁] at hone
  exact finite_two_moments_card (fun ν : RayRemaining r a t f g i => t i ν.val)
    (fun ν => residualCoefficients r a t c f g i ν.val)
    (ht.comp Subtype.val_injective) (fun ν => mul_ne_zero (hc _) ν.property)
    (by simpa only [pow_zero, mul_one] using hzero) (by simpa only [pow_one] using hone)

theorem ray_remaining_card_upper (r : I → ℕ) (a : I → Fin 3 → K)
    (t c : ∀ i, Fin (r i) → K) (f g : PlaneRing K) (i : I) (hr : 2 ≤ r i)
    (ht : Function.Injective (t i)) (hc : ∀ ν, c i ν ≠ 0)
    (hM0 : rayMoment r t c i 0 = 0)
    (hM2 : rayMoment r t c i 2 = eval (a i) f * rayMoment r t c i 1)
    (hM3 : rayMoment r t c i 3 = eval (a i) g * rayMoment r t c i 1) :
    Fintype.card (RayRemaining r a t f g i) ≤ 3 * (r i - 2) := by
  by_cases htwo : r i = 2
  · have hroot := quadric_zero_on_two_ray r a t c f g i htwo ht hc hM0 hM2 hM3
    let : IsEmpty (RayRemaining r a t f g i) := ⟨fun ν => ν.property (hroot ν.val)⟩
    simp
  · have hcard : Fintype.card (RayRemaining r a t f g i) ≤ r i := by
      simpa only [Fintype.card_fin] using Fintype.card_le_of_injective
        (Subtype.val : RayRemaining r a t f g i → Fin (r i)) Subtype.val_injective
    omega

theorem remaining_card_upper [Fintype I] (r : I → ℕ) (a : I → Fin 3 → K)
    (t c : ∀ i, Fin (r i) → K) (f g : PlaneRing K) (hr : ∀ i, 2 ≤ r i)
    (ht : ∀ i, Function.Injective (t i)) (hc : ∀ i ν, c i ν ≠ 0)
    (hM0 : ∀ i, rayMoment r t c i 0 = 0)
    (hM2 : ∀ i, rayMoment r t c i 2 = eval (a i) f * rayMoment r t c i 1)
    (hM3 : ∀ i, rayMoment r t c i 3 = eval (a i) g * rayMoment r t c i 1) :
    Fintype.card (Remaining r a t f g) ≤ 3 * ∑ i, (r i - 2) := by
  rw [remaining_card, Finset.mul_sum]
  exact Finset.sum_le_sum (fun i _ => ray_remaining_card_upper r a t c f g i
    (hr i) (ht i) (hc i) (hM0 i) (hM2 i) (hM3 i))

theorem remaining_full_support_relation [Fintype I] (r : I → ℕ) (a : I → Fin 3 → K)
    (t c : ∀ i, Fin (r i) → K) (f g : PlaneRing K)
    (hf : f.IsHomogeneous 1) (hg : g.IsHomogeneous 2)
    (hc : ∀ i ν, c i ν ≠ 0) (d : ℕ) (hd : 2 ≤ d) (hrel : EvaluationRelation a r t c d) :
    (∀ x : Remaining r a t f g, c x.val.1 x.val.2 *
      eval (rayPoint (a x.val.1) (t x.val.1 x.val.2)) (quadric f g) ≠ 0) ∧
    PowerEvaluationRelation.Relation
      (fun x : Remaining r a t f g => rayPoint (a x.val.1) (t x.val.1 x.val.2))
      (fun x => c x.val.1 x.val.2 * eval (rayPoint (a x.val.1) (t x.val.1 x.val.2)) (quadric f g)) (d - 2) := by
  refine ⟨fun x => mul_ne_zero (hc _ _) x.property, ?_⟩
  intro P hP
  have hQP : (quadric f g * P).IsHomogeneous d := by
    simpa only [Nat.add_sub_cancel' hd] using (quadric_homogeneous f g hf hg).mul hP
  have hfull := hrel (quadric f g * P) hQP
  have hsum : (∑ x : Σ i, Fin (r i), (c x.1 x.2 *
      eval (rayPoint (a x.1) (t x.1 x.2)) (quadric f g)) *
        eval (rayPoint (a x.1) (t x.1 x.2)) P) = 0 := by
    rw [Fintype.sum_sigma]
    simpa only [map_mul, mul_assoc] using hfull
  have hsplit := Fintype.sum_subtype_add_sum_subtype
    (fun x : Σ i, Fin (r i) => eval (rayPoint (a x.1) (t x.1 x.2)) (quadric f g) ≠ 0)
    (fun x => (c x.1 x.2 * eval (rayPoint (a x.1) (t x.1 x.2)) (quadric f g)) *
      eval (rayPoint (a x.1) (t x.1 x.2)) P)
  have hout : (∑ x : {x : Σ i, Fin (r i) // ¬eval (rayPoint (a x.1) (t x.1 x.2)) (quadric f g) ≠ 0},
      (c x.val.1 x.val.2 * eval (rayPoint (a x.val.1) (t x.val.1 x.val.2)) (quadric f g)) *
        eval (rayPoint (a x.val.1) (t x.val.1 x.val.2)) P) = 0 := by
    apply Finset.sum_eq_zero
    intro x _
    have hz : eval (rayPoint (a x.val.1) (t x.val.1 x.val.2)) (quadric f g) = 0 := not_not.mp x.property
    rw [hz, mul_zero, zero_mul]
  rw [hout, add_zero, hsum] at hsplit
  exact hsplit

#print axioms remaining_card
#print axioms finite_two_moments_card
#print axioms ray_remaining_card_ge_three
#print axioms remaining_card_upper
#print axioms remaining_full_support_relation

end Cylinder.ResidualRaySupport
end
