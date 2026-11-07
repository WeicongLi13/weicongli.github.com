module

public import Cylinder.ProductRescaling

/-! Changing the plane equations while retaining the prescribed product
residues.  Both polynomial identities are transported by the same family. -/

@[expose] public section
noncomputable section
open scoped Classical BigOperators
namespace Cylinder.MomentResidueChange
open MvPolynomial Cylinder.ProjectiveGeometry Cylinder.ProjectiveBalance
open Cylinder.ProductRescaling Cylinder.ProductFrobenius

variable (p : ℕ) [Fact p.Prime]

def scaleRatio (a a₀ : DualPoint p → ZMod p) (E : DualPoint p) : ZMod p :=
  a E / a₀ E

def globalRatio (S : Finset (Geometry.Point p)) (a a₀ : DualPoint p → ZMod p) : ZMod p :=
  blackScalar p S (scaleRatio p a a₀) / whiteScalar p S (scaleRatio p a a₀)

def residueChange (S : Finset (Geometry.Point p))
    (a a₀ c : DualPoint p → ZMod p) (E : DualPoint p) : ZMod p :=
  c E / (globalRatio p S a a₀ * scaleRatio p a a₀ E)

theorem scaleRatio_ne_zero (a a₀ : DualPoint p → ZMod p)
    (ha : ∀ E, a E ≠ 0) (ha₀ : ∀ E, a₀ E ≠ 0) (E : DualPoint p) :
    scaleRatio p a a₀ E ≠ 0 := div_ne_zero (ha E) (ha₀ E)

theorem globalRatio_ne_zero (S : Finset (Geometry.Point p))
    (a a₀ : DualPoint p → ZMod p) (ha : ∀ E, a E ≠ 0) (ha₀ : ∀ E, a₀ E ≠ 0) :
    globalRatio p S a a₀ ≠ 0 :=
  div_ne_zero (blackScalar_ne_zero p S _ (fun E _ => scaleRatio_ne_zero p a a₀ ha ha₀ E))
    (whiteScalar_ne_zero p S _ (fun E _ => scaleRatio_ne_zero p a a₀ ha ha₀ E))

theorem residueChange_spec (S : Finset (Geometry.Point p))
    (a a₀ c : DualPoint p → ZMod p) (ha : ∀ E, a E ≠ 0) (ha₀ : ∀ E, a₀ E ≠ 0)
    (E : DualPoint p) :
    c E = globalRatio p S a a₀ * scaleRatio p a a₀ E * residueChange p S a a₀ c E := by
  unfold residueChange
  rw [mul_div_cancel₀ _ (mul_ne_zero (globalRatio_ne_zero p S a a₀ ha ha₀)
    (scaleRatio_ne_zero p a a₀ ha ha₀ E))]

theorem planeForm_change (a a₀ : DualPoint p → ZMod p)
    (ha₀ : ∀ E, a₀ E ≠ 0) (E : DualPoint p) :
    scaledPlaneForm p a E = C (scaleRatio p a a₀ E) * scaledPlaneForm p a₀ E := by
  simp only [scaledPlaneForm, ← mul_assoc, ← map_mul, scaleRatio,
    div_mul_cancel₀ _ (ha₀ E)]

theorem product_change (T : Finset (DualPoint p)) (a a₀ : DualPoint p → ZMod p)
    (ha₀ : ∀ E, a₀ E ≠ 0) (m : DualPoint p → ℕ) :
    (∏ H ∈ T, scaledPlaneForm p a H ^ m H) =
      C (∏ H ∈ T, scaleRatio p a a₀ H ^ m H) *
        ∏ H ∈ T, scaledPlaneForm p a₀ H ^ m H := by
  simp only [planeForm_change p a a₀ ha₀, mul_pow, ← map_pow]
  rw [Finset.prod_mul_distrib, ← map_prod]

theorem residue_term_change (S : Finset (Geometry.Point p))
    (a a₀ c : DualPoint p → ZMod p) (ha : ∀ E, a E ≠ 0) (ha₀ : ∀ E, a₀ E ≠ 0)
    (E : DualPoint p) (hE : E ∈ whitePoints p S) :
    C (c E) * (∏ H ∈ (whitePoints p S).erase E, scaledPlaneForm p a H) =
      C (blackScalar p S (scaleRatio p a a₀)) *
        (C (residueChange p S a a₀ c E) *
          ∏ H ∈ (whitePoints p S).erase E, scaledPlaneForm p a₀ H) := by
  have hprod := product_change p ((whitePoints p S).erase E) a a₀ ha₀ (fun _ => 1)
  simp only [pow_one] at hprod
  rw [hprod]
  have he : c E * erasedScalar p S (scaleRatio p a a₀) E =
      blackScalar p S (scaleRatio p a a₀) * residueChange p S a a₀ c E := by
    rw [residueChange_spec p S a a₀ c ha ha₀ E]
    calc
      _ = (globalRatio p S a a₀ * (scaleRatio p a a₀ E *
        erasedScalar p S (scaleRatio p a a₀) E)) * residueChange p S a a₀ c E := by ring
      _ = _ := by
        rw [erasedScalar_factor p S (scaleRatio p a a₀) E hE]
        unfold globalRatio
        rw [div_mul_cancel₀ _ (whiteScalar_ne_zero p S _
          (fun H _ => scaleRatio_ne_zero p a a₀ ha ha₀ H))]
  change C (c E) * (C (erasedScalar p S (scaleRatio p a a₀) E) * _) = _
  rw [← mul_assoc, ← map_mul, he, map_mul, mul_assoc]

theorem power_term_change (S : Finset (Geometry.Point p))
    (a a₀ c : DualPoint p → ZMod p) (ha : ∀ E, a E ≠ 0) (ha₀ : ∀ E, a₀ E ≠ 0)
    (E : DualPoint p) :
    C (c E) * scaledPlaneForm p a E ^ (p - 2) =
      C (globalRatio p S a a₀) *
        (C (residueChange p S a a₀ c E) * scaledPlaneForm p a₀ E ^ (p - 2)) := by
  rw [planeForm_change p a a₀ ha₀ E, mul_pow, ← map_pow]
  have he : c E * scaleRatio p a a₀ E ^ (p - 2) =
      globalRatio p S a a₀ * residueChange p S a a₀ c E := by
    rw [residueChange_spec p S a a₀ c ha ha₀ E]
    calc
      _ = globalRatio p S a a₀ * residueChange p S a a₀ c E *
        (scaleRatio p a a₀ E * scaleRatio p a a₀ E ^ (p - 2)) := by ring
      _ = _ := by rw [scalar_fermat_shift p (scaleRatio_ne_zero p a a₀ ha ha₀ E), mul_one]
  rw [← mul_assoc, ← map_mul, he, map_mul, mul_assoc]

/-- Inverse rescaling for a fixed coefficient family, not an existential
replacement.  In particular, both identities concern exactly `residueChange`. -/
theorem for_fixed_product (S : Finset (Geometry.Point p))
    (a a₀ c : DualPoint p → ZMod p) (ha : ∀ E, a E ≠ 0) (ha₀ : ∀ E, a₀ E ≠ 0)
    (hc : ∀ E ∈ whitePoints p S, c E ≠ 0)
    (hprod : (∏ H ∈ blackPoints p S, scaledPlaneForm p a H ^ weight p S H) =
      ∑ E ∈ whitePoints p S, C (c E) *
        ∏ H ∈ (whitePoints p S).erase E, scaledPlaneForm p a H)
    (hpower : (∑ E ∈ whitePoints p S, C (c E) * scaledPlaneForm p a E ^ (p - 2)) = 0) :
    (∀ E ∈ whitePoints p S, residueChange p S a a₀ c E ≠ 0) ∧
    (∏ H ∈ blackPoints p S, scaledPlaneForm p a₀ H ^ weight p S H) =
      (∑ E ∈ whitePoints p S, C (residueChange p S a a₀ c E) *
        ∏ H ∈ (whitePoints p S).erase E, scaledPlaneForm p a₀ H) ∧
    (∑ E ∈ whitePoints p S, C (residueChange p S a a₀ c E) *
      scaledPlaneForm p a₀ E ^ (p - 2)) = 0 ∧
    ∀ E, c E = globalRatio p S a a₀ * scaleRatio p a a₀ E * residueChange p S a a₀ c E := by
  have hb : blackScalar p S (scaleRatio p a a₀) ≠ 0 :=
    blackScalar_ne_zero p S _ (fun E _ => scaleRatio_ne_zero p a a₀ ha ha₀ E)
  have hbC : (C (blackScalar p S (scaleRatio p a a₀)) : Form p) ≠ 0 :=
    fun h => hb ((MvPolynomial.C_injective (Fin 4) (ZMod p)) (by simpa only [map_zero] using h))
  have htC : (C (globalRatio p S a a₀) : Form p) ≠ 0 :=
    fun h => globalRatio_ne_zero p S a a₀ ha ha₀
      ((MvPolynomial.C_injective (Fin 4) (ZMod p)) (by simpa only [map_zero] using h))
  refine ⟨fun E hE => div_ne_zero (hc E hE)
    (mul_ne_zero (globalRatio_ne_zero p S a a₀ ha ha₀)
      (scaleRatio_ne_zero p a a₀ ha ha₀ E)), ?_, ?_, residueChange_spec p S a a₀ c ha ha₀⟩
  · apply mul_left_cancel₀ hbC
    change C (∏ H ∈ blackPoints p S, scaleRatio p a a₀ H ^ weight p S H) * _ = _
    rw [← product_change p (blackPoints p S) a a₀ ha₀ (weight p S), hprod, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun E hE => residue_term_change p S a a₀ c ha ha₀ E hE)
  · apply (mul_eq_zero.mp (show C (globalRatio p S a a₀) * _ = 0 from ?_)).resolve_left htC
    rw [Finset.mul_sum]
    simpa only [← power_term_change p S a a₀ c ha ha₀] using hpower

end Cylinder.MomentResidueChange
end
