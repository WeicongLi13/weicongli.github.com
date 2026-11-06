module

public import Cylinder.ExactRayMomentsActualProduct

/-! The exponents of the actual direction products are the actual white
ray sizes and the total weights of the other black points on the same ray. -/

@[expose] public section
noncomputable section
open scoped Classical BigOperators LinearAlgebra.Projectivization
namespace Cylinder.ExactRayMomentsActualBalance
open Cylinder.ProjectiveGeometry Cylinder.ProjectiveBalance Cylinder.DualLineBalance
open Cylinder.BlackProjection Cylinder.ProjectiveProjection Cylinder.ProjectiveProjectionFibres
open Cylinder.ExactRayMomentsMultiplicity Cylinder.ExactRayMomentsActualProduct
open Cylinder.ExactRayMomentsBlackBalance Cylinder.BlackProjectionVandermonde
variable (p : ℕ) [Fact p.Prime]
local instance directionFintype : Fintype (BlackProjection.Direction p) := Fintype.ofFinite _

def whiteRayEquiv {S : Finset (Geometry.Point p)} {b : DualPoint p}
    (hb : b ∈ blackPoints p S) (i : BlackProjection.directionSet p S b hb) :
    {H : whitePoints p S // whiteDirection p hb H = i.val} ≃
      RayIndex (ZMod p) (Fin 3) (whiteImage p S) (coordinatePoint p b)
        (black_outside_whiteImage p hb) i where
  toFun x := ⟨whiteCoordinateEquiv p S x.val, by
    apply Subtype.ext
    change projection (ZMod p) (Fin 3) (whiteImage p S) (coordinatePoint p b)
      (black_outside_whiteImage p hb) (whiteCoordinateEquiv p S x.val) = i.val
    rw [← whiteDirection_projection]
    exact x.property⟩
  invFun x := ⟨(whiteCoordinateEquiv p S).symm x.val, by
    rw [whiteDirection_projection, Equiv.apply_symm_apply]
    exact congrArg Subtype.val x.property⟩
  left_inv x := by
    apply Subtype.ext
    exact (whiteCoordinateEquiv p S).symm_apply_apply x.val
  right_inv x := by
    apply Subtype.ext
    exact (whiteCoordinateEquiv p S).apply_symm_apply x.val

theorem white_exponent_eq_raySize {S : Finset (Geometry.Point p)} {b : DualPoint p}
    (hb : b ∈ blackPoints p S) (i : BlackProjection.directionSet p S b hb) :
    directionExponent (whiteDirection p hb) (fun _ => 1) i.val = BlackProjection.raySize p S b hb i := by
  calc
    _ = (Finset.univ.filter (fun H : whitePoints p S => whiteDirection p hb H = i.val)).card := by
      simp [directionExponent]
    _ = Fintype.card {H : whitePoints p S // whiteDirection p hb H = i.val} :=
      (Fintype.card_subtype _).symm
    _ = BlackProjection.raySize p S b hb i := Fintype.card_congr (whiteRayEquiv p hb i)

theorem black_exponent_eq_other_weight {S : Finset (Geometry.Point p)} {b : DualPoint p}
    (hb : b ∈ blackPoints p S) (i : BlackProjection.directionSet p S b hb) :
    directionExponent (blackDirection p S b) (fun H => weight p S H.val) i.val =
      ∑ H ∈ otherBlackOnRay p S b hb i, weight p S H := by
  unfold directionExponent
  apply Finset.sum_bij (fun H _ => H.val)
  · intro H hH
    have hdir := (Finset.mem_filter.mp hH).2
    have hline := (blackDirection_mem_ray p S b H i.val).mp hdir
    exact Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp H.property).1,
      Finset.mem_inter.mpr ⟨hline, (Finset.mem_erase.mp H.property).2⟩⟩
  · intro H _ Q _ h
    exact Subtype.ext h
  · intro H hH
    have h := Finset.mem_erase.mp hH
    have hblack := (Finset.mem_inter.mp h.2).2
    let Q : (blackPoints p S).erase b := ⟨H, Finset.mem_erase.mpr ⟨h.1, hblack⟩⟩
    refine ⟨Q, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, rfl⟩
    exact (blackDirection_mem_ray p S b Q i.val).mpr (Finset.mem_inter.mp h.2).1
  · intro H _
    rfl

theorem supported_actual_weight_balance {S : Finset (Geometry.Point p)}
    (hcard : S.card = p ^ 2) (hS : Geometry.PDivisible p S)
    {b : DualPoint p} (hb : b ∈ blackPoints p S) (i : BlackProjection.Direction p)
    (hi : 0 < directionExponent (whiteDirection p hb) (fun _ => 1) i) :
    directionExponent (whiteDirection p hb) (fun _ => 1) i = weight p S b + 1 +
      directionExponent (blackDirection p S b) (fun H => weight p S H.val) i := by
  have hpos : 0 < (Finset.univ.filter
      (fun H : whitePoints p S => whiteDirection p hb H = i)).card := by
    simpa [directionExponent] using hi
  obtain ⟨H, hH⟩ := Finset.card_pos.mp hpos
  have hdir := (Finset.mem_filter.mp hH).2
  have himem : i ∈ BlackProjection.directionSet p S b hb := by
    exact Finset.mem_image.mpr ⟨whiteCoordinateEquiv p S H, Finset.mem_univ _,
      (whiteDirection_projection p hb H).symm.trans hdir⟩
  let wi : BlackProjection.directionSet p S b hb := ⟨i, himem⟩
  have hw := actual_white_ray_weight_balance p hcard hS hb wi
  rw [← white_exponent_eq_raySize p hb wi, ← black_exponent_eq_other_weight p hb wi] at hw
  exact hw

end Cylinder.ExactRayMomentsActualBalance
end
