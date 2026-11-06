module

public import Cylinder.BlackProjection

/-! The direction-line cap follows from the actual finite ray partition in a dual plane. -/

@[expose] public section
noncomputable section

namespace Cylinder.BlackProjectionLineCap

open Cylinder.BlackProjection Cylinder.ProjectiveGeometry Cylinder.ProjectiveBalance
open Cylinder.DualPlaneModel Cylinder.ProjectiveProjectionFibres
open scoped Classical LinearAlgebra.Projectivization BigOperators

variable (p : ℕ) [Fact p.Prime]

def directionLine (S : Finset (Geometry.Point p)) (b : DualPoint p) (hb : b ∈ blackPoints p S)
    (U : Submodule (ZMod p) (Fin 3 → ZMod p)) : Finset (Direction p) :=
  (directionSet p S b hb).filter (fun d => d.submodule ≤ U)

def directionLineEquiv {S : Finset (Geometry.Point p)} {b : DualPoint p}
    (hb : b ∈ blackPoints p S) (U : Submodule (ZMod p) (Fin 3 → ZMod p)) :
    {i : directionSet p S b hb // i.val.submodule ≤ U} ≃ directionLine p S b hb U where
  toFun i := ⟨i.val.val, Finset.mem_filter.mpr ⟨i.val.property, i.property⟩⟩
  invFun i := ⟨⟨i.val, (Finset.mem_filter.mp i.property).1⟩, (Finset.mem_filter.mp i.property).2⟩
  left_inv i := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv i := by
    apply Subtype.ext
    rfl

theorem directionLine_card {S : Finset (Geometry.Point p)} {b : DualPoint p}
    (hb : b ∈ blackPoints p S) (U : Submodule (ZMod p) (Fin 3 → ZMod p)) :
    Fintype.card {i : directionSet p S b hb // i.val.submodule ≤ U} =
      (directionLine p S b hb U).card := by
  rw [Fintype.card_congr (directionLineEquiv p hb U), Fintype.card_coe]

def planeDualSpace (b : DualPoint p) (U : Submodule (ZMod p) (Fin 3 → ZMod p)) :
    Submodule (ZMod p) (Module.Dual (ZMod p) (Vector p)) :=
  (liftedSpace (ZMod p) (Fin 3) (coordinatePoint p b) U).map (dualCoordinates p).symm.toLinearMap

theorem point_mem_planeDualSpace (b H : DualPoint p) (U : Submodule (ZMod p) (Fin 3 → ZMod p)) :
    H.submodule ≤ planeDualSpace p b U ↔
      (coordinatePoint p H).submodule ≤ liftedSpace (ZMod p) (Fin 3) (coordinatePoint p b) U := by
  rw [coordinatePoint_submodule, planeDualSpace, Submodule.map_equiv_eq_comap_symm]
  exact Submodule.map_le_iff_le_comap.symm

theorem planeDualSpace_finrank (b : DualPoint p) (U : Submodule (ZMod p) (Fin 3 → ZMod p))
    (hU : Module.finrank (ZMod p) U = 2) :
    Module.finrank (ZMod p) (planeDualSpace p b U) = 3 := by
  rw [planeDualSpace, LinearEquiv.finrank_map_eq, liftedSpace_finrank, hU]

theorem white_plane_image (S : Finset (Geometry.Point p)) (b : DualPoint p)
    (U : Submodule (ZMod p) (Fin 3 → ZMod p)) :
    (whitePoints p S ∩ dualPlanePoints p (planeDualSpace p b U)).image (coordinatePoint p) =
      (whiteImage p S).filter
        (fun P => P.submodule ≤ liftedSpace (ZMod p) (Fin 3) (coordinatePoint p b) U) := by
  ext P
  constructor
  · intro hP
    obtain ⟨H, hH, rfl⟩ := Finset.mem_image.mp hP
    obtain ⟨hwhite, hplane⟩ := Finset.mem_inter.mp hH
    exact Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨H, hwhite, rfl⟩,
      (point_mem_planeDualSpace p b H U).mp (Finset.mem_filter.mp hplane).2⟩
  · intro hP
    obtain ⟨himage, hspace⟩ := Finset.mem_filter.mp hP
    obtain ⟨H, hwhite, rfl⟩ := Finset.mem_image.mp himage
    exact Finset.mem_image.mpr ⟨H, Finset.mem_inter.mpr
      ⟨hwhite, Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        (point_mem_planeDualSpace p b H U).mpr hspace⟩⟩, rfl⟩

theorem minimum_times_directionLine_le {S : Finset (Geometry.Point p)}
    (hcard : S.card = p ^ 2) (hS : Geometry.PDivisible p S) (hnon : ¬ Geometry.IsCylinder p S)
    {b : DualPoint p} (hb : b ∈ blackPoints p S) (r : ℕ)
    (hr : ∀ i : directionSet p S b hb, r ≤ raySize p S b hb i)
    (U : Submodule (ZMod p) (Fin 3 → ZMod p)) (hU : Module.finrank (ZMod p) U = 2) :
    r * (directionLine p S b hb U).card ≤ p - 1 := by
  let J := {i : directionSet p S b hb // i.val.submodule ≤ U}
  calc
    r * (directionLine p S b hb U).card = ∑ _i : J, r := by
      rw [← directionLine_card p hb U]
      simp [J, mul_comm]
    _ ≤ ∑ i : J, raySize p S b hb i.val := Finset.sum_le_sum fun i _ => hr i.val
    _ = Fintype.card (Σ i : J,
        ProjectiveProjection.RayIndex (ZMod p) (Fin 3) (whiteImage p S) (coordinatePoint p b)
          (black_outside_whiteImage p hb) i.val) := (Fintype.card_sigma).symm
    _ = ((whiteImage p S).filter
        (fun P => P.submodule ≤ liftedSpace (ZMod p) (Fin 3) (coordinatePoint p b) U)).card :=
      restricted_rays_card (ZMod p) (Fin 3) (whiteImage p S) (coordinatePoint p b)
        (black_outside_whiteImage p hb) U
    _ = (whitePoints p S ∩ dualPlanePoints p (planeDualSpace p b U)).card := by
      rw [← white_plane_image]
      exact Finset.card_image_of_injective _ (coordinatePoint_injective p)
    _ ≤ p - 1 := ProjectivePlaneCap.dual_plane_white_card_le p hcard hS hnon
      (planeDualSpace p b U) (planeDualSpace_finrank p b U hU)

theorem directionLine_card_le {S : Finset (Geometry.Point p)} (hcard : S.card = p ^ 2)
    (hS : Geometry.PDivisible p S) (hnon : ¬ Geometry.IsCylinder p S)
    {b : DualPoint p} (hb : b ∈ blackPoints p S) (r : ℕ) (hrpos : 0 < r)
    (hr : ∀ i : directionSet p S b hb, r ≤ raySize p S b hb i)
    (U : Submodule (ZMod p) (Fin 3 → ZMod p)) (hU : Module.finrank (ZMod p) U = 2) :
    (directionLine p S b hb U).card ≤ (p - 1) / r := by
  apply (Nat.le_div_iff_mul_le hrpos).mpr
  simpa only [mul_comm] using minimum_times_directionLine_le p hcard hS hnon hb r hr U hU

theorem exists_minimum_with_bounds {S : Finset (Geometry.Point p)} (hcard : S.card = p ^ 2)
    (hS : Geometry.PDivisible p S) (hnon : ¬ Geometry.IsCylinder p S)
    {b : DualPoint p} (hb : b ∈ blackPoints p S) :
    ∃ r : ℕ, 2 ≤ r ∧ r ≤ (p - 1) / 2 ∧
      (∃ i : directionSet p S b hb, raySize p S b hb i = r) ∧
      (∀ i : directionSet p S b hb, r ≤ raySize p S b hb i) ∧
      r * (directionSet p S b hb).card ≤ (whitePoints p S).card ∧
      ∀ U : Submodule (ZMod p) (Fin 3 → ZMod p), Module.finrank (ZMod p) U = 2 →
        (directionLine p S b hb U).card ≤ (p - 1) / r := by
  obtain ⟨i, hmin⟩ := exists_minimal_ray p hb
  refine ⟨raySize p S b hb i, two_le_raySize p hcard hS hb i,
    raySize_le_half p hcard hS hnon hb i, ⟨i, rfl⟩, hmin,
    minimum_times_directions_le_white p hb _ hmin, ?_⟩
  intro U hU
  exact directionLine_card_le p hcard hS hnon hb _
    (lt_of_lt_of_le (by decide : 0 < 2) (two_le_raySize p hcard hS hb i)) hmin U hU

end Cylinder.BlackProjectionLineCap

end
