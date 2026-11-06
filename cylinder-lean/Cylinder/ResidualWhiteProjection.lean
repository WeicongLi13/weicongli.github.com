module

public import Cylinder.BlackProjectionRationalLines
public import Cylinder.RationalProjectionRelations
public import Cylinder.ResidualDependentDirections

/-! The actual projection of a subset of white points from any rational point
outside it. Its ray and direction-line caps follow from the original white
line and plane bounds, without assuming that the centre is black. -/

@[expose] public section
noncomputable section
open scoped Classical BigOperators

namespace Cylinder.ResidualWhiteProjection
open Module MvPolynomial Cylinder.ProjectiveGeometry Cylinder.ProjectiveBalance
open Cylinder.DualLineBalance
open Cylinder.BlackProjection Cylinder.BlackProjectionLineCap Cylinder.BlackProjectionRationalLines
open Cylinder.ProjectiveProjectionFibres Cylinder.RationalPlaneLine

variable (p : ℕ) [Fact p.Prime]
local instance : DecidableEq (ZMod p) := Classical.decEq _

def image (Z : Finset (DualPoint p)) : Finset (CoordinatePoint p) := Z.image (coordinatePoint p)

theorem outside_image (Z : Finset (DualPoint p)) (b : DualPoint p) (hb : b ∉ Z) :
    coordinatePoint p b ∉ image p Z := by
  rintro h
  obtain ⟨P, hP, hPb⟩ := Finset.mem_image.mp h
  exact hb ((coordinatePoint_injective p hPb) ▸ hP)

abbrev directions (Z : Finset (DualPoint p)) (b : DualPoint p) (hb : b ∉ Z) :=
  ProjectiveProjection.directionSet (ZMod p) (Fin 3) (image p Z) (coordinatePoint p b) (outside_image p Z b hb)

abbrev raySize (Z : Finset (DualPoint p)) (b : DualPoint p) (hb : b ∉ Z) (i : directions p Z b hb) :=
  ProjectiveProjection.raySize (ZMod p) (Fin 3) (image p Z) (coordinatePoint p b) (outside_image p Z b hb) i

theorem image_subset_white {S : Finset (Geometry.Point p)} (Z : Finset (DualPoint p))
    (hZ : Z ⊆ whitePoints p S) : image p Z ⊆ whiteImage p S := Finset.image_subset_image hZ

theorem raySize_le_half {S : Finset (Geometry.Point p)} (hcard : S.card = p ^ 2)
    (hS : Geometry.PDivisible p S) (hnon : ¬Geometry.IsCylinder p S)
    (Z : Finset (DualPoint p)) (hZ : Z ⊆ whitePoints p S) (b : DualPoint p) (hb : b ∉ Z)
    (i : directions p Z b hb) : raySize p Z b hb i ≤ (p - 1) / 2 := by
  change ProjectiveProjection.raySize _ _ _ _ _ i ≤ _
  rw [ProjectiveProjectionFibres.raySize_eq_card]
  calc
    ((image p Z).filter (fun P => P.submodule ≤ raySpace (ZMod p) (Fin 3) (coordinatePoint p b) i.val)).card ≤
      ((whiteImage p S).filter (fun P => P.submodule ≤ raySpace (ZMod p) (Fin 3) (coordinatePoint p b) i.val)).card :=
      Finset.card_le_card (Finset.filter_subset_filter _ (image_subset_white p Z hZ))
    _ = (linePoints p (rayDualSpace p b i.val) ∩ whitePoints p S).card := by
      rw [← white_ray_image p S b i.val]
      exact Finset.card_image_of_injective _ (coordinatePoint_injective p)
    _ ≤ _ := ProjectiveLineCap.line_white_card_le_half p hcard hS hnon
      (rayDualSpace p b i.val) (rayDualSpace_finrank p b i.val)

theorem minimum_times_line_le {S : Finset (Geometry.Point p)} (hcard : S.card = p ^ 2)
    (hS : Geometry.PDivisible p S) (hnon : ¬Geometry.IsCylinder p S)
    (Z : Finset (DualPoint p)) (hZ : Z ⊆ whitePoints p S) (b : DualPoint p) (hb : b ∉ Z)
    (r : ℕ) (hr : ∀ i : directions p Z b hb, r ≤ raySize p Z b hb i)
    (U : Submodule (ZMod p) (Fin 3 → ZMod p)) (hU : finrank (ZMod p) U = 2) :
    r * Fintype.card {i : directions p Z b hb // i.val.submodule ≤ U} ≤ p - 1 := by
  let J := {i : directions p Z b hb // i.val.submodule ≤ U}
  calc
    _ = ∑ _i : J, r := by simp only [J, Finset.sum_const, Finset.card_univ, Nat.nsmul_eq_mul, mul_comm]
    _ ≤ ∑ i : J, raySize p Z b hb i.val := Finset.sum_le_sum (fun i _ => hr i.val)
    _ = Fintype.card (Σ i : J, ProjectiveProjection.RayIndex (ZMod p) (Fin 3) (image p Z)
      (coordinatePoint p b) (outside_image p Z b hb) i.val) := Fintype.card_sigma.symm
    _ = ((image p Z).filter (fun P => P.submodule ≤
      liftedSpace (ZMod p) (Fin 3) (coordinatePoint p b) U)).card :=
      restricted_rays_card (ZMod p) (Fin 3) (image p Z) (coordinatePoint p b) (outside_image p Z b hb) U
    _ ≤ ((whiteImage p S).filter (fun P => P.submodule ≤
      liftedSpace (ZMod p) (Fin 3) (coordinatePoint p b) U)).card :=
      Finset.card_le_card (Finset.filter_subset_filter _ (image_subset_white p Z hZ))
    _ = (whitePoints p S ∩ DualPlaneModel.dualPlanePoints p (planeDualSpace p b U)).card := by
      rw [← white_plane_image p S b U]
      exact Finset.card_image_of_injective _ (coordinatePoint_injective p)
    _ ≤ _ := ProjectivePlaneCap.dual_plane_white_card_le p hcard hS hnon
      (planeDualSpace p b U) (planeDualSpace_finrank p b U hU)

theorem lineCap {S : Finset (Geometry.Point p)} (hcard : S.card = p ^ 2)
    (hS : Geometry.PDivisible p S) (hnon : ¬Geometry.IsCylinder p S)
    (Z : Finset (DualPoint p)) (hZ : Z ⊆ whitePoints p S) (b : DualPoint p) (hb : b ∉ Z)
    (r : ℕ) (hrpos : 0 < r) (hr : ∀ i : directions p Z b hb, r ≤ raySize p Z b hb i) :
    RationalPlaneLine.LineCap (directions p Z b hb) ((p - 1) / r) := by
  intro c hc
  have hmin := minimum_times_line_le p hcard hS hnon Z hZ b hb r hr
    (LinearMap.ker (dotMap c)) (dotMap_kernel_finrank c hc)
  have heq : Fintype.card {i : directions p Z b hb // i.val.submodule ≤ LinearMap.ker (dotMap c)} =
      ((directions p Z b hb).filter (fun P => PlaneCrossProduct.dot c P.rep = 0)).card := by
    rw [Fintype.card_subtype]
    apply Finset.card_bij (fun i _ => i.val)
    · intro i hi
      have hc' := (Finset.mem_filter.mp hi).2
      exact Finset.mem_filter.mpr ⟨i.property, by
        rw [ProjectiveIncidence.submodule_le_iff_rep_mem, LinearMap.mem_ker] at hc'
        change PlaneCrossProduct.dot c i.val.rep = 0 at hc'
        exact hc'⟩
    · intro i _ j _ hij
      exact Subtype.ext hij
    · intro P hP
      refine ⟨⟨P, (Finset.mem_filter.mp hP).1⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, rfl⟩
      rw [ProjectiveIncidence.submodule_le_iff_rep_mem, LinearMap.mem_ker]
      change PlaneCrossProduct.dot c P.rep = 0
      exact (Finset.mem_filter.mp hP).2
  rw [heq] at hmin
  exact (Nat.le_div_iff_mul_le hrpos).mpr (by simpa only [mul_comm] using hmin)

theorem minimum_times_directions_le (Z : Finset (DualPoint p)) (b : DualPoint p) (hb : b ∉ Z)
    (r : ℕ) (hr : ∀ i : directions p Z b hb, r ≤ raySize p Z b hb i) :
    r * (directions p Z b hb).card ≤ Z.card := by
  calc
    _ = ∑ _i : directions p Z b hb, r := by simp only [Finset.sum_const, Finset.card_univ,
      Fintype.card_coe, Nat.nsmul_eq_mul, mul_comm]
    _ ≤ ∑ i : directions p Z b hb, raySize p Z b hb i := Finset.sum_le_sum (fun i _ => hr i)
    _ = (image p Z).card := sum_raySize (ZMod p) (Fin 3) (image p Z) (coordinatePoint p b) (outside_image p Z b hb)
    _ = Z.card := Finset.card_image_of_injective _ (coordinatePoint_injective p)

theorem exists_minimum {S : Finset (Geometry.Point p)} (hcard : S.card = p ^ 2)
    (hS : Geometry.PDivisible p S) (hnon : ¬Geometry.IsCylinder p S)
    (Z : Finset (DualPoint p)) (hZ : Z ⊆ whitePoints p S) (hZnon : Z.Nonempty)
    (b : DualPoint p) (hb : b ∉ Z) (hthree : ∀ i : directions p Z b hb, 3 ≤ raySize p Z b hb i) :
    ∃ r : ℕ, 3 ≤ r ∧ r ≤ (p - 1) / 2 ∧
      (∃ i : directions p Z b hb, raySize p Z b hb i = r) ∧
      (∀ i : directions p Z b hb, r ≤ raySize p Z b hb i) ∧
      r * (directions p Z b hb).card ≤ Z.card ∧
      RationalPlaneLine.LineCap (directions p Z b hb) ((p - 1) / r) := by
  obtain ⟨P, hP⟩ := hZnon
  let x : image p Z := ⟨coordinatePoint p P, Finset.mem_image.mpr ⟨P, hP, rfl⟩⟩
  let : Nonempty (directions p Z b hb) := ⟨ProjectiveProjection.projectionIndex (ZMod p) (Fin 3)
    (image p Z) (coordinatePoint p b) (outside_image p Z b hb) x⟩
  obtain ⟨i, _hi, hmin⟩ := Finset.exists_min_image Finset.univ (raySize p Z b hb) Finset.univ_nonempty
  have hr := fun j : directions p Z b hb => hmin j (Finset.mem_univ _)
  refine ⟨raySize p Z b hb i, hthree i, raySize_le_half p hcard hS hnon Z hZ b hb i,
    ⟨i, rfl⟩, hr, minimum_times_directions_le p Z b hb _ hr, ?_⟩
  exact lineCap p hcard hS hnon Z hZ b hb _ (by have hh := hthree i; omega) hr

#print axioms raySize_le_half
#print axioms minimum_times_line_le
#print axioms lineCap
#print axioms minimum_times_directions_le
#print axioms exists_minimum

end Cylinder.ResidualWhiteProjection
end
