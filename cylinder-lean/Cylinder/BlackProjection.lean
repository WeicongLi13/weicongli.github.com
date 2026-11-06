module

public import Cylinder.ProjectiveProjectionFibres
public import Cylinder.ProjectiveLineCap
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Data.Fintype.Lattice

/-!
# Projection of the actual white set from a black point over the prime field

The coordinate change, directions, rays and their sizes are all defined
over `ZMod p`. Each ray is the actual white intersection with a dual line,
so its lower and upper bounds follow from line balance and the line cap.
-/

@[expose] public section
noncomputable section

namespace Cylinder.BlackProjection

open Cylinder.ProjectiveGeometry Cylinder.ProjectiveBalance Cylinder.DualLineBalance
open Cylinder.ProjectiveProjectionFibres
open scoped Classical LinearAlgebra.Projectivization BigOperators

variable (p : ℕ) [Fact p.Prime]

abbrev CoordinateSpace := Option (Fin 3) → ZMod p
abbrev CoordinatePoint := Projectivization (ZMod p) (CoordinateSpace p)
abbrev Direction := Projectivization (ZMod p) (Fin 3 → ZMod p)

def dualCoordinates : DualSpace p ≃ₗ[ZMod p] CoordinateSpace p :=
  (pairingEquiv p).symm.trans
    (LinearEquiv.piCongrLeft' (ZMod p) (fun _ : Fin 4 => ZMod p) (finSuccEquiv 3))

def coordinatePoint (H : DualPoint p) : CoordinatePoint p :=
  Projectivization.map (dualCoordinates p).toLinearMap (dualCoordinates p).injective H

theorem coordinatePoint_injective : Function.Injective (coordinatePoint p) :=
  Projectivization.map_injective (dualCoordinates p).toLinearMap (dualCoordinates p).injective

theorem coordinatePoint_submodule (H : DualPoint p) :
    (coordinatePoint p H).submodule = H.submodule.map (dualCoordinates p).toLinearMap := by
  induction H using Projectivization.ind with
  | h f hf =>
    simp only [coordinatePoint, Projectivization.map_mk, Projectivization.submodule_mk,
      Submodule.map_span, Set.image_singleton]

def whiteImage (S : Finset (Geometry.Point p)) : Finset (CoordinatePoint p) :=
  (whitePoints p S).image (coordinatePoint p)

theorem whiteImage_card (S : Finset (Geometry.Point p)) :
    (whiteImage p S).card = (whitePoints p S).card :=
  Finset.card_image_of_injective _ (coordinatePoint_injective p)

theorem black_outside_whiteImage {S : Finset (Geometry.Point p)} {b : DualPoint p}
    (hb : b ∈ blackPoints p S) : coordinatePoint p b ∉ whiteImage p S := by
  intro h
  obtain ⟨e, he, heb⟩ := Finset.mem_image.mp h
  exact ProjectiveLineCap.white_ne_black p he hb (coordinatePoint_injective p heb)

abbrev directionSet (S : Finset (Geometry.Point p)) (b : DualPoint p) (hb : b ∈ blackPoints p S) :
    Finset (Direction p) :=
  ProjectiveProjection.directionSet (ZMod p) (Fin 3) (whiteImage p S) (coordinatePoint p b)
    (black_outside_whiteImage p hb)

abbrev raySize (S : Finset (Geometry.Point p)) (b : DualPoint p) (hb : b ∈ blackPoints p S)
    (i : directionSet p S b hb) : ℕ :=
  ProjectiveProjection.raySize (ZMod p) (Fin 3) (whiteImage p S) (coordinatePoint p b)
    (black_outside_whiteImage p hb) i

def rayDualSpace (b : DualPoint p) (d : Direction p) : Submodule (ZMod p) (DualSpace p) :=
  (raySpace (ZMod p) (Fin 3) (coordinatePoint p b) d).map (dualCoordinates p).symm.toLinearMap

theorem point_mem_rayDualSpace (b H : DualPoint p) (d : Direction p) :
    H.submodule ≤ rayDualSpace p b d ↔
      (coordinatePoint p H).submodule ≤ raySpace (ZMod p) (Fin 3) (coordinatePoint p b) d := by
  rw [coordinatePoint_submodule, rayDualSpace, Submodule.map_equiv_eq_comap_symm]
  exact Submodule.map_le_iff_le_comap.symm

theorem rayDualSpace_finrank (b : DualPoint p) (d : Direction p) :
    Module.finrank (ZMod p) (rayDualSpace p b d) = 2 := by
  rw [rayDualSpace, LinearEquiv.finrank_map_eq, raySpace_finrank]

theorem black_mem_rayDualSpace (b : DualPoint p) (d : Direction p) :
    b ∈ linePoints p (rayDualSpace p b d) := by
  rw [mem_linePoints, point_mem_rayDualSpace]
  exact centre_mem_liftedSpace (ZMod p) (Fin 3) (coordinatePoint p b) d.submodule

theorem white_ray_image (S : Finset (Geometry.Point p)) (b : DualPoint p) (d : Direction p) :
    (linePoints p (rayDualSpace p b d) ∩ whitePoints p S).image (coordinatePoint p) =
      (whiteImage p S).filter
        (fun P => P.submodule ≤ raySpace (ZMod p) (Fin 3) (coordinatePoint p b) d) := by
  ext P
  constructor
  · intro hP
    obtain ⟨H, hH, rfl⟩ := Finset.mem_image.mp hP
    obtain ⟨hline, hwhite⟩ := Finset.mem_inter.mp hH
    exact Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨H, hwhite, rfl⟩,
      (point_mem_rayDualSpace p b H d).mp ((mem_linePoints p _ H).mp hline)⟩
  · intro hP
    obtain ⟨himage, hspace⟩ := Finset.mem_filter.mp hP
    obtain ⟨H, hwhite, rfl⟩ := Finset.mem_image.mp himage
    exact Finset.mem_image.mpr ⟨H, Finset.mem_inter.mpr
      ⟨(mem_linePoints p _ H).mpr ((point_mem_rayDualSpace p b H d).mpr hspace), hwhite⟩, rfl⟩

theorem raySize_white_card {S : Finset (Geometry.Point p)} {b : DualPoint p}
    (hb : b ∈ blackPoints p S) (i : directionSet p S b hb) :
    raySize p S b hb i = (linePoints p (rayDualSpace p b i.val) ∩ whitePoints p S).card := by
  calc
    _ = ((whiteImage p S).filter (fun P => P.submodule ≤
        raySpace (ZMod p) (Fin 3) (coordinatePoint p b) i.val)).card :=
      ProjectiveProjectionFibres.raySize_eq_card (ZMod p) (Fin 3) (whiteImage p S)
        (coordinatePoint p b) (black_outside_whiteImage p hb) i
    _ = _ := by
      rw [← white_ray_image]
      exact Finset.card_image_of_injective _ (coordinatePoint_injective p)

theorem white_ray_nonempty {S : Finset (Geometry.Point p)} {b : DualPoint p}
    (hb : b ∈ blackPoints p S) (i : directionSet p S b hb) :
    (linePoints p (rayDualSpace p b i.val) ∩ whitePoints p S).Nonempty := by
  apply Finset.card_pos.mp
  rw [← raySize_white_card p hb i]
  exact ProjectiveProjection.raySize_pos (ZMod p) (Fin 3) _ _ _ i

theorem two_le_raySize {S : Finset (Geometry.Point p)} (hcard : S.card = p ^ 2)
    (hS : Geometry.PDivisible p S) {b : DualPoint p} (hb : b ∈ blackPoints p S)
    (i : directionSet p S b hb) : 2 ≤ raySize p S b hb i := by
  have h := ProjectiveBlackLine.weight_add_one_le_white_on_line p hcard hS
    (rayDualSpace p b i.val) (rayDualSpace_finrank p b i.val) (white_ray_nonempty p hb i)
    b hb (black_mem_rayDualSpace p b i.val)
  have hw := ProjectiveLineCap.black_weight_pos p hb
  rw [← raySize_white_card p hb i] at h
  omega

theorem raySize_le_half {S : Finset (Geometry.Point p)} (hcard : S.card = p ^ 2)
    (hS : Geometry.PDivisible p S) (hnon : ¬ Geometry.IsCylinder p S)
    {b : DualPoint p} (hb : b ∈ blackPoints p S) (i : directionSet p S b hb) :
    raySize p S b hb i ≤ (p - 1) / 2 := by
  rw [raySize_white_card p hb i]
  exact ProjectiveLineCap.line_white_card_le_half p hcard hS hnon
    (rayDualSpace p b i.val) (rayDualSpace_finrank p b i.val)

theorem sum_raySize {S : Finset (Geometry.Point p)} {b : DualPoint p}
    (hb : b ∈ blackPoints p S) :
    (∑ i : directionSet p S b hb, raySize p S b hb i) = (whitePoints p S).card := by
  exact (ProjectiveProjectionFibres.sum_raySize (ZMod p) (Fin 3) (whiteImage p S)
    (coordinatePoint p b) (black_outside_whiteImage p hb)).trans (whiteImage_card p S)

theorem directionSet_nonempty {S : Finset (Geometry.Point p)} {b : DualPoint p}
    (hb : b ∈ blackPoints p S) : (directionSet p S b hb).Nonempty := by
  let x : whiteImage p S := ⟨coordinatePoint p (infinity p),
    Finset.mem_image.mpr ⟨infinity p, ProjectiveCover.infinity_mem_whitePoints p S, rfl⟩⟩
  exact ⟨ProjectiveProjection.projection (ZMod p) (Fin 3) (whiteImage p S)
    (coordinatePoint p b) (black_outside_whiteImage p hb) x,
    Finset.mem_image.mpr ⟨x, Finset.mem_univ _, rfl⟩⟩

theorem exists_minimal_ray {S : Finset (Geometry.Point p)} {b : DualPoint p}
    (hb : b ∈ blackPoints p S) :
    ∃ i : directionSet p S b hb, ∀ j : directionSet p S b hb,
      raySize p S b hb i ≤ raySize p S b hb j := by
  let : Nonempty (directionSet p S b hb) := (directionSet_nonempty p hb).to_subtype
  obtain ⟨i, _hi, hmin⟩ := Finset.exists_min_image Finset.univ (raySize p S b hb) Finset.univ_nonempty
  exact ⟨i, fun j => hmin j (Finset.mem_univ _)⟩

theorem minimum_times_directions_le_white {S : Finset (Geometry.Point p)} {b : DualPoint p}
    (hb : b ∈ blackPoints p S) (r : ℕ) (hr : ∀ i : directionSet p S b hb, r ≤ raySize p S b hb i) :
    r * (directionSet p S b hb).card ≤ (whitePoints p S).card := by
  calc
    _ = ∑ _i : directionSet p S b hb, r := by simp [mul_comm]
    _ ≤ ∑ i : directionSet p S b hb, raySize p S b hb i := Finset.sum_le_sum fun i _ => hr i
    _ = _ := sum_raySize p hb

def whiteRay (S : Finset (Geometry.Point p)) (b : DualPoint p) (hb : b ∈ blackPoints p S)
    (i : directionSet p S b hb) : Finset (DualPoint p) :=
  linePoints p (rayDualSpace p b i.val) ∩ whitePoints p S

theorem rays_partition {S : Finset (Geometry.Point p)} {b : DualPoint p}
    (hb : b ∈ blackPoints p S) :
    Finset.univ.biUnion (whiteRay p S b hb) = whitePoints p S := by
  ext H
  constructor
  · intro hH
    obtain ⟨i, _hi, hH⟩ := Finset.mem_biUnion.mp hH
    exact (Finset.mem_inter.mp hH).2
  · intro hH
    let P : whiteImage p S := ⟨coordinatePoint p H, Finset.mem_image.mpr ⟨H, hH, rfl⟩⟩
    let i := ProjectiveProjection.projectionIndex (ZMod p) (Fin 3) (whiteImage p S)
      (coordinatePoint p b) (black_outside_whiteImage p hb) P
    have hP : coordinatePoint p H ≠ coordinatePoint p b := by
      intro h
      exact ProjectiveLineCap.white_ne_black p hH hb (coordinatePoint_injective p h)
    have hspace : H.submodule ≤ rayDualSpace p b i.val := by
      rw [point_mem_rayDualSpace, point_mem_raySpace (ZMod p) (Fin 3) (coordinatePoint p b)
        (coordinatePoint p H) hP i.val]
      rfl
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, Finset.mem_inter.mpr
      ⟨(mem_linePoints p _ H).mpr hspace, hH⟩⟩

theorem rays_pairwise_disjoint {S : Finset (Geometry.Point p)} {b : DualPoint p}
    (hb : b ∈ blackPoints p S) :
    Pairwise (fun i j : directionSet p S b hb => Disjoint (whiteRay p S b hb i) (whiteRay p S b hb j)) := by
  intro i j hij
  apply Finset.disjoint_left.mpr
  intro H hHi hHj
  obtain ⟨hHi, hwhite⟩ := Finset.mem_inter.mp hHi
  obtain ⟨hHj, _hwhite⟩ := Finset.mem_inter.mp hHj
  have hP : coordinatePoint p H ≠ coordinatePoint p b := by
    intro h
    exact ProjectiveLineCap.white_ne_black p hwhite hb (coordinatePoint_injective p h)
  have hi := (point_mem_raySpace (ZMod p) (Fin 3) (coordinatePoint p b) (coordinatePoint p H) hP i.val).mp
    ((point_mem_rayDualSpace p b H i.val).mp ((mem_linePoints p _ H).mp hHi))
  have hj := (point_mem_raySpace (ZMod p) (Fin 3) (coordinatePoint p b) (coordinatePoint p H) hP j.val).mp
    ((point_mem_rayDualSpace p b H j.val).mp ((mem_linePoints p _ H).mp hHj))
  exact hij (Subtype.ext (hi.symm.trans hj))

end Cylinder.BlackProjection

end
