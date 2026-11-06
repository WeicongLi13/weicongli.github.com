module

public import Cylinder.BlackProjection

/-! The exact weight count on each actual white ray through a black point. -/

@[expose] public section
noncomputable section
open scoped Classical BigOperators
namespace Cylinder.ExactRayMomentsBlackBalance
open Cylinder.ProjectiveGeometry Cylinder.ProjectiveBalance Cylinder.DualLineBalance
open Cylinder.BlackProjection
variable (p : ℕ) [Fact p.Prime]

def otherBlackOnRay (S : Finset (Geometry.Point p)) (b : DualPoint p) (hb : b ∈ blackPoints p S)
    (i : directionSet p S b hb) : Finset (DualPoint p) :=
  (linePoints p (rayDualSpace p b i.val) ∩ blackPoints p S).erase b

theorem actual_white_ray_weight_balance {S : Finset (Geometry.Point p)}
    (hcard : S.card = p ^ 2) (hS : Geometry.PDivisible p S)
    {b : DualPoint p} (hb : b ∈ blackPoints p S) (i : directionSet p S b hb) :
    raySize p S b hb i = weight p S b + 1 + ∑ B ∈ otherBlackOnRay p S b hb i, weight p S B := by
  let T := linePoints p (rayDualSpace p b i.val) ∩ blackPoints p S
  have hbT : b ∈ T := Finset.mem_inter.mpr ⟨black_mem_rayDualSpace p b i.val, hb⟩
  have hsum := Finset.add_sum_erase T (weight p S) hbT
  have hbalance := line_balance p hcard hS (rayDualSpace p b i.val)
    (rayDualSpace_finrank p b i.val) (white_ray_nonempty p hb i)
  rw [← raySize_white_card p hb i] at hbalance
  have hpos := ProjectiveProjection.raySize_pos (ZMod p) (Fin 3) (whiteImage p S)
    (coordinatePoint p b) (black_outside_whiteImage p hb) i
  change weight p S b + (∑ B ∈ otherBlackOnRay p S b hb i, weight p S B) =
    (∑ B ∈ T, weight p S B) at hsum
  change (∑ B ∈ T, weight p S B) = raySize p S b hb i - 1 at hbalance
  change 0 < raySize p S b hb i at hpos
  have hri := (Nat.sub_add_cancel (show 1 ≤ raySize p S b hb i by omega)).symm
  rw [← hbalance] at hri
  calc
    raySize p S b hb i = (∑ B ∈ T, weight p S B) + 1 := hri
    _ = (weight p S b + ∑ B ∈ otherBlackOnRay p S b hb i, weight p S B) + 1 :=
      congrArg (fun n => n + 1) hsum.symm
    _ = _ := by omega

end Cylinder.ExactRayMomentsBlackBalance
end
