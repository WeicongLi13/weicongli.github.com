module

public import Cylinder.BlackProjectionLineCap
public import Cylinder.RationalPlaneLine

/-! Prime-field coefficient line equations are the actual rank-two direction subspaces. -/

@[expose] public section
noncomputable section

namespace Cylinder.BlackProjectionRationalLines

open Cylinder.BlackProjection Cylinder.BlackProjectionLineCap Cylinder.ProjectiveGeometry
open Cylinder.ProjectiveBalance Cylinder.PlaneCrossProduct
open scoped Classical BigOperators

section LinearEquation

variable {K : Type*} [Field K]

def dotMap (c : Fin 3 → K) : (Fin 3 → K) →ₗ[K] K where
  toFun := dot c
  map_add' x y := by simp [dot, mul_add, Finset.sum_add_distrib]
  map_smul' a x := by simp [dot, mul_left_comm, Finset.mul_sum]

theorem dotMap_surjective (c : Fin 3 → K) (hc : c ≠ 0) : Function.Surjective (dotMap c) := by
  obtain ⟨j, hj⟩ : ∃ j, c j ≠ 0 := by
    by_contra h
    apply hc
    funext j
    simpa using not_exists.mp h j
  intro a
  refine ⟨Pi.single j (a / c j), ?_⟩
  change dot c (Pi.single j (a / c j)) = a
  simp [dot, Pi.single_apply, mul_div_cancel₀ a hj]

theorem dotMap_kernel_finrank (c : Fin 3 → K) (hc : c ≠ 0) :
    Module.finrank K (LinearMap.ker (dotMap c)) = 2 := by
  have h := (dotMap c).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr (dotMap_surjective c hc), finrank_top,
    Module.finrank_self, Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at h
  omega

end LinearEquation

variable (p : ℕ) [Fact p.Prime]

theorem coefficient_line_eq_directionLine {S : Finset (Geometry.Point p)} {b : DualPoint p}
    (hb : b ∈ blackPoints p S) (c : Fin 3 → ZMod p) :
    (directionSet p S b hb).filter (fun P => dot c P.rep = 0) =
      directionLine p S b hb (LinearMap.ker (dotMap c)) := by
  ext P
  simp only [directionLine, Finset.mem_filter]
  rw [ProjectiveIncidence.submodule_le_iff_rep_mem, LinearMap.mem_ker]
  rfl

theorem lineCap {S : Finset (Geometry.Point p)} (hcard : S.card = p ^ 2)
    (hS : Geometry.PDivisible p S) (hnon : ¬ Geometry.IsCylinder p S)
    {b : DualPoint p} (hb : b ∈ blackPoints p S) (r : ℕ) (hrpos : 0 < r)
    (hr : ∀ i : directionSet p S b hb, r ≤ raySize p S b hb i) :
    RationalPlaneLine.LineCap (directionSet p S b hb) ((p - 1) / r) := by
  intro c hc
  convert directionLine_card_le p hcard hS hnon hb r hrpos hr (LinearMap.ker (dotMap c))
    (dotMap_kernel_finrank c hc) using 1
  congr 1
  ext P
  simp only [directionLine, Finset.mem_filter]
  rw [ProjectiveIncidence.submodule_le_iff_rep_mem, LinearMap.mem_ker]
  rfl

end Cylinder.BlackProjectionRationalLines

end
