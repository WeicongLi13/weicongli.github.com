module

public import Cylinder.RationalFractionEvaluation
public import Cylinder.FinitePointSheaf

/-! Actual evaluation of sections of the global homogeneous-fraction
twist at normalized rational points, compatible with restriction. -/

@[expose] public section
noncomputable section
open scoped Classical
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Cylinder.RationalTwistEvaluation

open MvPolynomial AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open TopCat TopologicalSpace Opposite
open Cylinder.CoordinateLaurentLocalization Cylinder.CoordinateTwistChartModule
open Cylinder.GlobalTwistLocalFractions Cylinder.GlobalTwistKSheaf
open Cylinder.ProjectivePointInProj Cylinder.RationalFractionEvaluation

attribute [local instance] MvPolynomial.gradedAlgebra

universe u
variable (K : Type u) [Field K]

theorem section_value_mem_range (v : ℤ) (x : Fin 2 → K) (U : (plane K).Opens)
    (hx : rayPoint x ∈ U) (s : sectionsSubmodule K v U) :
    s.val ⟨rayPoint x, hx⟩ ∈ (toFull K x).range := by
  rcases s.property ⟨rayPoint x, hx⟩ with ⟨V, hv, i, m, n, H, B, hd, hH, hB, hb, he⟩
  have hs : s.val ⟨rayPoint x, hx⟩ = Localization.mk H ⟨B, hb ⟨rayPoint x, hv⟩⟩ := by
    simpa only [Opens.apply_mk] using he ⟨rayPoint x, hv⟩
  exact hs ▸ fraction_mem_range K x H B n hB (hb ⟨rayPoint x, hv⟩)

def sectionToRange (v : ℤ) (x : Fin 2 → K) (U : (plane K).Opens)
    (hx : rayPoint x ∈ U) : sectionsSubmodule K v U →ₗ[K] (toFull K x).range where
  toFun s := ⟨s.val ⟨rayPoint x, hx⟩, section_value_mem_range K v x U hx s⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def evaluation (v : ℤ) (x : Fin 2 → K) (U : (plane K).Opens)
    (hx : rayPoint x ∈ U) : sectionsSubmodule K v U →ₗ[K] K :=
  (rangeEvaluation K x).toLinearMap.comp (sectionToRange K v x U hx)

theorem evaluation_restrict (v : ℤ) (x : Fin 2 → K) {U V : (plane K).Opens}
    (i : U ⟶ V) (hx : rayPoint x ∈ U) (s : sectionsSubmodule K v V) :
    evaluation K v x U hx ((twistK K v).obj.map i.op s) =
      evaluation K v x V (i.le hx) s := rfl

theorem evaluation_fraction (v : ℤ) (x : Fin 2 → K) (U : (plane K).Opens)
    (hx : rayPoint x ∈ U) (s : sectionsSubmodule K v U)
    (H B : PlaneRing K) (n : ℕ) (hB : B.IsHomogeneous n)
    (hb : B ∉ (rayPoint x).asHomogeneousIdeal)
    (hs : s.val ⟨rayPoint x, hx⟩ = Localization.mk H ⟨B, hb⟩) :
    evaluation K v x U hx s = eval (normalized K x) H / eval (normalized K x) B := by
  have hm := section_value_mem_range K v x U hx s
  have hf := fraction_mem_range K x H B n hB hb
  change rangeEvaluation K x ⟨s.val ⟨rayPoint x, hx⟩, hm⟩ = _
  have he : (⟨s.val ⟨rayPoint x, hx⟩, hm⟩ : (toFull K x).range) =
      ⟨Localization.mk H ⟨B, hb⟩, hf⟩ := Subtype.ext hs
  rw [he]
  exact rangeEvaluation_fraction K x H B n hB hb hf

end Cylinder.RationalTwistEvaluation
end
