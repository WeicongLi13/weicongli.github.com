module

public import Cylinder.ConicStandardBlocks
public import Cylinder.ConicRootPairsGeometry

/-! Subgroup cosets forced by actual point blocks on either standard conic.
The finite product and sum cardinalities are derived from their secants
and bijective matchings. -/

@[expose] public section
noncomputable section
open scoped Classical

namespace Cylinder.ConicFiniteBlocks
open Cylinder.RationalPlaneLine Cylinder.ConicAffineParametrization
open Cylinder.ConicAffineDirections Cylinder.ConicStandardBlocks
open Cylinder.ConicFiniteProductMatchings Cylinder.ConicRootPairsGeometry

variable {R K : Type*} [Field R] [Field K]
local instance : DecidableEq Kˣ := Classical.decEq _

theorem hyperbola_blocks_are_cosets (ι : R →+* K)
    (g : (Fin 3 → K) ≃ₗ[K] (Fin 3 → K)) (X Y C : Finset (PlanePoint R))
    (A : StandardBlocks ι g (fun x => x⁻¹) X Y C)
    (hn : ∀ P ∈ X ∪ Y, parameter ι g P ≠ 0) (anchor : X) (other : Y) :
    ∃ H : Subgroup Kˣ, Finite H ∧ Nat.card H = C.card ∧
      ∃ a : Kˣ, ∀ t ∈ H, ∃ P : X,
        affineRepresentative ι g P.val = hyperbolaVector (a * t) := by
  let u : X → Kˣ := fun P => Units.mk0 (parameter ι g P.val)
    (hn P.val (Finset.mem_union_left _ P.property))
  let v : Y → Kˣ := fun P => Units.mk0 (parameter ι g P.val)
    (hn P.val (Finset.mem_union_right _ P.property))
  let slope : C → K := fun T => directionSlope ι g T.val
  have hu : Function.Injective u := by
    intro P Q heq
    exact left_parameter_injective ι g (fun x => x⁻¹) X Y C A (congrArg Units.val heq)
  have hv : Function.Injective v := by
    intro P Q heq
    exact right_parameter_injective ι g (fun x => x⁻¹) X Y C A (congrArg Units.val heq)
  have hs : Function.Injective slope := slope_injective ι g (fun x => x⁻¹) X Y C A anchor
  have hcross : ∀ P Q, ∃ T, slope T = hyperbolaSlope (u P * v Q) := by
    intro P Q
    obtain ⟨T, hT⟩ := cross_slopes ι g (fun x => x⁻¹) X Y C A P Q
    refine ⟨T, hT.trans ?_⟩
    exact hyperbola_slope _ _ (Units.ne_zero (u P)) (Units.ne_zero (v Q))
      (cross_parameter_ne ι g (fun x => x⁻¹) X Y C A P Q)
  have hmatch : ∀ T, ∃ e : X ≃ Y, ∀ P, slope T = hyperbolaSlope (u P * v (e P)) := by
    intro T
    obtain ⟨e, he⟩ := matching_slopes ι g (fun x => x⁻¹) X Y C A T
    refine ⟨e, fun P => (he P).trans ?_⟩
    exact hyperbola_slope _ _ (Units.ne_zero (u P)) (Units.ne_zero (v (e P)))
      (cross_parameter_ne ι g (fun x => x⁻¹) X Y C A P (e P))
  obtain ⟨H, hfin, hcard, hleft, _hright⟩ := hyperbola_parameters_are_cosets u v slope hu hv hs
    anchor other (by simpa only [Fintype.card_coe] using A.cardX)
      (by simpa only [Fintype.card_coe] using A.cardY) hcross hmatch
  refine ⟨H, hfin, by simpa only [Fintype.card_coe] using hcard, u anchor, ?_⟩
  intro t ht
  have hmem : u anchor * t ∈ parameterSet u := (hleft _).mpr (by simpa using ht)
  obtain ⟨P, _hP, heq⟩ := Finset.mem_image.mp hmem
  refine ⟨P, ?_⟩
  rw [A.shape P.val (Finset.mem_union_left _ P.property), ← heq]
  rfl

theorem parabola_blocks_are_cosets (ι : R →+* K)
    (g : (Fin 3 → K) ≃ₗ[K] (Fin 3 → K)) (X Y C : Finset (PlanePoint R))
    (A : StandardBlocks ι g (fun x => x ^ 2) X Y C) (anchor : X) (other : Y) :
    ∃ H : AddSubgroup K, Finite H ∧ Nat.card H = C.card := by
  let u : X → K := fun P => parameter ι g P.val
  let v : Y → K := fun P => parameter ι g P.val
  let slope : C → K := fun T => directionSlope ι g T.val
  have hcross : ∀ P Q, ∃ T, slope T = u P + v Q := by
    intro P Q
    obtain ⟨T, hT⟩ := cross_slopes ι g (fun x => x ^ 2) X Y C A P Q
    exact ⟨T, hT.trans (parabola_slope _ _ (cross_parameter_ne ι g (fun x => x ^ 2) X Y C A P Q))⟩
  have hmatch : ∀ T, ∃ e : X ≃ Y, ∀ P, slope T = u P + v (e P) := by
    intro T
    obtain ⟨e, he⟩ := matching_slopes ι g (fun x => x ^ 2) X Y C A T
    exact ⟨e, fun P => (he P).trans
      (parabola_slope _ _ (cross_parameter_ne ι g (fun x => x ^ 2) X Y C A P (e P)))⟩
  obtain ⟨H, hfin, hcard, _⟩ := parabola_parameters_are_cosets u v slope
    (left_parameter_injective ι g (fun x => x ^ 2) X Y C A)
    (right_parameter_injective ι g (fun x => x ^ 2) X Y C A)
    (slope_injective ι g (fun x => x ^ 2) X Y C A anchor) anchor other
    (by simpa only [Fintype.card_coe] using A.cardX)
    (by simpa only [Fintype.card_coe] using A.cardY) hcross hmatch
  exact ⟨H, hfin, by simpa only [Fintype.card_coe] using hcard⟩

end Cylinder.ConicFiniteBlocks
end
