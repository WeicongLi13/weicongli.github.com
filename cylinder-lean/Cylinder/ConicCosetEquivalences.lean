module

public import Cylinder.ConicFiniteBlocks

/-! Actual parameter bijections for both conic blocks, with the same
finite subgroup. These retain the full pointwise data for vector sums. -/

@[expose] public section
noncomputable section
open scoped Classical

namespace Cylinder.ConicCosetEquivalences
open Cylinder.RationalPlaneLine Cylinder.ConicAffineParametrization
open Cylinder.ConicAffineDirections Cylinder.ConicStandardBlocks
open Cylinder.ConicFiniteProductMatchings Cylinder.ConicRootPairsGeometry

theorem parameter_coset_equiv {G I : Type*} [Group G] [Fintype I]
    (u : I → G) (hu : Function.Injective u) (H : Subgroup G) (a : G)
    (hcoset : ∀ x, x ∈ parameterSet u ↔ a⁻¹ * x ∈ H) :
    ∃ e : I ≃ H, ∀ i, u i = a * (e i).val := by
  let f : I → H := fun i => ⟨a⁻¹ * u i,
    (hcoset _).mp (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)⟩
  have hbij : Function.Bijective f := by
    constructor
    · intro i j hij
      exact hu (mul_left_cancel (congrArg Subtype.val hij))
    · intro t
      have hmem : a * t.val ∈ parameterSet u := (hcoset _).mpr (by simpa using t.property)
      obtain ⟨i, _hi, heq⟩ := Finset.mem_image.mp hmem
      refine ⟨i, Subtype.ext ?_⟩
      change a⁻¹ * u i = t.val
      rw [heq, inv_mul_cancel_left]
  refine ⟨Equiv.ofBijective f hbij, ?_⟩
  intro i
  change u i = a * (a⁻¹ * u i)
  simp

variable {R K : Type*} [Field R] [Field K]
local instance : DecidableEq Kˣ := Classical.decEq _

theorem hyperbola_block_equivalences (ι : R →+* K)
    (g : (Fin 3 → K) ≃ₗ[K] (Fin 3 → K)) (X Y C : Finset (PlanePoint R))
    (A : StandardBlocks ι g (fun x => x⁻¹) X Y C)
    (hn : ∀ P ∈ X ∪ Y, parameter ι g P ≠ 0) (anchor : X) (other : Y) :
    ∃ H : Subgroup Kˣ, Finite H ∧ Nat.card H = C.card ∧
      ∃ a b : Kˣ, ∃ eX : X ≃ H, ∃ eY : Y ≃ H,
        (∀ P : X, affineRepresentative ι g P.val = hyperbolaVector (a * (eX P).val)) ∧
        (∀ P : Y, affineRepresentative ι g P.val = hyperbolaVector (b * (eY P).val)) := by
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
    exact ⟨T, hT.trans (hyperbola_slope _ _ (Units.ne_zero (u P)) (Units.ne_zero (v Q))
      (cross_parameter_ne ι g (fun x => x⁻¹) X Y C A P Q))⟩
  have hmatch : ∀ T, ∃ e : X ≃ Y, ∀ P, slope T = hyperbolaSlope (u P * v (e P)) := by
    intro T
    obtain ⟨e, he⟩ := matching_slopes ι g (fun x => x⁻¹) X Y C A T
    exact ⟨e, fun P => (he P).trans (hyperbola_slope _ _ (Units.ne_zero (u P))
      (Units.ne_zero (v (e P))) (cross_parameter_ne ι g (fun x => x⁻¹) X Y C A P (e P)))⟩
  obtain ⟨H, hfin, hcard, hleft, hright⟩ := hyperbola_parameters_are_cosets u v slope hu hv hs
    anchor other (by simpa only [Fintype.card_coe] using A.cardX)
      (by simpa only [Fintype.card_coe] using A.cardY) hcross hmatch
  obtain ⟨eX, heX⟩ := parameter_coset_equiv u hu H (u anchor) hleft
  obtain ⟨eY, heY⟩ := parameter_coset_equiv v hv H (v other)
    (fun x => by simpa only [mul_comm] using hright x)
  refine ⟨H, hfin, by simpa only [Fintype.card_coe] using hcard, u anchor, v other, eX, eY, ?_, ?_⟩
  · intro P
    rw [← heX P, A.shape P.val (Finset.mem_union_left _ P.property)]
    rfl
  · intro P
    rw [← heY P, A.shape P.val (Finset.mem_union_right _ P.property)]
    rfl

end Cylinder.ConicCosetEquivalences
end
