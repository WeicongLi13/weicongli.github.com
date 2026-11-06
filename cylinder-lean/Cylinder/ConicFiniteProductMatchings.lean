module

public import Cylinder.FiniteCosetNormalization
public import Cylinder.ConicAffineParametrization

/-! Actual conic secant parameters and bijective block matchings force
the smallest possible product or sum set. Subgroup cosets are conclusions,
never closure or coset hypotheses. -/

@[expose] public section
noncomputable section
open scoped Classical

namespace Cylinder.ConicFiniteProductMatchings
open Cylinder.FiniteCosetAlgebra Cylinder.FiniteCosetNormalization

variable {K I J T : Type*} [Field K] [Fintype I] [Fintype J] [Fintype T]
local instance : DecidableEq Kˣ := Classical.decEq _

def parameterSet {G : Type*} (u : I → G) : Finset G := Finset.univ.image u

theorem parameterSet_card {G : Type*} (u : I → G) (hu : Function.Injective u) :
    (parameterSet u).card = Fintype.card I := by
  rw [parameterSet, Finset.card_image_of_injective _ hu, Finset.card_univ]

def hyperbolaSlope (x : Kˣ) : K := -(x : K)⁻¹

theorem hyperbolaSlope_injective : Function.Injective (hyperbolaSlope (K := K)) := by
  intro x y h
  apply Units.ext
  exact inv_injective (neg_injective h)

theorem hyperbola_product_image (u : I → Kˣ) (v : J → Kˣ) (slope : T → K) (anchor : I)
    (hcross : ∀ i j, ∃ t, slope t = hyperbolaSlope (u i * v j))
    (hmatch : ∀ t, ∃ e : I ≃ J, ∀ i, slope t = hyperbolaSlope (u i * v (e i))) :
    (products (parameterSet u) (parameterSet v)).image hyperbolaSlope = parameterSet slope := by
  ext x
  constructor
  · intro hx
    obtain ⟨a, ha, hax⟩ := Finset.mem_image.mp hx
    obtain ⟨⟨b, c⟩, hbc, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨hb, hc⟩ := Finset.mem_product.mp hbc
    obtain ⟨i, _hi, rfl⟩ := Finset.mem_image.mp hb
    obtain ⟨j, _hj, rfl⟩ := Finset.mem_image.mp hc
    obtain ⟨t, ht⟩ := hcross i j
    exact Finset.mem_image.mpr ⟨t, Finset.mem_univ _, ht.trans hax⟩
  · intro hx
    obtain ⟨t, _ht, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨e, he⟩ := hmatch t
    refine Finset.mem_image.mpr ⟨u anchor * v (e anchor), ?_, (he anchor).symm⟩
    exact Finset.mem_image.mpr ⟨(u anchor, v (e anchor)), Finset.mem_product.mpr
      ⟨Finset.mem_image.mpr ⟨anchor, Finset.mem_univ _, rfl⟩,
        Finset.mem_image.mpr ⟨e anchor, Finset.mem_univ _, rfl⟩⟩, rfl⟩

theorem hyperbola_parameters_are_cosets (u : I → Kˣ) (v : J → Kˣ) (slope : T → K)
    (hu : Function.Injective u) (hv : Function.Injective v) (hs : Function.Injective slope)
    (anchor : I) (other : J) (hI : Fintype.card I = Fintype.card T)
    (hJ : Fintype.card J = Fintype.card T)
    (hcross : ∀ i j, ∃ t, slope t = hyperbolaSlope (u i * v j))
    (hmatch : ∀ t, ∃ e : I ≃ J, ∀ i, slope t = hyperbolaSlope (u i * v (e i))) :
    ∃ H : Subgroup Kˣ, Finite H ∧ Nat.card H = Fintype.card T ∧
      (∀ x, x ∈ parameterSet u ↔ (u anchor)⁻¹ * x ∈ H) ∧
      (∀ y, y ∈ parameterSet v ↔ y * (v other)⁻¹ ∈ H) := by
  have himage := hyperbola_product_image u v slope anchor hcross hmatch
  have hc : (products (parameterSet u) (parameterSet v)).card = Fintype.card T := by
    have h := congrArg Finset.card himage
    rw [Finset.card_image_of_injective _ hyperbolaSlope_injective, parameterSet_card slope hs] at h
    exact h
  obtain ⟨H, hfin, hcard, hleft, hright⟩ := minimal_products_are_cosets (parameterSet u) (parameterSet v)
    (u anchor) (v other) (Finset.mem_image.mpr ⟨anchor, Finset.mem_univ _, rfl⟩)
    (Finset.mem_image.mpr ⟨other, Finset.mem_univ _, rfl⟩)
    (by rw [hc, parameterSet_card u hu, hI]) (by rw [hc, parameterSet_card v hv, hJ])
  rw [parameterSet_card u hu, hI] at hcard
  exact ⟨H, hfin, hcard, hleft, hright⟩

theorem parabola_sum_image (u : I → K) (v : J → K) (slope : T → K) (anchor : I)
    (hcross : ∀ i j, ∃ t, slope t = u i + v j)
    (hmatch : ∀ t, ∃ e : I ≃ J, ∀ i, slope t = u i + v (e i)) :
    sums (parameterSet u) (parameterSet v) = parameterSet slope := by
  ext x
  constructor
  · intro hx
    obtain ⟨⟨b, c⟩, hbc, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨hb, hc⟩ := Finset.mem_product.mp hbc
    obtain ⟨i, _hi, rfl⟩ := Finset.mem_image.mp hb
    obtain ⟨j, _hj, rfl⟩ := Finset.mem_image.mp hc
    obtain ⟨t, ht⟩ := hcross i j
    exact Finset.mem_image.mpr ⟨t, Finset.mem_univ _, ht⟩
  · intro hx
    obtain ⟨t, _ht, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨e, he⟩ := hmatch t
    exact Finset.mem_image.mpr ⟨(u anchor, v (e anchor)), Finset.mem_product.mpr
      ⟨Finset.mem_image.mpr ⟨anchor, Finset.mem_univ _, rfl⟩,
        Finset.mem_image.mpr ⟨e anchor, Finset.mem_univ _, rfl⟩⟩, (he anchor).symm⟩

theorem parabola_parameters_are_cosets (u : I → K) (v : J → K) (slope : T → K)
    (hu : Function.Injective u) (hv : Function.Injective v) (hs : Function.Injective slope)
    (anchor : I) (other : J) (hI : Fintype.card I = Fintype.card T)
    (hJ : Fintype.card J = Fintype.card T)
    (hcross : ∀ i j, ∃ t, slope t = u i + v j)
    (hmatch : ∀ t, ∃ e : I ≃ J, ∀ i, slope t = u i + v (e i)) :
    ∃ H : AddSubgroup K, Finite H ∧ Nat.card H = Fintype.card T ∧
      (∀ x, x ∈ parameterSet u ↔ -u anchor + x ∈ H) ∧
      (∀ y, y ∈ parameterSet v ↔ y + -v other ∈ H) := by
  have hc : (sums (parameterSet u) (parameterSet v)).card = Fintype.card T := by
    rw [parabola_sum_image u v slope anchor hcross hmatch, parameterSet_card slope hs]
  obtain ⟨H, hfin, hcard, hleft, hright⟩ := minimal_sums_are_cosets (parameterSet u) (parameterSet v)
    (u anchor) (v other) (Finset.mem_image.mpr ⟨anchor, Finset.mem_univ _, rfl⟩)
    (Finset.mem_image.mpr ⟨other, Finset.mem_univ _, rfl⟩)
    (by rw [hc, parameterSet_card u hu, hI]) (by rw [hc, parameterSet_card v hv, hJ])
  rw [parameterSet_card u hu, hI] at hcard
  exact ⟨H, hfin, hcard, hleft, hright⟩

end Cylinder.ConicFiniteProductMatchings
end
