module

public import Cylinder.ProductFrobenius
public import Cylinder.DualLineBalance
public import Cylinder.AffinePlanes
public import Cylinder.ProjectiveCover

/-!
# Restriction of the actual products to the plane at infinity

Each non-infinity dual point has a nonzero spatial normal. Normalising
that normal groups the restricted factors into the actual parallel
pencils, so the equality of exponents follows from the proved line balance.
-/

@[expose] public section

noncomputable section

namespace Cylinder.ProductRestriction

open MvPolynomial Cylinder.ProjectiveGeometry Cylinder.ProjectivePointSet
open Cylinder.ProjectiveBalance Cylinder.ProductFrobenius Cylinder.DualPencils
open Cylinder.DualLineBalance Cylinder.AffinePlanes
open scoped BigOperators Classical LinearAlgebra.Projectivization

variable (p : ℕ) [Fact p.Prime]

abbrev SpatialForm := MvPolynomial (Fin 3) (ZMod p)

def restrictInfinity : Form p →+* SpatialForm p :=
  eval₂Hom C (Fin.cons 0 (fun i => X i))

def spatialForm (d : NormalParam p) : SpatialForm p :=
  ∑ i, C (AffinePlanes.normal p d i) * X i

theorem restrict_planeForm (H : DualPoint p) :
    restrictInfinity p (planeForm p H) =
      ∑ i : Fin 3, C (ProjectivePointSet.normal p H i) * X i := by
  unfold restrictInfinity planeForm linearForm
  rw [map_sum, Fin.sum_univ_succ]
  simp only [map_mul, eval₂Hom_C, eval₂Hom_X', Fin.cons_zero, Fin.cons_succ,
    mul_zero, zero_add]
  rfl

def normalData (a : Geometry.Point p) : NormalParam p × ZMod p :=
  if ha : a = 0 then (Sum.inr (Sum.inr ()), 0)
  else let h := normalisation_exists p ha
       (Classical.choose h, Classical.choose (Classical.choose_spec h))

theorem normalData_spec {a : Geometry.Point p} (ha : a ≠ 0) :
    (normalData p a).2 ≠ 0 ∧ a = (normalData p a).2 •
      AffinePlanes.normal p (normalData p a).1 := by
  simpa only [normalData, dite_eq_right ha] using
    Classical.choose_spec (Classical.choose_spec (normalisation_exists p ha))

def normalDirection (H : DualPoint p) : NormalParam p :=
  (normalData p (ProjectivePointSet.normal p H)).1

def normalScale (H : DualPoint p) : ZMod p :=
  (normalData p (ProjectivePointSet.normal p H)).2

theorem normal_nonzero {H : DualPoint p} (hH : H ≠ infinity p) :
    ProjectivePointSet.normal p H ≠ 0 :=
  fun hz => hH (normal_zero_eq_infinity p hz)

theorem normalScale_ne_zero {H : DualPoint p} (hH : H ≠ infinity p) :
    normalScale p H ≠ 0 := (normalData_spec p (normal_nonzero p hH)).1

theorem normal_eq_scaled {H : DualPoint p} (hH : H ≠ infinity p) :
    ProjectivePointSet.normal p H = normalScale p H •
      AffinePlanes.normal p (normalDirection p H) :=
  (normalData_spec p (normal_nonzero p hH)).2

theorem restrict_planeForm_scaled {H : DualPoint p} (hH : H ≠ infinity p) :
    restrictInfinity p (planeForm p H) =
      C (normalScale p H) * spatialForm p (normalDirection p H) := by
  rw [restrict_planeForm, normal_eq_scaled p hH]
  simp [spatialForm, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum, mul_assoc]

def directionPencil (d : NormalParam p) :=
  pencilSubspace p (AffinePlanes.normal p d) 0

theorem directionPencil_rank (d : NormalParam p) :
    Module.finrank (ZMod p) (directionPencil p d) = 2 :=
  finrank_pencilSubspace p (normal_ne_zero p d) 0

theorem normal_on_pencil {H : DualPoint p} {d : NormalParam p}
    (hH : H.submodule ≤ directionPencil p d) :
    ∃ t : ZMod p, ProjectivePointSet.normal p H = t • AffinePlanes.normal p d := by
  have hrep := (ProjectiveIncidence.submodule_le_iff_rep_mem H _).mp hH
  obtain ⟨a, b, hab⟩ := (Submodule.mem_span_pair).mp hrep
  refine ⟨b, ?_⟩
  funext i
  have hi := LinearMap.congr_fun hab (Pi.single i.succ 1)
  simpa [ProjectivePointSet.normal, infinityFunctional, smul_eq_mul] using hi.symm

theorem direction_eq_of_on_pencil {H : DualPoint p} (hH : H ≠ infinity p)
    {d : NormalParam p} (hline : H.submodule ≤ directionPencil p d) :
    normalDirection p H = d := by
  obtain ⟨b, hb⟩ := normal_on_pencil p hline
  have hb0 : b ≠ 0 := by
    intro hz
    exact normal_nonzero p hH (by simpa [hz] using hb)
  have ht := normalScale_ne_zero p hH
  have heq : AffinePlanes.normal p (normalDirection p H) =
      ((normalScale p H)⁻¹ * b) • AffinePlanes.normal p d := by
    have he := congrArg (fun a : Geometry.Point p => (normalScale p H)⁻¹ • a)
      ((normal_eq_scaled p hH).symm.trans hb)
    simpa only [smul_smul, inv_mul_cancel₀ ht, one_smul] using he
  exact (normal_proportional_unique p (mul_ne_zero (inv_ne_zero ht) hb0) heq).1

theorem on_pencil_of_direction_eq {H : DualPoint p} (hH : H ≠ infinity p)
    {d : NormalParam p} (hd : normalDirection p H = d) :
    H.submodule ≤ directionPencil p d := by
  rw [ProjectiveIncidence.submodule_le_iff_rep_mem]
  apply (Submodule.mem_span_pair).mpr
  refine ⟨constantTerm p H, normalScale p H, ?_⟩
  apply LinearMap.ext
  intro x
  rw [functional_expansion p H.rep x]
  have hn := normal_eq_scaled p hH
  rw [hd] at hn
  have hcoeff : ∀ i : Fin 3, H.rep (Pi.single i.succ 1) =
      normalScale p H * AffinePlanes.normal p d i := by
    intro i
    exact congrFun hn i
  simp [infinityFunctional, affinePlaneFunctional, pairingMap,
    ProjectiveGeometry.pairing, Fin.sum_univ_succ, constantTerm,
    hcoeff, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]
  ring

theorem direction_eq_iff_on_pencil {H : DualPoint p} (hH : H ≠ infinity p)
    (d : NormalParam p) :
    normalDirection p H = d ↔ H ∈ linePoints p (directionPencil p d) := by
  rw [mem_linePoints]
  exact ⟨on_pencil_of_direction_eq p hH, direction_eq_of_on_pencil p hH⟩

theorem black_ne_infinity (S : Finset (Geometry.Point p)) {H : DualPoint p}
    (hH : H ∈ blackPoints p S) : H ≠ infinity p := by
  intro he
  subst H
  have hq : 2 ≤ quotient p S (infinity p) := (Finset.mem_filter.mp hH).2
  simpa [quotient, intersection_infinity_eq_empty] using hq

def whiteWithoutInfinity (S : Finset (Geometry.Point p)) :=
  (whitePoints p S).erase (infinity p)

theorem black_direction_fiber (S : Finset (Geometry.Point p)) (d : NormalParam p) :
    (blackPoints p S).filter (fun H => normalDirection p H = d) =
      linePoints p (directionPencil p d) ∩ blackPoints p S := by
  ext H
  simp only [Finset.mem_filter, Finset.mem_inter]
  constructor
  · rintro ⟨hb, hd⟩
    exact ⟨(direction_eq_iff_on_pencil p (black_ne_infinity p S hb) d).mp hd, hb⟩
  · rintro ⟨hl, hb⟩
    exact ⟨hb, (direction_eq_iff_on_pencil p (black_ne_infinity p S hb) d).mpr hl⟩

theorem white_direction_fiber (S : Finset (Geometry.Point p)) (d : NormalParam p) :
    (whiteWithoutInfinity p S).filter (fun H => normalDirection p H = d) =
      (linePoints p (directionPencil p d) ∩ whitePoints p S).erase (infinity p) := by
  ext H
  by_cases hi : H = infinity p
  · simp [whiteWithoutInfinity, hi]
  · simp only [Finset.mem_filter, whiteWithoutInfinity, Finset.mem_erase,
      Finset.mem_inter, hi, true_and]
    rw [direction_eq_iff_on_pencil p hi]
    constructor
    · rintro ⟨⟨hne, hw⟩, hl⟩
      exact ⟨hne, hl, hw⟩
    · rintro ⟨hne, hl, hw⟩
      exact ⟨⟨hne, hw⟩, hl⟩

theorem direction_exponents_equal {S : Finset (Geometry.Point p)}
    (hcard : S.card = p ^ 2) (hS : Geometry.PDivisible p S) (d : NormalParam p) :
    (∑ H ∈ (blackPoints p S).filter (fun H => normalDirection p H = d), weight p S H) =
      ((whiteWithoutInfinity p S).filter (fun H => normalDirection p H = d)).card := by
  have hi : infinity p ∈ linePoints p (directionPencil p d) ∩ whitePoints p S :=
    Finset.mem_inter.mpr ⟨(mem_linePoints p _ _).mpr (infinity_on_pencil p _ _),
      ProjectiveCover.infinity_mem_whitePoints p S⟩
  rw [black_direction_fiber, white_direction_fiber, Finset.card_erase_of_mem hi]
  exact line_balance p hcard hS _ (directionPencil_rank p d) ⟨_, hi⟩

def canonicalProduct (S : Finset (Geometry.Point p)) : SpatialForm p :=
  ∏ d : NormalParam p,
    spatialForm p d ^ ((whiteWithoutInfinity p S).filter
      (fun H => normalDirection p H = d)).card

def whiteScaleProduct (S : Finset (Geometry.Point p)) : ZMod p :=
  ∏ H ∈ whiteWithoutInfinity p S, normalScale p H

def blackScaleProduct (S : Finset (Geometry.Point p)) : ZMod p :=
  ∏ H ∈ blackPoints p S, normalScale p H ^ weight p S H

theorem whiteScaleProduct_ne_zero (S : Finset (Geometry.Point p)) :
    whiteScaleProduct p S ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro H hH
  exact normalScale_ne_zero p (Finset.mem_erase.mp hH).1

theorem blackScaleProduct_ne_zero (S : Finset (Geometry.Point p)) :
    blackScaleProduct p S ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro H hH
  exact pow_ne_zero _ (normalScale_ne_zero p (black_ne_infinity p S hH))

theorem restricted_white_without_infinity (S : Finset (Geometry.Point p)) :
    restrictInfinity p (∏ H ∈ whiteWithoutInfinity p S, planeForm p H) =
      C (whiteScaleProduct p S) * canonicalProduct p S := by
  rw [map_prod]
  have hf : ∀ H ∈ whiteWithoutInfinity p S,
      restrictInfinity p (planeForm p H) =
      C (normalScale p H) * spatialForm p (normalDirection p H) := by
    intro H hH
    exact restrict_planeForm_scaled p (Finset.mem_erase.mp hH).1
  rw [Finset.prod_congr rfl hf, Finset.prod_mul_distrib, ← map_prod]
  congr 1
  symm
  unfold canonicalProduct
  calc
    _ = ∏ d : NormalParam p, ∏ H ∈ (whiteWithoutInfinity p S).filter
        (fun H => normalDirection p H = d), spatialForm p d := by
      simp only [Finset.prod_const]
    _ = ∏ H ∈ whiteWithoutInfinity p S, spatialForm p (normalDirection p H) :=
      Finset.prod_fiberwise' _ _ _

theorem restricted_black_product {S : Finset (Geometry.Point p)}
    (hcard : S.card = p ^ 2) (hS : Geometry.PDivisible p S) :
    restrictInfinity p (blackProduct p S) =
      C (blackScaleProduct p S) * canonicalProduct p S := by
  unfold blackProduct
  rw [map_prod]
  have hf : ∀ H ∈ blackPoints p S,
      restrictInfinity p (planeForm p H ^ weight p S H) =
      C (normalScale p H ^ weight p S H) *
        spatialForm p (normalDirection p H) ^ weight p S H := by
    intro H hH
    rw [map_pow, restrict_planeForm_scaled p (black_ne_infinity p S hH),
      mul_pow, ← map_pow]
  rw [Finset.prod_congr rfl hf, Finset.prod_mul_distrib, ← map_prod]
  congr 1
  rw [← Finset.prod_fiberwise (blackPoints p S) (normalDirection p)]
  apply Finset.prod_congr rfl
  intro d _
  have hrepl : ∀ H ∈ (blackPoints p S).filter (fun H => normalDirection p H = d),
      spatialForm p (normalDirection p H) ^ weight p S H =
        spatialForm p d ^ weight p S H := by
    intro H hH
    rw [(Finset.mem_filter.mp hH).2]
  rw [Finset.prod_congr rfl hrepl, Finset.prod_pow_eq_pow_sum,
    direction_exponents_equal p hcard hS]

/-- The nonzero residue at infinity is proved from the actual pencil exponents. -/
theorem exists_infinity_residue {S : Finset (Geometry.Point p)}
    (hcard : S.card = p ^ 2) (hS : Geometry.PDivisible p S) :
    ∃ c : ZMod p, c ≠ 0 ∧
      restrictInfinity p (blackProduct p S) =
        C c * restrictInfinity p (∏ H ∈ whiteWithoutInfinity p S, planeForm p H) := by
  refine ⟨blackScaleProduct p S / whiteScaleProduct p S,
    div_ne_zero (blackScaleProduct_ne_zero p S) (whiteScaleProduct_ne_zero p S), ?_⟩
  rw [restricted_black_product p hcard hS, restricted_white_without_infinity,
    ← mul_assoc, ← map_mul, div_mul_cancel₀ _ (whiteScaleProduct_ne_zero p S)]

#print axioms direction_exponents_equal
#print axioms exists_infinity_residue

end Cylinder.ProductRestriction

end
