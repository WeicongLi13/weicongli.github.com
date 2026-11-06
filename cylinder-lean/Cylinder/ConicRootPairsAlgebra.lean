module

public import Cylinder.FieldSubgroupCyclic
public import Cylinder.BMMFieldExtension
public import Mathlib.Tactic.Group

/-! Five actual powers of a finite subgroup generator, and the two
distinct black pair sums used in the hyperbolic case of BMM Lemma 5.
Containment in a geometric white block is not asserted here. -/

@[expose] public section
noncomputable section
open scoped Classical

namespace Cylinder.ConicRootPairsAlgebra

open Cylinder.FieldSubgroupCyclic Cylinder.RationalPlaneLine Cylinder.PlaneCrossProduct
open Cylinder.BMMArcGeometry Cylinder.BMMFieldExtension

variable {K : Type*} [Field K]

def fiveUnits (v : Kˣ) : Fin 5 → Kˣ := ![1, v, v⁻¹, v ^ 2, (v ^ 2)⁻¹]

def shiftedExponent : Fin 5 → Fin 5 := ![2, 3, 1, 4, 0]

theorem shiftedExponent_injective : Function.Injective shiftedExponent := by decide

theorem fiveUnits_shift (v : Kˣ) (i : Fin 5) :
    v ^ 2 * fiveUnits v i = v ^ (shiftedExponent i).val := by
  fin_cases i <;> simp [fiveUnits, shiftedExponent] <;> group

theorem fiveUnits_injective (v : Kˣ) (horder : 5 ≤ orderOf v) : Function.Injective (fiveUnits v) := by
  intro i j hij
  have h := congrArg (fun u : Kˣ => v ^ 2 * u) hij
  rw [fiveUnits_shift, fiveUnits_shift] at h
  have hi : (shiftedExponent i).val < orderOf v := lt_of_lt_of_le (shiftedExponent i).isLt horder
  have hj : (shiftedExponent j).val < orderOf v := lt_of_lt_of_le (shiftedExponent j).isLt horder
  exact shiftedExponent_injective (Fin.ext (pow_injOn_Iio_orderOf hi hj h))

def fiveValues (v : Kˣ) : Fin 5 → K := fun i => (fiveUnits v i : K)

theorem fiveValues_injective (v : Kˣ) (horder : 5 ≤ orderOf v) : Function.Injective (fiveValues v) :=
  Units.val_injective.comp (fiveUnits_injective v horder)

theorem generator_five_mem (H : Subgroup Kˣ) [Finite H] (i : Fin 5) :
    fiveUnits (generator H).val i ∈ H := by
  fin_cases i
  · exact H.one_mem
  · exact (generator H).property
  · exact H.inv_mem (generator H).property
  · exact H.pow_mem (generator H).property 2
  · exact H.inv_mem (H.pow_mem (generator H).property 2)

theorem exists_generator_five (H : Subgroup Kˣ) [Finite H] (hm : 5 ≤ Nat.card H) :
    ∃ v : Kˣ, v ∈ H ∧ orderOf v = Nat.card H ∧ Function.Injective (fiveValues v) ∧
      ∀ i, fiveUnits v i ∈ H := by
  have hord := unit_generator_order H
  exact ⟨(generator H).val, (generator H).property, hord,
    fiveValues_injective _ (by rw [hord]; exact hm), generator_five_mem H⟩

theorem reciprocal_sum_difference_factor (v : K) (hv : v ≠ 0) :
    ((v ^ 2 + (v ^ 2)⁻¹) - (v + v⁻¹)) * v ^ 2 = (v - 1) * (v ^ 3 - 1) := by
  field_simp [hv]
  ring

theorem reciprocal_sums_ne (v : Kˣ) (horder : 5 ≤ orderOf v) :
    (v : K) + (v : K)⁻¹ ≠ (v : K) ^ 2 + ((v : K) ^ 2)⁻¹ := by
  have h1 : v ≠ 1 := by
    simpa only [pow_one] using pow_ne_one_of_lt_orderOf (x := v) (n := 1) (by decide) (by omega)
  have h3 : v ^ 3 ≠ 1 := pow_ne_one_of_lt_orderOf (x := v) (n := 3) (by decide) (by omega)
  intro heq
  have hf := reciprocal_sum_difference_factor (v : K) (Units.ne_zero v)
  rw [← heq, sub_self, zero_mul] at hf
  rcases mul_eq_zero.mp hf.symm with hz | hz
  · exact h1 (Units.ext (sub_eq_zero.mp hz))
  · apply h3
    exact Units.ext (by simpa only [Units.val_pow_eq_pow_val, Units.val_one] using sub_eq_zero.mp hz)

def whiteVector : Fin 3 → K := ![1, 1, 1]

def pairVector (v : Kˣ) : Fin 3 → K :=
  ![(v : K) + (v : K)⁻¹, (v : K) + (v : K)⁻¹, 2]

def squarePairVector (v : Kˣ) : Fin 3 → K :=
  ![(v : K) ^ 2 + ((v : K) ^ 2)⁻¹, (v : K) ^ 2 + ((v : K) ^ 2)⁻¹, 2]

theorem whiteVector_nonzero : (whiteVector : Fin 3 → K) ≠ 0 := by
  intro h
  exact one_ne_zero (congrFun h 0)

theorem pairVector_nonzero (v : Kˣ) (htwo : (2 : K) ≠ 0) : pairVector v ≠ 0 := by
  intro h
  exact htwo (congrFun h 2)

theorem squarePairVector_nonzero (v : Kˣ) (htwo : (2 : K) ≠ 0) : squarePairVector v ≠ 0 := by
  intro h
  exact htwo (congrFun h 2)

theorem pair_vectors_not_proportional (v : Kˣ) (horder : 5 ≤ orderOf v) (htwo : (2 : K) ≠ 0) :
    ∀ a : K, squarePairVector v ≠ a • pairVector v := by
  intro a h
  have hz : (2 : K) = a * 2 := congrFun h 2
  have ha : a = 1 := mul_right_cancel₀ htwo (by simpa only [one_mul] using hz.symm)
  have h0 := congrFun h 0
  have hs : (v : K) ^ 2 + ((v : K) ^ 2)⁻¹ = (v : K) + (v : K)⁻¹ := by
    simpa [squarePairVector, pairVector, ha, Pi.smul_apply, smul_eq_mul] using h0
  exact reciprocal_sums_ne v horder hs.symm

theorem pair_triple_zero (v : Kˣ) :
    dot (cross (whiteVector : Fin 3 → K) (pairVector v)) (squarePairVector v) = 0 := by
  simp [whiteVector, pairVector, squarePairVector, cross, dot, Fin.sum_univ_succ]
  ring

theorem collinear_mk_of_triple_zero (v w x : Fin 3 → K) (hv : v ≠ 0) (hw : w ≠ 0) (hx : x ≠ 0)
    (h : dot (cross v w) x = 0) :
    Collinear (Projectivization.mk K v hv) (Projectivization.mk K w hw) (Projectivization.mk K x hx) := by
  obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep K v hv
  obtain ⟨b, hb⟩ := Projectivization.exists_smul_eq_mk_rep K w hw
  obtain ⟨c, hc⟩ := Projectivization.exists_smul_eq_mk_rep K x hx
  change (a : K) • v = (Projectivization.mk K v hv).rep at ha
  change (b : K) • w = (Projectivization.mk K w hw).rep at hb
  change (c : K) • x = (Projectivization.mk K x hx).rep at hc
  change dot (cross _ _) _ = 0
  rw [← ha, ← hb, ← hc, triple_smul, h, mul_zero]

def whitePoint (K : Type*) [Field K] : PlanePoint K :=
  Projectivization.mk K whiteVector whiteVector_nonzero

def pairPoint (v : Kˣ) (htwo : (2 : K) ≠ 0) : PlanePoint K :=
  Projectivization.mk K (pairVector v) (pairVector_nonzero v htwo)

def squarePairPoint (v : Kˣ) (htwo : (2 : K) ≠ 0) : PlanePoint K :=
  Projectivization.mk K (squarePairVector v) (squarePairVector_nonzero v htwo)

theorem pair_points_distinct (v : Kˣ) (horder : 5 ≤ orderOf v) (htwo : (2 : K) ≠ 0) :
    pairPoint v htwo ≠ squarePairPoint v htwo := by
  intro heq
  obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff' K
    (squarePairVector v) (pairVector v) (squarePairVector_nonzero v htwo)
    (pairVector_nonzero v htwo)).mp heq.symm
  exact pair_vectors_not_proportional v horder htwo a ha.symm

theorem pair_points_collinear (v : Kˣ) (htwo : (2 : K) ≠ 0) :
    Collinear (whitePoint K) (pairPoint v htwo) (squarePairPoint v htwo) :=
  collinear_mk_of_triple_zero whiteVector (pairVector v) (squarePairVector v)
    whiteVector_nonzero (pairVector_nonzero v htwo) (squarePairVector_nonzero v htwo) (pair_triple_zero v)

end Cylinder.ConicRootPairsAlgebra

end
