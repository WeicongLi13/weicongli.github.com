module

public import Cylinder.ConicRootPairsAlgebra

/-! The actual hyperbola points parameterized by a finite subgroup.
The two vectors in the pair-sum calculation are literal sums of these
point representatives. The subgroup model is separate from the original
white point set. -/

@[expose] public section
noncomputable section
open scoped Classical

namespace Cylinder.ConicRootPairsGeometry

open Cylinder.RationalPlaneLine Cylinder.ConicRootPairsAlgebra Cylinder.FieldSubgroupCyclic

variable {K : Type*} [Field K]

def hyperbolaVector (v : Kˣ) : Fin 3 → K := ![(v : K), (v : K)⁻¹, 1]

theorem hyperbolaVector_nonzero (v : Kˣ) : hyperbolaVector v ≠ 0 := by
  intro h
  exact one_ne_zero (congrFun h 2)

theorem hyperbolaVector_injective : Function.Injective (hyperbolaVector (K := K)) := by
  intro v w h
  exact Units.ext (congrFun h 0)

theorem hyperbola_equation (v : Kˣ) :
    hyperbolaVector v 0 * hyperbolaVector v 1 = hyperbolaVector v 2 ^ 2 := by
  change (v : K) * (v : K)⁻¹ = (1 : K) ^ 2
  rw [mul_inv_cancel₀ (Units.ne_zero v), one_pow]

theorem hyperbola_pair_sum (v : Kˣ) :
    hyperbolaVector v + hyperbolaVector v⁻¹ = pairVector v := by
  ext i
  fin_cases i
  · simp [hyperbolaVector, pairVector, Units.val_inv_eq_inv_val, add_comm]
  · simp [hyperbolaVector, pairVector, Units.val_inv_eq_inv_val, add_comm]
  · change (1 : K) + 1 = 2
    ring

theorem hyperbola_square_pair_sum (v : Kˣ) :
    hyperbolaVector (v ^ 2) + hyperbolaVector (v ^ 2)⁻¹ = squarePairVector v := by
  rw [hyperbola_pair_sum]
  simp only [pairVector, squarePairVector, Units.val_pow_eq_pow_val]

def hyperbolaPoint (v : Kˣ) : PlanePoint K :=
  Projectivization.mk K (hyperbolaVector v) (hyperbolaVector_nonzero v)

theorem hyperbolaPoint_injective : Function.Injective (hyperbolaPoint (K := K)) := by
  intro v w h
  obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff' K (hyperbolaVector v) (hyperbolaVector w)
    (hyperbolaVector_nonzero v) (hyperbolaVector_nonzero w)).mp h
  have haz : a = 1 := by
    simpa [hyperbolaVector, Pi.smul_apply, smul_eq_mul] using congrFun ha 2
  apply hyperbolaVector_injective
  rw [haz, one_smul] at ha
  exact ha.symm

theorem hyperbola_one_point : hyperbolaPoint (1 : Kˣ) = whitePoint K := by
  unfold hyperbolaPoint whitePoint
  congr 1
  ext i
  fin_cases i <;> simp [hyperbolaVector, whiteVector]

def parameterPointSet (H : Subgroup Kˣ) [Finite H] : Finset (PlanePoint K) := by
  let : Fintype H := Fintype.ofFinite H
  exact Finset.univ.image (fun v : H => hyperbolaPoint v.val)

theorem parameterPointSet_card (H : Subgroup Kˣ) [Finite H] : (parameterPointSet H).card = Nat.card H := by
  let : Fintype H := Fintype.ofFinite H
  change (Finset.univ.image (fun v : H => hyperbolaPoint v.val)).card = Nat.card H
  have hinj : Function.Injective (fun v : H => hyperbolaPoint v.val) :=
    fun v w h => Subtype.ext (hyperbolaPoint_injective h)
  rw [Finset.card_image_of_injective _ hinj, Finset.card_univ]
  exact Fintype.card_eq_nat_card

theorem hyperbolaPoint_mem_parameterPointSet (H : Subgroup Kˣ) [Finite H] (v : Kˣ) (hv : v ∈ H) :
    hyperbolaPoint v ∈ parameterPointSet H := by
  let : Fintype H := Fintype.ofFinite H
  exact Finset.mem_image.mpr ⟨⟨v, hv⟩, Finset.mem_univ _, rfl⟩

theorem generator_five_points (H : Subgroup Kˣ) [Finite H] (hm : 5 ≤ Nat.card H) :
    Function.Injective (fun i : Fin 5 => hyperbolaPoint (fiveUnits (generator H).val i)) ∧
      ∀ i : Fin 5, hyperbolaPoint (fiveUnits (generator H).val i) ∈ parameterPointSet H := by
  refine ⟨hyperbolaPoint_injective.comp (fiveUnits_injective _ ?_), ?_⟩
  · rw [unit_generator_order]
    exact hm
  · intro i
    exact hyperbolaPoint_mem_parameterPointSet H _ (generator_five_mem H i)

theorem inverse_pair_distinct (v : Kˣ) (horder : 5 ≤ orderOf v) :
    hyperbolaPoint v ≠ hyperbolaPoint v⁻¹ := by
  intro h
  exact (by decide : (1 : Fin 5) ≠ 2)
    (fiveUnits_injective v horder (hyperbolaPoint_injective h))

theorem inverse_square_pair_distinct (v : Kˣ) (horder : 5 ≤ orderOf v) :
    hyperbolaPoint (v ^ 2) ≠ hyperbolaPoint (v ^ 2)⁻¹ := by
  intro h
  exact (by decide : (3 : Fin 5) ≠ 4)
    (fiveUnits_injective v horder (hyperbolaPoint_injective h))

theorem pairPoint_eq_mk_sum (v : Kˣ) (htwo : (2 : K) ≠ 0) :
    pairPoint v htwo = Projectivization.mk K (hyperbolaVector v + hyperbolaVector v⁻¹)
      (by rw [hyperbola_pair_sum]; exact pairVector_nonzero v htwo) := by
  unfold pairPoint
  congr 1
  exact (hyperbola_pair_sum v).symm

theorem squarePairPoint_eq_mk_sum (v : Kˣ) (htwo : (2 : K) ≠ 0) :
    squarePairPoint v htwo =
      Projectivization.mk K (hyperbolaVector (v ^ 2) + hyperbolaVector (v ^ 2)⁻¹)
        (by rw [hyperbola_square_pair_sum]; exact squarePairVector_nonzero v htwo) := by
  unfold squarePairPoint
  congr 1
  exact (hyperbola_square_pair_sum v).symm

end Cylinder.ConicRootPairsGeometry

end
