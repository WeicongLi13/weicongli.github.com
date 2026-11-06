module

public import Cylinder.ProductRestriction

/-!
# Polynomial restriction kernels and residues

The restriction to infinity is a genuine polynomial homomorphism.
Its kernel is the principal ideal of the actual infinity plane form.
-/

@[expose] public section

noncomputable section

namespace Cylinder.ProductResidue

open MvPolynomial Cylinder.ProjectiveGeometry Cylinder.ProjectivePointSet
open Cylinder.ProjectiveBalance Cylinder.ProductFrobenius Cylinder.ProductRestriction
open Cylinder.DualPencils Cylinder.ProjectiveChart
open scoped BigOperators Classical LinearAlgebra.Projectivization

variable (p : ℕ) [Fact p.Prime]

def restoreInfinity : Form p →+* Form p :=
  (MvPolynomial.rename (Fin.succ : Fin 3 → Fin 4)).toRingHom.comp (restrictInfinity p)

@[simp] theorem restoreInfinity_C (a : ZMod p) : restoreInfinity p (C a) = C a := by
  simp [restoreInfinity, restrictInfinity]

@[simp] theorem restoreInfinity_X_zero : restoreInfinity p (X (0 : Fin 4)) = 0 := by
  simp [restoreInfinity, restrictInfinity]

@[simp] theorem restoreInfinity_X_succ (i : Fin 3) :
    restoreInfinity p (X i.succ) = X i.succ := by
  simp [restoreInfinity, restrictInfinity]

theorem X_zero_dvd_sub_restore (F : Form p) :
    X (0 : Fin 4) ∣ F - restoreInfinity p F := by
  induction F using MvPolynomial.induction_on with
  | C a => simp
  | add F G hF hG =>
    rw [map_add]
    convert dvd_add hF hG using 1 <;> ring
  | mul_X F i hF =>
    cases i using Fin.cases with
    | zero => simp only [map_mul, restoreInfinity_X_zero, mul_zero, sub_zero]; exact dvd_mul_left _ _
    | succ i =>
      rw [map_mul, restoreInfinity_X_succ]
      convert dvd_mul_of_dvd_left hF (X i.succ) using 1 <;> ring

theorem X_zero_dvd_of_restrict_eq_zero {F : Form p}
    (hF : restrictInfinity p F = 0) : X (0 : Fin 4) ∣ F := by
  have h := X_zero_dvd_sub_restore p F
  simpa [restoreInfinity, hF] using h

theorem infinity_rep_scaled :
    ∃ a : (ZMod p)ˣ, (infinity p).rep = a • infinityFunctional p := by
  obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep (ZMod p)
    (infinityFunctional p) (infinityFunctional_ne_zero p)
  exact ⟨a, ha.symm⟩

theorem normal_infinity : ProjectivePointSet.normal p (infinity p) = 0 := by
  obtain ⟨a, ha⟩ := infinity_rep_scaled p
  funext i
  simp [ProjectivePointSet.normal, ha, infinityFunctional]

theorem infinity_constant_ne_zero : constantTerm p (infinity p) ≠ 0 :=
  constantTerm_ne_zero_of_normal_eq_zero p (normal_infinity p)

theorem planeForm_infinity : planeForm p (infinity p) =
    C (constantTerm p (infinity p)) * X (0 : Fin 4) := by
  have hi : ∀ i : Fin 3, (infinity p).rep (Pi.single i.succ 1) = 0 :=
    fun i => congrFun (normal_infinity p) i
  simp [planeForm, linearForm, Fin.sum_univ_succ, hi, constantTerm]

theorem infinityForm_dvd_of_restrict_eq_zero {F : Form p}
    (hF : restrictInfinity p F = 0) : planeForm p (infinity p) ∣ F := by
  obtain ⟨Q, hQ⟩ := X_zero_dvd_of_restrict_eq_zero p hF
  refine ⟨C ((constantTerm p (infinity p))⁻¹) * Q, ?_⟩
  rw [hQ, planeForm_infinity]
  rw [show C (constantTerm p (infinity p)) * X (0 : Fin 4) *
      (C ((constantTerm p (infinity p))⁻¹) * Q) =
      (C (constantTerm p (infinity p)) * C ((constantTerm p (infinity p))⁻¹)) *
        (X (0 : Fin 4) * Q) by ring]
  rw [← map_mul, mul_inv_cancel₀ (infinity_constant_ne_zero p), map_one, one_mul]

theorem exists_infinity_residue_dvd {S : Finset (Geometry.Point p)}
    (hcard : S.card = p ^ 2) (hS : Geometry.PDivisible p S) :
    ∃ c : ZMod p, c ≠ 0 ∧ planeForm p (infinity p) ∣
      blackProduct p S - C c * (∏ H ∈ whiteWithoutInfinity p S, planeForm p H) := by
  obtain ⟨c, hc, hres⟩ := exists_infinity_residue p hcard hS
  refine ⟨c, hc, infinityForm_dvd_of_restrict_eq_zero p ?_⟩
  simpa only [map_sub, map_mul, restrictInfinity, eval₂Hom_C] using sub_eq_zero.mpr hres

#print axioms X_zero_dvd_sub_restore
#print axioms exists_infinity_residue_dvd

end Cylinder.ProductResidue

end
