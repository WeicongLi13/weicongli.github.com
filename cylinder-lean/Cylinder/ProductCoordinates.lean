module

public import Cylinder.ProductResidue

/-!
# Actual linear coordinate changes of the polynomial ring
-/

@[expose] public section

noncomputable section

namespace Cylinder.ProductCoordinates

open MvPolynomial Cylinder.ProjectiveGeometry Cylinder.ProjectivePointSet
open Cylinder.ProjectiveBalance Cylinder.ProductFrobenius Cylinder.ProductRestriction
open Cylinder.ProductResidue Cylinder.ProjectiveChart
open scoped BigOperators Classical LinearAlgebra.Projectivization

variable (p : ℕ) [Fact p.Prime]

def functionalForm (f : Module.Dual (ZMod p) (Vector p)) : Form p :=
  linearForm p (fun i => f (Pi.single i 1))

@[simp] theorem functionalForm_proj (i : Fin 4) :
    functionalForm p (LinearMap.proj i) = X i := by
  simp [functionalForm, linearForm, Pi.single_apply]

def polynomialChange (e : Vector p →ₗ[ZMod p] Vector p) : Form p →+* Form p :=
  eval₂Hom C (fun i => functionalForm p ((LinearMap.proj i).comp e))

@[simp] theorem polynomialChange_C (e : Vector p →ₗ[ZMod p] Vector p) (a : ZMod p) :
    polynomialChange p e (C a) = C a := by
  simp [polynomialChange]

@[simp] theorem polynomialChange_X (e : Vector p →ₗ[ZMod p] Vector p) (i : Fin 4) :
    polynomialChange p e (X i) = functionalForm p ((LinearMap.proj i).comp e) := by
  simp [polynomialChange]

theorem polynomialChange_functionalForm (e : Vector p →ₗ[ZMod p] Vector p)
    (f : Module.Dual (ZMod p) (Vector p)) :
    polynomialChange p e (functionalForm p f) = functionalForm p (f.comp e) := by
  unfold functionalForm linearForm
  simp only [map_sum, map_mul, polynomialChange_C, polynomialChange_X]
  unfold functionalForm linearForm
  simp only [Finset.mul_sum, ← mul_assoc, ← map_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [← Finset.sum_mul, ← map_sum]
  congr 2
  exact (functional_expansion p f (e (Pi.single j 1))).symm

theorem polynomialChange_comp (e d : Vector p →ₗ[ZMod p] Vector p) :
    (polynomialChange p e).comp (polynomialChange p d) =
      polynomialChange p (d.comp e) := by
  apply MvPolynomial.ringHom_ext
  · intro a
    simp
  · intro i
    simp only [RingHom.comp_apply, polynomialChange_X, polynomialChange_functionalForm]
    rfl

theorem polynomialChange_id :
    polynomialChange p (LinearMap.id : Vector p →ₗ[ZMod p] Vector p) = RingHom.id (Form p) := by
  apply MvPolynomial.ringHom_ext
  · intro a
    simp
  · intro i
    simp only [polynomialChange_X, LinearMap.comp_id, functionalForm_proj, RingHom.id_apply]

def polynomialEquiv (g : Vector p ≃ₗ[ZMod p] Vector p) : Form p ≃+* Form p :=
  { toFun := polynomialChange p g.toLinearMap
    invFun := polynomialChange p g.symm.toLinearMap
    left_inv := by
      intro F
      have hcomp : (polynomialChange p g.symm.toLinearMap).comp
          (polynomialChange p g.toLinearMap) = RingHom.id (Form p) := by
        rw [polynomialChange_comp]
        have he : g.toLinearMap.comp g.symm.toLinearMap = LinearMap.id := by ext x; simp
        rw [he, polynomialChange_id]
      exact RingHom.congr_fun hcomp F
    right_inv := by
      intro F
      have hcomp : (polynomialChange p g.toLinearMap).comp
          (polynomialChange p g.symm.toLinearMap) = RingHom.id (Form p) := by
        rw [polynomialChange_comp]
        have he : g.symm.toLinearMap.comp g.toLinearMap = LinearMap.id := by ext x; simp
        rw [he, polynomialChange_id]
      exact RingHom.congr_fun hcomp F
    map_add' := (polynomialChange p g.toLinearMap).map_add
    map_mul' := (polynomialChange p g.toLinearMap).map_mul }

@[simp] theorem polynomialEquiv_C (g : Vector p ≃ₗ[ZMod p] Vector p) (a : ZMod p) :
    polynomialEquiv p g (C a) = C a := polynomialChange_C p _ _

theorem polynomialEquiv_functionalForm (g : Vector p ≃ₗ[ZMod p] Vector p)
    (f : Module.Dual (ZMod p) (Vector p)) :
    polynomialEquiv p g (functionalForm p f) = functionalForm p (g.dualMap f) :=
  polynomialChange_functionalForm p _ _

theorem functionalForm_smul (a : ZMod p) (f : Module.Dual (ZMod p) (Vector p)) :
    functionalForm p (a • f) = C a * functionalForm p f := by
  simp [functionalForm, linearForm, smul_eq_mul, Finset.mul_sum, mul_assoc]

theorem transformed_planeForm (g : Vector p ≃ₗ[ZMod p] Vector p) (H : DualPoint p) :
    ∃ a : ZMod p, a ≠ 0 ∧
      polynomialEquiv p g.symm (planeForm p H) = C a * planeForm p (mapDual p g H) := by
  have hf : g.symm.dualMap H.rep ≠ 0 := by
    intro hz
    exact H.rep_nonzero (g.symm.dualMap.injective (by simpa using hz))
  obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep (ZMod p)
    (g.symm.dualMap H.rep) hf
  have hm : mapDual p g H = Projectivization.mk (ZMod p) (g.symm.dualMap H.rep) hf := by
    conv_lhs => rw [← Projectivization.mk_rep H]
    simp only [mapDual, Projectivization.map_mk]
    apply (Projectivization.mk_eq_mk_iff' (ZMod p) _ _ _ _).mpr
    refine ⟨1, ?_⟩
    simp only [one_smul]
    apply LinearMap.ext
    intro x
    rfl
  have hrep : (mapDual p g H).rep = a • g.symm.dualMap H.rep := by
    rw [hm]
    exact ha.symm
  refine ⟨(a : ZMod p)⁻¹, inv_ne_zero a.ne_zero, ?_⟩
  change polynomialEquiv p g.symm (functionalForm p H.rep) =
    C ((a : ZMod p)⁻¹) * functionalForm p (mapDual p g H).rep
  rw [polynomialEquiv_functionalForm, hrep]
  have he : (a : ZMod p)⁻¹ • (a • g.symm.dualMap H.rep) = g.symm.dualMap H.rep := by
    simp only [Units.smul_def, smul_smul, inv_mul_cancel₀ a.ne_zero, one_smul]
  rw [← functionalForm_smul, he]

#print axioms polynomialEquiv
#print axioms transformed_planeForm

end Cylinder.ProductCoordinates

end
