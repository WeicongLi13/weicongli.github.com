module

public import Cylinder.ConicLineCoordinates
public import Cylinder.BMMVectorSecants
public import Cylinder.ThreeNetFullSupportRelations

/-! A prescribed actual line becomes the line at infinity. The finite set
on that line has distinct finite slope parameters, and actual collinear
matchings become equal affine projections. -/

@[expose] public section
noncomputable section
open scoped Classical BigOperators

namespace Cylinder.LineAffineCoordinates

open Cylinder.RationalPlaneLine Cylinder.PlaneCrossProduct Cylinder.BMMArcGeometry
open Cylinder.BMMVectorSecants Cylinder.BMMTriangleFrame Cylinder.BMMFrameRatios
open Cylinder.BlackProjectionRationalLines Cylinder.ThreeNetFullSupportRelations

variable {K : Type*} [Field K]

def swapEnds : (Fin 3 → K) ≃ₗ[K] (Fin 3 → K) where
  toFun x := ![x 2, x 1, x 0]
  invFun x := ![x 2, x 1, x 0]
  left_inv x := by funext i; fin_cases i <;> rfl
  right_inv x := by funext i; fin_cases i <;> rfl
  map_add' x y := by funext i; fin_cases i <;> rfl
  map_smul' a x := by funext i; fin_cases i <;> rfl

def shear (u : K) : (Fin 3 → K) ≃ₗ[K] (Fin 3 → K) where
  toFun x := ![x 0, x 1 + u * x 2, x 2]
  invFun x := ![x 0, x 1 - u * x 2, x 2]
  left_inv x := by funext i; fin_cases i <;> simp
  right_inv x := by funext i; fin_cases i <;> simp
  map_add' x y := by funext i; fin_cases i <;> simp [mul_add]; ring
  map_smul' a x := by funext i; fin_cases i <;> simp [Pi.smul_apply, smul_eq_mul]; ring

theorem exists_first_line_coordinate (l : Fin 3 → K) (hl : l ≠ 0) :
    ∃ g : (Fin 3 → K) ≃ₗ[K] (Fin 3 → K), ∀ x, g x 0 = dot l x := by
  have hmap : dotMap l ≠ 0 := by
    intro hz
    obtain ⟨x, hx⟩ := dotMap_surjective l hl 1
    have h := LinearMap.congr_fun hz x
    rw [hx] at h
    exact one_ne_zero h
  obtain ⟨g, hg⟩ := ConicLineCoordinates.exists_functional_coordinates (dotMap l) hmap
  refine ⟨g.symm.trans swapEnds, fun x => ?_⟩
  have h := hg (g.symm x)
  rw [LinearEquiv.apply_symm_apply] at h
  exact h.symm

theorem exists_line_affine_coordinates [Infinite K] (l : Fin 3 → K) (hl : l ≠ 0)
    (C : Finset (PlanePoint K)) (hC : ∀ R ∈ C, dot l R.rep = 0) :
    ∃ g : (Fin 3 → K) ≃ₗ[K] (Fin 3 → K),
      (∀ x, g x 0 = dot l x) ∧ ∀ R ∈ C, g R.rep 1 ≠ 0 := by
  obtain ⟨h, hh⟩ := exists_first_line_coordinate l hl
  obtain ⟨u, hu⟩ := (C.image (fun R => -(h R.rep 1) / h R.rep 2)).exists_notMem
  refine ⟨h.trans (shear u), fun x => hh x, fun R hR hz => ?_⟩
  change h R.rep 1 + u * h R.rep 2 = 0 at hz
  by_cases htwo : h R.rep 2 = 0
  · have hone : h R.rep 1 = 0 := by simpa only [htwo, mul_zero, add_zero] using hz
    have hzero : h R.rep = 0 := by
      funext j
      fin_cases j
      · exact (hh R.rep).trans (hC R hR)
      · exact hone
      · exact htwo
    exact R.rep_nonzero (h.injective (hzero.trans (map_zero h).symm))
  · have heq : u = -(h R.rep 1) / h R.rep 2 := by
      apply (eq_div_iff htwo).mpr
      exact eq_neg_of_add_eq_zero_right hz
    exact hu (Finset.mem_image.mpr ⟨R, hR, heq.symm⟩)

def affineCoordinates (g : (Fin 3 → K) ≃ₗ[K] (Fin 3 → K)) (P : PlanePoint K) : Fin 2 → K :=
  ![g P.rep 1 / g P.rep 0, g P.rep 2 / g P.rep 0]

def lineParameter (g : (Fin 3 → K) ≃ₗ[K] (Fin 3 → K)) (R : PlanePoint K) : K :=
  -(g R.rep 2) / g R.rep 1

theorem normalized_affine_vector (g : (Fin 3 → K) ≃ₗ[K] (Fin 3 → K))
    (P : PlanePoint K) (hP : g P.rep 0 ≠ 0) :
    affineVector (affineCoordinates g P) = (g P.rep 0)⁻¹ • g P.rep := by
  funext j
  fin_cases j <;> simp [affineVector, affineCoordinates, Pi.smul_apply,
    smul_eq_mul, div_eq_mul_inv, mul_comm, hP]

theorem collinear_after_linearEquiv (g : (Fin 3 → K) ≃ₗ[K] (Fin 3 → K))
    (P Q R : PlanePoint K) (hPQ : P ≠ Q) (hcol : Collinear P Q R) :
    dot (cross (g P.rep) (g Q.rep)) (g R.rep) = 0 := by
  let x := pairFrame P Q hPQ R.rep
  have hx2 : x 2 = 0 := secant_coordinate_zero P Q R hPQ hcol
  have hr : R.rep = x 0 • P.rep + x 1 • Q.rep := by
    apply (pairFrame P Q hPQ).injective
    rw [map_add, map_smul, map_smul, pairFrame_left, pairFrame_right]
    funext j
    fin_cases j <;> simp [x, hx2, Pi.single_apply, Pi.smul_apply, smul_eq_mul]
  rw [hr, map_add, map_smul, map_smul]
  simp [dot, cross, Fin.sum_univ_succ, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem collinear_projection_equal (g : (Fin 3 → K) ≃ₗ[K] (Fin 3 → K))
    (P Q R : PlanePoint K) (hPQ : P ≠ Q) (hcol : Collinear P Q R)
    (hP : g P.rep 0 ≠ 0) (hQ : g Q.rep 0 ≠ 0)
    (hRzero : g R.rep 0 = 0) (hR : g R.rep 1 ≠ 0) :
    lineParameter g R * affineCoordinates g P 0 + affineCoordinates g P 1 =
      lineParameter g R * affineCoordinates g Q 0 + affineCoordinates g Q 1 := by
  have hdet := collinear_after_linearEquiv g P Q R hPQ hcol
  simp [dot, cross, Fin.sum_univ_succ, hRzero] at hdet
  change (-(g R.rep 2) / g R.rep 1) * (g P.rep 1 / g P.rep 0) + g P.rep 2 / g P.rep 0 =
    (-(g R.rep 2) / g R.rep 1) * (g Q.rep 1 / g Q.rep 0) + g Q.rep 2 / g Q.rep 0
  field_simp [hP, hQ, hR]
  linear_combination hdet

theorem lineParameter_injective (g : (Fin 3 → K) ≃ₗ[K] (Fin 3 → K))
    (C : Finset (PlanePoint K)) (hzero : ∀ R ∈ C, g R.rep 0 = 0)
    (hone : ∀ R ∈ C, g R.rep 1 ≠ 0) :
    Function.Injective (fun R : C => lineParameter g R.val) := by
  intro P Q heq
  have hp := hone P.val P.property
  have hq := hone Q.val Q.property
  have heq' : g P.val.rep 2 / g P.val.rep 1 = g Q.val.rep 2 / g Q.val.rep 1 := by
    simpa only [lineParameter, neg_div, neg_neg] using congrArg Neg.neg heq
  have hcross := (div_eq_div_iff hp hq).mp heq'
  have hv : g P.val.rep = (g P.val.rep 1 / g Q.val.rep 1) • g Q.val.rep := by
    funext j
    fin_cases j
    · change g P.val.rep 0 = (g P.val.rep 1 / g Q.val.rep 1) * g Q.val.rep 0
      rw [hzero P.val P.property, hzero Q.val Q.property, mul_zero]
    · change g P.val.rep 1 = (g P.val.rep 1 / g Q.val.rep 1) * g Q.val.rep 1
      exact (div_mul_cancel₀ _ hq).symm
    · change g P.val.rep 2 = (g P.val.rep 1 / g Q.val.rep 1) * g Q.val.rep 2
      field_simp [hq]
      linear_combination hcross
  have hrep : (g P.val.rep 1 / g Q.val.rep 1) • Q.val.rep = P.val.rep := by
    apply g.injective
    rw [map_smul]
    exact hv.symm
  have h := (Projectivization.mk_eq_mk_iff' K P.val.rep Q.val.rep
    P.val.rep_nonzero Q.val.rep_nonzero).mpr ⟨_, hrep⟩
  exact Subtype.ext (by simpa only [Projectivization.mk_rep] using h)

end Cylinder.LineAffineCoordinates

end
