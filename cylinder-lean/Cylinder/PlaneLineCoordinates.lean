module

public import Cylinder.GenericPlaneLine
public import Cylinder.HomogeneousAffineChart
public import Mathlib.Logic.Equiv.Fin.Basic

/-! Extending the selected actual line to genuine invertible plane coordinates. -/

@[expose] public section
noncomputable section

namespace Cylinder.PlaneLineCoordinates

open MvPolynomial Cylinder.GenericPlaneLine Cylinder.HilbertEvaluation
open Cylinder.HomogeneousAffineChart
open scoped Classical

variable {K : Type*} [Field K]

def pencilExtension (w : Fin 2 → K) (hw : w 0 ≠ 0) : PlaneRing K ≃ₐ[K] PlaneRing K :=
  let s := MvPolynomial.renameEquiv K (Equiv.swap (0 : Fin 3) 1)
  s.trans ((triangularEquiv (![w 0, 0, w 1] : Fin 3 → K) hw).trans s)

@[simp] theorem pencilExtension_C (w : Fin 2 → K) (hw : w 0 ≠ 0) (c : K) :
    pencilExtension w hw (C c) = C c := (pencilExtension w hw).commutes c

theorem pencilExtension_X (w : Fin 2 → K) (hw : w 0 ≠ 0) (i : Fin 3) :
    pencilExtension w hw (X i) = ![X 0, C (w 0) * X 1, C (w 1) * X 1 + X 2] i := by
  fin_cases i
  · simp [pencilExtension, triangularEquiv, triangularMap, MvPolynomial.renameEquiv_apply]
  · simp [pencilExtension, triangularEquiv, triangularMap, MvPolynomial.renameEquiv_apply]
  · have hs2 : (Equiv.swap (0 : Fin 3) 1) (2 : Fin 3) = 2 := by decide
    simp [pencilExtension, triangularEquiv, triangularMap, MvPolynomial.renameEquiv_apply, hs2]
    ring

theorem pencilExtension_homogeneous (w : Fin 2 → K) (hw : w 0 ≠ 0)
    (F : PlaneRing K) (d : ℕ) (hF : F.IsHomogeneous d) :
    (pencilExtension w hw F).IsHomogeneous d := by
  exact (triangularMap_homogeneous (![w 0, 0, w 1] : Fin 3 → K)
    (rename (Equiv.swap (0 : Fin 3) 1) F) d hF.rename_isHomogeneous).rename_isHomogeneous

def coordinates (p : Fin 3 → K) (w : Fin 2 → K) (hp : p 0 ≠ 0) (hw : w 0 ≠ 0) :
    PlaneRing K ≃ₐ[K] PlaneRing K := (triangularEquiv p hp).trans (pencilExtension w hw)

@[simp] theorem coordinates_C (p : Fin 3 → K) (w : Fin 2 → K) (hp : p 0 ≠ 0) (hw : w 0 ≠ 0) (c : K) :
    coordinates p w hp hw (C c) = C c := (coordinates p w hp hw).commutes c

theorem coordinates_X (p : Fin 3 → K) (w : Fin 2 → K) (hp : p 0 ≠ 0) (hw : w 0 ≠ 0)
    (i : Fin 3) : coordinates p w hp hw (X i) =
      ![C (p 0) * X 0, C (p 1) * X 0 + C (w 0) * X 1,
        C (p 2) * X 0 + C (w 1) * X 1 + X 2] i := by
  fin_cases i
  · simp [coordinates, triangularEquiv, triangularMap, pencilExtension_X]
  · simp [coordinates, triangularEquiv, triangularMap, pencilExtension_X]
    ring
  · simp [coordinates, triangularEquiv, triangularMap, pencilExtension_X]
    ring

theorem coordinates_homogeneous (p : Fin 3 → K) (w : Fin 2 → K)
    (hp : p 0 ≠ 0) (hw : w 0 ≠ 0) (F : PlaneRing K) (d : ℕ) (hF : F.IsHomogeneous d) :
    (coordinates p w hp hw F).IsHomogeneous d :=
  pencilExtension_homogeneous w hw _ d (triangularMap_homogeneous p F d hF)

def coordinateVector (p : Fin 3 → K) (w : Fin 2 → K) (x : Fin 3 → K) : Fin 3 → K :=
  ![p 0 * x 0, p 1 * x 0 + w 0 * x 1, p 2 * x 0 + w 1 * x 1 + x 2]

def coordinateInverse (p : Fin 3 → K) (w : Fin 2 → K) (x : Fin 3 → K) : Fin 3 → K :=
  let a := x 0 / p 0
  let b := (x 1 - p 1 * a) / w 0
  ![a, b, x 2 - p 2 * a - w 1 * b]

def coordinateLinearEquiv (p : Fin 3 → K) (w : Fin 2 → K) (hp : p 0 ≠ 0) (hw : w 0 ≠ 0) :
    (Fin 3 → K) ≃ₗ[K] (Fin 3 → K) where
  toFun := coordinateVector p w
  invFun := coordinateInverse p w
  left_inv x := by
    funext i
    fin_cases i <;> simp [coordinateVector, coordinateInverse]
    all_goals field_simp
    all_goals ring
  right_inv x := by
    funext i
    fin_cases i <;> simp [coordinateVector, coordinateInverse]
    all_goals field_simp
    all_goals ring
  map_add' x y := by
    funext i
    fin_cases i <;> simp [coordinateVector]
    all_goals ring
  map_smul' a x := by
    funext i
    fin_cases i <;> simp [coordinateVector]
    all_goals ring

theorem eval_coordinates (p : Fin 3 → K) (w : Fin 2 → K) (hp : p 0 ≠ 0) (hw : w 0 ≠ 0)
    (x : Fin 3 → K) (F : PlaneRing K) :
    eval x (coordinates p w hp hw F) = eval (coordinateLinearEquiv p w hp hw x) F := by
  have he : (eval x).comp (coordinates p w hp hw).toRingHom =
      eval (coordinateLinearEquiv p w hp hw x) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      change eval x (coordinates p w hp hw (C c)) = eval (coordinateLinearEquiv p w hp hw x) (C c)
      rw [coordinates_C, eval_C, eval_C]
    · intro i
      change eval x (coordinates p w hp hw (X i)) = eval (coordinateLinearEquiv p w hp hw x) (X i)
      rw [coordinates_X]
      fin_cases i <;> simp [coordinateLinearEquiv, coordinateVector]
  exact RingHom.congr_fun he F

def lastEquiv : Fin 3 ≃ Option (Fin 2) := finSuccEquiv' (2 : Fin 3)

@[simp] theorem lastEquiv_zero : lastEquiv (0 : Fin 3) = some (0 : Fin 2) := by decide
@[simp] theorem lastEquiv_one : lastEquiv (1 : Fin 3) = some (1 : Fin 2) := by decide
@[simp] theorem lastEquiv_two : lastEquiv (2 : Fin 3) = none := by decide

def chartCoordinates (p : Fin 3 → K) (w : Fin 2 → K) (hp : p 0 ≠ 0) (hw : w 0 ≠ 0) :
    PlaneRing K ≃ₐ[K] Cylinder.CurvePolarLocal.HomogeneousPlanePolynomial (K := K) :=
  (coordinates p w hp hw).trans (MvPolynomial.renameEquiv K lastEquiv)

@[simp] theorem chartCoordinates_C (p : Fin 3 → K) (w : Fin 2 → K)
    (hp : p 0 ≠ 0) (hw : w 0 ≠ 0) (c : K) : chartCoordinates p w hp hw (C c) = C c :=
  (chartCoordinates p w hp hw).commutes c

theorem chartCoordinates_homogeneous (p : Fin 3 → K) (w : Fin 2 → K)
    (hp : p 0 ≠ 0) (hw : w 0 ≠ 0) (F : PlaneRing K) (d : ℕ) (hF : F.IsHomogeneous d) :
    (chartCoordinates p w hp hw F).IsHomogeneous d :=
  (coordinates_homogeneous p w hp hw F d hF).rename_isHomogeneous

theorem chart_at_zero_coordinates (p : Fin 3 → K) (w : Fin 2 → K)
    (hp : p 0 ≠ 0) (hw : w 0 ≠ 0) (F : PlaneRing K) :
    chartAt 0 (chartCoordinates p w hp hw F) = lineRestriction p w F := by
  have he : (chartAt (0 : K)).toRingHom.comp (chartCoordinates p w hp hw).toRingHom =
      (lineRestriction p w).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro c
      change chartAt 0 (chartCoordinates p w hp hw (C c)) = lineRestriction p w (C c)
      rw [chartCoordinates_C, chartAt_C]
      simp [lineRestriction]
    · intro i
      change chartAt 0 (rename lastEquiv (coordinates p w hp hw (X i))) = lineRestriction p w (X i)
      rw [coordinates_X]
      fin_cases i <;> simp [lineRestriction, triangularMap_X, pencilRestriction_X]
      all_goals ring
  exact RingHom.congr_fun he F

end Cylinder.PlaneLineCoordinates

end
