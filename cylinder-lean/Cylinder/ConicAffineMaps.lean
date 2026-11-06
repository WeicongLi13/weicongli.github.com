module

public import Cylinder.ConicLineCoordinates

/-! Explicit invertible coordinate changes preserving the prescribed
line at infinity. Every inverse and composition is verified. -/

@[expose] public section
noncomputable section
open scoped Classical

namespace Cylinder.ConicAffineMaps
open MvPolynomial Cylinder.HilbertEvaluation Cylinder.LinearEvaluationTransport

variable {K : Type*} [Field K]

def rootVector (r s : K) (x : Fin 3 → K) : Fin 3 → K :=
  ![r * x 0 + s * x 1, x 0 + x 1, x 2]

def rootInverse (r s : K) (x : Fin 3 → K) : Fin 3 → K :=
  ![(x 0 - s * x 1) / (r - s), (r * x 1 - x 0) / (r - s), x 2]

def rootCoordinates (r s : K) (hrs : r ≠ s) : (Fin 3 → K) ≃ₗ[K] (Fin 3 → K) where
  toFun := rootVector r s
  invFun := rootInverse r s
  left_inv x := by
    funext i
    fin_cases i <;> simp [rootVector, rootInverse]
    all_goals field_simp [sub_ne_zero.mpr hrs]
    all_goals ring
  right_inv x := by
    funext i
    fin_cases i <;> simp [rootVector, rootInverse]
    all_goals field_simp [sub_ne_zero.mpr hrs]
    all_goals ring
  map_add' x y := by
    funext i
    fin_cases i <;> simp [rootVector]
    all_goals ring
  map_smul' a x := by
    funext i
    fin_cases i <;> simp [rootVector]
    all_goals ring

def doubleRootCoordinates (r : K) : (Fin 3 → K) ≃ₗ[K] (Fin 3 → K) where
  toFun x := ![x 0 + r * x 1, x 1, x 2]
  invFun x := ![x 0 - r * x 1, x 1, x 2]
  left_inv x := by funext i; fin_cases i <;> simp
  right_inv x := by funext i; fin_cases i <;> simp
  map_add' x y := by
    funext i
    fin_cases i <;> simp
    ring
  map_smul' a x := by
    funext i
    fin_cases i <;> simp
    ring

def affineVector (a b c d e : K) (x : Fin 3 → K) : Fin 3 → K :=
  ![a * x 0 + c * x 2, b * x 1 + d * x 0 + e * x 2, x 2]

def affineInverse (a b c d e : K) (x : Fin 3 → K) : Fin 3 → K :=
  let x₀ := (x 0 - c * x 2) / a
  ![x₀, (x 1 - d * x₀ - e * x 2) / b, x 2]

def affineCoordinates (a b c d e : K) (ha : a ≠ 0) (hb : b ≠ 0) :
    (Fin 3 → K) ≃ₗ[K] (Fin 3 → K) where
  toFun := affineVector a b c d e
  invFun := affineInverse a b c d e
  left_inv x := by
    funext i
    fin_cases i <;> simp [affineVector, affineInverse]
    all_goals field_simp [ha, hb]
    all_goals ring
  right_inv x := by
    funext i
    fin_cases i <;> simp [affineVector, affineInverse]
    all_goals field_simp [ha, hb]
    all_goals ring
  map_add' x y := by
    funext i
    fin_cases i <;> simp [affineVector]
    all_goals ring
  map_smul' a' x := by
    funext i
    fin_cases i <;> simp [affineVector]
    all_goals ring

def swapCoordinates : (Fin 3 → K) ≃ₗ[K] (Fin 3 → K) where
  toFun x := ![x 1, x 0, x 2]
  invFun x := ![x 1, x 0, x 2]
  left_inv x := by funext i; fin_cases i <;> rfl
  right_inv x := by funext i; fin_cases i <;> rfl
  map_add' x y := by funext i; fin_cases i <;> rfl
  map_smul' a x := by funext i; fin_cases i <;> rfl

theorem rootCoordinates_last (r s : K) (hrs : r ≠ s) (x : Fin 3 → K) :
    rootCoordinates r s hrs x 2 = x 2 := rfl

theorem doubleRootCoordinates_last (r : K) (x : Fin 3 → K) :
    doubleRootCoordinates r x 2 = x 2 := rfl

theorem affineCoordinates_last (a b c d e : K) (ha : a ≠ 0) (hb : b ≠ 0) (x : Fin 3 → K) :
    affineCoordinates a b c d e ha hb x 2 = x 2 := rfl

theorem swapCoordinates_last (x : Fin 3 → K) : swapCoordinates (K := K) x 2 = x 2 := rfl

theorem pullback_trans [Infinite K] (g h : (Fin 3 → K) ≃ₗ[K] (Fin 3 → K)) (Q : PlaneRing K) :
    linearPullback (g.trans h) Q = linearPullback g (linearPullback h Q) := by
  apply MvPolynomial.funext
  intro x
  simp only [linearPullback_eval, LinearEquiv.trans_apply]

theorem pullback_last [Infinite K] (g : (Fin 3 → K) ≃ₗ[K] (Fin 3 → K))
    (hg : ∀ x, g x 2 = x 2) : linearPullback g (X 2 : PlaneRing K) = X 2 := by
  apply MvPolynomial.funext
  intro x
  rw [linearPullback_eval, eval_X, eval_X, hg]

end Cylinder.ConicAffineMaps
end
