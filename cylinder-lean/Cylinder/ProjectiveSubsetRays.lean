module

public import Cylinder.ProjectiveProjectionFibres

/-! Projection of a literal subset from the same centre. New directions
inject into the old directions, and each new fibre is exactly the old
fibre restricted to points in the subset. -/

@[expose] public section
noncomputable section
open scoped Classical

namespace Cylinder.ProjectiveSubsetRays

open Cylinder.ProjectiveProjection

variable (K σ : Type*) [Field K]
variable (E Z : Finset (Point K σ)) (centre : Point K σ) (hZE : Z ⊆ E) (hout : centre ∉ E)

theorem outsideSubset (E Z : Finset (Point K σ)) (centre : Point K σ)
    (hZE : Z ⊆ E) (hout : centre ∉ E) : centre ∉ Z := fun h => hout (hZE h)

def pointInclusion (P : Z) : E := ⟨P.val, hZE P.property⟩

theorem projection_pointInclusion (P : Z) :
    projection K σ E centre hout (pointInclusion K σ E Z hZE P) =
      projection K σ Z centre (outsideSubset K σ E Z centre hZE hout) P := rfl

def directionInjection (j : directionSet K σ Z centre (outsideSubset K σ E Z centre hZE hout)) :
    directionSet K σ E centre hout := ⟨j.val, by
  obtain ⟨P, _hP, hPj⟩ := Finset.mem_image.mp j.property
  exact Finset.mem_image.mpr ⟨pointInclusion K σ E Z hZE P, Finset.mem_univ _,
    (projection_pointInclusion K σ E Z centre hZE hout P).trans hPj⟩⟩

theorem directionInjection_val
    (j : directionSet K σ Z centre (outsideSubset K σ E Z centre hZE hout)) :
    (directionInjection K σ E Z centre hZE hout j).val = j.val := rfl

theorem directionInjection_injective :
    Function.Injective (directionInjection K σ E Z centre hZE hout) := by
  intro i j h
  exact Subtype.ext (congrArg (fun x : directionSet K σ E centre hout => x.val) h)

theorem directionInjection_projectionIndex (P : Z) :
    directionInjection K σ E Z centre hZE hout
      (projectionIndex K σ Z centre (outsideSubset K σ E Z centre hZE hout) P) =
      projectionIndex K σ E centre hout (pointInclusion K σ E Z hZE P) :=
  Subtype.ext (projection_pointInclusion K σ E Z centre hZE hout P).symm

def subsetRayEquiv (j : directionSet K σ Z centre (outsideSubset K σ E Z centre hZE hout)) :
    RayIndex K σ Z centre (outsideSubset K σ E Z centre hZE hout) j ≃
      {x : RayIndex K σ E centre hout (directionInjection K σ E Z centre hZE hout j) // x.val.val ∈ Z} where
  toFun x := ⟨⟨pointInclusion K σ E Z hZE x.val, by
    rw [← directionInjection_projectionIndex]
    exact congrArg (directionInjection K σ E Z centre hZE hout) x.property⟩, x.val.property⟩
  invFun x := ⟨⟨x.val.val.val, x.property⟩, by
    apply directionInjection_injective K σ E Z centre hZE hout
    rw [directionInjection_projectionIndex]
    exact x.val.property⟩
  left_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    rfl

theorem subsetRayEquiv_point
    (j : directionSet K σ Z centre (outsideSubset K σ E Z centre hZE hout))
    (x : RayIndex K σ Z centre (outsideSubset K σ E Z centre hZE hout) j) :
    (subsetRayEquiv K σ E Z centre hZE hout j x).val.val.val = x.val.val := rfl

theorem normalisingUnit_eq
    (j : directionSet K σ Z centre (outsideSubset K σ E Z centre hZE hout))
    (x : RayIndex K σ Z centre (outsideSubset K σ E Z centre hZE hout) j) :
    normalisingUnit K σ Z centre (outsideSubset K σ E Z centre hZE hout) j x =
      normalisingUnit K σ E centre hout (directionInjection K σ E Z centre hZE hout j)
        (subsetRayEquiv K σ E Z centre hZE hout j x).val := rfl

theorem normalizedVector_eq
    (j : directionSet K σ Z centre (outsideSubset K σ E Z centre hZE hout))
    (x : RayIndex K σ Z centre (outsideSubset K σ E Z centre hZE hout) j) :
    normalizedVector K σ Z centre (outsideSubset K σ E Z centre hZE hout) j x =
      normalizedVector K σ E centre hout (directionInjection K σ E Z centre hZE hout j)
        (subsetRayEquiv K σ E Z centre hZE hout j x).val := rfl

theorem rayParameter_eq
    (j : directionSet K σ Z centre (outsideSubset K σ E Z centre hZE hout))
    (x : RayIndex K σ Z centre (outsideSubset K σ E Z centre hZE hout) j) :
    rayParameter K σ Z centre (outsideSubset K σ E Z centre hZE hout) j x =
      rayParameter K σ E centre hout (directionInjection K σ E Z centre hZE hout j)
        (subsetRayEquiv K σ E Z centre hZE hout j x).val := rfl

theorem raySize_eq_filtered_fibre
    (j : directionSet K σ Z centre (outsideSubset K σ E Z centre hZE hout)) :
    raySize K σ Z centre (outsideSubset K σ E Z centre hZE hout) j =
      Fintype.card {x : RayIndex K σ E centre hout (directionInjection K σ E Z centre hZE hout j) // x.val.val ∈ Z} :=
  Fintype.card_congr (subsetRayEquiv K σ E Z centre hZE hout j)

def filteredEnumerationEquiv
    (j : directionSet K σ Z centre (outsideSubset K σ E Z centre hZE hout)) :
    {ν : Fin (raySize K σ E centre hout (directionInjection K σ E Z centre hZE hout j)) //
      (rayEnumeration K σ E centre hout (directionInjection K σ E Z centre hZE hout j) ν).val.val ∈ Z} ≃
    {x : RayIndex K σ E centre hout (directionInjection K σ E Z centre hZE hout j) // x.val.val ∈ Z} where
  toFun ν := ⟨rayEnumeration K σ E centre hout _ ν.val, ν.property⟩
  invFun x := ⟨(rayEnumeration K σ E centre hout _).symm x.val, by
    simpa only [Equiv.apply_symm_apply] using x.property⟩
  left_inv ν := Subtype.ext ((rayEnumeration K σ E centre hout _).symm_apply_apply ν.val)
  right_inv x := Subtype.ext ((rayEnumeration K σ E centre hout _).apply_symm_apply x.val)

def subsetRayEnumerationEquiv
    (j : directionSet K σ Z centre (outsideSubset K σ E Z centre hZE hout)) :
    Fin (raySize K σ Z centre (outsideSubset K σ E Z centre hZE hout) j) ≃
    {ν : Fin (raySize K σ E centre hout (directionInjection K σ E Z centre hZE hout j)) //
      (rayEnumeration K σ E centre hout (directionInjection K σ E Z centre hZE hout j) ν).val.val ∈ Z} :=
  (rayEnumeration K σ Z centre (outsideSubset K σ E Z centre hZE hout) j).trans
    ((subsetRayEquiv K σ E Z centre hZE hout j).trans
      (filteredEnumerationEquiv K σ E Z centre hZE hout j).symm)

theorem raySize_eq_filtered_enumeration
    (j : directionSet K σ Z centre (outsideSubset K σ E Z centre hZE hout)) :
    raySize K σ Z centre (outsideSubset K σ E Z centre hZE hout) j =
      ((Finset.univ : Finset (Fin (raySize K σ E centre hout
        (directionInjection K σ E Z centre hZE hout j)))).filter (fun ν =>
          (rayEnumeration K σ E centre hout (directionInjection K σ E Z centre hZE hout j) ν).val.val ∈ Z)).card := by
  have hc := Fintype.card_congr (subsetRayEnumerationEquiv K σ E Z centre hZE hout j)
  rw [Fintype.card_fin, Fintype.card_subtype] at hc
  exact hc

theorem subsetRayEnumeration_point
    (j : directionSet K σ Z centre (outsideSubset K σ E Z centre hZE hout))
    (ν : Fin (raySize K σ Z centre (outsideSubset K σ E Z centre hZE hout) j)) :
    (rayEnumeration K σ Z centre (outsideSubset K σ E Z centre hZE hout) j ν).val.val =
      (rayEnumeration K σ E centre hout (directionInjection K σ E Z centre hZE hout j)
        (subsetRayEnumerationEquiv K σ E Z centre hZE hout j ν).val).val.val := by
  change _ = ((rayEnumeration K σ E centre hout _)
    ((rayEnumeration K σ E centre hout _).symm
      (subsetRayEquiv K σ E Z centre hZE hout j
        (rayEnumeration K σ Z centre (outsideSubset K σ E Z centre hZE hout) j ν)).val)).val.val
  rw [Equiv.apply_symm_apply]
  rfl

theorem raySize_le_old_raySize
    (j : directionSet K σ Z centre (outsideSubset K σ E Z centre hZE hout)) :
    raySize K σ Z centre (outsideSubset K σ E Z centre hZE hout) j ≤
      raySize K σ E centre hout (directionInjection K σ E Z centre hZE hout j) := by
  rw [raySize_eq_filtered_fibre]
  exact Fintype.card_subtype_le _

end Cylinder.ProjectiveSubsetRays

end
