module

public import Cylinder.ProjectiveProjection
public import Cylinder.ProjectiveIncidence
public import Mathlib.LinearAlgebra.Dimension.Constructions

/-! Actual linear preimages of projective directions and their finite fibres. -/

@[expose] public section
noncomputable section

namespace Cylinder.ProjectiveProjectionFibres

open Cylinder.ProjectiveProjection
open scoped Classical LinearAlgebra.Projectivization BigOperators

variable (K σ : Type*) [Field K] [Fintype σ]

def tailMap : Space K σ →ₗ[K] (σ → K) where
  toFun x s := x (some s)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def tailPreimageEquiv (U : Submodule K (σ → K)) :
    U.comap (tailMap K σ) ≃ₗ[K] K × U where
  toFun x := (x.val none, ⟨tailMap K σ x.val, x.property⟩)
  invFun x := ⟨fun o => o.elim x.1 x.2.val, by
    change (fun s => (some s).elim x.1 x.2.val) ∈ U
    exact x.2.property⟩
  left_inv x := by
    apply Subtype.ext
    funext o
    cases o <;> rfl
  right_inv x := by
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem tail_preimage_finrank (U : Submodule K (σ → K)) :
    Module.finrank K (U.comap (tailMap K σ)) = 1 + Module.finrank K U := by
  rw [(tailPreimageEquiv K σ U).finrank_eq, Module.finrank_prod, Module.finrank_self]

def liftedSpace (centre : Point K σ) (U : Submodule K (σ → K)) :
    Submodule K (Space K σ) :=
  (U.comap (tailMap K σ)).map (coordinateChange K σ centre).symm.toLinearMap

theorem liftedSpace_finrank (centre : Point K σ) (U : Submodule K (σ → K)) :
    Module.finrank K (liftedSpace K σ centre U) = 1 + Module.finrank K U := by
  rw [liftedSpace, LinearEquiv.finrank_map_eq, tail_preimage_finrank]

omit [Fintype σ] in
theorem rep_mem_liftedSpace (centre P : Point K σ) (U : Submodule K (σ → K)) :
    P.rep ∈ liftedSpace K σ centre U ↔ directionVector K σ centre P ∈ U := by
  simp only [liftedSpace, Submodule.mem_map_equiv, LinearEquiv.symm_symm,
    Submodule.mem_comap]
  rfl

omit [Fintype σ] in
theorem point_mem_liftedSpace (centre P : Point K σ) (hP : P ≠ centre)
    (U : Submodule K (σ → K)) :
    P.submodule ≤ liftedSpace K σ centre U ↔ (projectPoint K σ centre P hP).submodule ≤ U := by
  rw [Cylinder.ProjectiveIncidence.submodule_le_iff_rep_mem, rep_mem_liftedSpace,
    projectPoint, Projectivization.submodule_mk, Submodule.span_singleton_le_iff_mem]

omit [Fintype σ] in
theorem centre_mem_liftedSpace (centre : Point K σ) (U : Submodule K (σ → K)) :
    centre.submodule ≤ liftedSpace K σ centre U := by
  rw [Cylinder.ProjectiveIncidence.submodule_le_iff_rep_mem, rep_mem_liftedSpace]
  have hz : directionVector K σ centre centre = 0 := by
    funext s
    simp [directionVector, coordinateChange_centre, centreAxis]
  rw [hz]
  exact U.zero_mem

def raySpace (centre : Point K σ) (d : Direction K σ) : Submodule K (Space K σ) :=
  liftedSpace K σ centre d.submodule

theorem raySpace_finrank (centre : Point K σ) (d : Direction K σ) :
    Module.finrank K (raySpace K σ centre d) = 2 := by
  rw [raySpace, liftedSpace_finrank K σ centre d.submodule, Projectivization.finrank_submodule]

omit [Fintype σ] in
theorem point_mem_raySpace (centre P : Point K σ) (hP : P ≠ centre) (d : Direction K σ) :
    P.submodule ≤ raySpace K σ centre d ↔ projectPoint K σ centre P hP = d := by
  rw [raySpace, point_mem_liftedSpace K σ centre P hP d.submodule]
  constructor
  · intro hle
    apply Projectivization.submodule_injective
    apply Submodule.eq_of_le_of_finrank_eq hle
    simp only [Projectivization.finrank_submodule]
  · intro h
    rw [h]

variable (E : Finset (Point K σ)) (centre : Point K σ) (houtside : centre ∉ E)

def rayFibreEquiv (i : directionSet K σ E centre houtside) :
    RayIndex K σ E centre houtside i ≃
      (E.filter (fun P => P.submodule ≤ raySpace K σ centre i.val)) where
  toFun x := ⟨x.val.val, Finset.mem_filter.mpr ⟨x.val.property,
    (point_mem_raySpace K σ centre x.val.val
      (fun h => houtside (h ▸ x.val.property)) i.val).mpr (congrArg Subtype.val x.property)⟩⟩
  invFun x := ⟨⟨x.val, (Finset.mem_filter.mp x.property).1⟩,
    Subtype.ext ((point_mem_raySpace K σ centre x.val
      (fun h => houtside (h ▸ (Finset.mem_filter.mp x.property).1)) i.val).mp
      (Finset.mem_filter.mp x.property).2)⟩
  left_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv x := by
    apply Subtype.ext
    rfl

omit [Fintype σ] in
theorem raySize_eq_card (i : directionSet K σ E centre houtside) :
    raySize K σ E centre houtside i =
      (E.filter (fun P => P.submodule ≤ raySpace K σ centre i.val)).card := by
  rw [raySize, Fintype.card_congr (rayFibreEquiv K σ E centre houtside i), Fintype.card_coe]

omit [Fintype σ] in
theorem sum_raySize :
    (∑ i : directionSet K σ E centre houtside, raySize K σ E centre houtside i) = E.card := by
  calc
    _ = Fintype.card (Σ i : directionSet K σ E centre houtside,
        RayIndex K σ E centre houtside i) := (Fintype.card_sigma).symm
    _ = Fintype.card E := Fintype.card_congr (Equiv.sigmaFiberEquiv
      (projectionIndex K σ E centre houtside))
    _ = E.card := Fintype.card_coe _

def restrictedRayEquiv (U : Submodule K (σ → K)) :
    (Σ i : {i : directionSet K σ E centre houtside // i.val.submodule ≤ U},
      RayIndex K σ E centre houtside i.val) ≃
      (E.filter (fun P => P.submodule ≤ liftedSpace K σ centre U)) where
  toFun x := ⟨x.2.val.val, Finset.mem_filter.mpr ⟨x.2.val.property, by
    rw [point_mem_liftedSpace K σ centre x.2.val.val
      (fun h => houtside (h ▸ x.2.val.property)) U]
    have hx := congrArg Subtype.val x.2.property
    change projection K σ E centre houtside x.2.val = x.1.val.val at hx
    change (projection K σ E centre houtside x.2.val).submodule ≤ U
    rw [hx]
    exact x.1.property⟩⟩
  invFun x :=
    let P : E := ⟨x.val, (Finset.mem_filter.mp x.property).1⟩
    let i := projectionIndex K σ E centre houtside P
    ⟨⟨i, (point_mem_liftedSpace K σ centre x.val
      (fun h => houtside (h ▸ P.property)) U).mp (Finset.mem_filter.mp x.property).2⟩,
      ⟨P, rfl⟩⟩
  left_inv x := by
    rcases x with ⟨⟨i, hi⟩, ⟨P, hP⟩⟩
    dsimp
    change projectionIndex K σ E centre houtside P = i at hP
    subst i
    rfl
  right_inv x := by
    apply Subtype.ext
    rfl

omit [Fintype σ] in
theorem restricted_rays_card (U : Submodule K (σ → K)) :
    Fintype.card (Σ i : {i : directionSet K σ E centre houtside // i.val.submodule ≤ U},
      RayIndex K σ E centre houtside i.val) =
      (E.filter (fun P => P.submodule ≤ liftedSpace K σ centre U)).card := by
  rw [Fintype.card_congr (restrictedRayEquiv K σ E centre houtside U), Fintype.card_coe]

end Cylinder.ProjectiveProjectionFibres

end
