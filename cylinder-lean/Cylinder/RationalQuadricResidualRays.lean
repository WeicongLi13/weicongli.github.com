module

public import Cylinder.RationalQuadricResidual
public import Cylinder.ProjectiveSubsetRays

/-! Every actual nonempty ray of the moment-quadric residual has at least
three points. The new rational fibre is the literal old fibre with its
quadric zeros removed. -/

@[expose] public section
noncomputable section
open scoped Classical

namespace Cylinder.RationalQuadricResidualRays
open MvPolynomial Cylinder.HilbertEvaluation Cylinder.ProjectiveProjection
open Cylinder.RationalProjectionRelations Cylinder.RationalQuadricResidual
open Cylinder.ProjectiveSubsetRays Cylinder.ResidualRaySupport

variable {R K : Type*} [Field R] [Field K]
variable (ι : R →+* K) (E : Finset (ProjectiveProjection.Point R (Fin 3)))
variable (centre : ProjectiveProjection.Point R (Fin 3)) (hout : centre ∉ E)
variable (f g : PlaneRing K) (hf : f.IsHomogeneous 1) (hg : g.IsHomogeneous 2)

include hout in
theorem residualOutside : centre ∉ residualSet ι E centre f g :=
  outsideSubset R (Fin 3) E (residualSet ι E centre f g) centre
    (residualSet_subset ι E centre f g) hout

def residualRayEquiv (j : directionSet R (Fin 3) (residualSet ι E centre f g) centre
    (residualOutside ι E centre hout f g)) :
    Fin (raySize R (Fin 3) (residualSet ι E centre f g) centre
      (residualOutside ι E centre hout f g) j) ≃
    RayRemaining (raySize R (Fin 3) E centre hout) (directionRepresentatives ι E centre hout)
      (rayParameters ι E centre hout) f g
      (directionInjection R (Fin 3) E (residualSet ι E centre f g) centre
        (residualSet_subset ι E centre f g) hout j) :=
  (subsetRayEnumerationEquiv R (Fin 3) E (residualSet ι E centre f g) centre
    (residualSet_subset ι E centre f g) hout j).trans
      (Equiv.subtypeEquivRight (fun ν => mem_residualSet_rayEnumeration ι E centre hout f g hf hg _ ν))

include hf hg in
theorem residual_rays_ge_three
    (c : ∀ i : directionSet R (Fin 3) E centre hout, Fin (raySize R (Fin 3) E centre hout i) → K)
    (hc : ∀ i ν, c i ν ≠ 0)
    (hM0 : ∀ i, EvaluationProjection.rayMoment _ (rayParameters ι E centre hout) c i 0 = 0)
    (hM2 : ∀ i, EvaluationProjection.rayMoment _ (rayParameters ι E centre hout) c i 2 =
      eval (directionRepresentatives ι E centre hout i) f *
        EvaluationProjection.rayMoment _ (rayParameters ι E centre hout) c i 1)
    (hM3 : ∀ i, EvaluationProjection.rayMoment _ (rayParameters ι E centre hout) c i 3 =
      eval (directionRepresentatives ι E centre hout i) g *
        EvaluationProjection.rayMoment _ (rayParameters ι E centre hout) c i 1) :
    ∀ j : directionSet R (Fin 3) (residualSet ι E centre f g) centre
      (residualOutside ι E centre hout f g),
      3 ≤ raySize R (Fin 3) (residualSet ι E centre f g) centre
        (residualOutside ι E centre hout f g) j := by
  intro j
  let i := directionInjection R (Fin 3) E (residualSet ι E centre f g) centre
    (residualSet_subset ι E centre f g) hout j
  let e := residualRayEquiv ι E centre hout f g hf hg j
  let _ : Nonempty (RayRemaining (raySize R (Fin 3) E centre hout)
      (directionRepresentatives ι E centre hout) (rayParameters ι E centre hout) f g i) :=
    ⟨e ⟨0, raySize_pos R (Fin 3) (residualSet ι E centre f g) centre
      (residualOutside ι E centre hout f g) j⟩⟩
  have h := ray_remaining_card_ge_three (raySize R (Fin 3) E centre hout)
    (directionRepresentatives ι E centre hout) (rayParameters ι E centre hout) c f g i
    (rayParameters_injective ι E centre hout i) (hc i) (hM0 i) (hM2 i) (hM3 i)
  have he := Fintype.card_congr e
  rw [Fintype.card_fin] at he
  exact he ▸ h

end Cylinder.RationalQuadricResidualRays
end
