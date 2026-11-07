module
public import Cylinder.ProjectionTransportGeometry
public import Cylinder.ProjectiveVandermonde
@[expose] public section
noncomputable section
open scoped Classical
namespace Cylinder.ProjectionTransportVandermonde
open ProjectiveProjection ProjectionChart ProjectionTransport ProjectionTransportGeometry
variable {K σ : Type*} [Field K] [Fintype σ] [Infinite K]
variable (E : Finset (Point K σ)) (centre : Point K σ) (houtside : centre ∉ E)

/-- Lemma 4.8 for every prescribed coordinate chart, including an arbitrary nonzero
last coordinate of the centre's representative. -/
theorem ray_card_lower_bound (C : Chart centre) (d a : ℕ) (ha : a ≤ d)
    (hfull : ProjectiveVandermonde.HasFullSupportRelation K σ E d)
    (hind : EvaluationProjection.Independent
      (fun i : ProjectionTransport.directionSet E houtside C => i.val.rep) a)
    (i : ProjectionTransport.directionSet E houtside C) :
    d - a + 2 ≤ ProjectionTransport.raySize E houtside C i := by
  let j := (indexEquiv E houtside C).symm i
  have h := ProjectiveVandermonde.ray_card_lower_bound K σ E centre houtside d a ha hfull
    ((independent_directionSet E houtside C a).mp hind) j
  rw [ProjectiveVandermonde.rayPoints_card] at h
  have hs := ProjectionTransport.raySize_eq E houtside C j
  simpa [j] using h.trans_eq hs.symm

#print axioms ray_card_lower_bound
end Cylinder.ProjectionTransportVandermonde
end


