module

public import Cylinder.RationalProjectionRelations
public import Cylinder.ResidualRaySupport

/-! The residual of the literal moment quadric, on the actual rational
projective point set. Coordinates, support, fibres and coefficients are
transported by explicit equivalences. -/

@[expose] public section
noncomputable section
open scoped Classical BigOperators

namespace Cylinder.RationalQuadricResidual
open MvPolynomial Cylinder.HilbertEvaluation Cylinder.ProjectiveFieldEmbedding
open Cylinder.ProjectiveProjection Cylinder.RationalProjectionRelations
open Cylinder.EvaluationProjection Cylinder.MomentQuadric Cylinder.ResidualRaySupport
open Cylinder.LinearEvaluationTransport

variable {R K : Type*} [Field R] [Field K]
variable (ι : R →+* K) (E : Finset (ProjectiveProjection.Point R (Fin 3)))
variable (centre : ProjectiveProjection.Point R (Fin 3)) (hout : centre ∉ E)

def originalQuadric (f g : PlaneRing K) : MvPolynomial (Option (Fin 3)) K :=
  rationalPullback ι (coordinateChange R (Fin 3) centre) (quadric f g)

theorem originalQuadric_homogeneous (f g : PlaneRing K)
    (hf : f.IsHomogeneous 1) (hg : g.IsHomogeneous 2) :
    (originalQuadric ι centre f g).IsHomogeneous 2 :=
  rationalPullback_homogeneous ι _ _ 2 (quadric_homogeneous f g hf hg)

theorem originalQuadric_eval_centre (f g : PlaneRing K)
    (hf : f.IsHomogeneous 1) (hg : g.IsHomogeneous 2) :
    eval (vectorMap ι centre.rep) (originalQuadric ι centre f g) = 1 := by
  rw [originalQuadric, rationalPullback_eval, coordinateChange_centre]
  have hv : vectorMap ι (centreAxis R (Fin 3)) = rayPoint (0 : Fin 3 → K) 1 := by
    funext j
    cases j <;> simp [vectorMap, centreAxis, rayPoint]
  rw [hv, quadric_eval_ray, homogeneous_eval_zero f 1 hf (by decide),
    homogeneous_eval_zero g 2 hg (by decide)]
  ring

theorem originalQuadric_nonzero (f g : PlaneRing K)
    (hf : f.IsHomogeneous 1) (hg : g.IsHomogeneous 2) :
    originalQuadric ι centre f g ≠ 0 := by
  intro hz
  have h := originalQuadric_eval_centre ι centre f g hf hg
  rw [hz, map_zero] at h
  exact zero_ne_one h

def residualSet (f g : PlaneRing K) : Finset (ProjectiveProjection.Point R (Fin 3)) :=
  E.filter (fun P => eval (vectorMap ι P.rep) (originalQuadric ι centre f g) ≠ 0)

theorem residualSet_subset (f g : PlaneRing K) : residualSet ι E centre f g ⊆ E :=
  Finset.filter_subset _ _

def rayScale (i : directionSet R (Fin 3) E centre hout)
    (ν : Fin (raySize R (Fin 3) E centre hout i)) : K :=
  ι (normalisingUnit R (Fin 3) E centre hout i
    (rayEnumeration R (Fin 3) E centre hout i ν) : R)

theorem rayScale_nonzero (i : directionSet R (Fin 3) E centre hout)
    (ν : Fin (raySize R (Fin 3) E centre hout i)) : rayScale ι E centre hout i ν ≠ 0 :=
  fun hz => Units.ne_zero _ ((map_eq_zero_iff ι ι.injective).mp hz)

theorem normalized_rayPoint (i : directionSet R (Fin 3) E centre hout)
    (ν : Fin (raySize R (Fin 3) E centre hout i)) :
    rayPoint (directionRepresentatives ι E centre hout i) (rayParameters ι E centre hout i ν) =
      rayScale ι E centre hout i ν • vectorMap ι
        (coordinateChange R (Fin 3) centre (rayEnumeration R (Fin 3) E centre hout i ν).val.val.rep) := by
  let x := rayEnumeration R (Fin 3) E centre hout i ν
  let u := normalisingUnit R (Fin 3) E centre hout i x
  have hnorm := congrArg (vectorMap ι) (normalizedVector_eq_rayPoint R (Fin 3) E centre hout i x)
  change vectorMap ι ((u : R) • coordinateChange R (Fin 3) centre x.val.val.rep) = _ at hnorm
  have hs : vectorMap ι ((u : R) • coordinateChange R (Fin 3) centre x.val.val.rep) =
      ι (u : R) • vectorMap ι (coordinateChange R (Fin 3) centre x.val.val.rep) := by
    funext j
    exact ι.map_mul _ _
  rw [hs] at hnorm
  have hp : vectorMap ι (rayPoint i.val.rep (rayParameter R (Fin 3) E centre hout i x)) =
      rayPoint (directionRepresentatives ι E centre hout i) (rayParameters ι E centre hout i ν) := by
    funext j
    cases j <;> rfl
  rw [hp] at hnorm
  exact hnorm.symm

theorem quadric_eval_ray_scaled (f g : PlaneRing K)
    (hf : f.IsHomogeneous 1) (hg : g.IsHomogeneous 2)
    (i : directionSet R (Fin 3) E centre hout)
    (ν : Fin (raySize R (Fin 3) E centre hout i)) :
    eval (rayPoint (directionRepresentatives ι E centre hout i) (rayParameters ι E centre hout i ν))
      (quadric f g) = rayScale ι E centre hout i ν ^ 2 *
        eval (vectorMap ι (rayEnumeration R (Fin 3) E centre hout i ν).val.val.rep)
          (originalQuadric ι centre f g) := by
  rw [normalized_rayPoint, homogeneous_eval_smul _ 2 (quadric_homogeneous f g hf hg),
    originalQuadric, rationalPullback_eval]

theorem mem_residualSet_rayEnumeration (f g : PlaneRing K)
    (hf : f.IsHomogeneous 1) (hg : g.IsHomogeneous 2)
    (i : directionSet R (Fin 3) E centre hout)
    (ν : Fin (raySize R (Fin 3) E centre hout i)) :
    (rayEnumeration R (Fin 3) E centre hout i ν).val.val ∈ residualSet ι E centre f g ↔
      eval (rayPoint (directionRepresentatives ι E centre hout i) (rayParameters ι E centre hout i ν))
        (quadric f g) ≠ 0 := by
  rw [quadric_eval_ray_scaled ι E centre hout f g hf hg]
  simp only [residualSet, Finset.mem_filter,
    (rayEnumeration R (Fin 3) E centre hout i ν).val.property, true_and, mul_ne_zero_iff]
  exact (and_iff_right (pow_ne_zero 2 (rayScale_nonzero ι E centre hout i ν))).symm

def rayCoordinateEquiv : (Σ i : directionSet R (Fin 3) E centre hout,
    Fin (raySize R (Fin 3) E centre hout i)) ≃ E :=
  (Equiv.sigmaCongrRight (fun i => rayEnumeration R (Fin 3) E centre hout i)).trans
    (Equiv.sigmaFiberEquiv (projectionIndex R (Fin 3) E centre hout))

def residualCoordinateEquiv (f g : PlaneRing K)
    (hf : f.IsHomogeneous 1) (hg : g.IsHomogeneous 2) :
    Remaining (raySize R (Fin 3) E centre hout) (directionRepresentatives ι E centre hout)
      (rayParameters ι E centre hout) f g ≃ residualSet ι E centre f g :=
  ((rayCoordinateEquiv E centre hout).subtypeEquiv
    (q := fun P : E => P.val ∈ residualSet ι E centre f g) (fun x =>
    (mem_residualSet_rayEnumeration ι E centre hout f g hf hg x.1 x.2).symm)).trans
      (⟨(fun x => ⟨x.val.val, x.property⟩),
        (fun x => ⟨⟨x.val, residualSet_subset ι E centre f g x.property⟩, x.property⟩),
        (fun _ => rfl), (fun _ => rfl)⟩ : {P : E // P.val ∈ residualSet ι E centre f g} ≃
        residualSet ι E centre f g)

theorem residualCoordinateEquiv_point (f g : PlaneRing K)
    (hf : f.IsHomogeneous 1) (hg : g.IsHomogeneous 2)
    (x : Remaining (raySize R (Fin 3) E centre hout) (directionRepresentatives ι E centre hout)
      (rayParameters ι E centre hout) f g) :
    (residualCoordinateEquiv ι E centre hout f g hf hg x).val =
      (rayEnumeration R (Fin 3) E centre hout x.val.1 x.val.2).val.val := rfl

theorem residual_card_upper (f g : PlaneRing K)
    (hf : f.IsHomogeneous 1) (hg : g.IsHomogeneous 2)
    (c : ∀ i : directionSet R (Fin 3) E centre hout, Fin (raySize R (Fin 3) E centre hout i) → K)
    (hr : ∀ i, 2 ≤ raySize R (Fin 3) E centre hout i) (hc : ∀ i ν, c i ν ≠ 0)
    (hM0 : ∀ i, rayMoment _ (rayParameters ι E centre hout) c i 0 = 0)
    (hM2 : ∀ i, rayMoment _ (rayParameters ι E centre hout) c i 2 =
      eval (directionRepresentatives ι E centre hout i) f * rayMoment _ (rayParameters ι E centre hout) c i 1)
    (hM3 : ∀ i, rayMoment _ (rayParameters ι E centre hout) c i 3 =
      eval (directionRepresentatives ι E centre hout i) g * rayMoment _ (rayParameters ι E centre hout) c i 1) :
    (residualSet ι E centre f g).card ≤ 3 * ∑ i, (raySize R (Fin 3) E centre hout i - 2) := by
  have h := remaining_card_upper (raySize R (Fin 3) E centre hout)
    (directionRepresentatives ι E centre hout) (rayParameters ι E centre hout) c f g hr
    (rayParameters_injective ι E centre hout) hc hM0 hM2 hM3
  rw [Fintype.card_congr (residualCoordinateEquiv ι E centre hout f g hf hg), Fintype.card_coe] at h
  exact h

theorem residual_full_support_relation (f g : PlaneRing K)
    (hf : f.IsHomogeneous 1) (hg : g.IsHomogeneous 2)
    (c : ∀ i : directionSet R (Fin 3) E centre hout, Fin (raySize R (Fin 3) E centre hout i) → K)
    (hc : ∀ i ν, c i ν ≠ 0) (d : ℕ) (hd : 2 ≤ d)
    (hrel : EvaluationRelation (directionRepresentatives ι E centre hout)
      (raySize R (Fin 3) E centre hout) (rayParameters ι E centre hout) c d) :
    ∃ c' : residualSet ι E centre f g → K, (∀ P, c' P ≠ 0) ∧
      PowerEvaluationRelation.Relation (fun P : residualSet ι E centre f g => vectorMap ι P.val.rep) c' (d - 2) := by
  let T := Remaining (raySize R (Fin 3) E centre hout) (directionRepresentatives ι E centre hout)
    (rayParameters ι E centre hout) f g
  let v : T → Option (Fin 3) → R := fun x =>
    coordinateChange R (Fin 3) centre (rayEnumeration R (Fin 3) E centre hout x.val.1 x.val.2).val.val.rep
  let c₀ : T → K := fun x => c x.val.1 x.val.2 *
    eval (rayPoint (directionRepresentatives ι E centre hout x.val.1)
      (rayParameters ι E centre hout x.val.1 x.val.2)) (quadric f g)
  let c₁ : T → K := fun x => c₀ x * rayScale ι E centre hout x.val.1 x.val.2 ^ (d - 2)
  obtain ⟨hc₀, hres⟩ := remaining_full_support_relation (raySize R (Fin 3) E centre hout)
    (directionRepresentatives ι E centre hout) (rayParameters ι E centre hout) c f g hf hg hc d hd hrel
  have htrans : PowerEvaluationRelation.Relation (fun x => vectorMap ι (v x)) c₁ (d - 2) := by
    intro P hP
    calc
      _ = ∑ x : T, c₀ x * eval (rayPoint (directionRepresentatives ι E centre hout x.val.1)
          (rayParameters ι E centre hout x.val.1 x.val.2)) P := by
        apply Finset.sum_congr rfl
        intro x _
        rw [normalized_rayPoint, homogeneous_eval_smul P (d - 2) hP]
        change (c₀ x * rayScale ι E centre hout x.val.1 x.val.2 ^ (d - 2)) *
          eval (vectorMap ι (v x)) P = c₀ x *
            (rayScale ι E centre hout x.val.1 x.val.2 ^ (d - 2) * eval (vectorMap ι (v x)) P)
        exact mul_assoc _ _ _
      _ = 0 := hres P hP
  have hback := relation_after_rational_change ι (coordinateChange R (Fin 3) centre).symm v c₁ (d - 2) htrans
  have hback' : PowerEvaluationRelation.Relation (fun x : T => vectorMap ι
      (rayEnumeration R (Fin 3) E centre hout x.val.1 x.val.2).val.val.rep) c₁ (d - 2) := by
    simpa only [v, LinearEquiv.symm_apply_apply] using hback
  let e := residualCoordinateEquiv ι E centre hout f g hf hg
  refine ⟨fun P => c₁ (e.symm P), fun P => mul_ne_zero (hc₀ _)
    (pow_ne_zero _ (rayScale_nonzero ι E centre hout _ _)), ?_⟩
  intro P hP
  rw [← e.sum_comp (fun x => c₁ (e.symm x) * eval (vectorMap ι x.val.rep) P)]
  simpa only [Equiv.symm_apply_apply, e, residualCoordinateEquiv_point] using hback' P hP

end Cylinder.RationalQuadricResidual
end
