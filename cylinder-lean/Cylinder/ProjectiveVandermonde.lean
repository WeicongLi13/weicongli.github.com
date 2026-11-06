module

public import Cylinder.ProjectiveProjection

/-!
# Vandermonde's bound for actual finite projective point sets

The original relation is tested after a constructed centre coordinate
change. On each actual projection fibre, representatives and coefficients
are rescaled by the normalizing unit. The normalized relation is proved,
and the coordinate Vandermonde theorem gives the bound on actual ray size.
-/

@[expose] public section

noncomputable section

namespace Cylinder.ProjectiveVandermonde

open Cylinder.ProjectiveProjection Cylinder.LinearEvaluationTransport
open scoped Classical BigOperators

variable (K σ : Type*) [Field K] [Fintype σ]
variable (E : Finset (Point K σ)) (centre : Point K σ) (houtside : centre ∉ E)

def rayPoints (i : directionSet K σ E centre houtside) : Finset (Point K σ) :=
  Finset.univ.image (fun x : RayIndex K σ E centre houtside i => x.val.val)

theorem rayPoints_card (i : directionSet K σ E centre houtside) :
    (rayPoints K σ E centre houtside i).card = raySize K σ E centre houtside i := by
  rw [rayPoints, Finset.card_image_of_injective]
  · exact Finset.card_univ
  · intro x y h
    exact Subtype.ext (Subtype.ext h)

theorem rayPoints_subset (i : directionSet K σ E centre houtside) :
    rayPoints K σ E centre houtside i ⊆ E := by
  intro P hP
  obtain ⟨x, _hx, rfl⟩ := Finset.mem_image.mp hP
  exact x.val.property

theorem rays_partition :
    Finset.univ.biUnion (rayPoints K σ E centre houtside) = E := by
  ext P
  constructor
  · intro hP
    obtain ⟨i, _hi, hP⟩ := Finset.mem_biUnion.mp hP
    exact rayPoints_subset K σ E centre houtside i hP
  · intro hP
    let x : E := ⟨P, hP⟩
    let i := projectionIndex K σ E centre houtside x
    let y : RayIndex K σ E centre houtside i := ⟨x, rfl⟩
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _,
      Finset.mem_image.mpr ⟨y, Finset.mem_univ _, rfl⟩⟩

theorem rays_pairwise_disjoint : Pairwise (fun i j =>
    Disjoint (rayPoints K σ E centre houtside i) (rayPoints K σ E centre houtside j)) := by
  intro i j hij
  apply Finset.disjoint_left.mpr
  intro P hPi hPj
  obtain ⟨x, _hx, hxP⟩ := Finset.mem_image.mp hPi
  obtain ⟨y, _hy, hyP⟩ := Finset.mem_image.mp hPj
  have hxy : x.val = y.val := Subtype.ext (hxP.trans hyP.symm)
  apply hij
  exact x.property.symm.trans ((congrArg (projectionIndex K σ E centre houtside) hxy).trans y.property)

def HasFullSupportRelation (d : ℕ) : Prop :=
  ∃ c : E → K, (∀ x, c x ≠ 0) ∧
    PowerEvaluationRelation.Relation (fun x : E => x.val.rep) c d

def normalizedCoefficients (c : E → K) (d : ℕ)
    (i : directionSet K σ E centre houtside) (ν : Fin (raySize K σ E centre houtside i)) : K :=
  c (rayEnumeration K σ E centre houtside i ν).val /
    (normalisingUnit K σ E centre houtside i (rayEnumeration K σ E centre houtside i ν) : K) ^ d

theorem normalizedCoefficients_ne_zero (c : E → K) (hc : ∀ x, c x ≠ 0) (d : ℕ)
    (i : directionSet K σ E centre houtside) (ν : Fin (raySize K σ E centre houtside i)) :
    normalizedCoefficients K σ E centre houtside c d i ν ≠ 0 :=
  rescaled_coefficient_ne_zero _ _ d (hc _)
    (Units.ne_zero (normalisingUnit K σ E centre houtside i (rayEnumeration K σ E centre houtside i ν)))

theorem normalized_evaluation_relation (c : E → K) (d : ℕ)
    (hrel : PowerEvaluationRelation.Relation (fun x : E => x.val.rep) c d) :
    EvaluationProjection.EvaluationRelation
      (fun i : directionSet K σ E centre houtside => i.val.rep)
      (raySize K σ E centre houtside) (rayTimes K σ E centre houtside)
      (normalizedCoefficients K σ E centre houtside c d) d := by
  intro F hF
  have hlinear := relation_after_linearEquiv (fun x : E => x.val.rep) c d
    (coordinateChange K σ centre) hrel
  calc
    (∑ i : directionSet K σ E centre houtside, ∑ ν : Fin (raySize K σ E centre houtside i),
      normalizedCoefficients K σ E centre houtside c d i ν *
        MvPolynomial.eval (EvaluationProjection.rayPoint i.val.rep
          (rayTimes K σ E centre houtside i ν)) F) =
        ∑ i : directionSet K σ E centre houtside, ∑ ν : Fin (raySize K σ E centre houtside i),
          c (rayEnumeration K σ E centre houtside i ν).val *
            MvPolynomial.eval (coordinateChange K σ centre
              (rayEnumeration K σ E centre houtside i ν).val.val.rep) F := by
      apply Finset.sum_congr rfl
      intro i _hi
      apply Finset.sum_congr rfl
      intro ν _hν
      let x := rayEnumeration K σ E centre houtside i ν
      let u := normalisingUnit K σ E centre houtside i x
      change (c x.val / (u : K) ^ d) *
        MvPolynomial.eval (EvaluationProjection.rayPoint i.val.rep
          (rayParameter K σ E centre houtside i x)) F =
        c x.val * MvPolynomial.eval (coordinateChange K σ centre x.val.val.rep) F
      rw [← normalizedVector_eq_rayPoint K σ E centre houtside i x]
      change (c x.val / (u : K) ^ d) *
        MvPolynomial.eval ((u : K) • coordinateChange K σ centre x.val.val.rep) F = _
      rw [homogeneous_eval_smul F d hF, ← mul_assoc, div_mul_cancel₀ _ (pow_ne_zero d (Units.ne_zero u))]
    _ = ∑ x : E, c x * MvPolynomial.eval (coordinateChange K σ centre x.val.rep) F :=
      sum_over_rays K σ E centre houtside
        (fun x => c x * MvPolynomial.eval (coordinateChange K σ centre x.val.rep) F)
    _ = 0 := hlinear F hF

/-- The full geometric form of Lemma `lem:vandermonde`. -/
theorem ray_card_lower_bound [Infinite K] (d a : ℕ) (ha : a ≤ d)
    (hfull : HasFullSupportRelation K σ E d)
    (hind : EvaluationProjection.Independent
      (fun i : directionSet K σ E centre houtside => i.val.rep) a)
    (i : directionSet K σ E centre houtside) :
    d - a + 2 ≤ (rayPoints K σ E centre houtside i).card := by
  rw [rayPoints_card]
  obtain ⟨c, hc, hrel⟩ := hfull
  exact EvaluationProjection.ray_size_lower_bound_of_evaluation_relation
    (fun i : directionSet K σ E centre houtside => i.val.rep) (fun i => i.val.rep_nonzero)
    (raySize K σ E centre houtside) (raySize_pos K σ E centre houtside)
    (rayTimes K σ E centre houtside) (normalizedCoefficients K σ E centre houtside c d)
    (rayTimes_injective K σ E centre houtside) (normalizedCoefficients_ne_zero K σ E centre houtside c hc d)
    d a ha hind (normalized_evaluation_relation K σ E centre houtside c d hrel) i

end Cylinder.ProjectiveVandermonde

end
