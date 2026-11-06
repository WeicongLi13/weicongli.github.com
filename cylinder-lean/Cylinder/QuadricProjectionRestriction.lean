module

public import Cylinder.QuadricRayAlgebra
public import Cylinder.ProjectiveProjection
public import Cylinder.FiniteGrid

/-! The centre-coordinate quadric calculation applied to the actual finite
projective projection and its constructed, distinct ray parameters. -/

@[expose] public section
noncomputable section
open scoped Classical

namespace Cylinder.QuadricProjectionRestriction

open MvPolynomial Cylinder.LinearEvaluationTransport Cylinder.ProjectiveProjection

variable {K : Type} [Field K] [Fintype K]

theorem small_degree_pullback_nonzero {σ : Type} [Fintype σ]
    (g : (σ → K) ≃ₗ[K] (σ → K)) (Q : MvPolynomial σ K) (d : ℕ)
    (hQ : Q.IsHomogeneous d) (hQ0 : Q ≠ 0) (hd : d < Fintype.card K) :
    linearPullback g Q ≠ 0 := by
  intro hz
  apply hQ0
  apply FiniteGrid.eq_zero_of_degreeOf_lt_card Q
    (fun i => lt_of_le_of_lt ((degreeOf_le_totalDegree Q i).trans hQ.totalDegree_le) hd)
  intro x
  have he := congrArg (eval (g.symm x)) hz
  simpa only [linearPullback_eval, g.apply_symm_apply, map_zero] using he

omit [Field K] [Fintype K] in
theorem reindex_cons_rayPoint (v : Fin 3 → K) (t : K) :
    (fun o => (Fin.cons t v : Fin 4 → K) ((finSuccEquiv 3).symm o)) = EvaluationProjection.rayPoint v t := by
  funext o
  cases o <;> rfl

theorem centered_quadric_on_rays
    (E : Finset (Point K (Fin 3))) (centre : Point K (Fin 3)) (houtside : centre ∉ E)
    (Q : MvPolynomial (Option (Fin 3)) K) (hQ : Q.IsHomogeneous 2) (hQ0 : Q ≠ 0)
    (hK : 2 < Fintype.card K) (hcentre : eval centre.rep Q = 0)
    (hzero : ∀ P ∈ E, eval P.rep Q = 0) :
    ∃ R : MvPolynomial (Fin 4) K, R.IsHomogeneous 2 ∧ R ≠ 0 ∧
      eval (Fin.cons 1 0) R = 0 ∧
      ∀ (i : directionSet K (Fin 3) E centre houtside) (ν : Fin (raySize K (Fin 3) E centre houtside i)),
        eval (Fin.cons (rayTimes K (Fin 3) E centre houtside i ν) i.val.rep) R = 0 := by
  let g := coordinateChange K (Fin 3) centre
  let Q' := linearPullback g.symm Q
  have hQ' : Q'.IsHomogeneous 2 := linearPullback_homogeneous g.symm Q 2 hQ
  have hQ'0 : Q' ≠ 0 := small_degree_pullback_nonzero g.symm Q 2 hQ hQ0 hK
  have haxis : eval (centreAxis K (Fin 3)) Q' = 0 := by
    change eval (centreAxis K (Fin 3)) (linearPullback g.symm Q) = 0
    rw [linearPullback_eval]
    have he : g.symm (centreAxis K (Fin 3)) = centre.rep := by
      rw [← coordinateChange_centre K (Fin 3) centre]
      exact g.symm_apply_apply _
    rwa [he]
  have hnorm : ∀ (i : directionSet K (Fin 3) E centre houtside)
      (x : RayIndex K (Fin 3) E centre houtside i),
      eval (normalizedVector K (Fin 3) E centre houtside i x) Q' = 0 := by
    intro i x
    rw [normalizedVector, homogeneous_eval_smul Q' 2 hQ']
    change (normalisingUnit K (Fin 3) E centre houtside i x : K) ^ 2 *
      eval (g x.val.val.rep) (linearPullback g.symm Q) = 0
    rw [linearPullback_eval, g.symm_apply_apply, hzero x.val.val x.val.property, mul_zero]
  let R := rename (finSuccEquiv 3).symm Q'
  have hR : R.IsHomogeneous 2 := hQ'.rename_isHomogeneous (f := (finSuccEquiv 3).symm)
  have hR0 : R ≠ 0 := by
    intro hz
    exact hQ'0 ((rename_injective (finSuccEquiv 3).symm (finSuccEquiv 3).symm.injective)
      (by simpa only [R, map_zero] using hz))
  have hRaxis : eval (Fin.cons 1 0) R = 0 := by
    dsimp only [R]
    rw [eval_rename]
    have he : (Fin.cons 1 (0 : Fin 3 → K)) ∘ (finSuccEquiv 3).symm = centreAxis K (Fin 3) := by
      funext o
      cases o <;> rfl
    rwa [he]
  refine ⟨R, hR, hR0, hRaxis, ?_⟩
  intro i ν
  dsimp only [R]
  rw [eval_rename]
  change eval (fun o => (Fin.cons (rayTimes K (Fin 3) E centre houtside i ν) i.val.rep : Fin 4 → K)
    ((finSuccEquiv 3).symm o)) Q' = 0
  rw [reindex_cons_rayPoint, rayTimes]
  rw [← normalizedVector_eq_rayPoint K (Fin 3) E centre houtside i
    (rayEnumeration K (Fin 3) E centre houtside i ν)]
  exact hnorm i _

theorem quadric_directions_equation
    (E : Finset (Point K (Fin 3))) (centre : Point K (Fin 3)) (houtside : centre ∉ E)
    (Q : MvPolynomial (Option (Fin 3)) K) (hQ : Q.IsHomogeneous 2) (hQ0 : Q ≠ 0)
    (hK : 2 < Fintype.card K) (hcentre : eval centre.rep Q = 0)
    (hzero : ∀ P ∈ E, eval P.rep Q = 0)
    (hrays : ∀ i : directionSet K (Fin 3) E centre houtside, 2 ≤ raySize K (Fin 3) E centre houtside i) :
    ∃ d : ℕ, (d = 1 ∨ d = 2) ∧ ∃ F : MvPolynomial (Fin 3) K,
      F.IsHomogeneous d ∧ F ≠ 0 ∧ ∀ i : directionSet K (Fin 3) E centre houtside, eval i.val.rep F = 0 := by
  obtain ⟨R, hR, hR0, hRa, hz⟩ := centered_quadric_on_rays E centre houtside Q hQ hQ0 hK hcentre hzero
  have hex : ∀ i : directionSet K (Fin 3) E centre houtside, ∃ t u : K,
      t ≠ u ∧ eval (Fin.cons t i.val.rep) R = 0 ∧ eval (Fin.cons u i.val.rep) R = 0 := by
    intro i
    let zeroIndex : Fin (raySize K (Fin 3) E centre houtside i) := ⟨0, by have h := hrays i; omega⟩
    let oneIndex : Fin (raySize K (Fin 3) E centre houtside i) := ⟨1, by have h := hrays i; omega⟩
    refine ⟨rayTimes K (Fin 3) E centre houtside i zeroIndex,
      rayTimes K (Fin 3) E centre houtside i oneIndex, ?_, hz i zeroIndex, hz i oneIndex⟩
    intro he
    have hh := rayTimes_injective K (Fin 3) E centre houtside i he
    have hv := congrArg Fin.val hh
    norm_num [zeroIndex, oneIndex] at hv
  choose t u htu ht hu using hex
  exact QuadricRayAlgebra.equation_from_two_points_per_ray
    (I := directionSet K (Fin 3) E centre houtside) R hR hR0 hRa (fun i => i.val.rep) t u htu ht hu

end Cylinder.QuadricProjectionRestriction

end
