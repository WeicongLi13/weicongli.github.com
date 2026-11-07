module
public import Cylinder.ProjectionTransport
public import Cylinder.RationalPlaneLine
@[expose] public section
noncomputable section
open scoped Classical LinearAlgebra.Projectivization BigOperators
namespace Cylinder.ProjectionTransportGeometry
open ProjectiveProjection ProjectionChart ProjectionTransport
open MvPolynomial EvaluationProjection LinearEvaluationTransport PlaneBinaryReduction
open PlaneCrossProduct RationalPlaneLine PlaneLinearForms PowerEvaluationRelation
variable {K σ : Type*} [Field K]

theorem projectiveEquiv_rep_scale (A : (σ → K) ≃ₗ[K] (σ → K))
    (P : Direction K σ) : ∃ u : Kˣ, (projectiveEquiv A P).rep = (u : K) • A P.rep := by
  have he : projectiveEquiv A P = Projectivization.mk K (A P.rep)
      (fun h => P.rep_nonzero (A.injective (by simpa using h))) := by
    conv_lhs => rw [← Projectivization.mk_rep P]
    rfl
  rw [he]
  obtain ⟨u, hu⟩ := Projectivization.exists_smul_eq_mk_rep K (A P.rep)
    (fun h => P.rep_nonzero (A.injective (by simpa using h)))
  exact ⟨u, hu.symm⟩

theorem dot_projectiveEquiv_zero_iff (A : (Fin 3 → K) ≃ₗ[K] (Fin 3 → K))
    (P : PlanePoint K) (c : Fin 3 → K) :
    dot c (projectiveEquiv A P).rep = 0 ↔ dot c (A P.rep) = 0 := by
  obtain ⟨u, hu⟩ := projectiveEquiv_rep_scale A P
  rw [hu]
  have hd : dot c ((u : K) • A P.rep) = (u : K) * dot c (A P.rep) := by
    simp [dot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_left_comm]
  rw [hd, mul_eq_zero]
  exact or_iff_right u.ne_zero

/-- Projective linear changes preserve the genuine rational-line cap. -/
theorem lineCap_image (A : (Fin 3 → K) ≃ₗ[K] (Fin 3 → K))
    (D : Finset (PlanePoint K)) (b : ℕ) (hcap : LineCap D b) :
    LineCap (D.image (projectiveEquiv A)) b := by
  intro c hc
  let F := linearPullback A (linearForm c)
  have hF : F.IsHomogeneous 1 := linearPullback_homogeneous A _ 1 (linearFormMap c).property
  obtain ⟨d, hd⟩ := exists_coefficients F hF
  have hdval (x : Fin 3 → K) : dot d x = dot c (A x) := by
    have he := congrArg (eval x) hd
    simpa [F, linearPullback_eval, eval_linearForm] using he.symm
  have hd0 : d ≠ 0 := by
    intro hz
    apply hc
    funext j
    have he := hdval (A.symm (Pi.single j 1))
    simpa [hz, dot, Pi.single_apply] using he.symm
  have hset : (D.image (projectiveEquiv A)).filter (fun P => dot c P.rep = 0) =
      (D.filter (fun P => dot d P.rep = 0)).image (projectiveEquiv A) := by
    ext P
    simp only [Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro ⟨⟨Q, hQ, rfl⟩, hz⟩
      exact ⟨Q, ⟨hQ, (hdval Q.rep).trans ((dot_projectiveEquiv_zero_iff A Q c).mp hz)⟩, rfl⟩
    · rintro ⟨Q, ⟨hQ, hz⟩, rfl⟩
      exact ⟨⟨Q, hQ, rfl⟩, (dot_projectiveEquiv_zero_iff A Q c).mpr
        ((hdval Q.rep).symm.trans hz)⟩
  rw [hset, Finset.card_image_of_injective _ (projectiveEquiv A).injective]
  exact hcap d hd0

variable [Fintype σ] {centre : Point K σ} (E : Finset (Point K σ)) (houtside : centre ∉ E)

theorem independent_directionSet (C : Chart centre) (d : ℕ) :
    Independent (fun i : ProjectionTransport.directionSet E houtside C => i.val.rep) d ↔
      Independent (fun i : ProjectiveProjection.directionSet K σ E centre houtside => i.val.rep) d := by
  let e := indexEquiv E houtside C
  have h := (independent_reindex e.symm
    (fun i : ProjectionTransport.directionSet E houtside C => i.val.rep) d).symm
  simp only [Equiv.symm_symm] at h
  rw [h]
  simp only [e, representativeScale_spec]
  exact (independent_rescaling _ _ (fun i => (representativeScale E houtside C i).ne_zero) d).trans
    (independent_linearEquiv C.directionEquiv _ d)

#print axioms lineCap_image
#print axioms independent_directionSet
end Cylinder.ProjectionTransportGeometry
end

