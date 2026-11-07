module
public import Cylinder.ProjectionChart
public import Cylinder.LocalRepresentativeTransport
public import Cylinder.LocalPointReindexing
public import Cylinder.MomentCoordinatePullback
@[expose] public section
noncomputable section
open scoped Classical LinearAlgebra.Projectivization
namespace Cylinder.ProjectionTransport
open ProjectiveProjection ProjectionChart LinearEvaluationTransport EvaluationProjection
open MvPolynomial HilbertEvaluation PlaneNumericalCharacter PlaneBinaryReduction
variable {K σ I J : Type*} [Field K]

/-- Independence is invariant under every invertible linear coordinate change. -/
theorem independent_linearEquiv [Fintype σ] (A : (σ → K) ≃ₗ[K] (σ → K))
    (v : I → σ → K) (d : ℕ) :
    Independent (fun i => A (v i)) d ↔ Independent v d := by
  constructor
  · intro h w
    obtain ⟨F, hF, hval⟩ := h w
    exact ⟨linearPullback A F, linearPullback_homogeneous A F d hF,
      fun i => (linearPullback_eval A F (v i)).trans (hval i)⟩
  · intro h w
    obtain ⟨F, hF, hval⟩ := h w
    refine ⟨linearPullback A.symm F, linearPullback_homogeneous A.symm F d hF, ?_⟩
    intro i
    simpa only [linearPullback_eval, A.symm_apply_apply] using hval i

theorem independent_rescaling [Fintype σ] (v : I → σ → K)
    (a : I → K) (ha : ∀ i, a i ≠ 0) (d : ℕ) :
    Independent (fun i => a i • v i) d ↔ Independent v d := by
  constructor
  · intro h w
    obtain ⟨F, hF, hval⟩ := h (fun i => a i ^ d * w i)
    refine ⟨F, hF, ?_⟩
    intro i
    have hi := hval i
    rw [homogeneous_eval_smul F d hF] at hi
    exact mul_left_cancel₀ (pow_ne_zero d (ha i)) hi
  · intro h w
    obtain ⟨F, hF, hval⟩ := h (fun i => w i / a i ^ d)
    refine ⟨F, hF, ?_⟩
    intro i
    rw [homogeneous_eval_smul F d hF, hval i, mul_div_cancel₀ _ (pow_ne_zero d (ha i))]

theorem independent_reindex (e : I ≃ J) (v : I → σ → K) (d : ℕ) :
    Independent (fun j => v (e.symm j)) d ↔ Independent v d := by
  constructor
  · intro h w
    obtain ⟨F, hF, hval⟩ := h (fun j => w (e.symm j))
    exact ⟨F, hF, fun i => by simpa using hval (e i)⟩
  · intro h w
    obtain ⟨F, hF, hval⟩ := h (fun i => w (e i))
    exact ⟨F, hF, fun j => by simpa using hval (e.symm j)⟩

/-- Actual substitution, with its inverse, on all polynomials. -/
def pullbackEquiv [Fintype σ] (A : (σ → K) ≃ₗ[K] (σ → K)) :
    MvPolynomial σ K ≃ₐ[K] MvPolynomial σ K where
  toFun := linearPullback A
  invFun := linearPullback A.symm
  left_inv F := MomentCoordinateTransport.linearPullback_symm A F
  right_inv F := by simpa using MomentCoordinateTransport.linearPullback_symm A.symm F
  map_mul' := map_mul (aeval (linearCoordinate A))
  map_add' := map_add (aeval (linearCoordinate A))
  commutes' := (aeval (linearCoordinate A)).commutes

theorem idealPiece_ne_bot_iff [Fintype I] (v : I → Fin 3 → K) (d : ℕ) :
    idealPiece v d ≠ ⊥ ↔ ∃ F : PlaneRing K, F ≠ 0 ∧ F.IsHomogeneous d ∧
      ∀ i, eval (v i) F = 0 := by
  constructor
  · intro h
    obtain ⟨F, hmem, hne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h
    refine ⟨F.val, fun hz => hne (Subtype.ext hz), F.property, ?_⟩
    exact (homogeneous_mem_vanishingIdeal v F.val d F.property).mp hmem
  · rintro ⟨F, hne, hF, hv⟩ hz
    have hm : (⟨F, hF⟩ : Forms K d) ∈ idealPiece v d :=
      (homogeneous_mem_vanishingIdeal v F d hF).mpr hv
    rw [hz, Submodule.mem_bot] at hm
    exact hne (congrArg Subtype.val hm)

theorem idealPiece_linearEquiv_ne_bot [Fintype I]
    (A : (Fin 3 → K) ≃ₗ[K] (Fin 3 → K)) (v : I → Fin 3 → K) (d : ℕ) :
    idealPiece (fun i => A (v i)) d ≠ ⊥ ↔ idealPiece v d ≠ ⊥ := by
  rw [idealPiece_ne_bot_iff, idealPiece_ne_bot_iff]
  constructor
  · rintro ⟨F, hne, hF, hv⟩
    refine ⟨linearPullback A F, ?_, linearPullback_homogeneous A F d hF, ?_⟩
    · exact (map_ne_zero_iff (pullbackEquiv A) (pullbackEquiv A).injective).mpr hne
    · intro i; simpa using hv i
  · rintro ⟨F, hne, hF, hv⟩
    refine ⟨linearPullback A.symm F, ?_, linearPullback_homogeneous A.symm F d hF, ?_⟩
    · exact (map_ne_zero_iff (pullbackEquiv A.symm) (pullbackEquiv A.symm).injective).mpr hne
    · intro i; simpa using hv i

theorem initialDegree_linearEquiv [Fintype I]
    (A : (Fin 3 → K) ≃ₗ[K] (Fin 3 → K)) (v : I → Fin 3 → K) (s : ℕ) :
    InitialDegree (fun i => A (v i)) s ↔ InitialDegree v s := by
  have hb (d : ℕ) : idealPiece (fun i => A (v i)) d = ⊥ ↔ idealPiece v d = ⊥ :=
    not_iff_not.mp (idealPiece_linearEquiv_ne_bot A v d)
  simp only [InitialDegree, idealPiece_linearEquiv_ne_bot A v, hb]

theorem initialDegree_linearEquiv_rescaling [Fintype I]
    (A : (Fin 3 → K) ≃ₗ[K] (Fin 3 → K)) (v : I → Fin 3 → K)
    (a : I → K) (ha : ∀ i, a i ≠ 0) (s : ℕ) :
    InitialDegree (fun i => a i • A (v i)) s ↔ InitialDegree v s :=
  (LocalRepresentativeTransport.initialDegree_rescaling _ a ha s).trans
    (initialDegree_linearEquiv A v s)

/-- The actual induced projective map, as a bijection. -/
def projectiveEquiv (A : (σ → K) ≃ₗ[K] (σ → K)) : Direction K σ ≃ Direction K σ where
  toFun := Projectivization.map A.toLinearMap A.injective
  invFun := Projectivization.map A.symm.toLinearMap A.symm.injective
  left_inv P := by
    induction P using Projectivization.ind with
    | h v hv => simp only [Projectivization.map_mk, LinearEquiv.coe_coe,
        LinearEquiv.symm_apply_apply]
  right_inv P := by
    induction P using Projectivization.ind with
    | h v hv => simp only [Projectivization.map_mk, LinearEquiv.coe_coe,
        LinearEquiv.apply_symm_apply]

variable [Finite σ] {centre : Point K σ}

def projectPoint (C : Chart centre) (P : Point K σ) (hP : P ≠ centre) : Direction K σ :=
  Projectivization.mk K (tail (C.g P.rep)) (by
    rw [C.directionVector_eq]
    exact fun h => directionVector_ne_zero K σ centre P hP
      (C.directionEquiv.injective (by simpa using h)))

theorem projectPoint_eq (C : Chart centre) (P : Point K σ) (hP : P ≠ centre) :
    projectPoint C P hP = projectiveEquiv C.directionEquiv
      (ProjectiveProjection.projectPoint K σ centre P hP) := by
  simp only [projectPoint, projectiveEquiv, Equiv.coe_fn_mk,
    ProjectiveProjection.projectPoint, Projectivization.map_mk, LinearEquiv.coe_coe,
    C.directionVector_eq]

variable (E : Finset (Point K σ)) (houtside : centre ∉ E)

def directionSet (C : Chart centre) : Finset (Direction K σ) :=
  (ProjectiveProjection.directionSet K σ E centre houtside).image
    (projectiveEquiv C.directionEquiv)

theorem directionSet_actual (C : Chart centre) : directionSet E houtside C =
    Finset.univ.image (fun x : E => projectPoint C x.val (fun h => houtside (h ▸ x.property))) := by
  simp only [directionSet, ProjectiveProjection.directionSet, Finset.image_image]
  congr 1
  funext x
  exact (projectPoint_eq C x.val _).symm

def indexEquiv (C : Chart centre) : ProjectiveProjection.directionSet K σ E centre houtside ≃
    directionSet E houtside C :=
  (projectiveEquiv C.directionEquiv).imageFinset _

theorem directionSet_card (C : Chart centre) :
    (directionSet E houtside C).card =
      (ProjectiveProjection.directionSet K σ E centre houtside).card := by
  exact Finset.card_image_of_injective _ (projectiveEquiv C.directionEquiv).injective

def projectionIndex (C : Chart centre) (x : E) : directionSet E houtside C :=
  indexEquiv E houtside C (ProjectiveProjection.projectionIndex K σ E centre houtside x)

abbrev RayIndex (C : Chart centre) (i : directionSet E houtside C) :=
  {x : E // projectionIndex E houtside C x = i}

def raySize (C : Chart centre) (i : directionSet E houtside C) : ℕ :=
  Fintype.card (RayIndex E houtside C i)

def rayEquiv (C : Chart centre) (i : ProjectiveProjection.directionSet K σ E centre houtside) :
    ProjectiveProjection.RayIndex K σ E centre houtside i ≃
      RayIndex E houtside C (indexEquiv E houtside C i) where
  toFun x := ⟨x.val, congrArg (indexEquiv E houtside C) x.property⟩
  invFun x := ⟨x.val, (indexEquiv E houtside C).injective x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem raySize_eq (C : Chart centre) (i : ProjectiveProjection.directionSet K σ E centre houtside) :
    raySize E houtside C (indexEquiv E houtside C i) =
      ProjectiveProjection.raySize K σ E centre houtside i :=
  Fintype.card_congr (rayEquiv E houtside C i).symm

/-- Every arbitrary choice of representative on each projected ray. -/
theorem representative_scale_exists (C : Chart centre)
    (i : ProjectiveProjection.directionSet K σ E centre houtside) :
    ∃ u : Kˣ, (indexEquiv E houtside C i).val.rep =
      (u : K) • C.directionEquiv i.val.rep := by
  have he : (indexEquiv E houtside C i).val =
      Projectivization.mk K (C.directionEquiv i.val.rep)
        (fun hz => i.val.rep_nonzero (C.directionEquiv.injective (by simpa using hz))) := by
    change projectiveEquiv C.directionEquiv i.val = _
    conv_lhs => rw [← Projectivization.mk_rep i.val]
    rfl
  rw [he]
  obtain ⟨u, hu⟩ := Projectivization.exists_smul_eq_mk_rep K
    (C.directionEquiv i.val.rep)
    (fun hz => i.val.rep_nonzero (C.directionEquiv.injective (by simpa using hz)))
  exact ⟨u, hu.symm⟩
/-- An arbitrary prescribed nonzero representative of the same projected
point is a nonzero multiple of the induced linear image. -/
theorem arbitrary_representative_scale (C : Chart centre)
    (i : ProjectiveProjection.directionSet K σ E centre houtside)
    (a : σ → K) (ha : a ≠ 0)
    (hpoint : Projectivization.mk K a ha = (indexEquiv E houtside C i).val) :
    ∃ u : Kˣ, a = (u : K) • C.directionEquiv i.val.rep := by
  have hA : (indexEquiv E houtside C i).val =
      Projectivization.mk K (C.directionEquiv i.val.rep)
        (fun hz => i.val.rep_nonzero (C.directionEquiv.injective (by simpa using hz))) := by
    change projectiveEquiv C.directionEquiv i.val = _
    conv_lhs => rw [← Projectivization.mk_rep i.val]
    rfl
  obtain ⟨u, hu⟩ := (Projectivization.mk_eq_mk_iff K _ _ _ _).mp (hpoint.trans hA)
  exact ⟨u, hu.symm⟩
def representativeScale (C : Chart centre)
    (i : ProjectiveProjection.directionSet K σ E centre houtside) : Kˣ :=
  Classical.choose (representative_scale_exists E houtside C i)

theorem representativeScale_spec (C : Chart centre)
    (i : ProjectiveProjection.directionSet K σ E centre houtside) :
    (indexEquiv E houtside C i).val.rep =
      (representativeScale E houtside C i : K) • C.directionEquiv i.val.rep :=
  Classical.choose_spec (representative_scale_exists E houtside C i)


theorem smul_rayPoint (u : K) (a : σ → K) (t : K) :
    u • rayPoint a t = rayPoint (u • a) (u * t) := by
  ext o
  cases o <;> simp [rayPoint]
/-- The same original point, in arbitrary coordinates and any chosen direction scale. -/
theorem normalizedVector_eq_rayPoint (C : Chart centre)
    (i : ProjectiveProjection.directionSet K σ E centre houtside)
    (x : ProjectiveProjection.RayIndex K σ E centre houtside i) (u : Kˣ) :
    ((u : K) * (ProjectiveProjection.normalisingUnit K σ E centre houtside i x : K)) •
        C.g x.val.val.rep =
      rayPoint ((u : K) • C.directionEquiv i.val.rep)
        ((u : K) * (C.timeShift i.val.rep + (C.c : K) *
          ProjectiveProjection.rayParameter K σ E centre houtside i x)) := by
  have hv := congrArg C.transition
    (ProjectiveProjection.normalizedVector_eq_rayPoint K σ E centre houtside i x)
  rw [C.transition_rayPoint] at hv
  have h := congrArg (fun y => (u : K) • y) hv
  simpa [ProjectiveProjection.normalizedVector, Chart.transition, map_smul,
    smul_smul, smul_rayPoint] using h

end Cylinder.ProjectionTransport
end




