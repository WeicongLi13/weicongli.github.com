module
public import Cylinder.ArbitraryProjectionHyperplane
public import Cylinder.ProjectionTransport
@[expose] public section
noncomputable section
open scoped Classical LinearAlgebra.Projectivization
namespace Cylinder.ArbitraryProjectionModel
open ProjectiveProjection ProjectionChart ProjectionTransport ArbitraryProjectionHyperplane
variable {K σ : Type*} [Field K] [Finite σ]
variable (centre : Point K σ) (ell : Module.Dual K (Space K σ)) (hb : ell centre.rep ≠ 0)

def projectToPlane (P : Point K σ) (hP : P ≠ centre) :
    Projectivization K (LinearMap.ker ell) :=
  Projectivization.mk K ⟨retract centre ell P.rep, retract_mem centre ell hb P.rep⟩
    (fun hz => retract_ne_zero centre P ell hP (congrArg Subtype.val hz))

theorem projectToPlane_original (P : Point K σ) (hP : P ≠ centre) :
    Projectivization.map (LinearMap.ker ell).subtype (LinearMap.ker ell).subtype_injective
      (projectToPlane centre ell hb P hP) = ArbitraryProjectionHyperplane.projectPoint centre P ell hP := by
  rw [projectToPlane, Projectivization.map_mk]
  rfl

def planeEquiv : Projectivization K (LinearMap.ker ell) ≃ Direction K σ where
  toFun := Projectivization.map (hyperplaneEquiv centre ell hb).toLinearMap
    (hyperplaneEquiv centre ell hb).injective
  invFun := Projectivization.map (hyperplaneEquiv centre ell hb).symm.toLinearMap
    (hyperplaneEquiv centre ell hb).symm.injective
  left_inv P := by
    induction P using Projectivization.ind with
    | h v hv => simp only [Projectivization.map_mk, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
  right_inv P := by
    induction P using Projectivization.ind with
    | h v hv => simp only [Projectivization.map_mk, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]

theorem planeEquiv_projectToPlane (P : Point K σ) (hP : P ≠ centre) :
    planeEquiv centre ell hb (projectToPlane centre ell hb P hP) =
      ProjectionTransport.projectPoint (chart centre ell hb) P hP := by
  simp only [planeEquiv, projectToPlane, Equiv.coe_fn_mk, Projectivization.map_mk,
    LinearEquiv.coe_coe, hyperplaneEquiv_projection, ProjectionTransport.projectPoint]

/-- Identify the actual given hyperplane with the directions in any prescribed chart. -/
def planeLinearEquivForChart (C : Chart centre) :
    LinearMap.ker ell ≃ₗ[K] (σ → K) :=
  (hyperplaneEquiv centre ell hb).trans
    ((chart centre ell hb).directionEquiv.symm.trans C.directionEquiv)

def planeEquivForChart (C : Chart centre) :
    Projectivization K (LinearMap.ker ell) ≃ Direction K σ :=
  (planeEquiv centre ell hb).trans
    ((projectiveEquiv (chart centre ell hb).directionEquiv).symm.trans
      (projectiveEquiv C.directionEquiv))

/-- The projective bijection is induced by this explicit linear coordinate map. -/
theorem planeEquivForChart_map (C : Chart centre)
    (P : Projectivization K (LinearMap.ker ell)) :
    planeEquivForChart centre ell hb C P =
      Projectivization.map (planeLinearEquivForChart centre ell hb C).toLinearMap
        (planeLinearEquivForChart centre ell hb C).injective P := by
  induction P using Projectivization.ind with
  | h v hv =>
    simp [planeEquivForChart, planeLinearEquivForChart, planeEquiv,
      projectiveEquiv, Projectivization.map_mk]

theorem planeEquivForChart_projectToPlane (C : Chart centre)
    (P : Point K σ) (hP : P ≠ centre) :
    planeEquivForChart centre ell hb C (projectToPlane centre ell hb P hP) =
      ProjectionTransport.projectPoint C P hP := by
  change projectiveEquiv C.directionEquiv
    ((projectiveEquiv (chart centre ell hb).directionEquiv).symm
      (planeEquiv centre ell hb (projectToPlane centre ell hb P hP))) = _
  rw [planeEquiv_projectToPlane, ProjectionTransport.projectPoint_eq,
    Equiv.symm_apply_apply, ProjectionTransport.projectPoint_eq]

variable (E : Finset (Point K σ)) (houtside : centre ∉ E)

def planeProjectionSet : Finset (Projectivization K (LinearMap.ker ell)) :=
  Finset.univ.image (fun x : E => projectToPlane centre ell hb x.val
    (fun h => houtside (h ▸ x.property)))

theorem planeProjectionSet_image :
    (planeProjectionSet centre ell hb E houtside).image (planeEquiv centre ell hb) =
      ProjectionTransport.directionSet E houtside (chart centre ell hb) := by
  rw [ProjectionTransport.directionSet_actual]
  simp only [planeProjectionSet, Finset.image_image, Function.comp_def, planeEquiv_projectToPlane]

theorem planeProjectionSet_card :
    (planeProjectionSet centre ell hb E houtside).card =
      (ProjectiveProjection.directionSet K σ E centre houtside).card := by
  rw [← ProjectionTransport.directionSet_card E houtside (chart centre ell hb),
    ← planeProjectionSet_image, Finset.card_image_of_injective _ (planeEquiv centre ell hb).injective]

/-- The finite set on the actual hyperplane is in bijection with the
arbitrary-coordinate direction set, preserving the point on each original ray. -/
def planeSetEquiv : planeProjectionSet centre ell hb E houtside ≃
    ProjectionTransport.directionSet E houtside (chart centre ell hb) where
  toFun x := ⟨planeEquiv centre ell hb x.val, by
    rw [← planeProjectionSet_image]
    exact Finset.mem_image.mpr ⟨x.val, x.property, rfl⟩⟩
  invFun y := ⟨(planeEquiv centre ell hb).symm y.val, by
    have hy : y.val ∈ (planeProjectionSet centre ell hb E houtside).image
        (planeEquiv centre ell hb) := by
      simpa only [planeProjectionSet_image] using y.property
    obtain ⟨x, hx, he⟩ := Finset.mem_image.mp hy
    rw [← he, Equiv.symm_apply_apply]
    exact hx⟩
  left_inv x := by
    apply Subtype.ext
    exact (planeEquiv centre ell hb).symm_apply_apply x.val
  right_inv y := by
    apply Subtype.ext
    exact (planeEquiv centre ell hb).apply_symm_apply y.val


def planeProjectionIndex (x : E) : planeProjectionSet centre ell hb E houtside :=
  ⟨projectToPlane centre ell hb x.val (fun h => houtside (h ▸ x.property)),
    Finset.mem_image.mpr ⟨x, Finset.mem_univ _, rfl⟩⟩

theorem planeSetEquiv_projectionIndex (x : E) :
    planeSetEquiv centre ell hb E houtside (planeProjectionIndex centre ell hb E houtside x) =
      ProjectionTransport.projectionIndex E houtside (chart centre ell hb) x := by
  apply Subtype.ext
  simp [planeSetEquiv, planeProjectionIndex, ProjectionTransport.projectionIndex,
    ProjectionTransport.indexEquiv, ProjectiveProjection.projectionIndex,
    ProjectiveProjection.projection, planeEquiv_projectToPlane,
    ProjectionTransport.projectPoint_eq, Equiv.imageFinset, Equiv.subtypeEquiv,
    Equiv.coe_fn_mk] <;> rfl

abbrev PlaneRayIndex (i : planeProjectionSet centre ell hb E houtside) :=
  {x : E // planeProjectionIndex centre ell hb E houtside x = i}

def planeRayEquiv (i : planeProjectionSet centre ell hb E houtside) :
    PlaneRayIndex centre ell hb E houtside i ≃
      ProjectionTransport.RayIndex E houtside (chart centre ell hb)
        (planeSetEquiv centre ell hb E houtside i) where
  toFun x := ⟨x.val, by rw [← planeSetEquiv_projectionIndex, x.property]⟩
  invFun x := ⟨x.val, by
    apply (planeSetEquiv centre ell hb E houtside).injective
    rw [planeSetEquiv_projectionIndex]
    exact x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem planeRay_card (i : planeProjectionSet centre ell hb E houtside) :
    Fintype.card (PlaneRayIndex centre ell hb E houtside i) =
      ProjectiveProjection.raySize K σ E centre houtside
        ((indexEquiv E houtside (chart centre ell hb)).symm
          (planeSetEquiv centre ell hb E houtside i)) := by
  rw [Fintype.card_congr (planeRayEquiv centre ell hb E houtside i)]
  let j := (indexEquiv E houtside (chart centre ell hb)).symm
    (planeSetEquiv centre ell hb E houtside i)
  have h := ProjectionTransport.raySize_eq E houtside (chart centre ell hb) j
  simpa [j, ProjectionTransport.raySize] using h
theorem actual_unique_intersection (P : Point K σ) (hP : P ≠ centre) (Q : Point K σ) :
    Q.submodule ≤ joiningLine centre P ∧ Q.submodule ≤ LinearMap.ker ell ↔
      Q = Projectivization.map (LinearMap.ker ell).subtype (LinearMap.ker ell).subtype_injective
        (projectToPlane centre ell hb P hP) := by
  rw [projectToPlane_original]
  exact intersection_unique centre P ell hb hP Q

/-- A single interface starting with an arbitrary given hyperplane and an
arbitrary prescribed coordinate chart.  The points returned live in the
original hyperplane itself, and are the unique intersections of the original
projective lines with that hyperplane. The exact point set and every fibre
are transported to the prescribed chart. -/
theorem exists_actual_model [Fintype σ]
    (H : Submodule K (Space K σ))
    (hH : Module.finrank K H + 1 = Fintype.card (Option σ))
    (hcentre : centre.rep ∉ H) (C : Chart centre) :
    ∃ ell : Module.Dual K (Space K σ), ∃ hell : ell centre.rep ≠ 0,
      LinearMap.ker ell = H ∧
      ∃ project : ∀ P : Point K σ, P ≠ centre → Projectivization K H,
      ∃ A : H ≃ₗ[K] (σ → K),
      ∃ e : Projectivization K H ≃ Direction K σ,
        (∀ P, e P = Projectivization.map A.toLinearMap A.injective P) ∧
        (∀ (P : Point K σ) (hP : P ≠ centre) (Q : Point K σ),
          Q.submodule ≤ joiningLine centre P ∧ Q.submodule ≤ H ↔
            Q = Projectivization.map H.subtype H.subtype_injective (project P hP)) ∧
        (∀ (P : Point K σ) (hP : P ≠ centre),
          e (project P hP) = ProjectionTransport.projectPoint C P hP) ∧
        (Finset.univ.image (fun x : E => project x.val
          (fun h => houtside (h ▸ x.property)))).image e =
            ProjectionTransport.directionSet E houtside C ∧
        ∀ i : Projectivization K H,
          (E.attach.filter (fun x => project x.val
            (fun h => houtside (h ▸ x.property)) = i)).card =
          (E.attach.filter (fun x => ProjectionTransport.projectPoint C x.val
            (fun h => houtside (h ▸ x.property)) = e i)).card := by
  obtain ⟨ell, hell, heq⟩ := exists_equation centre H hH hcentre
  subst H
  refine ⟨ell, hell, rfl, projectToPlane centre ell hell,
    planeLinearEquivForChart centre ell hell C,
    planeEquivForChart centre ell hell C, ?_, ?_, ?_, ?_, ?_⟩
  · exact planeEquivForChart_map centre ell hell C
  · exact actual_unique_intersection centre ell hell
  · exact planeEquivForChart_projectToPlane centre ell hell C
  · rw [ProjectionTransport.directionSet_actual, Finset.image_image]
    congr 1
    funext x
    exact planeEquivForChart_projectToPlane centre ell hell C x.val _
  · intro i
    congr 1
    apply Finset.filter_congr
    intro x _
    rw [← planeEquivForChart_projectToPlane centre ell hell C x.val]
    exact (planeEquivForChart centre ell hell C).injective.eq_iff.symm

#print axioms planeSetEquiv_projectionIndex
#print axioms planeRay_card
#print axioms actual_unique_intersection
#print axioms planeEquivForChart_map
#print axioms planeEquivForChart_projectToPlane
#print axioms exists_actual_model

end Cylinder.ArbitraryProjectionModel
end

