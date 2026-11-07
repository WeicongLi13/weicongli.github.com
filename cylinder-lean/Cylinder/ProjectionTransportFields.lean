module
public import Cylinder.ProjectionTransportScalarExtension
public import Cylinder.ProjectionTransportGeometry
@[expose] public section
noncomputable section
open scoped Classical LinearAlgebra.Projectivization
namespace Cylinder.ProjectionTransportFields
open ProjectionTransport ProjectionTransportScalarExtension ProjectionTransportGeometry
open ProjectiveProjection ProjectionChart PlaneBinaryReduction LinearEvaluationTransport
variable {K L I : Type*} [Field K] [Field L]

theorem initialDegree_mapped_linearEquiv_rescaling [Fintype I] [Infinite L]
    (f : K →+* L) (A : (Fin 3 → K) ≃ₗ[K] (Fin 3 → K)) (v : I → Fin 3 → K)
    (u : I → K) (hu : ∀ i, u i ≠ 0) (s : ℕ) :
    InitialDegree (fun i j => f ((u i • A (v i)) j)) s ↔
      InitialDegree (fun i j => f (v i j)) s := by
  have hv : (fun i j => f ((u i • A (v i)) j)) =
      (fun i => f (u i) • scalarExtensionEquiv f A (fun j => f (v i j))) := by
    funext i
    rw [scalarExtensionEquiv_apply]
    exact mapped_smul f (u i) (A (v i))
  rw [hv]
  exact initialDegree_linearEquiv_rescaling (scalarExtensionEquiv f A) _ _
    (fun i => (map_ne_zero f).mpr (hu i)) s

variable {centre : Point K (Fin 3)}
    (E : Finset (Point K (Fin 3))) (houtside : centre ∉ E)

theorem initialDegree_mapped_directionSet [Infinite L] (f : K →+* L) (C : Chart centre) (s : ℕ) :
    InitialDegree (fun i : ProjectionTransport.directionSet E houtside C => fun j => f (i.val.rep j)) s ↔
      InitialDegree (fun i : ProjectiveProjection.directionSet K (Fin 3) E centre houtside =>
        fun j => f (i.val.rep j)) s := by
  let e := indexEquiv E houtside C
  have h := (LocalPointReindexing.initialDegree_reindex e.symm
    (fun i : ProjectionTransport.directionSet E houtside C => fun j => f (i.val.rep j)) s).symm
  simp only [Equiv.symm_symm] at h
  rw [h]
  simp only [e, representativeScale_spec]
  exact initialDegree_mapped_linearEquiv_rescaling f C.directionEquiv _ _
    (fun i => (representativeScale E houtside C i).ne_zero) s

theorem full_support_mapped_directionSet (f : K →+* L) (C : Chart centre) (d : ℕ)
    (hrel : ∃ c : ProjectiveProjection.directionSet K (Fin 3) E centre houtside → L,
      (∀ i, c i ≠ 0) ∧ PowerEvaluationRelation.Relation
        (fun i : ProjectiveProjection.directionSet K (Fin 3) E centre houtside => fun j => f (i.val.rep j)) c d) :
    ∃ c : ProjectionTransport.directionSet E houtside C → L,
      (∀ i, c i ≠ 0) ∧ PowerEvaluationRelation.Relation
        (fun i : ProjectionTransport.directionSet E houtside C => fun j => f (i.val.rep j)) c d := by
  obtain ⟨c, hc, hr⟩ := hrel
  let e := indexEquiv E houtside C
  let u := fun i => f (representativeScale E houtside C i : K)
  have hu : ∀ i, u i ≠ 0 := fun i => (map_ne_zero f).mpr (representativeScale E houtside C i).ne_zero
  have hlin := relation_after_linearEquiv _ c d (scalarExtensionEquiv f C.directionEquiv) hr
  have hscale := relation_after_rescaling _ c u hu d hlin
  have hreindex := LocalPointReindexing.relation_reindex e _ _ d hscale
  refine ⟨fun j => c (e.symm j) / u (e.symm j) ^ d,
    fun j => div_ne_zero (hc _) (pow_ne_zero d (hu _)), ?_⟩
  have hv : (fun j : ProjectionTransport.directionSet E houtside C =>
      u (e.symm j) • scalarExtensionEquiv f C.directionEquiv
        (fun k => f ((e.symm j).val.rep k))) =
      (fun j : ProjectionTransport.directionSet E houtside C => fun k => f (j.val.rep k)) := by
    funext j
    rw [scalarExtensionEquiv_apply, ← mapped_smul]
    have hs := representativeScale_spec E houtside C (e.symm j)
    have he : indexEquiv E houtside C (e.symm j) = j := e.apply_symm_apply j
    rw [he] at hs
    rw [hs]
  rw [hv] at hreindex
  exact hreindex

#print axioms initialDegree_mapped_directionSet
#print axioms full_support_mapped_directionSet
end Cylinder.ProjectionTransportFields
end


