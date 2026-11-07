module
public import Cylinder.ProjectionTransport
public import Mathlib.LinearAlgebra.Matrix.ToLin
@[expose] public section
noncomputable section
open scoped Classical
namespace Cylinder.ProjectionTransportScalarExtension
open ProjectionTransport
variable {K L σ I : Type*} [Field K] [Field L] [Fintype σ]

def scalarMap (f : K →+* L) (A : (σ → K) →ₗ[K] (σ → K)) :
    (σ → L) →ₗ[L] (σ → L) :=
  Matrix.toLin' (f.mapMatrix (LinearMap.toMatrix' A))

theorem scalarMap_comp (f : K →+* L) (A B : (σ → K) →ₗ[K] (σ → K)) :
    scalarMap f (A.comp B) = (scalarMap f A).comp (scalarMap f B) := by
  simp only [scalarMap, LinearMap.toMatrix'_comp, map_mul, Matrix.toLin'_mul]

@[simp] theorem scalarMap_id (f : K →+* L) : scalarMap f (LinearMap.id : (σ → K) →ₗ[K] _) = LinearMap.id := by
  simp [scalarMap]

def scalarExtensionEquiv (f : K →+* L) (A : (σ → K) ≃ₗ[K] (σ → K)) :
    (σ → L) ≃ₗ[L] (σ → L) where
  toLinearMap := scalarMap f A.toLinearMap
  invFun := scalarMap f A.symm.toLinearMap
  left_inv x := by
    change ((scalarMap f A.symm.toLinearMap).comp (scalarMap f A.toLinearMap)) x = x
    rw [← scalarMap_comp]
    have he : A.symm.toLinearMap.comp A.toLinearMap = LinearMap.id := by ext y; simp
    rw [he, scalarMap_id, LinearMap.id_apply]
  right_inv x := by
    change ((scalarMap f A.toLinearMap).comp (scalarMap f A.symm.toLinearMap)) x = x
    rw [← scalarMap_comp]
    have he : A.toLinearMap.comp A.symm.toLinearMap = LinearMap.id := by ext y; simp
    rw [he, scalarMap_id, LinearMap.id_apply]

theorem scalarExtensionEquiv_apply (f : K →+* L) (A : (σ → K) ≃ₗ[K] (σ → K)) (x : σ → K) :
    scalarExtensionEquiv f A (fun s => f (x s)) = fun s => f (A x s) := by
  change Matrix.toLin' (f.mapMatrix (LinearMap.toMatrix' A.toLinearMap)) (fun s => f (x s)) = _
  ext s
  rw [Matrix.toLin'_apply, RingHom.mapMatrix_apply]
  simpa only [Function.comp_def, LinearMap.toMatrix'_mulVec, LinearEquiv.coe_coe] using
    (RingHom.map_mulVec f (LinearMap.toMatrix' A.toLinearMap) x s).symm

theorem mapped_smul (f : K →+* L) (u : K) (x : σ → K) :
    (fun s => f ((u • x) s)) = f u • (fun s => f (x s)) := by
  ext s
  simp [Pi.smul_apply, smul_eq_mul]

theorem independent_mapped_linearEquiv_rescaling (f : K →+* L)
    (A : (σ → K) ≃ₗ[K] (σ → K)) (v : I → σ → K)
    (u : I → K) (hu : ∀ i, u i ≠ 0) (d : ℕ) :
    EvaluationProjection.Independent (fun i s => f ((u i • A (v i)) s)) d ↔
      EvaluationProjection.Independent (fun i s => f (v i s)) d := by
  have hv : (fun i s => f ((u i • A (v i)) s)) =
      (fun i => f (u i) • scalarExtensionEquiv f A (fun s => f (v i s))) := by
    funext i
    rw [scalarExtensionEquiv_apply]
    exact mapped_smul f (u i) (A (v i))
  rw [hv]
  exact (independent_rescaling _ _ (fun i => (map_ne_zero f).mpr (hu i)) d).trans
    (independent_linearEquiv (scalarExtensionEquiv f A) _ d)

end Cylinder.ProjectionTransportScalarExtension
end


