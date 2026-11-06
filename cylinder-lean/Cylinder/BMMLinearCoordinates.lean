module

public import Cylinder.ConicRootPairsAlgebra
public import Cylinder.LineAffineCoordinates

/-! Actual projective points under an invertible linear coordinate change,
with collinearity in both directions and no coordinate-change hypothesis. -/

@[expose] public section
noncomputable section
open scoped Classical

namespace Cylinder.BMMLinearCoordinates

open Cylinder.RationalPlaneLine Cylinder.BMMArcGeometry Cylinder.BMMFieldExtension
open Cylinder.PlaneCrossProduct Cylinder.ProjectiveFieldEmbedding
open Cylinder.ConicRootPairsAlgebra Cylinder.LineAffineCoordinates

variable {R K : Type*} [Field R] [Field K]

def linearPointMap (g : (Fin 3 → K) ≃ₗ[K] (Fin 3 → K)) : PlanePoint K → PlanePoint K :=
  Projectivization.map g.toLinearMap g.injective

theorem linearPointMap_mk (g : (Fin 3 → K) ≃ₗ[K] (Fin 3 → K))
    (v : Fin 3 → K) (hv : v ≠ 0) :
    linearPointMap g (Projectivization.mk K v hv) =
      Projectivization.mk K (g v) (by intro h; exact hv (g.injective (h.trans (map_zero g).symm))) :=
  Projectivization.map_mk _ _ _ _

theorem linearPointMap_rep (g : (Fin 3 → K) ≃ₗ[K] (Fin 3 → K)) (P : PlanePoint K) :
    linearPointMap g P = Projectivization.mk K (g P.rep)
      (by intro h; exact P.rep_nonzero (g.injective (h.trans (map_zero g).symm))) := by
  simpa only [Projectivization.mk_rep] using linearPointMap_mk g P.rep P.rep_nonzero

theorem linearPointMap_injective (g : (Fin 3 → K) ≃ₗ[K] (Fin 3 → K)) :
    Function.Injective (linearPointMap g) := Projectivization.map_injective g.toLinearMap g.injective

theorem linearPointMap_inverse (g : (Fin 3 → K) ≃ₗ[K] (Fin 3 → K)) (P : PlanePoint K) :
    linearPointMap g.symm (linearPointMap g P) = P := by
  rw [linearPointMap_rep g P, linearPointMap_mk]
  simp only [LinearEquiv.symm_apply_apply, Projectivization.mk_rep]

theorem linearPointMap_collinear (g : (Fin 3 → K) ≃ₗ[K] (Fin 3 → K))
    (P Q R : PlanePoint K) (hPQ : P ≠ Q) (hcol : Collinear P Q R) :
    Collinear (linearPointMap g P) (linearPointMap g Q) (linearPointMap g R) := by
  rw [linearPointMap_rep, linearPointMap_rep, linearPointMap_rep]
  exact collinear_mk_of_triple_zero _ _ _ _ _ _ (collinear_after_linearEquiv g P Q R hPQ hcol)

theorem linearPointMap_collinear_iff (g : (Fin 3 → K) ≃ₗ[K] (Fin 3 → K))
    (P Q R : PlanePoint K) (hPQ : P ≠ Q) :
    Collinear (linearPointMap g P) (linearPointMap g Q) (linearPointMap g R) ↔ Collinear P Q R := by
  constructor
  · intro h
    have hPQ' := fun heq => hPQ (linearPointMap_injective g heq)
    have hh := linearPointMap_collinear g.symm _ _ _ hPQ' h
    simpa only [linearPointMap_inverse] using hh
  · exact linearPointMap_collinear g P Q R hPQ

def transformedPoint (f : R →+* K) (g : (Fin 3 → K) ≃ₗ[K] (Fin 3 → K))
    (P : PlanePoint R) : PlanePoint K := linearPointMap g (pointMap f P)

theorem transformedPoint_injective (f : R →+* K) (g : (Fin 3 → K) ≃ₗ[K] (Fin 3 → K)) :
    Function.Injective (transformedPoint f g) := (linearPointMap_injective g).comp (pointMap_injective f)

theorem transformedPoint_collinear_iff (f : R →+* K) (g : (Fin 3 → K) ≃ₗ[K] (Fin 3 → K))
    (P Q R : PlanePoint R) (hPQ : P ≠ Q) :
    Collinear (transformedPoint f g P) (transformedPoint f g Q) (transformedPoint f g R) ↔
      Collinear P Q R := by
  rw [transformedPoint, transformedPoint, transformedPoint,
    linearPointMap_collinear_iff g _ _ _ (fun heq => hPQ (pointMap_injective f heq)),
    pointMap_collinear_iff]

theorem transformedPoint_eq_mk (f : R →+* K) (g : (Fin 3 → K) ≃ₗ[K] (Fin 3 → K))
    (P : PlanePoint R) (v : Fin 3 → K) (hv : v ≠ 0) (a : K) (_ha : a ≠ 0)
    (h : g (vectorMap f P.rep) = a • v) :
    transformedPoint f g P = Projectivization.mk K v hv := by
  have hmap : pointMap f P = Projectivization.mk K (vectorMap f P.rep)
      (by intro hz; exact P.rep_nonzero (vectorMap_injective f (hz.trans (map_zero (vectorMap f)).symm))) := by
    simpa only [Projectivization.mk_rep] using pointMap_mk f P.rep P.rep_nonzero
  rw [transformedPoint, hmap, linearPointMap_mk]
  apply (Projectivization.mk_eq_mk_iff' K _ _ _ _).mpr
  exact ⟨a, h.symm⟩

theorem transformedPoint_eq_of_representative (f : R →+* K)
    (g : (Fin 3 → K) ≃ₗ[K] (Fin 3 → K)) (P : PlanePoint R) (z : Fin 3 → R)
    (a : R) (ha : a ≠ 0) (hz : z = a • P.rep)
    (v : Fin 3 → K) (hv : v ≠ 0) (c : K) (hc : c ≠ 0)
    (hg : g (vectorMap f z) = c • v) :
    transformedPoint f g P = Projectivization.mk K v hv := by
  have hfa : f a ≠ 0 := fun h => ha (f.injective (h.trans (map_zero f).symm))
  have hscaled : f a • g (vectorMap f P.rep) = c • v := by
    simpa only [hz, map_smulₛₗ, map_smul, RingHom.id_apply] using hg
  apply transformedPoint_eq_mk f g P v hv (c / f a) (div_ne_zero hc hfa)
  calc
    g (vectorMap f P.rep) = (f a)⁻¹ • (f a • g (vectorMap f P.rep)) := by
      rw [smul_smul, inv_mul_cancel₀ hfa, one_smul]
    _ = (f a)⁻¹ • (c • v) := congrArg (fun w : Fin 3 → K => (f a)⁻¹ • w) hscaled
    _ = (c / f a) • v := by rw [smul_smul]; simp only [div_eq_mul_inv, mul_comm]

end Cylinder.BMMLinearCoordinates

end
