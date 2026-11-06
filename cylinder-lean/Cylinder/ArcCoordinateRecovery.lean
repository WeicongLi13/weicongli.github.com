module

public import Cylinder.ArcSecantRecovery
public import Cylinder.BMMLinearCoordinates

/-! A true coordinate equation x = a y recovers its unordered pair
of points of an actual projective arc, also after a field embedding. -/

@[expose] public section
noncomputable section
open scoped Classical BigOperators

namespace Cylinder.ArcCoordinateRecovery

open Cylinder.RationalPlaneLine Cylinder.PlaneCrossProduct Cylinder.BMMArcGeometry
open Cylinder.ProjectiveFieldEmbedding Cylinder.BMMLinearCoordinates Cylinder.ConicRootPairsAlgebra

variable {R K : Type*} [Field R] [Field K]

theorem raw_transformed_rep_nonzero (f : R →+* K) (g : (Fin 3 → K) ≃ₗ[K] (Fin 3 → K))
    (P : PlanePoint R) : g (vectorMap f P.rep) ≠ 0 := by
  intro hz
  apply P.rep_nonzero
  apply vectorMap_injective f
  apply g.injective
  simpa only [map_zero] using hz

theorem diagonal_collinear (f : R →+* K) (g : (Fin 3 → K) ≃ₗ[K] (Fin 3 → K))
    (a : K) (P Q T : PlanePoint R) (hPQ : P ≠ Q)
    (hP : g (vectorMap f P.rep) 0 = a * g (vectorMap f P.rep) 1)
    (hQ : g (vectorMap f Q.rep) 0 = a * g (vectorMap f Q.rep) 1)
    (hT : g (vectorMap f T.rep) 0 = a * g (vectorMap f T.rep) 1) : Collinear P Q T := by
  have hz : dot (cross (g (vectorMap f P.rep)) (g (vectorMap f Q.rep)))
      (g (vectorMap f T.rep)) = 0 := by
    simp [dot, cross, Fin.sum_univ_succ, hP, hQ, hT]
    ring
  have heq (U : PlanePoint R) : transformedPoint f g U =
      Projectivization.mk K (g (vectorMap f U.rep)) (raw_transformed_rep_nonzero f g U) :=
    transformedPoint_eq_mk f g U _ (raw_transformed_rep_nonzero f g U) 1 one_ne_zero
      (by rw [one_smul])
  apply (transformedPoint_collinear_iff f g P Q T hPQ).mp
  rw [heq, heq, heq]
  exact collinear_mk_of_triple_zero _ _ _ _ _ _ hz

def diagonalSlice (W : Finset (PlanePoint R)) (f : R →+* K)
    (g : (Fin 3 → K) ≃ₗ[K] (Fin 3 → K)) (a : K) : Finset (PlanePoint R) :=
  W.filter (fun P => g (vectorMap f P.rep) 0 = a * g (vectorMap f P.rep) 1)

theorem diagonal_slice_eq_pair (W : Finset (PlanePoint R)) (hW : LineCap W 2)
    (f : R →+* K) (g : (Fin 3 → K) ≃ₗ[K] (Fin 3 → K)) (a : K)
    (P Q : PlanePoint R) (hP : P ∈ W) (hQ : Q ∈ W) (hPQ : P ≠ Q)
    (hPc : g (vectorMap f P.rep) 0 = a * g (vectorMap f P.rep) 1)
    (hQc : g (vectorMap f Q.rep) 0 = a * g (vectorMap f Q.rep) 1) :
    diagonalSlice W f g a = {P, Q} := by
  let l := cross P.rep Q.rep
  have hl : l ≠ 0 := cross_ne_zero P.rep Q.rep P.rep_nonzero (representatives_not_proportional P Q hPQ)
  have hsub : diagonalSlice W f g a ⊆ W.filter (fun U => dot l U.rep = 0) := by
    intro U hU
    obtain ⟨hUW, hUc⟩ := Finset.mem_filter.mp hU
    exact Finset.mem_filter.mpr ⟨hUW, diagonal_collinear f g a P Q U hPQ hPc hQc hUc⟩
  have hsubpair : ({P, Q} : Finset (PlanePoint R)) ⊆ diagonalSlice W f g a := by
    intro U hU
    rcases Finset.mem_insert.mp hU with rfl | hU
    · exact Finset.mem_filter.mpr ⟨hP, hPc⟩
    have hUQ := Finset.mem_singleton.mp hU
    subst U
    exact Finset.mem_filter.mpr ⟨hQ, hQc⟩
  apply (Finset.eq_of_subset_of_card_le hsubpair ?_).symm
  rw [Finset.card_pair hPQ]
  exact (Finset.card_le_card hsub).trans (hW l hl)

theorem diagonal_pairs_equal (W : Finset (PlanePoint R)) (hW : LineCap W 2)
    (f : R →+* K) (g : (Fin 3 → K) ≃ₗ[K] (Fin 3 → K)) (a : K)
    (P Q U V : PlanePoint R) (hP : P ∈ W) (hQ : Q ∈ W) (hU : U ∈ W) (hV : V ∈ W)
    (hPQ : P ≠ Q) (hUV : U ≠ V)
    (hPc : g (vectorMap f P.rep) 0 = a * g (vectorMap f P.rep) 1)
    (hQc : g (vectorMap f Q.rep) 0 = a * g (vectorMap f Q.rep) 1)
    (hUc : g (vectorMap f U.rep) 0 = a * g (vectorMap f U.rep) 1)
    (hVc : g (vectorMap f V.rep) 0 = a * g (vectorMap f V.rep) 1) :
    ({P, Q} : Finset (PlanePoint R)) = {U, V} :=
  (diagonal_slice_eq_pair W hW f g a P Q hP hQ hPQ hPc hQc).symm.trans
    (diagonal_slice_eq_pair W hW f g a U V hU hV hUV hUc hVc)

end Cylinder.ArcCoordinateRecovery

end
