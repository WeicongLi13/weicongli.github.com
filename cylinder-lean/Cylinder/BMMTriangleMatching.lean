module

public import Cylinder.BMMTriangleProducts

/-! Restricting the actual white-to-black blocker bijection at a triangle
vertex gives the precise complement matching. Collinearity preserves each
coordinate ratio, so the finite products agree without a product hypothesis. -/

@[expose] public section
noncomputable section
open scoped Classical BigOperators

namespace Cylinder.BMMTriangleMatching

open Cylinder.BMMTriangleProducts Cylinder.BMMTriangleBlockers Cylinder.BMMFrameRatios
open Cylinder.BMMBlockerPairs Cylinder.BMMArcGeometry

variable {K : Type*} [Field K]

theorem vertex_side_next (T : Triangle K) (i : Fin 3) :
    secantBlocker T.W T.B T.arc T.disjoint T.blocks T.card (T.P i) (T.P (previous i))
      (fun h => previous_ne i ((T.injective h).symm)) = sideBlocker T (next i) := by
  simpa only [sideBlocker, next_next, previous_next] using
    secantBlocker_symm T.W T.B T.arc T.disjoint T.blocks T.card (T.P i) (T.P (previous i))
      (fun h => previous_ne i ((T.injective h).symm))

theorem vertex_side_previous (T : Triangle K) (i : Fin 3) :
    secantBlocker T.W T.B T.arc T.disjoint T.blocks T.card (T.P i) (T.P (next i))
      (fun h => next_ne i ((T.injective h).symm)) = sideBlocker T (previous i) := by
  simp only [sideBlocker, next_previous, previous_previous]

def matchAt (T : Triangle K) (i : Fin 3) (R : T.W) (hR : R ∈ offTriangleWhites T) : T.B :=
  secantBlocker T.W T.B T.arc T.disjoint T.blocks T.card (T.P i) R
    ((Finset.mem_filter.mp hR).2 i).symm

theorem matchAt_collinear (T : Triangle K) (i : Fin 3) (R : T.W)
    (hR : R ∈ offTriangleWhites T) :
    Collinear (T.P i).val R.val (matchAt T i R hR).val :=
  secantBlocker_collinear T.W T.B T.arc T.disjoint T.blocks T.card (T.P i) R _

theorem matchAt_mem_complement (T : Triangle K) (i : Fin 3) (R : T.W)
    (hR : R ∈ offTriangleWhites T) : matchAt T i R hR ∈ blackComplementAt T i := by
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_, ?_⟩
  · rw [← vertex_side_next]
    exact secantBlocker_ne_at T.W T.B T.arc T.disjoint T.blocks T.card (T.P i) R (T.P (previous i))
      ((Finset.mem_filter.mp hR).2 i).symm
      (fun h => previous_ne i ((T.injective h).symm)) ((Finset.mem_filter.mp hR).2 (previous i))
  · rw [← vertex_side_previous]
    exact secantBlocker_ne_at T.W T.B T.arc T.disjoint T.blocks T.card (T.P i) R (T.P (next i))
      ((Finset.mem_filter.mp hR).2 i).symm
      (fun h => next_ne i ((T.injective h).symm)) ((Finset.mem_filter.mp hR).2 (next i))

theorem matchAt_injective (T : Triangle K) (i : Fin 3) (R Q : T.W)
    (hR : R ∈ offTriangleWhites T) (hQ : Q ∈ offTriangleWhites T)
    (h : matchAt T i R hR = matchAt T i Q hQ) : R = Q :=
  secantBlocker_injective_at T.W T.B T.arc T.disjoint T.blocks T.card (T.P i) R Q _ _ h

theorem matchAt_surjective (T : Triangle K) (i : Fin 3) (R : T.B)
    (hR : R ∈ blackComplementAt T i) :
    ∃ Q : T.W, ∃ hQ : Q ∈ offTriangleWhites T, matchAt T i Q hQ = R := by
  obtain ⟨Q, hQ, _hunique⟩ := exists_unique_partner T.W T.B T.arc T.disjoint T.blocks T.card
    (T.P i).val (T.P i).property R
  have hPiQ : T.P i ≠ Q := fun h => hQ.1 (congrArg Subtype.val h.symm)
  have hsec : secantBlocker T.W T.B T.arc T.disjoint T.blocks T.card (T.P i) Q hPiQ = R :=
    secantBlocker_unique T.W T.B T.arc T.disjoint T.blocks T.card (T.P i) Q hPiQ R hQ.2
  have hoff : Q ∈ offTriangleWhites T := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, fun j => ?_⟩
    rcases index_trichotomy i j with hji | hji | hji
    · subst j; exact hPiQ.symm
    · subst j
      intro hQP
      have hside : R = sideBlocker T (previous i) := by
        rw [← hsec]
        simpa only [hQP] using vertex_side_previous T i
      exact (Finset.mem_filter.mp hR).2.2 hside
    · subst j
      intro hQP
      have hside : R = sideBlocker T (next i) := by
        rw [← hsec]
        simpa only [hQP] using vertex_side_next T i
      exact (Finset.mem_filter.mp hR).2.1 hside
  exact ⟨Q, hoff, hsec⟩

theorem black_complement_coordinates_nonzero (T : Triangle K) (i : Fin 3) (R : T.B)
    (hR : R ∈ blackComplementAt T i) :
    blackCoordinates T R (next i) ≠ 0 ∧ blackCoordinates T R (previous i) ≠ 0 := by
  constructor
  · intro hzero
    exact (Finset.mem_filter.mp hR).2.1 ((black_zero_coordinate_iff_side T R (next i)).mp hzero)
  · intro hzero
    exact (Finset.mem_filter.mp hR).2.2 ((black_zero_coordinate_iff_side T R (previous i)).mp hzero)

theorem matchAt_ratio (T : Triangle K) (i : Fin 3) (R : T.W)
    (hR : R ∈ offTriangleWhites T) : whiteRatio T R i = blackRatio T (matchAt T i R hR) i := by
  exact collinear_anchor_ratio (vectors T) (determinant_ne_zero T) R.val.rep (matchAt T i R hR).val.rep i
    (matchAt_collinear T i R hR) (offTriangle_white_coordinates_nonzero T R hR (previous i))
    (black_complement_coordinates_nonzero T i _ (matchAt_mem_complement T i R hR)).2

theorem white_product_eq_black_complement (T : Triangle K) (i : Fin 3) :
    whiteProduct T i = ∏ R ∈ blackComplementAt T i, blackRatio T R i := by
  apply Finset.prod_bij (matchAt T i) (matchAt_mem_complement T i)
    (fun R hR Q hQ => matchAt_injective T i R Q hR hQ)
    (matchAt_surjective T i)
  exact fun R hR => matchAt_ratio T i R hR

theorem white_product_eq_side_mul_black (T : Triangle K) (i : Fin 3) :
    whiteProduct T i = blackRatio T (sideBlocker T i) i * blackProduct T i := by
  rw [white_product_eq_black_complement, black_complement_ratio_product]

theorem side_ratio_cycle (T : Triangle K) : (∏ i : Fin 3, blackRatio T (sideBlocker T i) i) = 1 := by
  have hprod := Finset.prod_congr rfl
    (fun i (_ : i ∈ (Finset.univ : Finset (Fin 3))) => white_product_eq_side_mul_black T i)
  rw [Finset.prod_mul_distrib, white_product_cycle, black_product_cycle, mul_one] at hprod
  exact hprod.symm

end Cylinder.BMMTriangleMatching

end
