module

public import Cylinder.PlateauPolynomial
public import Cylinder.ActualIdealCharacter

/-!
# Actual reduced point ideals and a common curve factor

The complement is the actual subtype of points where the curve does not
vanish. Multiplication by the curve identifies its vanishing equations with
the original low-degree equations whenever the proved common factor applies.
-/

@[expose] public section
noncomputable section
open scoped Classical
namespace Cylinder.ReducedGapIdeal
open MvPolynomial Module
open Cylinder.HilbertEvaluation Cylinder.PlaneNumericalCharacter
open Cylinder.PlaneBinaryReduction Cylinder.SaturatedPlaneLine
open Cylinder.PlaneIdealRestriction Cylinder.HomogeneousFactors
variable {K I : Type*} [Field K] [Fintype I]
local instance : GradedAlgebra (Forms K) := MvPolynomial.gradedAlgebra

theorem linear_mem_irrelevant (L : PlaneRing K) (hL : L.IsHomogeneous 1) :
    L ∈ irrelevant (K := K) := by
  have hle : Forms K 1 ≤ (irrelevant (K := K)).restrictScalars K := by
    rw [Forms, homogeneousSubmodule_one_eq_span_X]
    apply Submodule.span_le.mpr
    rintro P ⟨i, rfl⟩
    exact Ideal.subset_span ⟨i, rfl⟩
  exact hle hL

theorem vanishingIdeal_saturated [Infinite K] (v : I → Fin 3 → K)
    (hv : ∀ i, v i ≠ 0) : Saturated (vanishingIdeal v).toIdeal := by
  obtain ⟨L, hL, hLv, hcolon⟩ := exists_avoiding_colon v hv
  intro P n hP
  have hLP := hP (L ^ n) (Ideal.pow_mem_pow (linear_mem_irrelevant L hL) n)
  have hcancel : ∀ m, L ^ m * P ∈ (vanishingIdeal v).toIdeal → P ∈ (vanishingIdeal v).toIdeal := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      intro hm
      apply ih
      have hmem : L ^ m * P ∈ (vanishingIdeal v).toIdeal.colon {L} := by
        rw [Submodule.mem_colon_singleton, smul_eq_mul]
        simpa only [pow_succ, mul_assoc, mul_comm L, mul_left_comm L] using hm
      rwa [hcolon] at hmem
  exact hcancel n hLP

omit [Fintype I] in
theorem piece_finrank (v : I → Fin 3 → K) (d : ℕ) :
    finrank K (Cylinder.PlanePlateau.piece (vanishingIdeal v).toIdeal d) =
      finrank K (idealPiece v d) :=
  (idealForms_finrank (vanishingIdeal v).toIdeal d).symm

omit [Fintype I] in
theorem quotientHilbert_eq_hilbert (v : I → Fin 3 → K) (d : ℕ) :
    Cylinder.PlanePlateau.quotientHilbert (vanishingIdeal v).toIdeal d = hilbert v d := by
  have hq := Cylinder.PlanePlateau.quotient_dimension (vanishingIdeal v).toIdeal d
  have he := ideal_piece_dimension v d
  rw [← idealPiece_eq_kernel] at he
  rw [piece_finrank] at hq
  omega

omit [Fintype I] in
theorem initialDegree_ideal (v : I → Fin 3 → K) (s : ℕ) (hs : InitialDegree v s) :
    Cylinder.PlanePlateau.InitialDegree (vanishingIdeal v).toIdeal s := by
  constructor
  · intro hbot
    have hr := piece_finrank v s
    rw [hbot, finrank_bot] at hr
    exact hs.1 (Submodule.finrank_eq_zero.mp hr.symm)
  · intro d hd
    apply Submodule.finrank_eq_zero.mp
    rw [piece_finrank, hs.2 d hd, finrank_bot]

def Outside (v : I → Fin 3 → K) (G : PlaneRing K) := {i : I // eval (v i) G ≠ 0}

instance outside_fintype (v : I → Fin 3 → K) (G : PlaneRing K) : Fintype (Outside v G) := by
  unfold Outside
  infer_instance

def outsideRepresentatives (v : I → Fin 3 → K) (G : PlaneRing K) : Outside v G → Fin 3 → K :=
  fun i => v i.val

omit [Fintype I] in
theorem outside_nonzero (v : I → Fin 3 → K) (hv : ∀ i, v i ≠ 0) (G : PlaneRing K) :
    ∀ i, outsideRepresentatives v G i ≠ 0 := fun i => hv i.val

omit [Fintype I] in
theorem outside_distinct (v : I → Fin 3 → K) (hsep : ProjectivelyDistinct v) (G : PlaneRing K) :
    ProjectivelyDistinct (outsideRepresentatives v G) := by
  intro i j hij c
  exact hsep i.val j.val (fun h => hij (Subtype.ext h)) c

omit [Fintype I] in
theorem homogeneous_product_vanishing_iff (v : I → Fin 3 → K)
    (G Q : PlaneRing K) (j t : ℕ) (hG : G.IsHomogeneous j) (hQ : Q.IsHomogeneous t) :
    G * Q ∈ (vanishingIdeal v).toIdeal ↔
      Q ∈ (vanishingIdeal (outsideRepresentatives v G)).toIdeal := by
  rw [homogeneous_mem_vanishingIdeal v (G * Q) (j + t) (hG.mul hQ),
    homogeneous_mem_vanishingIdeal (outsideRepresentatives v G) Q t hQ]
  constructor
  · intro h i
    have hi := h i.val
    rw [map_mul] at hi
    exact (mul_eq_zero.mp hi).resolve_left i.property
  · intro h i
    rw [map_mul]
    by_cases hi : eval (v i) G = 0
    · rw [hi, zero_mul]
    · exact mul_eq_zero.mpr (Or.inr (h ⟨i, hi⟩))

def factorMultiplication (v : I → Fin 3 → K) (G : PlaneRing K) (j t : ℕ)
    (hG : G.IsHomogeneous j) :
    idealPiece (outsideRepresentatives v G) t →ₗ[K] idealPiece v (t + j) :=
  LinearMap.codRestrict (idealPiece v (t + j))
    ((LinearMap.codRestrict (Forms K (t + j))
      ((LinearMap.mul K (PlaneRing K) G).comp (Forms K t).subtype)
      (fun P => by change (G * P.val).IsHomogeneous (t + j); simpa only [add_comm j t] using hG.mul P.property)).comp
      (idealPiece (outsideRepresentatives v G) t).subtype)
    (fun P => (homogeneous_product_vanishing_iff v G P.val.val j t hG P.val.property).mpr P.property)

omit [Fintype I] in
theorem factorMultiplication_injective (v : I → Fin 3 → K) (G : PlaneRing K) (j t : ℕ)
    (hG : G.IsHomogeneous j) (hG0 : G ≠ 0) : Function.Injective (factorMultiplication v G j t hG) := by
  intro P Q h
  apply Subtype.ext
  apply Subtype.ext
  exact mul_left_cancel₀ hG0 (congrArg (fun R => R.val.val) h)

omit [Fintype I] in
theorem factorMultiplication_surjective (v : I → Fin 3 → K) (G : PlaneRing K) (j t : ℕ)
    (hG : G.IsHomogeneous j) (hG0 : G ≠ 0) (hdegree : G.totalDegree = j)
    (hdiv : ∀ P, P.IsHomogeneous (t + j) → P ∈ (vanishingIdeal v).toIdeal → G ∣ P) :
    Function.Surjective (factorMultiplication v G j t hG) := by
  intro P
  obtain ⟨Q, hQ⟩ := hdiv P.val.val P.val.property P.property
  have hhom : Q.IsHomogeneous t := by
    have hh := quotient_homogeneous G Q (t + j) hG0 (hQ ▸ P.val.property)
    simpa only [hdegree, Nat.add_sub_cancel] using hh
  have hvan : Q ∈ (vanishingIdeal (outsideRepresentatives v G)).toIdeal :=
    (homogeneous_product_vanishing_iff v G Q j t hG hhom).mp (hQ ▸ P.property)
  refine ⟨⟨⟨Q, hhom⟩, hvan⟩, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  exact hQ.symm

omit [Fintype I] in
theorem factor_piece_dimension (v : I → Fin 3 → K) (G : PlaneRing K) (j t : ℕ)
    (hG : G.IsHomogeneous j) (hG0 : G ≠ 0) (hdegree : G.totalDegree = j)
    (hdiv : ∀ P, P.IsHomogeneous (t + j) → P ∈ (vanishingIdeal v).toIdeal → G ∣ P) :
    finrank K (idealPiece v (t + j)) =
      finrank K (idealPiece (outsideRepresentatives v G) t) :=
  (LinearEquiv.ofBijective (factorMultiplication v G j t hG)
    ⟨factorMultiplication_injective v G j t hG hG0,
      factorMultiplication_surjective v G j t hG hG0 hdegree hdiv⟩).finrank_eq.symm

end Cylinder.ReducedGapIdeal
end
