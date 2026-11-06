module

public import Cylinder.IntersectionBinaryGeneration
public import Cylinder.IntersectionZeroSet

/-!
# From actual binary generation to intersection-point independence

A genuine graph restriction with relatively prime nonzero restricted
components makes the binary point ideal full from degree `s-1`. The
proved Artin quotient formula then makes the actual evaluation Hilbert
function constant from degree `s-2`; eventual interpolation identifies
that value with the point count. No regularity or surjectivity is assumed.
-/

@[expose] public section

noncomputable section

namespace Cylinder.IntersectionArtinBridge

open MvPolynomial Module
open Cylinder.HilbertEvaluation Cylinder.PlaneNumericalCharacter Cylinder.PlaneBinaryReduction
open Cylinder.IntersectionResolution Cylinder.IntersectionGradedResolution Cylinder.IntersectionZeroSet
open Cylinder.IntersectionBinaryGeneration
open scoped BigOperators Classical

variable {K I J : Type*} [Field K] [Fintype I] [Nonempty I] [Fintype J]

local instance planeGradedAlgebra : GradedAlgebra (Forms K) := MvPolynomial.gradedAlgebra

theorem graphRestriction_cofactor (a b : K) (F : I → HilbertEvaluation.PlaneRing K) (i : I) :
    graphRestriction a b (cofactor F i) = cofactor (fun j => graphRestriction a b (F j)) i := by
  unfold cofactor
  exact map_prod _ _ _

theorem binaryIdealPiece_full_at_bound (F : I → HilbertEvaluation.PlaneRing K) (e : I → ℕ)
    (he : ∀ i, 0 < e i) (hhom : ∀ i, (F i).IsHomogeneous (e i))
    (v : J → Fin 3 → K) (hJ : ∀ j, OnMultipleComponents F (v j))
    (a b : K) (hR0 : ∀ i, graphRestriction a b (F i) ≠ 0)
    (hRcop : Pairwise (fun i j => IsRelPrime (graphRestriction a b (F i)) (graphRestriction a b (F j)))) :
    binaryIdealPiece v a b (degreeSum e - 1) = BinaryForms K (degreeSum e - 1) := by
  apply le_antisymm
  · exact binaryIdealPiece_homogeneous v a b _
  · intro P hP
    have hRh : ∀ i, (graphRestriction a b (F i)).IsHomogeneous (e i) :=
      fun i => graphRestriction_homogeneous a b (F i) (e i) (hhom i)
    obtain ⟨A, hA, hPexp⟩ := exists_binary_cofactor_expansion
      (fun i => graphRestriction a b (F i)) e he hR0 hRcop hRh P hP
    let Q : HilbertEvaluation.PlaneRing K :=
      ∑ i, rename Fin.succ (A i) * cofactor F i
    have hQ : Q.IsHomogeneous (degreeSum e - 1) := by
      apply IsHomogeneous.sum
      intro i _
      have hrename : (rename (Fin.succ : Fin 2 → Fin 3) (A i)).IsHomogeneous (e i - 1) :=
        (hA i).rename_isHomogeneous
      have h := hrename.mul (IntersectionGradedResolution.cofactor_homogeneous F e hhom i)
      have hi := degree_le_sum e i
      have hipos := he i
      have hdegree : (e i - 1) + ((∑ j, e j) - e i) = degreeSum e - 1 := by
        unfold degreeSum at hi ⊢
        omega
      rw [hdegree] at h
      exact h
    have hQI : Q ∈ (vanishingIdeal v).toIdeal := by
      apply (homogeneous_mem_vanishingIdeal v Q _ hQ).mpr
      intro j
      have hH := (cofactors_vanish_iff F (v j)).mpr (hJ j)
      simp only [Q, map_sum, map_mul, hH, mul_zero, Finset.sum_const_zero]
    have hQR : graphRestriction a b Q = P := by
      simp only [Q, map_sum, map_mul, graphRestriction_rename, graphRestriction_cofactor]
      exact hPexp.symm
    exact (mem_binaryIdealPiece v a b _ P).mpr ⟨Q, hQ, hQI, hQR⟩

theorem binaryIdealPiece_full_succ (v : J → Fin 3 → K) (a b : K) (d : ℕ)
    (hfull : binaryIdealPiece v a b d = BinaryForms K d) :
    binaryIdealPiece v a b (d + 1) = BinaryForms K (d + 1) := by
  have hnonzero : binaryIdealPiece v a b d ≠ ⊥ := by
    intro hz
    have hdim := binaryForms_finrank (K := K) d
    rw [← hfull, hz, finrank_bot] at hdim
    omega
  have hg := binaryIdealPiece_growth v a b d hnonzero
  rw [hfull, binaryForms_finrank] at hg
  have hu := Submodule.finrank_mono (binaryIdealPiece_homogeneous v a b (d + 1))
  rw [binaryForms_finrank] at hu
  apply Submodule.eq_of_le_of_finrank_eq (binaryIdealPiece_homogeneous v a b (d + 1))
  rw [binaryForms_finrank]
  omega

theorem binaryIdealPiece_full_of_le (v : J → Fin 3 → K) (a b : K) (t : ℕ)
    (hfull : binaryIdealPiece v a b t = BinaryForms K t) (d : ℕ) (hd : t ≤ d) :
    binaryIdealPiece v a b d = BinaryForms K d := by
  induction d, hd using Nat.le_induction with
  | base => exact hfull
  | succ d hd ih => exact binaryIdealPiece_full_succ v a b d ih

theorem hilbert_succ_eq_of_binary_full (v : J → Fin 3 → K) (a b : K)
    (hLv : ∀ j, eval (v j) (graphEquation a b) ≠ 0) (d : ℕ)
    (hfull : binaryIdealPiece v a b (d + 1) = BinaryForms K (d + 1)) :
    hilbert v (d + 1) = hilbert v d := by
  have hbinary := artinComponent_add_binaryIdealPiece v a b d
  have hpoints := artinComponent_rank_add v (graphEquation a b) (graphEquation_homogeneous a b) hLv d
  rw [hfull, binaryForms_finrank] at hbinary
  omega

theorem hilbert_stable_of_binary_full (v : J → Fin 3 → K) (a b : K)
    (hLv : ∀ j, eval (v j) (graphEquation a b) ≠ 0) (s : ℕ)
    (hfull : binaryIdealPiece v a b (s - 1) = BinaryForms K (s - 1))
    (d : ℕ) (hd : s - 2 ≤ d) : hilbert v d = hilbert v (s - 2) := by
  induction d, hd using Nat.le_induction with
  | base => rfl
  | succ d hd ih =>
    have hnext : hilbert v (d + 1) = hilbert v d :=
      hilbert_succ_eq_of_binary_full v a b hLv d
        (binaryIdealPiece_full_of_le v a b (s - 1) hfull (d + 1) (by omega))
    exact hnext.trans ih

theorem independent_of_binary_full [Infinite K]
    (v : J → Fin 3 → K) (hv : ∀ j, v j ≠ 0) (hsep : ProjectivelyDistinct v)
    (a b : K) (hLv : ∀ j, eval (v j) (graphEquation a b) ≠ 0) (s : ℕ)
    (hfull : binaryIdealPiece v a b (s - 1) = BinaryForms K (s - 1))
    (d : ℕ) (hd : s - 2 ≤ d) : EvaluationProjection.Independent v d := by
  let T := max (s - 2) (Fintype.card J - 1)
  have hT : hilbert v T = Fintype.card J := hilbert_eq_card_of_card_sub_one_le
    v hv hsep T (le_max_right _ _)
  have hstableT := hilbert_stable_of_binary_full v a b hLv s hfull T (le_max_left _ _)
  have hstabled := hilbert_stable_of_binary_full v a b hLv s hfull d hd
  have hcard : hilbert v d = Fintype.card J := hstabled.trans (hstableT.symm.trans hT)
  have hspace : evaluationSpace v d = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    simpa only [hilbert, Module.finrank_pi] using hcard
  intro w
  have hw : w ∈ evaluationSpace v d := by rw [hspace]; trivial
  exact (mem_evaluationSpace v d w).mp hw

/-- The full desired evaluation conclusion, proved from an actual suitable graph line. -/
theorem independent_intersections_on_graph [Infinite K]
    (F : I → HilbertEvaluation.PlaneRing K) (e : I → ℕ)
    (he : ∀ i, 0 < e i) (hhom : ∀ i, (F i).IsHomogeneous (e i))
    (v : J → Fin 3 → K) (hv : ∀ j, v j ≠ 0) (hsep : ProjectivelyDistinct v)
    (hJ : ∀ j, OnMultipleComponents F (v j))
    (a b : K) (hLv : ∀ j, eval (v j) (graphEquation a b) ≠ 0)
    (hR0 : ∀ i, graphRestriction a b (F i) ≠ 0)
    (hRcop : Pairwise (fun i j => IsRelPrime (graphRestriction a b (F i)) (graphRestriction a b (F j))))
    (d : ℕ) (hd : degreeSum e - 2 ≤ d) : EvaluationProjection.Independent v d :=
  independent_of_binary_full v hv hsep a b hLv (degreeSum e)
    (binaryIdealPiece_full_at_bound F e he hhom v hJ a b hR0 hRcop) d hd

#print axioms binaryIdealPiece_full_at_bound
#print axioms independent_of_binary_full
#print axioms independent_intersections_on_graph

end Cylinder.IntersectionArtinBridge

end
