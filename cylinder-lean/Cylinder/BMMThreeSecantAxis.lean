module

public import Cylinder.BMMThreeSecantConfigurations
public import Cylinder.BMMFourTupleBlackGeometry

/-! The fixed three-secant is one of the two actual cross axes of every
constructed tuple. Its line equation agrees up to nonzero scalar, so
the classification identifies that same original line as the 3-axis. -/

@[expose] public section
noncomputable section
open scoped Classical

namespace Cylinder.BMMThreeSecantAxis
open Cylinder.RationalPlaneLine Cylinder.PlaneCrossProduct Cylinder.BMMArcGeometry
open Cylinder.BMMBlackLineBlocks Cylinder.BMMThreeSecantPartition
open Cylinder.BMMThreeSecantConfigurations Cylinder.TripleFiberConfigurations
open Cylinder.BMMSpecialFourTuple Cylinder.BMMFourTupleBlackGeometry

variable {K : Type*} [Field K]

theorem square_height_of_pair_member (N : NormalizedSystem K) (l : Fin 3 → K) (R : N.B)
    (hR : R ∈ lineBlacks N l) (P Q : matchingPairs N R) (hQ : Q ∈ pairIndices N l R P)
    (X : N.W) (hX : X.val ∈ whitePair N R Q) : height N l X ^ 2 = squareHeight N l R P := by
  let : DecidableEq (matchingPairs N R) := Classical.decEq _
  have hheight : squareHeight N l R Q = squareHeight N l R P :=
    (mem_fiber _ P Q).mp (Finset.mem_erase.mp hQ).2
  rcases Finset.mem_insert.mp hX with hx | hx
  · have heq : X = Q.val := Subtype.ext hx
    rw [heq]
    exact hheight
  · have heq : X = partner N R Q.val := Subtype.ext (Finset.mem_singleton.mp hx)
    rw [heq, partner_height_flip N l R hR, neg_sq]
    exact hheight

theorem square_height_of_key_pair (N : NormalizedSystem K) (l : Fin 3 → K) (R : N.B)
    (hR : R ∈ lineBlacks N l) (P : matchingPairs N R)
    (T : FourTuple (configuration N) N.E R)
    (hkey : fourTupleKey N R T = configurationKey N l R P)
    (S : Finset (PlanePoint K)) (hS : S ∈ fourTupleKey N R T)
    (X : N.W) (hX : X.val ∈ S) : height N l X ^ 2 = squareHeight N l R P := by
  rw [hkey] at hS
  obtain ⟨Q, hQ, heq⟩ := Finset.mem_image.mp hS
  exact square_height_of_pair_member N l R hR P Q hQ X (heq.symm ▸ hX)

theorem tuple_square_heights_equal (N : NormalizedSystem K) (l : Fin 3 → K) (R : N.B)
    (hR : R ∈ lineBlacks N l) (P : matchingPairs N R)
    (T : FourTuple (configuration N) N.E R)
    (hkey : fourTupleKey N R T = configurationKey N l R P) :
    height N l T.P ^ 2 = height N l T.U ^ 2 := by
  have hP := square_height_of_key_pair N l R hR P T hkey {T.P.val, T.Q.val}
    (Finset.mem_insert_self _ _) T.P (Finset.mem_insert_self _ _)
  have hU := square_height_of_key_pair N l R hR P T hkey {T.U.val, T.V.val}
    (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)) T.U (Finset.mem_insert_self _ _)
  exact hP.trans hU.symm

theorem cross_blockers_on_fixed_line (N : NormalizedSystem K) (l : Fin 3 → K) (R : N.B)
    (hR : R ∈ lineBlacks N l) (P : matchingPairs N R)
    (T : FourTuple (configuration N) N.E R)
    (hkey : fourTupleKey N R T = configurationKey N l R P) :
    (firstCross N T ∈ lineBlacks N l ∧ secondCross N T ∈ lineBlacks N l) ∨
      (thirdCross N T ∈ lineBlacks N l ∧ fourthCross N T ∈ lineBlacks N l) := by
  have hPQ : height N l T.Q = -height N l T.P := by
    apply (blocker_on_line_iff N l T.P T.Q T.hPQ).mp
    change Cylinder.BMMActualCoefficients.blocker (configuration N) T.P T.Q T.hPQ ∈ lineBlacks N l
    rw [first_blocker]
    exact hR
  have hUV : height N l T.V = -height N l T.U := by
    apply (blocker_on_line_iff N l T.U T.V T.hUV).mp
    change Cylinder.BMMActualCoefficients.blocker (configuration N) T.U T.V T.hUV ∈ lineBlacks N l
    rw [second_blocker]
    exact hR
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp (tuple_square_heights_equal N l R hR P T hkey) with hsame | hopp
  · right
    constructor
    · exact (blocker_on_line_iff N l T.P T.V T.hPV).mpr (by rw [hUV, hsame])
    · exact (blocker_on_line_iff N l T.Q T.U T.hQU).mpr (by rw [hPQ, neg_neg, hsame])
  · left
    constructor
    · exact (blocker_on_line_iff N l T.P T.U T.hPU).mpr (by rw [hopp, neg_neg])
    · exact (blocker_on_line_iff N l T.Q T.V T.hQV).mpr (by rw [hUV, hPQ, neg_neg, hopp])

theorem fixed_line_is_cross_axis (N : NormalizedSystem K) (l : Fin 3 → K) (hl : l ≠ 0) (R : N.B)
    (hR : R ∈ lineBlacks N l) (P : matchingPairs N R)
    (T : FourTuple (configuration N) N.E R)
    (hkey : fourTupleKey N R T = configurationKey N l R P) :
    (∃ u : K, u ≠ 0 ∧ l = u • cross R.val.rep (firstCross N T).val.rep) ∨
      (∃ u : K, u ≠ 0 ∧ l = u • cross R.val.rep (thirdCross N T).val.rep) := by
  have hRzero := (Finset.mem_filter.mp hR).2
  rcases cross_blockers_on_fixed_line N l R hR P T hkey with hfirst | hsecond
  · exact Or.inl (annihilator_proportional l _ _ hl (first_line_coefficients_nonzero N T)
      hRzero (Finset.mem_filter.mp hfirst.1).2)
  · exact Or.inr (annihilator_proportional l _ _ hl (second_line_coefficients_nonzero N T)
      hRzero (Finset.mem_filter.mp hsecond.1).2)

theorem fixed_projective_line_is_cross_axis (N : NormalizedSystem K) (l : Fin 3 → K) (hl : l ≠ 0) (R : N.B)
    (hR : R ∈ lineBlacks N l) (P : matchingPairs N R)
    (T : FourTuple (configuration N) N.E R)
    (hkey : fourTupleKey N R T = configurationKey N l R P) :
    Projectivization.mk K l hl = firstLine N T ∨ Projectivization.mk K l hl = secondLine N T := by
  rcases fixed_line_is_cross_axis N l hl R hR P T hkey with ⟨u, _hu, heq⟩ | ⟨u, _hu, heq⟩
  · exact Or.inl ((Projectivization.mk_eq_mk_iff' K _ _ hl (first_line_coefficients_nonzero N T)).mpr ⟨u, heq.symm⟩)
  · exact Or.inr ((Projectivization.mk_eq_mk_iff' K _ _ hl (second_line_coefficients_nonzero N T)).mpr ⟨u, heq.symm⟩)

theorem lineBlacks_smul (N : NormalizedSystem K) (l : Fin 3 → K) (u : K) (hu : u ≠ 0) :
    lineBlacks N (u • l) = lineBlacks N l := by
  ext X
  simp only [lineBlacks, Finset.mem_filter, Finset.mem_univ, true_and, dot_smul_coefficients,
    mul_eq_zero, hu, false_or]

theorem fixed_three_axis_identified (N : NormalizedSystem K) (l : Fin 3 → K) (hl : l ≠ 0) (R : N.B)
    (hR : R ∈ lineBlacks N l) (P : matchingPairs N R)
    (T : FourTuple (configuration N) N.E R)
    (hkey : fourTupleKey N R T = configurationKey N l R P)
    (hm : (lineBlacks N l).card = 3)
    (hclass : ((lineBlacks N (cross R.val.rep (firstCross N T).val.rep)).card = 3 ∧
        (lineBlacks N (cross R.val.rep (thirdCross N T).val.rep)).card = 4) ∨
      ((lineBlacks N (cross R.val.rep (firstCross N T).val.rep)).card = 4 ∧
        (lineBlacks N (cross R.val.rep (thirdCross N T).val.rep)).card = 3)) :
    ((lineBlacks N l = lineBlacks N (cross R.val.rep (firstCross N T).val.rep)) ∧
        (lineBlacks N (cross R.val.rep (thirdCross N T).val.rep)).card = 4) ∨
      ((lineBlacks N l = lineBlacks N (cross R.val.rep (thirdCross N T).val.rep)) ∧
        (lineBlacks N (cross R.val.rep (firstCross N T).val.rep)).card = 4) := by
  rcases fixed_line_is_cross_axis N l hl R hR P T hkey with ⟨u, hu, heq⟩ | ⟨u, hu, heq⟩
  · have hline : lineBlacks N l = lineBlacks N (cross R.val.rep (firstCross N T).val.rep) := by
      rw [heq, lineBlacks_smul N _ u hu]
    left
    refine ⟨hline, ?_⟩
    rcases hclass with hclass | hclass
    · exact hclass.2
    · rw [hline, hclass.1] at hm
      omega
  · have hline : lineBlacks N l = lineBlacks N (cross R.val.rep (thirdCross N T).val.rep) := by
      rw [heq, lineBlacks_smul N _ u hu]
    right
    refine ⟨hline, ?_⟩
    rcases hclass with hclass | hclass
    · rw [hline, hclass.2] at hm
      omega
    · exact hclass.1

theorem exists_indexed_axis_configurations (p : ℕ) [Fact p.Prime] (hp : 3 ≤ p)
    (N : NormalizedSystem (ZMod p)) (l : Fin 3 → ZMod p) (hl : l ≠ 0)
    (hm : (lineBlacks N l).card = 3) (R : N.B) (hR : R ∈ lineBlacks N l)
    (n : ℕ) (hn : N.W.card = 2 * n) :
    ∃ T : matchingPairs N R → FourTuple (configuration N) N.E R,
      (∀ P, fourTupleKey N R (T P) = configurationKey N l R P) ∧
      Function.Injective (fun P => fourTupleKey N R (T P)) ∧ Fintype.card (matchingPairs N R) = n ∧
      ∀ P, Projectivization.mk (ZMod p) l hl = firstLine N (T P) ∨
        Projectivization.mk (ZMod p) l hl = secondLine N (T P) := by
  choose T hT using exists_configuration_fourtuple p hp N l hl hm R hR
  refine ⟨T, hT, ?_, ?_, fun P => fixed_projective_line_is_cross_axis N l hl R hR P (T P) (hT P)⟩
  · intro P Q heq
    change fourTupleKey N R (T P) = fourTupleKey N R (T Q) at heq
    rw [hT P, hT Q] at heq
    exact configurationKey_injective N l hl (Cylinder.BMMFinitePlaneArcBound.prime_two_nonzero p hp) hm R hR heq
  · obtain ⟨_S, _hinj, hc⟩ := exists_indexed_nonspecial_configurations p hp N l hl hm R hR n hn
    exact hc

end Cylinder.BMMThreeSecantAxis
end
