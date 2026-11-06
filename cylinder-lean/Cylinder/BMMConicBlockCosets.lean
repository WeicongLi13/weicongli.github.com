module

public import Cylinder.ConicBlockNormalForm
public import Cylinder.ConicNormalizedBlockVectors
public import Cylinder.BMMPrimeBlackLineConic
public import Cylinder.ArcConicIrreducible
public import Cylinder.SmallAdditiveSubgroups

/-! The actual prime-field black-line blocks have one multiplicative
subgroup parameterization with their actual normalized representatives.
The additive standard form is excluded by the proved prime-field bound. -/

@[expose] public section
noncomputable section
open scoped Classical

namespace Cylinder.BMMConicBlockCosets
open MvPolynomial Cylinder.HilbertEvaluation Cylinder.RationalPlaneLine Cylinder.PlaneCrossProduct
open Cylinder.PowerEvaluationRelation Cylinder.ProjectiveFieldEmbedding Cylinder.BMMArcGeometry
open Cylinder.BMMActualCoefficients Cylinder.BMMActualBlackLineData Cylinder.BMMNormalizedGeometry
open Cylinder.BMMBlackLineBlocks Cylinder.BMMBlackLinePointSets Cylinder.BMMFieldExtension
open Cylinder.ConicBlockNormalForm Cylinder.ConicFiniteBlocks Cylinder.ConicCosetEquivalences
open Cylinder.ConicNormalizedBlockVectors Cylinder.ConicRootPairsGeometry
open Cylinder.BMMFinitePlaneArcBound Cylinder.ArcConicIrreducible Cylinder.SmallAdditiveSubgroups

variable {R K : Type*} [Field R] [Field K]

structure HyperbolaBlockData (ι : R →+* K) (N : NormalizedSystem R)
    (l : Fin 3 → R) (h : R) (m : ℕ) where
  H : Subgroup Kˣ
  finite : Finite H
  card : Nat.card H = m
  g : (Fin 3 → K) ≃ₗ[K] (Fin 3 → K)
  c : K
  c_ne : c ≠ 0
  a : Kˣ
  b : Kˣ
  posEquiv : pointFiber N l h ≃ H
  negEquiv : pointFiber N l (-h) ≃ H
  pos_vectors : ∀ P : pointFiber N l h,
    g (vectorMap ι (N.E (fiberWhite N l h P))) = c • hyperbolaVector (a * (posEquiv P).val)
  neg_vectors : ∀ P : pointFiber N l (-h),
    g (vectorMap ι (N.E (fiberWhite N l (-h) P))) = -c • hyperbolaVector (b * (negEquiv P).val)

set_option maxHeartbeats 1000000 in
theorem exists_actual_block_coset_data (p : ℕ) [Fact p.Prime] [IsAlgClosed K] [CharP K p]
    (hp : 3 ≤ p) (A : Configuration (ZMod p)) (anchor : A.W)
    (l : Fin 3 → ZMod p) (hl : l ≠ 0) (hm : 3 ≤ (blackLine A l).card) :
    Nonempty (HyperbolaBlockData (ProductEvaluationRelation.primeEmbedding p (K := K))
      (normalizedSystem A anchor) l (height (normalizedSystem A anchor) l anchor) (blackLine A l).card) := by
  let : DecidableEq (ZMod p) := Classical.decEq _
  let ι := ProductEvaluationRelation.primeEmbedding p (K := K)
  let N := normalizedSystem A anchor
  let h := height N l anchor
  have htwo := prime_two_nonzero p hp
  have hm2 : 2 ≤ (blackLine A l).card := by omega
  obtain ⟨hX, hY⟩ := actual_block_cards A anchor l hl htwo hm2
  obtain ⟨hdisj, _⟩ := actual_blocks_disjoint A anchor l hl htwo hm2
  obtain ⟨hXoff, hYoff⟩ := actual_blocks_off_line A anchor l hl hm2
  obtain ⟨Q, hQ, hQ0, hvan⟩ := BMMPrimeBlackLineConic.conic_on_prime_blocks p hp A anchor l hl hm2
  have hcard : 5 ≤ (positiveBlock A anchor l ∪ negativeBlock A anchor l).card := by
    rw [actual_blocks_union_card A anchor l hl htwo hm2]
    omega
  have hirr := arc_conic_irreducible_map ι _ (actual_blocks_arc A anchor l) hcard Q hQ hQ0 hvan
  let ell : PlaneRing K := linearForm (vectorMap ι l)
  have hell : ell.IsHomogeneous 1 := (Cylinder.PlaneLinearForms.linearFormMap (vectorMap ι l)).property
  have hell0 : ell ≠ 0 := linearForm_nonzero _ (by
    intro hz
    exact hl (vectorMap_injective ι (hz.trans (map_zero (vectorMap ι)).symm)))
  have hvan' : ∀ P ∈ positiveBlock A anchor l ∪ negativeBlock A anchor l,
      eval (vectorMap ι P.rep) (MvPolynomial.map ι Q) = 0 := by
    intro P hP
    exact (MvPolynomial.map_eval ι P.rep Q).symm.trans (by rw [hvan P hP, map_zero])
  have hoff : ∀ P ∈ positiveBlock A anchor l ∪ negativeBlock A anchor l,
      eval (vectorMap ι P.rep) ell ≠ 0 := by
    intro P hP
    have hd : dot l P.rep ≠ 0 := (Finset.mem_union.mp hP).elim (hXoff P) (hYoff P)
    change eval (vectorMap ι P.rep) (linearForm (vectorMap ι l)) ≠ 0
    rw [eval_linearForm]
    change dot (fun j => ι (l j)) (fun j => ι (P.rep j)) ≠ 0
    rw [← map_dot ι l P.rep]
    exact fun hz => hd (ι.injective (hz.trans (map_zero ι).symm))
  have hinfty : ∀ T ∈ blackLine A l, eval (vectorMap ι T.rep) ell = 0 := by
    intro T hT
    change eval (vectorMap ι T.rep) (linearForm (vectorMap ι l)) = 0
    rw [eval_linearForm]
    change dot (fun j => ι (l j)) (fun j => ι (T.rep j)) = 0
    rw [← map_dot ι l T.rep, (Finset.mem_filter.mp hT).2, map_zero]
  obtain ⟨g, hlast, hstd⟩ := blocks_from_conic_and_line ι _ _ _ hdisj hX hY
    (actual_cross_secants_blocked A anchor l hl htwo hm2)
    (fun T => ⟨blockMatching A anchor l T, blockMatching_collinear A anchor l T⟩)
    (MvPolynomial.map ι Q) ell (hQ.map ι) hirr hell hell0 hvan' hoff hinfty
  obtain ⟨P, hP⟩ := Finset.card_pos.mp (show 0 < (positiveBlock A anchor l).card by omega)
  obtain ⟨T, hT⟩ := Finset.card_pos.mp (show 0 < (negativeBlock A anchor l).card by omega)
  let pos : positiveBlock A anchor l := ⟨P, hP⟩
  let neg : negativeBlock A anchor l := ⟨T, hT⟩
  rcases hstd with ⟨hstd, hn⟩ | hstd
  · obtain ⟨H, hfinite, hHcard, a, b, eX, eY, heX, heY⟩ :=
      hyperbola_block_equivalences ι g _ _ _ hstd hn pos neg
    have hh : h ≠ 0 := white_height_ne_zero N l hl (by rwa [normalized_line_card]) anchor
    have hc : ι h ≠ 0 := fun hz => hh (ι.injective (hz.trans (map_zero ι).symm))
    refine ⟨⟨H, hfinite, hHcard, g, ι h, hc, a, b, eX, eY, ?_, ?_⟩⟩
    · intro P
      rw [fiber_vector_eq ι g N l hlast h hh P, heX P]
      rfl
    · intro P
      rw [fiber_vector_eq ι g N l hlast (-h) (neg_ne_zero.mpr hh) P, heY P, map_neg]
      rfl
  · obtain ⟨H, hfinite, hHcard⟩ := parabola_blocks_are_cosets ι g _ _ _ hstd pos neg
    let : Finite H := hfinite
    have hsmall : Nat.card H < p := by rw [hHcard]; exact actual_black_line_card_lt_prime p A hp l hl
    have hone := small_additive_subgroup_card_one p H hsmall
    omega

end Cylinder.BMMConicBlockCosets
end
