module

public import Cylinder.PlaneGap
public import Cylinder.InitialDegreeExists
public import Cylinder.PlanePointModel

/-! The full numerical-character prefix in the gap-decomposition proposition.
The inside and outside sets are the actual zero and nonzero loci of the
constructed homogeneous equation. -/

@[expose] public section
noncomputable section
open scoped Classical BigOperators

namespace Cylinder.FinalGapCharacter

open MvPolynomial Module Finset
open Cylinder.HilbertEvaluation Cylinder.PlaneNumericalCharacter
open Cylinder.PlaneBinaryReduction Cylinder.HilbertCharacterFormulas
open Cylinder.NumericCharacterSequence Cylinder.ReducedGapIdeal Cylinder.PlaneGap

variable {K I : Type*} [Field K] [Fintype I]
local instance : GradedAlgebra (Forms K) := MvPolynomial.gradedAlgebra

def insideRepresentatives (v : I → Fin 3 → K) (G : PlaneRing K) :
    Inside v G → Fin 3 → K := fun i => v i.val

omit [Fintype I] in
theorem inside_nonzero (v : I → Fin 3 → K) (hv : ∀ i, v i ≠ 0) (G : PlaneRing K) :
    ∀ i, insideRepresentatives v G i ≠ 0 := fun i => hv i.val

omit [Fintype I] in
theorem inside_distinct (v : I → Fin 3 → K) (hsep : ProjectivelyDistinct v) (G : PlaneRing K) :
    ProjectivelyDistinct (insideRepresentatives v G) := by
  intro i j hij a
  exact hsep i.val j.val (fun h => hij (Subtype.ext h)) a

def splitEvaluation (v : I → Fin 3 → K) (G : PlaneRing K) (d : ℕ) :
    evaluationSpace v d →ₗ[K]
      evaluationSpace (insideRepresentatives v G) d × (Outside v G → K) where
  toFun x := (⟨fun i => x.val i.val, by
    obtain ⟨P, hP⟩ := x.property
    exact ⟨P, funext fun i => congrFun hP i.val⟩⟩, fun i => x.val i.val)
  map_add' x y := rfl
  map_smul' a x := rfl

omit [Fintype I] in
theorem splitEvaluation_injective (v : I → Fin 3 → K) (G : PlaneRing K) (d : ℕ) :
    Function.Injective (splitEvaluation v G d) := by
  intro x y h
  apply Subtype.ext
  funext i
  by_cases hi : eval (v i) G = 0
  · exact congrFun (congrArg (fun z => z.1.val) h) ⟨i, hi⟩
  · exact congrFun (congrArg Prod.snd h) ⟨i, hi⟩

omit [Fintype I] in
theorem splitEvaluation_surjective (v : I → Fin 3 → K) (G : PlaneRing K)
    (j d : ℕ) (hG : G.IsHomogeneous j) (hjd : j ≤ d)
    (hind : Function.Surjective (evaluationMap (outsideRepresentatives v G) (d - j))) :
    Function.Surjective (splitEvaluation v G d) := by
  rintro ⟨x, y⟩
  obtain ⟨P, hP⟩ := x.property
  obtain ⟨Q, hQ⟩ := hind (fun i => (y i - eval (v i.val) P.val) / eval (v i.val) G)
  have hhom : (P.val + G * Q.val).IsHomogeneous d := by
    apply P.property.add
    simpa only [Nat.add_sub_cancel' hjd] using hG.mul Q.property
  let R : Forms K d := ⟨P.val + G * Q.val, hhom⟩
  refine ⟨⟨evaluationMap v d R, ⟨R, rfl⟩⟩, ?_⟩
  apply Prod.ext
  · apply Subtype.ext
    funext i
    change eval (v i.val) (P.val + G * Q.val) = x.val i
    rw [map_add, map_mul, i.property, zero_mul, add_zero]
    exact congrFun hP i
  · funext i
    change eval (v i.val) (P.val + G * Q.val) = y i
    have hQi := congrFun hQ i
    change eval (v i.val) Q.val = _ at hQi
    rw [map_add, map_mul, hQi, mul_comm (eval (v i.val) G), div_mul_cancel₀ _ i.property]
    ring

theorem hilbert_split (v : I → Fin 3 → K) (G : PlaneRing K)
    (j d : ℕ) (hG : G.IsHomogeneous j) (hjd : j ≤ d)
    (hind : Function.Surjective (evaluationMap (outsideRepresentatives v G) (d - j))) :
    hilbert v d = hilbert (insideRepresentatives v G) d + Fintype.card (Outside v G) := by
  have h := (LinearEquiv.ofBijective (splitEvaluation v G d)
    ⟨splitEvaluation_injective v G d, splitEvaluation_surjective v G j d hG hjd hind⟩).finrank_eq
  simpa only [hilbert, Module.finrank_prod, Module.finrank_fintype_fun_eq_card] using h

/-- The gap curve cuts out a point set whose *actual* numerical character
is precisely the initial segment of the original character. -/
theorem gap_character_prefix [Infinite K] [Nonempty I]
    (v : I → Fin 3 → K) (hv : ∀ i, v i ≠ 0) (hsep : ProjectivelyDistinct v)
    (s j : ℕ) (hs : InitialDegree v s) (hj0 : 0 < j) (hjs : j < s)
    (hgap : numericalCharacter v j + 2 ≤ numericalCharacter v (j - 1)) :
    ∃ G : PlaneRing K, G ≠ 0 ∧ G.IsHomogeneous j ∧ G.totalDegree = j ∧
      Nonempty (Inside v G) ∧ InitialDegree (insideRepresentatives v G) j ∧
      ∀ i < j, numericalCharacter (insideRepresentatives v G) i = numericalCharacter v i := by
  obtain ⟨G, hG0, hG, hdegree, hdiv⟩ := common_curve_of_gap v hv hsep s j hs hj0 hjs hgap
  obtain ⟨hqs, hq, hq1⟩ :=
    Cylinder.NumericalGapEvaluation.actual_gap_plateau v hv hsep s j hs hj0 hjs hgap
  let q := numericalCharacter v j
  have hqj : j < q := by dsimp [q]; omega
  have hind : ∀ w, q - j - 1 ≤ w →
      Function.Surjective (evaluationMap (outsideRepresentatives v G) w) := by
    intro w hw
    exact evaluationMap_surjective_of_hilbert_eq_card _ w
      (independence_of_common_factor v hv hsep q j hqj hq G hG0 hG hdegree hdiv w hw)
  have hlength := inside_length_of_common_factor v hv hsep s j hs hj0 hjs hgap
    G hG0 hG hdegree hdiv
  have hshape := derivationShape v hv hsep s hs
  have hn0 : s ≤ numericalCharacter v 0 := character_ge_initial_size hshape (by omega)
  have hinside : Nonempty (Inside v G) := by
    apply Fintype.card_pos_iff.mp
    rw [hlength]
    apply Finset.sum_pos_iff.mpr
    exact ⟨0, by simpa using hj0, by omega⟩
  let : Nonempty (Inside v G) := hinside
  let u := insideRepresentatives v G
  have huv : ∀ i, u i ≠ 0 := inside_nonzero v hv G
  have husep : ProjectivelyDistinct u := inside_distinct v hsep G
  have hsplit : ∀ d, q - 1 ≤ d →
      hilbert v d = hilbert u d + Fintype.card (Outside v G) := by
    intro d hd
    exact hilbert_split v G j d hG (by omega) (hind (d - j) (by omega))
  have hdiff : ∀ w, q ≤ w → differences u w = differences v w := by
    intro w hw
    cases w with
    | zero => omega
    | succ w =>
      have h0 := hsplit w (by omega)
      have h1 := hsplit (w + 1) (by omega)
      change hilbert u (w + 1) - hilbert u w = hilbert v (w + 1) - hilbert v w
      omega
  obtain ⟨r, hr⟩ := InitialDegreeExists.exists_initialDegree u
  have hrj : r ≤ j := by
    by_contra hbad
    have hmem : (⟨G, hG⟩ : Forms K j) ∈ idealPiece u j := by
      rw [idealPiece_eq_kernel]
      apply LinearMap.mem_ker.mpr
      funext i
      exact i.property
    rw [hr.2 j (by omega), Submodule.mem_bot] at hmem
    exact hG0 (congrArg Subtype.val hmem)
  have hshapeu := derivationShape u huv husep r hr
  have hqdiff : differences u q = j := (hdiff q (le_refl q)).trans hq
  have hjr : j ≤ r := by
    have hbound := value_le_initial_size hshapeu q
    change differences u q ≤ r at hbound
    omega
  have hr_eq : r = j := by omega
  subst r
  refine ⟨G, hG0, hG, hdegree, hinside, hr, ?_⟩
  intro i hi
  change numericalCharacter u i = numericalCharacter v i
  have hi_s : i < s := by omega
  have hn : q + 2 ≤ numericalCharacter v i := by
    have hmono := character_antitone (a := differences v) (N := Fintype.card I)
      (show i ≤ j - 1 by omega)
    change numericalCharacter v (j - 1) ≤ numericalCharacter v i at hmono
    dsimp [q]
    omega
  have hm : q < numericalCharacter u i := by
    have hz := (interval_iff_value hshapeu hi).mpr (show i < differences u q by omega)
    exact hz.2
  apply Nat.le_antisymm
  · have hpred : q ≤ numericalCharacter u i - 1 := by omega
    have hvu := (interval_iff_value hshapeu hi).mp
      (show i ≤ numericalCharacter u i - 1 ∧
        numericalCharacter u i - 1 < numericalCharacter u i by omega)
    change i < differences u (numericalCharacter u i - 1) at hvu
    rw [hdiff _ hpred] at hvu
    have hvv := ((interval_iff_value hshape hi_s).mpr hvu).2
    change numericalCharacter u i - 1 < numericalCharacter v i at hvv
    omega
  · have hpred : q ≤ numericalCharacter v i - 1 := by omega
    have hvv := (interval_iff_value hshape hi_s).mp
      (show i ≤ numericalCharacter v i - 1 ∧
        numericalCharacter v i - 1 < numericalCharacter v i by omega)
    change i < differences v (numericalCharacter v i - 1) at hvv
    rw [← hdiff _ hpred] at hvv
    have hvu := ((interval_iff_value hshapeu hi).mpr hvv).2
    change numericalCharacter v i - 1 < numericalCharacter u i at hvu
    omega

def reindexFunctions {J : Type*} (e : I ≃ J) : (I → K) ≃ₗ[K] (J → K) where
  toFun f i := f (e.symm i)
  invFun f i := f (e i)
  left_inv f := by funext i; simp
  right_inv f := by funext i; simp
  map_add' f g := rfl
  map_smul' a f := rfl

theorem hilbert_reindex {J : Type*} [Fintype J]
    (e : I ≃ J) (v : I → Fin 3 → K) (d : ℕ) :
    hilbert (fun i => v (e.symm i)) d = hilbert v d := by
  have hr : evaluationSpace (fun i => v (e.symm i)) d =
      (evaluationSpace v d).map (reindexFunctions (K := K) e).toLinearMap := by
    change LinearMap.range ((reindexFunctions (K := K) e).toLinearMap.comp (evaluationMap v d)) = _
    rw [LinearMap.range_comp]
    rfl
  unfold hilbert
  rw [hr]
  exact LinearEquiv.finrank_map_eq (reindexFunctions (K := K) e) (evaluationSpace v d)

theorem character_reindex [Infinite K] {J : Type*} [Fintype J]
    (e : I ≃ J) (v : I → Fin 3 → K) (i : ℕ) :
    numericalCharacter (fun k => v (e.symm k)) i = numericalCharacter v i := by
  have hh : hilbert (fun k => v (e.symm k)) = hilbert v := funext (hilbert_reindex e v)
  change character (firstDifference (hilbert (fun k => v (e.symm k)))) (Fintype.card J) i = _
  rw [hh, ← Fintype.card_congr e]
  rfl

theorem initialDegree_reindex {J : Type*} [Fintype J]
    (e : I ≃ J) (v : I → Fin 3 → K) (s : ℕ) :
    InitialDegree (fun i => v (e.symm i)) s ↔ InitialDegree v s := by
  have hi (d : ℕ) : idealPiece (fun i => v (e.symm i)) d = idealPiece v d := by
    ext P
    change P.val ∈ (vanishingIdeal (fun i => v (e.symm i))).toIdeal ↔
      P.val ∈ (vanishingIdeal v).toIdeal
    rw [homogeneous_mem_vanishingIdeal _ P.val d P.property,
      homogeneous_mem_vanishingIdeal _ P.val d P.property]
    constructor
    · intro h i
      simpa only [Equiv.symm_apply_apply] using h (e i)
    · intro h i
      exact h (e.symm i)
  simp only [InitialDegree, hi]

set_option maxHeartbeats 2000000 in
/-- Proposition 4.2 on the literal finite projective subset `D ∩ V(G)`.
Both its initial degree and every entry of its numerical character are
derived from the original gap; neither is an additional hypothesis. -/
theorem projective_gap_character_prefix [Infinite K]
    (D : Finset (PlanePointModel.Plane K)) (hD : D.Nonempty) (s j : ℕ)
    (hs : InitialDegree (PlanePointModel.representatives D) s)
    (hj0 : 0 < j) (hjs : j < s)
    (hgap : numericalCharacter (PlanePointModel.representatives D) j + 2 ≤
      numericalCharacter (PlanePointModel.representatives D) (j - 1)) :
    ∃ G : PlaneRing K, G ≠ 0 ∧ G.IsHomogeneous j ∧ G.totalDegree = j ∧
      let E := D.filter (fun P => eval P.rep G = 0)
      E.Nonempty ∧ InitialDegree (PlanePointModel.representatives E) j ∧
        ∀ i < j, numericalCharacter (PlanePointModel.representatives E) i =
          numericalCharacter (PlanePointModel.representatives D) i := by
  let : Nonempty D := Finset.nonempty_coe_sort.mpr hD
  obtain ⟨G, hG0, hG, hdegree, hnon, hinit, hchar⟩ :=
    gap_character_prefix (PlanePointModel.representatives D)
      (PlanePointModel.representatives_nonzero D) (PlanePointModel.representatives_distinct D)
      s j hs hj0 hjs hgap
  let E := D.filter (fun P => eval P.rep G = 0)
  let e : Inside (PlanePointModel.representatives D) G ≃ E :=
    { toFun := fun i => ⟨i.val.val, Finset.mem_filter.mpr ⟨i.val.property, i.property⟩⟩
      invFun := fun i => ⟨⟨i.val, (Finset.mem_filter.mp i.property).1⟩,
        (Finset.mem_filter.mp i.property).2⟩
      left_inv := fun i => by rfl
      right_inv := fun i => by rfl }
  refine ⟨G, hG0, hG, hdegree, ?_, ?_, ?_⟩
  · obtain ⟨i⟩ := hnon
    exact ⟨(e i).val, (e i).property⟩
  · exact (initialDegree_reindex e
      (insideRepresentatives (PlanePointModel.representatives D) G) j).mpr hinit
  · intro i hi
    exact (character_reindex e
      (insideRepresentatives (PlanePointModel.representatives D) G) i).trans (hchar i hi)

#print axioms hilbert_split
#print axioms gap_character_prefix
#print axioms projective_gap_character_prefix

end Cylinder.FinalGapCharacter

end
