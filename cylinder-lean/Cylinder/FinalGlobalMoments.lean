module

public import Cylinder.GlobalMomentsTheorem
public import Cylinder.EquationScalarDescent

/-! The manuscript's global moment theorem, including uniqueness and
descent to the prime field, for a fixed family of actual ray residues.
The proof uses component interpolation and the initial degree of the
projected point set. It does not use the final cylinder theorem. -/

@[expose] public section
noncomputable section
open scoped Classical BigOperators

namespace Cylinder.FinalGlobalMoments

open MvPolynomial Cylinder.HilbertEvaluation Cylinder.PlaneBinaryReduction
open Cylinder.EquationScalarDescent

section Descent
variable {K L I : Type*} [Field K] [Field L] [Algebra K L]

/-- A linear coefficient projection fixing 1 descends a weighted
interpolation equation whose points and weights are in the base field. -/
theorem descend_weighted_form (v : I → Fin 3 → K) (u m : I → K)
    (d : ℕ) (F : MvPolynomial (Fin 3) L) (hF : F.IsHomogeneous d)
    (hvalues : ∀ i, algebraMap K L (m i) =
      eval (fun j => algebraMap K L (v i j)) F * algebraMap K L (u i)) :
    ∃ f : MvPolynomial (Fin 3) K, f.IsHomogeneous d ∧
      ∀ i, m i = eval (v i) f * u i := by
  obtain ⟨l, hl⟩ := Module.Projective.exists_dual_eq_one K (one_ne_zero : (1 : L) ≠ 0)
  have hscalar (a : K) (x : L) : l (algebraMap K L a * x) = a * l x := by
    simpa only [Algebra.smul_def, smul_eq_mul, Algebra.algebraMap_self, RingHom.id_apply]
      using l.map_smul a x
  have hbase (a : K) : l (algebraMap K L a) = a := by
    simpa only [mul_one, hl] using hscalar a 1
  refine ⟨coefficientProjection l F, coefficientProjection_homogeneous l F d hF, ?_⟩
  intro i
  have h := congrArg l (hvalues i)
  rw [hbase, mul_comm, hscalar] at h
  rw [eval_coefficientProjection]
  exact h.trans (mul_comm _ _)

omit [Field L] [Algebra K L] in
/-- Below the initial degree, a nonzero weighting preserves injectivity
of homogeneous evaluation. -/
theorem weighted_form_unique (v : I → Fin 3 → K) (u m : I → K)
    (hu : ∀ i, u i ≠ 0) (s : ℕ) (hs : InitialDegree v s) (d : ℕ) (hd : d < s)
    (F G : MvPolynomial (Fin 3) K) (hF : F.IsHomogeneous d) (hG : G.IsHomogeneous d)
    (hFV : ∀ i, m i = eval (v i) F * u i)
    (hGV : ∀ i, m i = eval (v i) G * u i) : F = G := by
  apply sub_eq_zero.mp
  by_contra hne
  have hzero : ∀ i, eval (v i) (F - G) = 0 := by
    intro i
    rw [map_sub, sub_eq_zero]
    exact mul_right_cancel₀ (hu i) ((hFV i).symm.trans (hGV i))
  exact ((idealPiece_ne_bot_iff v d).mpr ⟨F - G, hF.sub hG, hne, hzero⟩) (hs.2 d hd)

end Descent

open Cylinder.ProjectiveGeometry Cylinder.ProjectiveBalance Cylinder.BlackProjection
open Cylinder.RationalPlanePointModel Cylinder.DirectionCurveBounds
open Cylinder.DirectionCurveProposition Cylinder.GlobalMomentResidues
open Cylinder.ExactRayMomentsTheorem Cylinder.BlackProjectionVandermonde
open Cylinder.EvaluationProjection Cylinder.PlaneCurveFactors

variable (p : ℕ) [Fact p.Prime]

/-- The actual moments before scalar extension. -/
def primeMoment {S : Finset (Geometry.Point p)} {b : DualPoint p}
    (hb : b ∈ blackPoints p S) (c : DualPoint p → ZMod p)
    (i : directionSet p S b hb) (j : ℕ) : ZMod p :=
  rayMoment (raySize p S b hb)
    (ProjectiveProjection.rayTimes (ZMod p) (Fin 3) (whiteImage p S)
      (coordinatePoint p b) (black_outside_whiteImage p hb))
    (ExactRayMomentsResidueRelation.rayResidues p hb c) i j

theorem actualMoment_eq_embedding {S : Finset (Geometry.Point p)} {b : DualPoint p}
    (hb : b ∈ blackPoints p S) (c : DualPoint p → ZMod p)
    (i : directionSet p S b hb) (j : ℕ) :
    actualMoment p hb c i j = embedding p (primeMoment p hb c i j) := by
  have he : ProductEvaluationRelation.primeEmbedding p (K := CurveField p) = embedding p :=
    Subsingleton.elim _ _
  simpa only [actualMoment, primeMoment, he] using rayMoment_map p (K := CurveField p) hb c i j

/- Component interpolation and gluing with a fixed residue family. -/
set_option maxHeartbeats 1000000 in
theorem fixed_residue_global_forms {S : Finset (Geometry.Point p)} (hp : 11 ≤ p)
    (hcard : S.card = p ^ 2) (hS : Geometry.PDivisible p S)
    (hnon : ¬Geometry.IsCylinder p S) {b : DualPoint p} (hb : b ∈ blackPoints p S)
    (c : DualPoint p → ZMod p)
    (hc : ∀ i ν, rayResiduesOverField p (K := CurveField p) hb c i ν ≠ 0)
    (hrel : EvaluationRelation (directionRepresentatives p (K := CurveField p) hb)
      (raySize p S b hb) (rayTimesOverField p hb) (rayResiduesOverField p hb c) (p - 2))
    (hM0 : ∀ i, actualMoment p hb c i 0 = 0)
    (hM1 : ∀ i, actualMoment p hb c i 1 ≠ 0) :
    ∃ f g : MvPolynomial (Fin 3) (CurveField p), f.IsHomogeneous 1 ∧ g.IsHomogeneous 2 ∧
      (∀ P, actualMoment p hb c P 2 =
        eval (representatives (embedding p) (directionSet p S b hb) P) f * actualMoment p hb c P 1) ∧
      (∀ P, actualMoment p hb c P 3 =
        eval (representatives (embedding p) (directionSet p S b hb) P) g * actualMoment p hb c P 1) := by
  obtain ⟨s, hs, _, _, _, _, _, F, hF, hF0, hzero, hsq, _, habs, _, hcomp⟩ :=
    exists_direction_curve p hp hcard hS hnon hb
  obtain ⟨fi, gi, hfi, hgi, hidf, hidg⟩ :=
    GlobalMomentComponentFamilies.assemble_component_form_families (embedding p)
      (directionSet p S b hb) F hF0 hsq hzero (fun P => actualMoment p hb c P 1)
      (fun P => actualMoment p hb c P 2) (fun P => actualMoment p hb c P 3) (by
        intro G hG H hGH
        exact ComponentInterpolation.component_interpolation_given_residues p hp hcard hS hnon hb
          s hs F G H hF hF0 hsq hzero hG (habs G hG) hcomp hGH c hc hrel hM0 hM1)
  obtain ⟨f, g, hf, hg, _, _, hfv, hgv⟩ :=
    global_actual_moments_given_component_forms p hp hcard hS hnon hb s hs F hF hF0 hsq hzero
      hcomp c hrel hM1 fi gi hfi hgi hidf hidg
  exact ⟨f, g, hf, hg, hfv, hgv⟩

/- Theorem 5.1 for fixed actual residue data: both forms exist uniquely
over the prime field itself. -/
set_option maxHeartbeats 1000000 in
theorem global_moments_unique_prime {S : Finset (Geometry.Point p)} (hp : 11 ≤ p)
    (hcard : S.card = p ^ 2) (hS : Geometry.PDivisible p S)
    (hnon : ¬Geometry.IsCylinder p S) {b : DualPoint p} (hb : b ∈ blackPoints p S)
    (c : DualPoint p → ZMod p)
    (hc : ∀ i ν, rayResiduesOverField p (K := CurveField p) hb c i ν ≠ 0)
    (hrel : EvaluationRelation (directionRepresentatives p (K := CurveField p) hb)
      (raySize p S b hb) (rayTimesOverField p hb) (rayResiduesOverField p hb c) (p - 2))
    (hM0 : ∀ i, actualMoment p hb c i 0 = 0)
    (hM1 : ∀ i, actualMoment p hb c i 1 ≠ 0) :
    ∃! fg : MvPolynomial (Fin 3) (ZMod p) × MvPolynomial (Fin 3) (ZMod p),
      fg.1.IsHomogeneous 1 ∧ fg.2.IsHomogeneous 2 ∧
      (∀ P, primeMoment p hb c P 2 = eval P.val.rep fg.1 * primeMoment p hb c P 1) ∧
      (∀ P, primeMoment p hb c P 3 = eval P.val.rep fg.2 * primeMoment p hb c P 1) := by
  obtain ⟨F, G, hF, hG, hFV, hGV⟩ :=
    fixed_residue_global_forms p hp hcard hS hnon hb c hc hrel hM0 hM1
  let v : directionSet p S b hb → Fin 3 → ZMod p := fun P => P.val.rep
  let u := fun P => primeMoment p hb c P 1
  have hu : ∀ P, u P ≠ 0 := by
    intro P hz
    apply hM1 P
    rw [actualMoment_eq_embedding, show primeMoment p hb c P 1 = 0 from hz, map_zero]
  obtain ⟨f, hf, hfv⟩ := descend_weighted_form (L := CurveField p) v u
    (fun P => primeMoment p hb c P 2) 1 F hF (by
      intro P
      change embedding p (primeMoment p hb c P 2) =
        eval (representatives (embedding p) (directionSet p S b hb) P) F *
          embedding p (primeMoment p hb c P 1)
      simpa only [actualMoment_eq_embedding] using hFV P)
  obtain ⟨g, hg, hgv⟩ := descend_weighted_form (L := CurveField p) v u
    (fun P => primeMoment p hb c P 3) 2 G hG (by
      intro P
      change embedding p (primeMoment p hb c P 3) =
        eval (representatives (embedding p) (directionSet p S b hb) P) G *
          embedding p (primeMoment p hb c P 1)
      simpa only [actualMoment_eq_embedding] using hGV P)
  obtain ⟨s, hs, hslo, _⟩ := exists_direction_curve p hp hcard hS hnon hb
  have hsbase : InitialDegree v s := by
    apply (initialDegree_scalar_extension_iff (L := CurveField p) v s).mp
    exact hs
  have hslarge : 2 < s := by
    unfold DirectionExcess.threshold at hslo
    omega
  refine ⟨(f, g), ⟨hf, hg, hfv, hgv⟩, ?_⟩
  rintro ⟨f', g'⟩ ⟨hf', hg', hfv', hgv'⟩
  apply Prod.ext
  · exact weighted_form_unique v u (fun P => primeMoment p hb c P 2) hu s hsbase 1
      (by omega) f' f hf' hf hfv' hfv
  · exact weighted_form_unique v u (fun P => primeMoment p hb c P 3) hu s hsbase 2
      hslarge g' g hg' hg hgv' hgv

open Cylinder.ProductRescaling Cylinder.ExactRayMomentsNormalization

/- The manuscript's geometric hypotheses supply the actual residue data;
the resulting linear and quadratic moment forms are unique over F_p. -/
set_option maxHeartbeats 1000000 in
theorem global_moments {S : Finset (Geometry.Point p)} (hp : 11 ≤ p)
    (hcard : S.card = p ^ 2) (hS : Geometry.PDivisible p S)
    (hnon : ¬Geometry.IsCylinder p S) {b : DualPoint p} (hb : b ∈ blackPoints p S) :
    ∃ c : DualPoint p → ZMod p,
      (∀ H ∈ whitePoints p S, c H ≠ 0) ∧
      ((∏ H ∈ blackPoints p S, scaledPlaneForm p (normalizationScale p b) H ^ weight p S H) =
        ∑ E ∈ whitePoints p S, MvPolynomial.C (c E) *
          ∏ H ∈ (whitePoints p S).erase E, scaledPlaneForm p (normalizationScale p b) H) ∧
      ∃! fg : MvPolynomial (Fin 3) (ZMod p) × MvPolynomial (Fin 3) (ZMod p),
        fg.1.IsHomogeneous 1 ∧ fg.2.IsHomogeneous 2 ∧
        (∀ P, primeMoment p hb c P 2 = eval P.val.rep fg.1 * primeMoment p hb c P 1) ∧
        (∀ P, primeMoment p hb c P 3 = eval P.val.rep fg.2 * primeMoment p hb c P 1) := by
  have hw := SimpleBlackWeights.black_weight_eq_one p hcard hS hnon hb
  obtain ⟨c, hcWhite, hproduct, _, hcRay, hRayRelation, hlow, hfirst, _⟩ :=
    exists_product_exact_moments p (K := CurveField p) hcard hS hb (by omega)
  have hM0 : ∀ P : directionSet p S b hb, actualMoment p hb c P 0 = 0 :=
    hlow 0 (by omega)
  have hM1 : ∀ P : directionSet p S b hb, actualMoment p hb c P 1 ≠ 0 := by
    simpa only [hw] using hfirst
  exact ⟨c, hcWhite, hproduct,
    global_moments_unique_prime p hp hcard hS hnon hb c hcRay hRayRelation hM0 hM1⟩

#print axioms global_moments_unique_prime
#print axioms global_moments

end Cylinder.FinalGlobalMoments
end
