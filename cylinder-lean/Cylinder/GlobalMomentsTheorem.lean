module

public import Cylinder.GlobalMomentComponentFamilies
public import Cylinder.ComponentInterpolation

/-! The original global moment theorem for the actual black projection.
One set of actual product residues is chosen and used throughout. -/

@[expose] public section
noncomputable section
open scoped Classical BigOperators

namespace Cylinder.GlobalMomentsTheorem

open MvPolynomial Cylinder.ProjectiveGeometry Cylinder.ProjectiveBalance
open Cylinder.BlackProjection Cylinder.RationalPlanePointModel Cylinder.PlaneBinaryReduction
open Cylinder.DirectionCurveBounds Cylinder.DirectionCurveProposition Cylinder.PlaneCurveFactors
open Cylinder.GlobalMomentResidues Cylinder.ExactRayMomentsTheorem
open Cylinder.ProductRescaling Cylinder.ExactRayMomentsNormalization

variable (p : ℕ) [Fact p.Prime]

set_option maxHeartbeats 1000000 in
theorem actual_global_moments {S : Finset (Geometry.Point p)} (hp : 11 ≤ p)
    (hcard : S.card = p ^ 2) (hS : Geometry.PDivisible p S)
    (hnon : ¬Geometry.IsCylinder p S) {b : DualPoint p} (hb : b ∈ blackPoints p S) :
    ∃ c : DualPoint p → ZMod p, ∃ f g : MvPolynomial (Fin 3) (CurveField p),
      (∀ H ∈ whitePoints p S, c H ≠ 0) ∧
      ((∏ H ∈ blackPoints p S, scaledPlaneForm p (normalizationScale p b) H ^ weight p S H) =
        ∑ E ∈ whitePoints p S, MvPolynomial.C (c E) *
          ∏ H ∈ (whitePoints p S).erase E, scaledPlaneForm p (normalizationScale p b) H) ∧
      f.IsHomogeneous 1 ∧ g.IsHomogeneous 2 ∧
      (∀ P : directionSet p S b hb, actualMoment p hb c P 1 ≠ 0) ∧
      (∀ P : directionSet p S b hb,
        actualMoment p hb c P 2 = eval (representatives (embedding p) (directionSet p S b hb) P) f *
          actualMoment p hb c P 1) ∧
      ∀ P : directionSet p S b hb,
        actualMoment p hb c P 3 = eval (representatives (embedding p) (directionSet p S b hb) P) g *
          actualMoment p hb c P 1 := by
  obtain ⟨s, hs, _hslow, _hsupper, _hklow, _hkwhite, _hkpolar, F, hF, hF0,
    hzero, hsq, _hsqmap, habs, _hsum, hcomp⟩ := exists_direction_curve p hp hcard hS hnon hb
  have hw := SimpleBlackWeights.black_weight_eq_one p hcard hS hnon hb
  obtain ⟨c, hcWhite, hproduct, _hpower, hcRay, hRayRelation, hlow, hnonzero, _hdirrel⟩ :=
    exists_product_exact_moments p (K := CurveField p) hcard hS hb (by omega)
  have hM0 : ∀ P : directionSet p S b hb, actualMoment p hb c P 0 = 0 :=
    hlow 0 (by omega)
  have hM1 : ∀ P : directionSet p S b hb, actualMoment p hb c P 1 ≠ 0 := by
    simpa only [hw] using hnonzero
  obtain ⟨fi, gi, hfi, hgi, hidf, hidg⟩ :=
    GlobalMomentComponentFamilies.assemble_component_form_families (embedding p)
      (directionSet p S b hb) F hF0 hsq hzero (fun P => actualMoment p hb c P 1)
      (fun P => actualMoment p hb c P 2) (fun P => actualMoment p hb c P 3) (by
        intro G hG H hGH
        exact ComponentInterpolation.component_interpolation_given_residues p hp hcard hS hnon hb
          s hs F G H hF hF0 hsq hzero hG (habs G hG) hcomp hGH c hcRay hRayRelation hM0 hM1)
  obtain ⟨f, g, hf, hg, _hfc, _hgc, hfv, hgv⟩ :=
    global_actual_moments_given_component_forms p hp hcard hS hnon hb s hs F hF hF0 hsq hzero
      hcomp c hRayRelation hM1 fi gi hfi hgi hidf hidg
  exact ⟨c, f, g, hcWhite, hproduct, hf, hg, hM1, hfv, hgv⟩

end Cylinder.GlobalMomentsTheorem

end
