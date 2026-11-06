module

public import Cylinder.GlobalMomentsTheorem

/-! One actual residue family carries the global moment forms, the full
ray relation, and the zero/first moment data needed for the residual set. -/

@[expose] public section
noncomputable section
open scoped Classical BigOperators

namespace Cylinder.GlobalMomentsResidualData

open MvPolynomial Cylinder.ProjectiveGeometry Cylinder.ProjectiveBalance
open Cylinder.BlackProjection Cylinder.RationalPlanePointModel
open Cylinder.DirectionCurveBounds Cylinder.DirectionCurveProposition
open Cylinder.GlobalMomentResidues Cylinder.ExactRayMomentsTheorem
open Cylinder.BlackProjectionVandermonde Cylinder.EvaluationProjection

variable (p : ℕ) [Fact p.Prime]

set_option maxHeartbeats 1000000 in
theorem exists_actual_global_residue_data {S : Finset (Geometry.Point p)} (hp : 11 ≤ p)
    (hcard : S.card = p ^ 2) (hS : Geometry.PDivisible p S)
    (hnon : ¬Geometry.IsCylinder p S) {b : DualPoint p} (hb : b ∈ blackPoints p S) :
    ∃ c : DualPoint p → ZMod p, ∃ f g : MvPolynomial (Fin 3) (CurveField p),
      f.IsHomogeneous 1 ∧ g.IsHomogeneous 2 ∧
      (∀ i ν, rayResiduesOverField p (K := CurveField p) hb c i ν ≠ 0) ∧
      EvaluationRelation (directionRepresentatives p (K := CurveField p) hb)
        (raySize p S b hb) (rayTimesOverField p hb) (rayResiduesOverField p hb c) (p - 2) ∧
      (∀ P : directionSet p S b hb, actualMoment p hb c P 0 = 0) ∧
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
  obtain ⟨c, _hcWhite, _hproduct, _hpower, hcRay, hRayRelation, hlow, hnonzero, _hdirrel⟩ :=
    exists_product_exact_moments p (K := CurveField p) hcard hS hb (by omega)
  have hM0 : ∀ P : directionSet p S b hb, actualMoment p hb c P 0 = 0 := hlow 0 (by omega)
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
  exact ⟨c, f, g, hf, hg, hcRay, hRayRelation, hM0, hM1, hfv, hgv⟩

end Cylinder.GlobalMomentsResidualData

end
