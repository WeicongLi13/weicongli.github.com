module

public import Cylinder.ArbitraryMomentData
public import Cylinder.ProjectionTransport

/-! The fixed-residue global moment theorem in arbitrary centred coordinates,
with arbitrary direction representatives and arbitrary ray enumerations. -/

@[expose] public section
noncomputable section
open scoped Classical BigOperators LinearAlgebra.Projectivization
namespace Cylinder.ArbitraryMoments
open MvPolynomial Cylinder.ProjectiveGeometry Cylinder.ProjectiveBalance
open Cylinder.BlackProjection Cylinder.ProjectionChart Cylinder.EvaluationProjection
open Cylinder.ExactRayMomentsNormalization Cylinder.ExactRayMomentsResidueRelation
open Cylinder.ExactRayMomentsTheorem Cylinder.ExactRayMomentsCanonicalTimes
open Cylinder.MomentResidueChange Cylinder.FinalGlobalMoments
open Cylinder.MomentCoordinateTransport Cylinder.MomentCoordinateFixedResidues
open Cylinder.ArbitraryMomentData Cylinder.ProductRescaling
open Cylinder.DirectionCurveBounds Cylinder.DirectionCurveProposition
open Cylinder.PlaneBinaryReduction Cylinder.HilbertEvaluation
open Cylinder.RationalPlanePointModel Cylinder.EquationScalarDescent

variable (p : ℕ) [Fact p.Prime]
variable {S : Finset (Geometry.Point p)} {b : DualPoint p}

/-- The degree p-2 relation is transported using the same actual residues.
The factor lam^(p-2) is cancelled by the local residue factor lam via Fermat. -/
theorem evaluation_relation (C : Chart (coordinatePoint p b)) (hb : b ∈ blackPoints p S)
    (lam : directionSet p S b hb → (ZMod p)ˣ) (β : DualPoint p → (ZMod p)ˣ)
    (c : DualPoint p → ZMod p) (hc : ∀ H ∈ whitePoints p S, c H ≠ 0)
    (hprod : (∏ H ∈ blackPoints p S, scaledPlaneForm p (planeScale p hb lam β) H ^ weight p S H) =
      ∑ E ∈ whitePoints p S, MvPolynomial.C (c E) *
        ∏ H ∈ (whitePoints p S).erase E, scaledPlaneForm p (planeScale p hb lam β) H)
    (hpower : (∑ E ∈ whitePoints p S, MvPolynomial.C (c E) *
      scaledPlaneForm p (planeScale p hb lam β) E ^ (p - 2)) = 0) :
    EvaluationRelation (direction p C hb lam) (raySize p S b hb) (time p C hb lam)
      (rayResidues p hb c) (p - 2) := by
  obtain ⟨hc₀, hprod₀, hpower₀, hres⟩ := for_fixed_product p S
    (planeScale p hb lam β) (normalizationScale p b) c
    (planeScale_ne_zero p hb lam β) (normalizationScale_nonzero p b) hc hprod hpower
  have hrel := same_residue_ray_relation p hb (canonicalResidues p hb lam β c) hpower₀
  intro F hF
  let t := ProjectiveProjection.rayTimes (ZMod p) (Fin 3) (whiteImage p S)
    (coordinatePoint p b) (black_outside_whiteImage p hb)
  have hv (i : directionSet p S b hb) (ν : Fin (raySize p S b hb i)) :
      rayPoint (direction p C hb lam i) (time p C hb lam i ν) =
        (lam i : ZMod p) • C.transition (rayPoint i.val.rep (t i ν)) := by
    rw [C.transition_rayPoint]
    ext o
    cases o <;> rfl
  calc
    _ = productScale p hb lam β *
        (∑ i : directionSet p S b hb, ∑ ν : Fin (raySize p S b hb i),
          rayResidues p hb (canonicalResidues p hb lam β c) i ν *
            eval (rayPoint i.val.rep (t i ν))
              (LinearEvaluationTransport.linearPullback C.transition F)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro ν _
      rw [hv, LinearEvaluationTransport.homogeneous_eval_smul F (p - 2) hF,
        LinearEvaluationTransport.linearPullback_eval]
      change c (rayWhitePoint p hb i ν).val * _ = _
      rw [residue_on_ray p hb lam β c i ν]
      have hlam := scalar_fermat_shift p (lam i).ne_zero
      calc
        _ = productScale p hb lam β *
            ((lam i : ZMod p) * (lam i : ZMod p) ^ (p - 2)) *
            (rayResidues p hb (canonicalResidues p hb lam β c) i ν *
              eval (C.transition (rayPoint i.val.rep (t i ν))) F) := by
          unfold rayResidues
          ring
        _ = _ := by rw [hlam, mul_one]
    _ = 0 := by
      rw [hrel _ (LinearEvaluationTransport.linearPullback_homogeneous _ _ _ hF), mul_zero]

/-- The first-moment relation of Proposition 4.10 in the given chart. -/
theorem first_moment_relation (hp : 3 ≤ p)
    (C : Chart (coordinatePoint p b)) (hb : b ∈ blackPoints p S)
    (lam : directionSet p S b hb → (ZMod p)ˣ) (β : DualPoint p → (ZMod p)ˣ)
    (c : DualPoint p → ZMod p) (hc : ∀ H ∈ whitePoints p S, c H ≠ 0)
    (hprod : (∏ H ∈ blackPoints p S, scaledPlaneForm p (planeScale p hb lam β) H ^ weight p S H) =
      ∑ E ∈ whitePoints p S, MvPolynomial.C (c E) *
        ∏ H ∈ (whitePoints p S).erase E, scaledPlaneForm p (planeScale p hb lam β) H)
    (hpower : (∑ E ∈ whitePoints p S, MvPolynomial.C (c E) *
      scaledPlaneForm p (planeScale p hb lam β) E ^ (p - 2)) = 0) :
    PowerEvaluationRelation.Relation (direction p C hb lam)
      (fun i => actualMoment p C hb lam c i 1) (p - 3) := by
  have h := RayMomentRelations.relation_of_moments (direction p C hb lam)
    (raySize p S b hb) (time p C hb lam) (rayResidues p hb c) (p - 2) 1 (by omega)
    (evaluation_relation p C hb lam β c hc hprod hpower)
  simpa only [Nat.sub_sub, Nat.reduceAdd, rayMoment, rayResidues, actualMoment] using h

/-- All moment relations extend to every coefficient field.  This invokes
the polynomial scalar-extension theorem, so it tests every homogeneous form
over K, not only the forms with prime-field coefficients. -/
theorem all_moment_relations_over_field {K : Type*} [Field K] (ι : ZMod p →+* K)
    (C : Chart (coordinatePoint p b)) (hb : b ∈ blackPoints p S)
    (lam : directionSet p S b hb → (ZMod p)ˣ) (β : DualPoint p → (ZMod p)ˣ)
    (c : DualPoint p → ZMod p) (hc : ∀ H ∈ whitePoints p S, c H ≠ 0)
    (hprod : (∏ H ∈ blackPoints p S, scaledPlaneForm p (planeScale p hb lam β) H ^ weight p S H) =
      ∑ E ∈ whitePoints p S, MvPolynomial.C (c E) *
        ∏ H ∈ (whitePoints p S).erase E, scaledPlaneForm p (planeScale p hb lam β) H)
    (hpower : (∑ E ∈ whitePoints p S, MvPolynomial.C (c E) *
      scaledPlaneForm p (planeScale p hb lam β) E ^ (p - 2)) = 0)
    (j : ℕ) (hj : j ≤ p - 2) :
    PowerEvaluationRelation.Relation (fun i k => ι (direction p C hb lam i k))
      (fun i => ∑ ν : Fin (raySize p S b hb i),
        ι (c (rayWhitePoint p hb i ν).val) * ι (time p C hb lam i ν) ^ j) (p - 2 - j) := by
  letI : CharP K p := charP_of_injective_ringHom ι.injective p
  have hbase := RayMomentRelations.relation_of_moments (direction p C hb lam)
    (raySize p S b hb) (time p C hb lam) (rayResidues p hb c) (p - 2) j hj
    (evaluation_relation p C hb lam β c hc hprod hpower)
  have hdeg : p - 2 - j < p := by
    have hp := (Fact.out : p.Prime).two_le
    omega
  have h := PowerRelationScalarExtension.relation_scalar_extension p ι
    (direction p C hb lam) (fun i => rayMoment (raySize p S b hb)
      (time p C hb lam) (rayResidues p hb c) i j) (p - 2 - j) hdeg hbase
  simpa only [rayMoment, rayResidues, map_sum, map_mul, map_pow] using h

/-- The given product coefficients satisfy zero zeroth moment and nonzero
first moment in every prescribed chart and choice of direction representatives. -/
theorem exact_moments (hcard : S.card = p ^ 2) (hS : Geometry.PDivisible p S)
    (hnon : ¬Geometry.IsCylinder p S) (C : Chart (coordinatePoint p b))
    (hb : b ∈ blackPoints p S)
    (lam : directionSet p S b hb → (ZMod p)ˣ) (β : DualPoint p → (ZMod p)ˣ)
    (c : DualPoint p → ZMod p) (hc : ∀ H ∈ whitePoints p S, c H ≠ 0)
    (hprod : (∏ H ∈ blackPoints p S, scaledPlaneForm p (planeScale p hb lam β) H ^ weight p S H) =
      ∑ E ∈ whitePoints p S, MvPolynomial.C (c E) *
        ∏ H ∈ (whitePoints p S).erase E, scaledPlaneForm p (planeScale p hb lam β) H)
    (hpower : (∑ E ∈ whitePoints p S, MvPolynomial.C (c E) *
      scaledPlaneForm p (planeScale p hb lam β) E ^ (p - 2)) = 0) :
    (∀ i, actualMoment p C hb lam c i 0 = 0) ∧
      ∀ i, actualMoment p C hb lam c i 1 ≠ 0 := by
  obtain ⟨hc₀, hprod₀, hpower₀, hres⟩ := for_fixed_product p S
    (planeScale p hb lam β) (normalizationScale p b) c
    (planeScale_ne_zero p hb lam β) (normalizationScale_nonzero p b) hc hprod hpower
  have hw := SimpleBlackWeights.black_weight_eq_one p hcard hS hnon hb
  have hm := fixed_product_moments p hcard hS hb (canonicalResidues p hb lam β c) hprod₀
  constructor
  · intro i
    rw [actualMoment_eq p C hb lam β c i 0, moment_affine_zero]
    change _ * primeMoment p hb (canonicalResidues p hb lam β c) i 0 = 0
    rw [hm.1 0 (by omega) i, mul_zero]
  · intro i
    rw [actualMoment_eq p C hb lam β c i 1, moment_affine_one]
    change _ * (_ * primeMoment p hb (canonicalResidues p hb lam β c) i 0 +
      _ * primeMoment p hb (canonicalResidues p hb lam β c) i 1) ≠ 0
    rw [hm.1 0 (by omega) i, mul_zero, zero_add]
    have hm1 : primeMoment p hb (canonicalResidues p hb lam β c) i 1 ≠ 0 := by
      simpa only [hw] using hm.2 i
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (productScale_ne_zero p hb lam β)
      (lam i).ne_zero) (lam i).ne_zero) (mul_ne_zero C.c.ne_zero hm1)

/-- Existence over the prime field, for the same originally fixed residues. -/
theorem global_moments_exists (hp : 11 ≤ p) (hcard : S.card = p ^ 2)
    (hS : Geometry.PDivisible p S) (hnon : ¬Geometry.IsCylinder p S)
    (C : Chart (coordinatePoint p b)) (hb : b ∈ blackPoints p S)
    (lam : directionSet p S b hb → (ZMod p)ˣ) (β : DualPoint p → (ZMod p)ˣ)
    (c : DualPoint p → ZMod p) (hc : ∀ H ∈ whitePoints p S, c H ≠ 0)
    (hprod : (∏ H ∈ blackPoints p S, scaledPlaneForm p (planeScale p hb lam β) H ^ weight p S H) =
      ∑ E ∈ whitePoints p S, MvPolynomial.C (c E) *
        ∏ H ∈ (whitePoints p S).erase E, scaledPlaneForm p (planeScale p hb lam β) H)
    (hpower : (∑ E ∈ whitePoints p S, MvPolynomial.C (c E) *
      scaledPlaneForm p (planeScale p hb lam β) E ^ (p - 2)) = 0) :
    ∃ f g : MvPolynomial (Fin 3) (ZMod p), f.IsHomogeneous 1 ∧ g.IsHomogeneous 2 ∧
      (∀ i, actualMoment p C hb lam c i 2 = eval (direction p C hb lam i) f *
        actualMoment p C hb lam c i 1) ∧
      (∀ i, actualMoment p C hb lam c i 3 = eval (direction p C hb lam i) g *
        actualMoment p C hb lam c i 1) := by
  obtain ⟨hc₀, hprod₀, hpower₀, hres⟩ := for_fixed_product p S
    (planeScale p hb lam β) (normalizationScale p b) c
    (planeScale_ne_zero p hb lam β) (normalizationScale_nonzero p b) hc hprod hpower
  obtain ⟨⟨f, g⟩, ⟨hf, hg, hfv, hgv⟩, _⟩ := fixed_product_global_moments p hp hcard hS hnon hb
    (canonicalResidues p hb lam β c) hc₀ hprod₀ hpower₀
  have hw := SimpleBlackWeights.black_weight_eq_one p hcard hS hnon hb
  have hm := fixed_product_moments p hcard hS hb (canonicalResidues p hb lam β c) hprod₀
  refine ⟨linearMomentForm C.directionEquiv C.timeShift (C.c : ZMod p) f,
    quadraticMomentForm C.directionEquiv C.timeShift (C.c : ZMod p) f g,
    linearMomentForm_homogeneous _ _ _ _ hf,
    quadraticMomentForm_homogeneous _ _ _ _ _ hf hg, ?_, ?_⟩
  · intro i
    rw [actualMoment_eq p C hb lam β c i 2, actualMoment_eq p C hb lam β c i 1]
    exact (interpolation_transport C.directionEquiv C.timeShift (C.c : ZMod p)
      (productScale p hb lam β * (lam i : ZMod p)) (lam i : ZMod p) i.val.rep
      (ProjectiveProjection.rayTimes (ZMod p) (Fin 3) (whiteImage p S)
        (coordinatePoint p b) (black_outside_whiteImage p hb) i)
      (rayResidues p hb (canonicalResidues p hb lam β c) i) f g hf hg
      (hm.1 0 (by omega) i) (hfv i) (hgv i)).1
  · intro i
    rw [actualMoment_eq p C hb lam β c i 3, actualMoment_eq p C hb lam β c i 1]
    exact (interpolation_transport C.directionEquiv C.timeShift (C.c : ZMod p)
      (productScale p hb lam β * (lam i : ZMod p)) (lam i : ZMod p) i.val.rep
      (ProjectiveProjection.rayTimes (ZMod p) (Fin 3) (whiteImage p S)
        (coordinatePoint p b) (black_outside_whiteImage p hb) i)
      (rayResidues p hb (canonicalResidues p hb lam β c) i) f g hf hg
      (hm.1 0 (by omega) i) (hfv i) (hgv i)).2

/-- Theorem 5.1 in the prescribed chart and representatives, with existence
and uniqueness in F_p for the originally fixed product residues. -/
theorem global_moments_unique (hp : 11 ≤ p) (hcard : S.card = p ^ 2)
    (hS : Geometry.PDivisible p S) (hnon : ¬Geometry.IsCylinder p S)
    (C : Chart (coordinatePoint p b)) (hb : b ∈ blackPoints p S)
    (lam : directionSet p S b hb → (ZMod p)ˣ) (β : DualPoint p → (ZMod p)ˣ)
    (c : DualPoint p → ZMod p) (hc : ∀ H ∈ whitePoints p S, c H ≠ 0)
    (hprod : (∏ H ∈ blackPoints p S, scaledPlaneForm p (planeScale p hb lam β) H ^ weight p S H) =
      ∑ E ∈ whitePoints p S, MvPolynomial.C (c E) *
        ∏ H ∈ (whitePoints p S).erase E, scaledPlaneForm p (planeScale p hb lam β) H)
    (hpower : (∑ E ∈ whitePoints p S, MvPolynomial.C (c E) *
      scaledPlaneForm p (planeScale p hb lam β) E ^ (p - 2)) = 0) :
    ∃! fg : MvPolynomial (Fin 3) (ZMod p) × MvPolynomial (Fin 3) (ZMod p),
      fg.1.IsHomogeneous 1 ∧ fg.2.IsHomogeneous 2 ∧
      (∀ i, actualMoment p C hb lam c i 2 = eval (direction p C hb lam i) fg.1 *
        actualMoment p C hb lam c i 1) ∧
      (∀ i, actualMoment p C hb lam c i 3 = eval (direction p C hb lam i) fg.2 *
        actualMoment p C hb lam c i 1) := by
  obtain ⟨f, g, hf, hg, hfv, hgv⟩ :=
    global_moments_exists p hp hcard hS hnon C hb lam β c hc hprod hpower
  have hm1 := (exact_moments p hcard hS hnon C hb lam β c hc hprod hpower).2
  obtain ⟨s, hs, hslo, _⟩ := exists_direction_curve p hp hcard hS hnon hb
  have hsbase : InitialDegree (fun i : directionSet p S b hb => i.val.rep) s := by
    apply (initialDegree_scalar_extension_iff (L := CurveField p)
      (fun i : directionSet p S b hb => i.val.rep) s).mp
    exact hs
  have hstarget : InitialDegree (direction p C hb lam) s :=
    (ProjectionTransport.initialDegree_linearEquiv_rescaling C.directionEquiv
      (fun i : directionSet p S b hb => i.val.rep) (fun i => (lam i : ZMod p))
      (fun i => (lam i).ne_zero) s).mpr hsbase
  have hslarge : 2 < s := by
    unfold DirectionExcess.threshold at hslo
    omega
  refine ⟨(f, g), ⟨hf, hg, hfv, hgv⟩, ?_⟩
  rintro ⟨f', g'⟩ ⟨hf', hg', hfv', hgv'⟩
  apply Prod.ext
  · exact weighted_form_unique (direction p C hb lam)
      (fun i => actualMoment p C hb lam c i 1) (fun i => actualMoment p C hb lam c i 2)
      hm1 s hstarget 1 (by omega) f' f hf' hf hfv' hfv
  · exact weighted_form_unique (direction p C hb lam)
      (fun i => actualMoment p C hb lam c i 1) (fun i => actualMoment p C hb lam c i 3)
      hm1 s hstarget 2 hslarge g' g hg' hg hgv' hgv

/-- Replacing the finite enumeration of a ray leaves its actual moment
unchanged, with each prescribed residue carried by its original white point. -/
theorem moment_any_enumeration {J : Type*} [Fintype J]
    (C : Chart (coordinatePoint p b)) (hb : b ∈ blackPoints p S)
    (lam : directionSet p S b hb → (ZMod p)ˣ) (c : DualPoint p → ZMod p)
    (i : directionSet p S b hb) (e : J ≃ Fin (raySize p S b hb i)) (j : ℕ) :
    (∑ ν : J, c (rayWhitePoint p hb i (e ν)).val * time p C hb lam i (e ν) ^ j) =
      actualMoment p C hb lam c i j := by
  exact e.sum_comp (fun ν => c (rayWhitePoint p hb i ν).val * time p C hb lam i ν ^ j)

def enumeratedMoment {I : Type*} (C : Chart (coordinatePoint p b))
    (hb : b ∈ blackPoints p S) (lam : directionSet p S b hb → (ZMod p)ˣ)
    (c : DualPoint p → ZMod p) (e : I ≃ directionSet p S b hb)
    {J : I → Type*} [∀ i, Fintype (J i)]
    (ν : ∀ i, J i ≃ Fin (raySize p S b hb (e i))) (i : I) (j : ℕ) : ZMod p :=
  ∑ x : J i, c (rayWhitePoint p hb (e i) (ν i x)).val * time p C hb lam (e i) (ν i x) ^ j

theorem enumeratedMoment_eq {I : Type*} (C : Chart (coordinatePoint p b))
    (hb : b ∈ blackPoints p S) (lam : directionSet p S b hb → (ZMod p)ˣ)
    (c : DualPoint p → ZMod p) (e : I ≃ directionSet p S b hb)
    {J : I → Type*} [∀ i, Fintype (J i)]
    (ν : ∀ i, J i ≃ Fin (raySize p S b hb (e i))) (i : I) (j : ℕ) :
    enumeratedMoment p C hb lam c e ν i j = actualMoment p C hb lam c (e i) j :=
  moment_any_enumeration p C hb lam c (e i) (ν i) j

/-- The complete prime-field conclusion with every direction index and every
finite enumeration supplied in advance. -/
theorem global_moments_reindexed {I : Type*} (hp : 11 ≤ p) (hcard : S.card = p ^ 2)
    (hS : Geometry.PDivisible p S) (hnon : ¬Geometry.IsCylinder p S)
    (C : Chart (coordinatePoint p b)) (hb : b ∈ blackPoints p S)
    (lam : directionSet p S b hb → (ZMod p)ˣ) (β : DualPoint p → (ZMod p)ˣ)
    (c : DualPoint p → ZMod p) (hc : ∀ H ∈ whitePoints p S, c H ≠ 0)
    (hprod : (∏ H ∈ blackPoints p S, scaledPlaneForm p (planeScale p hb lam β) H ^ weight p S H) =
      ∑ E ∈ whitePoints p S, MvPolynomial.C (c E) *
        ∏ H ∈ (whitePoints p S).erase E, scaledPlaneForm p (planeScale p hb lam β) H)
    (hpower : (∑ E ∈ whitePoints p S, MvPolynomial.C (c E) *
      scaledPlaneForm p (planeScale p hb lam β) E ^ (p - 2)) = 0)
    (e : I ≃ directionSet p S b hb) {J : I → Type*} [∀ i, Fintype (J i)]
    (ν : ∀ i, J i ≃ Fin (raySize p S b hb (e i))) :
    ∃! fg : MvPolynomial (Fin 3) (ZMod p) × MvPolynomial (Fin 3) (ZMod p),
      fg.1.IsHomogeneous 1 ∧ fg.2.IsHomogeneous 2 ∧
      (∀ i, enumeratedMoment p C hb lam c e ν i 2 = eval (direction p C hb lam (e i)) fg.1 *
        enumeratedMoment p C hb lam c e ν i 1) ∧
      (∀ i, enumeratedMoment p C hb lam c e ν i 3 = eval (direction p C hb lam (e i)) fg.2 *
        enumeratedMoment p C hb lam c e ν i 1) := by
  obtain ⟨fg, ⟨hf, hg, hfv, hgv⟩, huniq⟩ :=
    global_moments_unique p hp hcard hS hnon C hb lam β c hc hprod hpower
  refine ⟨fg, ⟨hf, hg, ?_, ?_⟩, ?_⟩
  · intro i
    simpa only [enumeratedMoment_eq] using hfv (e i)
  · intro i
    simpa only [enumeratedMoment_eq] using hgv (e i)
  · rintro fg' ⟨hf', hg', hfv', hgv'⟩
    apply huniq fg'
    refine ⟨hf', hg', ?_, ?_⟩
    · intro i
      simpa only [enumeratedMoment_eq, Equiv.apply_symm_apply] using hfv' (e.symm i)
    · intro i
      simpa only [enumeratedMoment_eq, Equiv.apply_symm_apply] using hgv' (e.symm i)

/-- Proposition 5.10 for any given component, encoded by its prescribed
cofactor H.  The same global forms restrict to every such component, so no
new equation or residue family is chosen at this step. -/
theorem component_moments (hp : 11 ≤ p) (hcard : S.card = p ^ 2)
    (hS : Geometry.PDivisible p S) (hnon : ¬Geometry.IsCylinder p S)
    (C : Chart (coordinatePoint p b)) (hb : b ∈ blackPoints p S)
    (lam : directionSet p S b hb → (ZMod p)ˣ) (β : DualPoint p → (ZMod p)ˣ)
    (c : DualPoint p → ZMod p) (hc : ∀ H ∈ whitePoints p S, c H ≠ 0)
    (hprod : (∏ H ∈ blackPoints p S, scaledPlaneForm p (planeScale p hb lam β) H ^ weight p S H) =
      ∑ E ∈ whitePoints p S, MvPolynomial.C (c E) *
        ∏ H ∈ (whitePoints p S).erase E, scaledPlaneForm p (planeScale p hb lam β) H)
    (hpower : (∑ E ∈ whitePoints p S, MvPolynomial.C (c E) *
      scaledPlaneForm p (planeScale p hb lam β) E ^ (p - 2)) = 0)
    (H : MvPolynomial (Fin 3) (ZMod p)) :
    ∃ f g : MvPolynomial (Fin 3) (ZMod p), f.IsHomogeneous 1 ∧ g.IsHomogeneous 2 ∧
      ∀ i, eval (direction p C hb lam i) H ≠ 0 →
        actualMoment p C hb lam c i 2 = eval (direction p C hb lam i) f *
          actualMoment p C hb lam c i 1 ∧
        actualMoment p C hb lam c i 3 = eval (direction p C hb lam i) g *
          actualMoment p C hb lam c i 1 := by
  obtain ⟨f, g, hf, hg, hfv, hgv⟩ :=
    global_moments_exists p hp hcard hS hnon C hb lam β c hc hprod hpower
  exact ⟨f, g, hf, hg, fun i _ => ⟨hfv i, hgv i⟩⟩

/-- The component statement after scalar extension, for any prescribed
cofactor over the extension field, including the algebraic closure. -/
theorem component_moments_over_field {K : Type*} [Field K]
    (ι : ZMod p →+* K) (hp : 11 ≤ p) (hcard : S.card = p ^ 2)
    (hS : Geometry.PDivisible p S) (hnon : ¬Geometry.IsCylinder p S)
    (C : Chart (coordinatePoint p b)) (hb : b ∈ blackPoints p S)
    (lam : directionSet p S b hb → (ZMod p)ˣ) (β : DualPoint p → (ZMod p)ˣ)
    (c : DualPoint p → ZMod p) (hc : ∀ H ∈ whitePoints p S, c H ≠ 0)
    (hprod : (∏ H ∈ blackPoints p S, scaledPlaneForm p (planeScale p hb lam β) H ^ weight p S H) =
      ∑ E ∈ whitePoints p S, MvPolynomial.C (c E) *
        ∏ H ∈ (whitePoints p S).erase E, scaledPlaneForm p (planeScale p hb lam β) H)
    (hpower : (∑ E ∈ whitePoints p S, MvPolynomial.C (c E) *
      scaledPlaneForm p (planeScale p hb lam β) E ^ (p - 2)) = 0)
    (H : MvPolynomial (Fin 3) K) :
    ∃ f g : MvPolynomial (Fin 3) K, f.IsHomogeneous 1 ∧ g.IsHomogeneous 2 ∧
      ∀ i, eval (fun j => ι (direction p C hb lam i j)) H ≠ 0 →
        ι (actualMoment p C hb lam c i 2) = eval (fun j => ι (direction p C hb lam i j)) f *
          ι (actualMoment p C hb lam c i 1) ∧
        ι (actualMoment p C hb lam c i 3) = eval (fun j => ι (direction p C hb lam i j)) g *
          ι (actualMoment p C hb lam c i 1) := by
  obtain ⟨f, g, hf, hg, hfv, hgv⟩ :=
    global_moments_exists p hp hcard hS hnon C hb lam β c hc hprod hpower
  refine ⟨MvPolynomial.map ι f, MvPolynomial.map ι g, hf.map ι, hg.map ι, ?_⟩
  intro i _
  constructor
  · rw [FrobeniusPolarBound.eval_map_at_mapped_point, ← map_mul, hfv i]
  · rw [FrobeniusPolarBound.eval_map_at_mapped_point, ← map_mul, hgv i]

/-- The final interface allows every original plane equation to be prescribed
first.  Its only normalization condition is the actual spatial coordinate
of each white point in the chosen chart. -/
theorem prescribed_coordinates (hp : 11 ≤ p) (hcard : S.card = p ^ 2)
    (hS : Geometry.PDivisible p S) (hnon : ¬Geometry.IsCylinder p S)
    (C : Chart (coordinatePoint p b)) (hb : b ∈ blackPoints p S)
    (lam : directionSet p S b hb → (ZMod p)ˣ)
    (a c : DualPoint p → ZMod p) (ha : ∀ H, a H ≠ 0)
    (hnorm : ∀ i ν, tail (C.g (a (rayWhitePoint p hb i ν).val •
      dualCoordinates p (rayWhitePoint p hb i ν).val.rep)) = direction p C hb lam i)
    (hc : ∀ H ∈ whitePoints p S, c H ≠ 0)
    (hprod : (∏ H ∈ blackPoints p S, scaledPlaneForm p a H ^ weight p S H) =
      ∑ E ∈ whitePoints p S, MvPolynomial.C (c E) *
        ∏ H ∈ (whitePoints p S).erase E, scaledPlaneForm p a H)
    (hpower : (∑ E ∈ whitePoints p S, MvPolynomial.C (c E) *
      scaledPlaneForm p a E ^ (p - 2)) = 0) :
    (∀ i, actualMoment p C hb lam c i 0 = 0) ∧
    (∀ i, actualMoment p C hb lam c i 1 ≠ 0) ∧
    PowerEvaluationRelation.Relation (direction p C hb lam)
      (fun i => actualMoment p C hb lam c i 1) (p - 3) ∧
    ∃! fg : MvPolynomial (Fin 3) (ZMod p) × MvPolynomial (Fin 3) (ZMod p),
      fg.1.IsHomogeneous 1 ∧ fg.2.IsHomogeneous 2 ∧
      (∀ i, actualMoment p C hb lam c i 2 = eval (direction p C hb lam i) fg.1 *
        actualMoment p C hb lam c i 1) ∧
      (∀ i, actualMoment p C hb lam c i 3 = eval (direction p C hb lam i) fg.2 *
        actualMoment p C hb lam c i 1) := by
  obtain ⟨β, hβ⟩ := planeScale_exhaustive p C hb lam a ha hnorm
  rw [← hβ] at hprod hpower
  have hm := exact_moments p hcard hS hnon C hb lam β c hc hprod hpower
  exact ⟨hm.1, hm.2, first_moment_relation p (by omega) C hb lam β c hc hprod hpower,
    global_moments_unique p hp hcard hS hnon C hb lam β c hc hprod hpower⟩

/-- The coordinates, every nonzero direction representative, and every plane
equation are all preassigned.  The moments are defined directly from the
last coordinates of those very plane equations under C.g. -/
theorem prescribed_representatives (hp : 11 ≤ p) (hcard : S.card = p ^ 2)
    (hS : Geometry.PDivisible p S) (hnon : ¬Geometry.IsCylinder p S)
    (C : Chart (coordinatePoint p b)) (hb : b ∈ blackPoints p S)
    (v : directionSet p S b hb → Fin 3 → ZMod p) (hv : ∀ i, v i ≠ 0)
    (hpoint : ∀ i, Projectivization.mk (ZMod p) (v i) (hv i) =
      (ProjectionTransport.indexEquiv (whiteImage p S) (black_outside_whiteImage p hb) C i).val)
    (a c : DualPoint p → ZMod p) (ha : ∀ H, a H ≠ 0)
    (hnorm : ∀ i ν, tail (C.g (a (rayWhitePoint p hb i ν).val •
      dualCoordinates p (rayWhitePoint p hb i ν).val.rep)) = v i)
    (hc : ∀ H ∈ whitePoints p S, c H ≠ 0)
    (hprod : (∏ H ∈ blackPoints p S, scaledPlaneForm p a H ^ weight p S H) =
      ∑ E ∈ whitePoints p S, MvPolynomial.C (c E) *
        ∏ H ∈ (whitePoints p S).erase E, scaledPlaneForm p a H)
    (hpower : (∑ E ∈ whitePoints p S, MvPolynomial.C (c E) *
      scaledPlaneForm p a E ^ (p - 2)) = 0) :
    (∀ i, prescribedMoment p C hb a c i 0 = 0) ∧
    (∀ i, prescribedMoment p C hb a c i 1 ≠ 0) ∧
    PowerEvaluationRelation.Relation v (fun i => prescribedMoment p C hb a c i 1) (p - 3) ∧
    ∃! fg : MvPolynomial (Fin 3) (ZMod p) × MvPolynomial (Fin 3) (ZMod p),
      fg.1.IsHomogeneous 1 ∧ fg.2.IsHomogeneous 2 ∧
      (∀ i, prescribedMoment p C hb a c i 2 = eval (v i) fg.1 * prescribedMoment p C hb a c i 1) ∧
      (∀ i, prescribedMoment p C hb a c i 3 = eval (v i) fg.2 * prescribedMoment p C hb a c i 1) := by
  have hs (i : directionSet p S b hb) :
      ∃ u : (ZMod p)ˣ, v i = (u : ZMod p) • C.directionEquiv i.val.rep :=
    ProjectionTransport.arbitrary_representative_scale (whiteImage p S)
      (black_outside_whiteImage p hb) C i (v i) (hv i) (hpoint i)
  let lam : directionSet p S b hb → (ZMod p)ˣ := fun i => Classical.choose (hs i)
  have hdir : v = direction p C hb lam := funext (fun i => Classical.choose_spec (hs i))
  have hnorm' : ∀ i ν, tail (C.g (a (rayWhitePoint p hb i ν).val •
      dualCoordinates p (rayWhitePoint p hb i ν).val.rep)) = direction p C hb lam i := by
    simpa only [hdir] using hnorm
  have hm (i : directionSet p S b hb) (j : ℕ) := prescribedMoment_eq p C hb lam a c hnorm' i j
  have h := prescribed_coordinates p hp hcard hS hnon C hb lam a c ha hnorm' hc hprod hpower
  simpa only [← hdir, ← hm] using h

end Cylinder.ArbitraryMoments
end
