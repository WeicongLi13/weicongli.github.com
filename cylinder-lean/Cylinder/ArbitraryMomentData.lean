module

public import Cylinder.ProjectionChart
public import Cylinder.ProjectionTransport
public import Cylinder.MomentResidueChange
public import Cylinder.MomentCoordinateFixedResidues
public import Cylinder.MomentCoordinateTransport

/-! Actual prescribed product residues and ray coordinates in an arbitrary
centre-adapted chart.  The white representative scales are arbitrary units;
the remaining plane equations also have arbitrary nonzero scales. -/

@[expose] public section
noncomputable section
open scoped Classical BigOperators LinearAlgebra.Projectivization
namespace Cylinder.ArbitraryMomentData
open MvPolynomial Cylinder.ProjectiveGeometry Cylinder.ProjectiveBalance
open Cylinder.BlackProjection Cylinder.ProjectionChart Cylinder.EvaluationProjection
open Cylinder.ExactRayMomentsNormalization Cylinder.ExactRayMomentsResidueRelation
open Cylinder.ExactRayMomentsCanonicalTimes Cylinder.ExactRayMomentsCoordinates
open Cylinder.MomentResidueChange Cylinder.FinalGlobalMoments
open Cylinder.MomentCoordinateTransport Cylinder.MomentCoordinateFixedResidues

variable (p : ℕ) [Fact p.Prime]
variable {S : Finset (Geometry.Point p)} {b : DualPoint p}

/-- The originally fixed plane equations for the chosen white direction
representatives; all other plane equations retain arbitrary unit scales. -/
def planeScale (hb : b ∈ blackPoints p S)
    (lam : directionSet p S b hb → (ZMod p)ˣ) (β : DualPoint p → (ZMod p)ˣ)
    (H : DualPoint p) : ZMod p :=
  (if hH : H ∈ whitePoints p S then
    (lam ((rayWhiteEquiv p hb).symm ⟨H, hH⟩).1 : ZMod p) else (β H : ZMod p)) *
      normalizationScale p b H

theorem planeScale_ne_zero (hb : b ∈ blackPoints p S)
    (lam : directionSet p S b hb → (ZMod p)ˣ) (β : DualPoint p → (ZMod p)ˣ)
    (H : DualPoint p) : planeScale p hb lam β H ≠ 0 := by
  unfold planeScale
  split_ifs <;> exact mul_ne_zero (Units.ne_zero _) (normalizationScale_nonzero p b H)

theorem planeScale_ray (hb : b ∈ blackPoints p S)
    (lam : directionSet p S b hb → (ZMod p)ˣ) (β : DualPoint p → (ZMod p)ˣ)
    (i : directionSet p S b hb) (ν : Fin (raySize p S b hb i)) :
    planeScale p hb lam β (rayWhitePoint p hb i ν).val =
      (lam i : ZMod p) * normalizationScale p b (rayWhitePoint p hb i ν).val := by
  unfold planeScale
  rw [dif_pos (rayWhitePoint p hb i ν).property]
  have h : (rayWhiteEquiv p hb).symm (rayWhitePoint p hb i ν) = ⟨i, ν⟩ :=
    (rayWhiteEquiv p hb).symm_apply_apply ⟨i, ν⟩
  rw [h]

def direction (C : Chart (coordinatePoint p b)) (hb : b ∈ blackPoints p S)
    (lam : directionSet p S b hb → (ZMod p)ˣ) (i : directionSet p S b hb) : Fin 3 → ZMod p :=
  (lam i : ZMod p) • C.directionEquiv i.val.rep

def time (C : Chart (coordinatePoint p b)) (hb : b ∈ blackPoints p S)
    (lam : directionSet p S b hb → (ZMod p)ˣ)
    (i : directionSet p S b hb) (ν : Fin (raySize p S b hb i)) : ZMod p :=
  (lam i : ZMod p) * (C.timeShift i.val.rep + (C.c : ZMod p) *
    ProjectiveProjection.rayTimes (ZMod p) (Fin 3) (whiteImage p S)
      (coordinatePoint p b) (black_outside_whiteImage p hb) i ν)

def actualMoment (C : Chart (coordinatePoint p b)) (hb : b ∈ blackPoints p S)
    (lam : directionSet p S b hb → (ZMod p)ˣ) (c : DualPoint p → ZMod p)
    (i : directionSet p S b hb) (j : ℕ) : ZMod p :=
  ∑ ν : Fin (raySize p S b hb i), c (rayWhitePoint p hb i ν).val * time p C hb lam i ν ^ j

theorem direction_ne_zero (C : Chart (coordinatePoint p b)) (hb : b ∈ blackPoints p S)
    (lam : directionSet p S b hb → (ZMod p)ˣ) (i : directionSet p S b hb) :
    direction p C hb lam i ≠ 0 := by
  apply smul_ne_zero (lam i).ne_zero
  exact fun h => i.val.rep_nonzero (C.directionEquiv.injective (by simpa using h))

theorem time_injective (C : Chart (coordinatePoint p b)) (hb : b ∈ blackPoints p S)
    (lam : directionSet p S b hb → (ZMod p)ˣ) (i : directionSet p S b hb) :
    Function.Injective (time p C hb lam i) := by
  intro ν μ h
  apply ProjectiveProjection.rayTimes_injective (ZMod p) (Fin 3) (whiteImage p S)
    (coordinatePoint p b) (black_outside_whiteImage p hb) i
  exact mul_left_cancel₀ C.c.ne_zero (add_left_cancel (mul_left_cancel₀ (lam i).ne_zero h))

/-- The displayed time is the last coordinate of the actual original white
point after the prescribed linear change and prescribed representative scale. -/
theorem actual_vector (C : Chart (coordinatePoint p b)) (hb : b ∈ blackPoints p S)
    (lam : directionSet p S b hb → (ZMod p)ˣ) (β : DualPoint p → (ZMod p)ˣ)
    (i : directionSet p S b hb) (ν : Fin (raySize p S b hb i)) :
    C.g (planeScale p hb lam β (rayWhitePoint p hb i ν).val •
      dualCoordinates p (rayWhitePoint p hb i ν).val.rep) =
      rayPoint (direction p C hb lam i) (time p C hb lam i ν) := by
  have h := congrArg C.transition (normalized_vector_eq_ray_point p hb i ν)
  rw [C.transition_rayPoint] at h
  have h' := congrArg (fun v => (lam i : ZMod p) • v) h
  rw [planeScale_ray]
  simpa [Chart.transition, transformedCoordinates, direction, time, map_smul,
    smul_smul, ProjectionTransport.smul_rayPoint] using h'

/-- A plane equation normalized to the prescribed new direction has the
forced scalar ratio lam on its ray.  The assumption is the actual spatial
coordinate equality, not an assumed relation between two residue families. -/
theorem normalized_scale (C : Chart (coordinatePoint p b)) (hb : b ∈ blackPoints p S)
    (lam : directionSet p S b hb → (ZMod p)ˣ) (a : DualPoint p → ZMod p)
    (i : directionSet p S b hb) (ν : Fin (raySize p S b hb i))
    (hnorm : tail (C.g (a (rayWhitePoint p hb i ν).val •
      dualCoordinates p (rayWhitePoint p hb i ν).val.rep)) = direction p C hb lam i) :
    a (rayWhitePoint p hb i ν).val =
      (lam i : ZMod p) * normalizationScale p b (rayWhitePoint p hb i ν).val := by
  let E := (rayWhitePoint p hb i ν).val
  have ha₀ := normalizationScale_nonzero p b E
  have hcanon := congrArg C.transition (normalized_vector_eq_ray_point p hb i ν)
  rw [C.transition_rayPoint] at hcanon
  have htail : tail (C.g (normalizationScale p b E • dualCoordinates p E.rep)) =
      C.directionEquiv i.val.rep := by
    have h := congrArg tail hcanon
    simpa [Chart.transition, transformedCoordinates, map_smul, tail, rayPoint, E] using h
  have hratio : (a E / normalizationScale p b E) • C.directionEquiv i.val.rep =
      (lam i : ZMod p) • C.directionEquiv i.val.rep := by
    rw [← htail, ← map_smul, ← map_smul, smul_smul, div_mul_cancel₀ _ ha₀]
    rw [htail]
    exact hnorm
  have hne : C.directionEquiv i.val.rep ≠ 0 :=
    fun h => i.val.rep_nonzero (C.directionEquiv.injective (by simpa using h))
  exact (div_eq_iff ha₀).mp (smul_left_injective (ZMod p) hne hratio)

/-- Every preassigned nonzero family of plane equations normalized to the
given white representatives occurs in `planeScale`; nothing is reselected. -/
theorem planeScale_exhaustive (C : Chart (coordinatePoint p b)) (hb : b ∈ blackPoints p S)
    (lam : directionSet p S b hb → (ZMod p)ˣ) (a : DualPoint p → ZMod p)
    (ha : ∀ E, a E ≠ 0)
    (hnorm : ∀ i ν, tail (C.g (a (rayWhitePoint p hb i ν).val •
      dualCoordinates p (rayWhitePoint p hb i ν).val.rep)) = direction p C hb lam i) :
    ∃ β : DualPoint p → (ZMod p)ˣ, planeScale p hb lam β = a := by
  let β : DualPoint p → (ZMod p)ˣ := fun E =>
    Units.mk0 (a E / normalizationScale p b E)
      (div_ne_zero (ha E) (normalizationScale_nonzero p b E))
  refine ⟨β, ?_⟩
  funext E
  unfold planeScale
  split_ifs with hE
  · let x := (rayWhiteEquiv p hb).symm ⟨E, hE⟩
    have hx : (rayWhitePoint p hb x.1 x.2).val = E :=
      congrArg Subtype.val ((rayWhiteEquiv p hb).apply_symm_apply ⟨E, hE⟩)
    have h := normalized_scale p C hb lam a x.1 x.2 (hnorm x.1 x.2)
    rw [hx] at h
    exact h.symm
  · exact div_mul_cancel₀ _ (normalizationScale_nonzero p b E)

/-- Identification of the affine time with the actual final coordinate of
any already prescribed normalized plane equation. -/
theorem time_eq_actual (C : Chart (coordinatePoint p b)) (hb : b ∈ blackPoints p S)
    (lam : directionSet p S b hb → (ZMod p)ˣ) (a : DualPoint p → ZMod p)
    (i : directionSet p S b hb) (ν : Fin (raySize p S b hb i))
    (hnorm : tail (C.g (a (rayWhitePoint p hb i ν).val •
      dualCoordinates p (rayWhitePoint p hb i ν).val.rep)) = direction p C hb lam i) :
    time p C hb lam i ν =
      C.g (a (rayWhitePoint p hb i ν).val • dualCoordinates p (rayWhitePoint p hb i ν).val.rep) none := by
  have h := actual_vector p C hb lam (fun _ => 1) i ν
  rw [planeScale_ray, ← normalized_scale p C hb lam a i ν hnorm] at h
  exact (congrArg (fun v => v none) h).symm

def prescribedMoment (C : Chart (coordinatePoint p b)) (hb : b ∈ blackPoints p S)
    (a c : DualPoint p → ZMod p) (i : directionSet p S b hb) (j : ℕ) : ZMod p :=
  ∑ ν : Fin (raySize p S b hb i), c (rayWhitePoint p hb i ν).val *
    C.g (a (rayWhitePoint p hb i ν).val • dualCoordinates p (rayWhitePoint p hb i ν).val.rep) none ^ j

theorem prescribedMoment_any_enumeration {J : Type*} [Fintype J]
    (C : Chart (coordinatePoint p b)) (hb : b ∈ blackPoints p S)
    (a c : DualPoint p → ZMod p) (i : directionSet p S b hb)
    (e : J ≃ Fin (raySize p S b hb i)) (j : ℕ) :
    (∑ ν : J, c (rayWhitePoint p hb i (e ν)).val *
      C.g (a (rayWhitePoint p hb i (e ν)).val •
        dualCoordinates p (rayWhitePoint p hb i (e ν)).val.rep) none ^ j) =
      prescribedMoment p C hb a c i j := by
  exact e.sum_comp (fun ν => c (rayWhitePoint p hb i ν).val *
    C.g (a (rayWhitePoint p hb i ν).val • dualCoordinates p (rayWhitePoint p hb i ν).val.rep) none ^ j)

theorem prescribedMoment_eq (C : Chart (coordinatePoint p b)) (hb : b ∈ blackPoints p S)
    (lam : directionSet p S b hb → (ZMod p)ˣ) (a c : DualPoint p → ZMod p)
    (hnorm : ∀ i ν, tail (C.g (a (rayWhitePoint p hb i ν).val •
      dualCoordinates p (rayWhitePoint p hb i ν).val.rep)) = direction p C hb lam i)
    (i : directionSet p S b hb) (j : ℕ) :
    prescribedMoment p C hb a c i j = actualMoment p C hb lam c i j := by
  unfold prescribedMoment actualMoment
  apply Finset.sum_congr rfl
  intro ν _
  rw [time_eq_actual p C hb lam a i ν (hnorm i ν)]

def canonicalResidues (hb : b ∈ blackPoints p S)
    (lam : directionSet p S b hb → (ZMod p)ˣ) (β : DualPoint p → (ZMod p)ˣ)
    (c : DualPoint p → ZMod p) : DualPoint p → ZMod p :=
  residueChange p S (planeScale p hb lam β) (normalizationScale p b) c

def productScale (hb : b ∈ blackPoints p S)
    (lam : directionSet p S b hb → (ZMod p)ˣ) (β : DualPoint p → (ZMod p)ˣ) : ZMod p :=
  globalRatio p S (planeScale p hb lam β) (normalizationScale p b)

theorem productScale_ne_zero (hb : b ∈ blackPoints p S)
    (lam : directionSet p S b hb → (ZMod p)ˣ) (β : DualPoint p → (ZMod p)ˣ) :
    productScale p hb lam β ≠ 0 :=
  globalRatio_ne_zero p S _ _ (planeScale_ne_zero p hb lam β) (normalizationScale_nonzero p b)

theorem residue_on_ray (hb : b ∈ blackPoints p S)
    (lam : directionSet p S b hb → (ZMod p)ˣ) (β : DualPoint p → (ZMod p)ˣ)
    (c : DualPoint p → ZMod p) (i : directionSet p S b hb) (ν : Fin (raySize p S b hb i)) :
    c (rayWhitePoint p hb i ν).val = productScale p hb lam β * (lam i : ZMod p) *
      canonicalResidues p hb lam β c (rayWhitePoint p hb i ν).val := by
  have h := residueChange_spec p S (planeScale p hb lam β) (normalizationScale p b) c
    (planeScale_ne_zero p hb lam β) (normalizationScale_nonzero p b)
    (rayWhitePoint p hb i ν).val
  simpa only [productScale, canonicalResidues, scaleRatio, planeScale_ray, mul_div_cancel_right₀ _
    (normalizationScale_nonzero p b (rayWhitePoint p hb i ν).val)] using h

/-- The fixed new residues, not a new existentially selected family, are
exactly the rescaled canonical weights in the finite affine moment formula. -/
theorem actualMoment_eq (C : Chart (coordinatePoint p b)) (hb : b ∈ blackPoints p S)
    (lam : directionSet p S b hb → (ZMod p)ˣ) (β : DualPoint p → (ZMod p)ˣ)
    (c : DualPoint p → ZMod p) (i : directionSet p S b hb) (j : ℕ) :
    actualMoment p C hb lam c i j =
      moment (fun ν => (lam i : ZMod p) * (C.timeShift i.val.rep + (C.c : ZMod p) *
        ProjectiveProjection.rayTimes (ZMod p) (Fin 3) (whiteImage p S)
          (coordinatePoint p b) (black_outside_whiteImage p hb) i ν))
        (fun ν => (productScale p hb lam β * (lam i : ZMod p)) *
          rayResidues p hb (canonicalResidues p hb lam β c) i ν) j := by
  unfold actualMoment moment
  apply Finset.sum_congr rfl
  intro ν _
  rw [residue_on_ray p hb lam β c i ν]
  rfl

end Cylinder.ArbitraryMomentData
end
