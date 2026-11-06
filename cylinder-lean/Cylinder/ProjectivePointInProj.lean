module

public import Cylinder.ProjectivePolynomialChart
public import Cylinder.AffineAmbientStalkQuotient
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
public import Mathlib.RingTheory.GradedAlgebra.Radical

/-! The canonical Proj point of an affine point is its homogeneous ray
vanishing prime. The actual standard-chart prime is precisely the
evaluation prime transported by the proved polynomial chart map. -/

@[expose] public section
noncomputable section
open scoped Classical
set_option autoImplicit false

namespace Cylinder.ProjectivePointInProj

open MvPolynomial Module AlgebraicGeometry
open Cylinder.ProjectivePolynomialChart Cylinder.CurvePolarLocal
open Cylinder.AffineIntersectionLocalRings Cylinder.AffineAmbientStalkQuotient
open Cylinder.ProjectiveChartData Cylinder.HilbertEvaluation
open Cylinder.CompleteIntersectionAffinePoints Cylinder.PlaneLineCoordinates

attribute [local instance] MvPolynomial.gradedAlgebra

variable {K : Type*} [Field K]

def evaluationIdeal (x : Fin 2 → K) : Ideal (HomogeneousPlanePolynomial (K := K)) :=
  Ideal.comap dehomogenize (pointIdeal x)

def rayIdeal (x : Fin 2 → K) : HomogeneousIdeal (grading K) :=
  (evaluationIdeal x).homogeneousCore (grading K)

instance rayIdeal_isPrime (x : Fin 2 → K) : (rayIdeal x).toIdeal.IsPrime := by
  have hprime : (evaluationIdeal x).IsPrime := by
    change (Ideal.comap dehomogenize (pointIdeal x)).IsPrime
    infer_instance
  exact hprime.homogeneousCore

theorem homogeneous_mem_rayIdeal (x : Fin 2 → K) (H : HomogeneousPlanePolynomial (K := K))
    (n : ℕ) (hH : H.IsHomogeneous n) :
    H ∈ rayIdeal x ↔ eval x (dehomogenize H) = 0 := by
  constructor
  · intro h
    exact Ideal.toIdeal_homogeneousCore_le (grading K) (evaluationIdeal x) h
  · intro h
    exact Ideal.mem_homogeneousCore_of_homogeneous_of_mem ⟨n, hH⟩ h

theorem coordinate_not_mem_rayIdeal (x : Fin 2 → K) :
    (X none : HomogeneousPlanePolynomial (K := K)) ∉ rayIdeal x := by
  intro h
  have hh := (homogeneous_mem_rayIdeal x (X none) 1 (isHomogeneous_X K none)).mp h
  simp only [dehomogenize_X_none, map_one] at hh
  exact one_ne_zero hh

def rayPoint (x : Fin 2 → K) : ProjectiveSpectrum (grading K) where
  asHomogeneousIdeal := rayIdeal x
  isPrime := inferInstance
  not_irrelevant_le h := coordinate_not_mem_rayIdeal x
    (h (HomogeneousIdeal.mem_irrelevant_of_mem (grading K) zero_lt_one (coordinate_mem K)))

theorem rayPoint_mem_standardOpen (x : Fin 2 → K) :
    rayPoint x ∈ Proj.basicOpen (grading K) (X none) :=
  coordinate_not_mem_rayIdeal x

theorem original_ray_membership (c : Chart K) (P : PlanePointModel.Plane K)
    (hP : c.line P.rep ≠ 0) (H : PlaneRing K) (n : ℕ) (hH : H.IsHomogeneous n) :
    c.coordinates H ∈ (rayPoint (c.affinePoint P)).asHomogeneousIdeal ↔ eval P.rep H = 0 := by
  change c.coordinates H ∈ rayIdeal (c.affinePoint P) ↔ eval P.rep H = 0
  rw [homogeneous_mem_rayIdeal (c.affinePoint P) (c.coordinates H) n
    (chartCoordinates_homogeneous c.a c.b c.ha c.hb H n hH)]
  change eval (normalizedAffinePoint c.a c.b c.ha c.hb P.rep)
    (dehomogenize (chartCoordinates c.a c.b c.ha c.hb H)) = 0 ↔ _
  rw [← affineForm_eq_dehomogenize, eval_affineForm_normalized c.a c.b c.ha c.hb P.rep hP H n hH]
  exact mul_eq_zero.trans (or_iff_right (pow_ne_zero n (inv_ne_zero hP)))

def rayChartPoint (x : Fin 2 → K) : PrimeSpectrum (ChartRing K) :=
  ProjIsoSpecTopComponent.ToSpec.toFun (𝒜 := grading K) (X none)
    ⟨rayPoint x, rayPoint_mem_standardOpen x⟩

theorem rayChartPoint_mk_mem (x : Fin 2 → K) (n : ℕ)
    (a : HomogeneousPlanePolynomial (K := K)) (ha : a ∈ grading K (n • (1 : ℕ))) :
    HomogeneousLocalization.Away.mk (grading K) (coordinate_mem K) n a ha ∈
      (rayChartPoint x).asIdeal ↔ eval x (dehomogenize a) = 0 := by
  let z : HomogeneousLocalization.NumDenSameDeg (grading K)
      (Submonoid.powers (X none : HomogeneousPlanePolynomial (K := K))) :=
    ⟨n • (1 : ℕ), ⟨a, ha⟩,
      ⟨X none ^ n, SetLike.pow_mem_graded n (coordinate_mem K)⟩, ⟨n, rfl⟩⟩
  have hmem : HomogeneousLocalization.Away.mk (grading K) (coordinate_mem K) n a ha ∈
      (rayChartPoint x).asIdeal ↔ a ∈ rayIdeal x :=
    ProjIsoSpecTopComponent.ToSpec.mk_mem_carrier
      (⟨rayPoint x, rayPoint_mem_standardOpen x⟩ :
        (ProjectiveSpectrum.basicOpen (grading K) (X none))) z
  exact hmem.trans (homogeneous_mem_rayIdeal x a n (by simpa using ha))

theorem rayChartPoint_eq_comap [Infinite K] (x : Fin 2 → K) :
    rayChartPoint x = PrimeSpectrum.comap (chartEquiv K).toRingHom (pointPrime x) := by
  apply PrimeSpectrum.ext
  ext q
  obtain ⟨n, a, ha, rfl⟩ := HomogeneousLocalization.Away.mk_surjective (grading K) (coordinate_mem K) q
  change HomogeneousLocalization.Away.mk (grading K) (coordinate_mem K) n a ha ∈
      (rayChartPoint x).asIdeal ↔
    eval x (chartEquiv K (HomogeneousLocalization.Away.mk (grading K) (coordinate_mem K) n a ha)) = 0
  rw [rayChartPoint_mk_mem, chartEquiv_mk]

end Cylinder.ProjectivePointInProj
end
