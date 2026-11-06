module

public import Cylinder.ProjectiveCompleteIntersectionCover
public import Cylinder.ProjectiveRayStalk
public import Cylinder.ProjectiveChartPointMap
public import Cylinder.ProjectiveIntersectionLocalLengths
public import Cylinder.AffineIntersectionStalkLengths

/-! All scheme points of the projective intersection, and their canonical
identification with the original geometric points over an algebraically closed field. -/

@[expose] public section
noncomputable section
open scoped Classical
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Cylinder.ProjectiveIntersectionSchemePoints

open AlgebraicGeometry MvPolynomial Module
open Cylinder.ProjectivePolynomialChart Cylinder.ProjectiveAffineOpen
open Cylinder.ProjectiveCompleteIntersectionCover Cylinder.ProjectivePointInProj
open Cylinder.ProjectiveChartPointMap Cylinder.ProjectiveRayStalk
open Cylinder.ProjectiveChartData Cylinder.HilbertEvaluation
open Cylinder.CurvePolarLocal Cylinder.HomogeneousAffineChart
open Cylinder.CompleteIntersectionAffineDimension Cylinder.CompleteIntersectionLocalLengths
open Cylinder.CompleteIntersectionKoszul
open Cylinder.ProjectiveIntersectionPoints Cylinder.ProjectiveIntersectionLocalLengths
open Cylinder.AffineIntersectionLocalRings Cylinder.AffineAmbientStalkQuotient

attribute [local instance] MvPolynomial.gradedAlgebra

variable {K : Type*} [Field K]

theorem homogeneous_chart_membership [Infinite K] (p : standardOpen K)
    (H : HomogeneousPlanePolynomial (K := K)) (n : ℕ) (hH : H.IsHomogeneous n) :
    dehomogenize H ∈ ((affineOpenIso K).hom p).asIdeal ↔
      H ∈ p.val.asHomogeneousIdeal := by
  rw [affineOpenIso_apply]
  change (chartEquiv K).symm (dehomogenize H) ∈
      (ProjIsoSpecTopComponent.ToSpec.toFun (𝒜 := grading K) (X none) p).asIdeal ↔ _
  have hh : H ∈ grading K (n • (1 : ℕ)) := by simpa using hH
  have hfrac : (chartEquiv K).symm (dehomogenize H) =
      HomogeneousLocalization.Away.mk (grading K) (coordinate_mem K) n H hh := by
    apply (chartEquiv K).injective
    rw [RingEquiv.apply_symm_apply, chartEquiv_mk]
  rw [hfrac]
  let z : HomogeneousLocalization.NumDenSameDeg (grading K)
      (Submonoid.powers (X none : HomogeneousPlanePolynomial (K := K))) :=
    ⟨n • (1 : ℕ), ⟨H, hh⟩,
      ⟨X none ^ n, SetLike.pow_mem_graded n (coordinate_mem K)⟩, ⟨n, rfl⟩⟩
  exact ProjIsoSpecTopComponent.ToSpec.mk_mem_carrier p z

abbrev SchemeCommonZero (c : Chart K) (F G : PlaneRing K) :=
  {q : ProjectiveSpectrum (grading K) //
    c.coordinates F ∈ q.asHomogeneousIdeal ∧ c.coordinates G ∈ q.asHomogeneousIdeal}

def zeroOpenEquiv (c : Chart K) (F G : PlaneRing K) (e t : ℕ)
    (he : 0 < e) (ht : 0 < t) (hF : F.IsHomogeneous e) (hG : G.IsHomogeneous t)
    (hgood : GoodChart c F G e t) :
    SchemeCommonZero c F G ≃
      {q : standardOpen K //
        c.coordinates F ∈ q.val.asHomogeneousIdeal ∧
        c.coordinates G ∈ q.val.asHomogeneousIdeal} where
  toFun q := ⟨⟨q.val, no_point_at_infinity c F G e t he ht hF hG hgood q.val
    q.property.1 q.property.2⟩, q.property⟩
  invFun q := ⟨q.val.val, q.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

def schemeEquivPrimeSpectrum [Infinite K] (c : Chart K) (F G : PlaneRing K) (e t : ℕ)
    (he : 0 < e) (ht : 0 < t) (hF : F.IsHomogeneous e) (hG : G.IsHomogeneous t)
    (hgood : GoodChart c F G e t) :
    SchemeCommonZero c F G ≃ PrimeSpectrum (ChartAlgebra c F G) := by
  let E : standardOpen K ≃ PrimeSpectrum (MvPolynomial (Fin 2) K) :=
    (affineOpenIso K).hom.homeomorph.toEquiv
  have hmem (p : standardOpen K) :
      (c.coordinates F ∈ p.val.asHomogeneousIdeal ∧
        c.coordinates G ∈ p.val.asHomogeneousIdeal) ↔
      E p ∈ PrimeSpectrum.zeroLocus
        (equationsIdeal (dehomogenize (c.coordinates F)) (dehomogenize (c.coordinates G))) := by
    have hcf := PlaneLineCoordinates.chartCoordinates_homogeneous c.a c.b c.ha c.hb F e hF
    have hcg := PlaneLineCoordinates.chartCoordinates_homogeneous c.a c.b c.ha c.hb G t hG
    have hf := homogeneous_chart_membership p (c.coordinates F) e hcf
    have hg := homogeneous_chart_membership p (c.coordinates G) t hcg
    change _ ↔ equationsIdeal _ _ ≤ (E p).asIdeal
    rw [CompleteIntersectionKoszul.equationsIdeal, Ideal.span_le]
    constructor
    · rintro ⟨hpf, hpg⟩ H hH
      rcases Set.mem_insert_iff.mp hH with rfl | hH
      · exact hf.mpr hpf
      · rw [Set.mem_singleton_iff] at hH
        exact hH ▸ hg.mpr hpg
    · intro hp
      exact ⟨hf.mp (hp (by simp)), hg.mp (hp (by simp))⟩
  exact (zeroOpenEquiv c F G e t he ht hF hG hgood).trans
    ((Equiv.subtypeEquiv E hmem).trans
      (Ideal.primeSpectrumQuotientOrderIsoZeroLocus
        (equationsIdeal (dehomogenize (c.coordinates F))
          (dehomogenize (c.coordinates G)))).toEquiv.symm)

@[instance_reducible] def schemeCommonZeroFintype [Infinite K] [IsAlgClosed K]
    (c : Chart K) (F G : PlaneRing K) (e t : ℕ)
    (he : 0 < e) (ht : 0 < t) (hF : F.IsHomogeneous e) (hG : G.IsHomogeneous t)
    (hgood : GoodChart c F G e t) : Fintype (SchemeCommonZero c F G) := by
  letI := chartAlgebra_finiteDimensional c F G e t he ht hgood
  letI : IsArtinianRing (ChartAlgebra c F G) := IsArtinianRing.of_finite K _
  letI := chartMaximalFintype c F G e t he ht hgood
  letI := AffineIntersectionStalkLengths.spectrumFintype (ChartAlgebra c F G)
  exact Fintype.ofEquiv (PrimeSpectrum (ChartAlgebra c F G))
    (schemeEquivPrimeSpectrum c F G e t he ht hF hG hgood).symm

def canonicalMap (c : Chart K) (F G : PlaneRing K) (e t : ℕ)
    (hF : F.IsHomogeneous e) (hG : G.IsHomogeneous t) (hgood : GoodChart c F G e t)
    (P : ProjectiveCommonZero F G) : SchemeCommonZero c F G := by
  have hp := hgood.avoids P.val.rep P.val.rep_nonzero P.property.1 P.property.2
  exact ⟨rayPoint (c.affinePoint P.val),
    (original_ray_membership c P.val hp F e hF).mpr P.property.1,
    (original_ray_membership c P.val hp G t hG).mpr P.property.2⟩

theorem pointPrime_injective : Function.Injective (pointPrime (K := K) (σ := Fin 2)) := by
  intro x y h
  funext i
  have hx : (X i - C (x i) : MvPolynomial (Fin 2) K) ∈ (pointPrime x).asIdeal := by
    change eval x (X i - C (x i)) = 0
    simp
  rw [h] at hx
  change eval y (X i - C (x i)) = 0 at hx
  simpa using (sub_eq_zero.mp (by simpa using hx)).symm

theorem canonicalMap_injective [Infinite K]
    (c : Chart K) (F G : PlaneRing K) (e t : ℕ)
    (hF : F.IsHomogeneous e) (hG : G.IsHomogeneous t) (hgood : GoodChart c F G e t) :
    Function.Injective (canonicalMap c F G e t hF hG hgood) := by
  intro P Q h
  have hxy : pointPrime (c.affinePoint P.val) = pointPrime (c.affinePoint Q.val) := by
    apply (affineEmbedding K).isOpenEmbedding.injective
    change affinePoint K (pointPrime (c.affinePoint P.val)) =
      affinePoint K (pointPrime (c.affinePoint Q.val))
    rw [affinePoint_eq_rayPoint, affinePoint_eq_rayPoint]
    exact congrArg Subtype.val h
  apply toAffine_injective c F G e t hF hG hgood
  exact Subtype.ext (pointPrime_injective hxy)

def canonicalEquiv [Infinite K] [IsAlgClosed K]
    (c : Chart K) (F G : PlaneRing K) (e t : ℕ)
    (he : 0 < e) (ht : 0 < t) (hF : F.IsHomogeneous e) (hG : G.IsHomogeneous t)
    (hgood : GoodChart c F G e t) : ProjectiveCommonZero F G ≃ SchemeCommonZero c F G := by
  letI := projectiveCommonZeroFintype c F G e t he ht hF hG hgood
  letI := schemeCommonZeroFintype c F G e t he ht hF hG hgood
  letI := chartAlgebra_finiteDimensional c F G e t he ht hgood
  letI : IsArtinianRing (ChartAlgebra c F G) := IsArtinianRing.of_finite K _
  let E : ProjectiveCommonZero F G ≃ SchemeCommonZero c F G :=
    (projectiveCommonZeroEquivMaximalSpectrum c F G e t he ht hF hG hgood).trans
      ((IsArtinianRing.primeSpectrumEquivMaximalSpectrum (R := ChartAlgebra c F G)).symm.trans
        (schemeEquivPrimeSpectrum c F G e t he ht hF hG hgood).symm)
  exact Equiv.ofBijective (canonicalMap c F G e t hF hG hgood)
    ((Fintype.bijective_iff_injective_and_card _).mpr
      ⟨canonicalMap_injective c F G e t hF hG hgood, Fintype.card_congr E⟩)

theorem canonicalEquiv_apply [Infinite K] [IsAlgClosed K]
    (c : Chart K) (F G : PlaneRing K) (e t : ℕ)
    (he : 0 < e) (ht : 0 < t) (hF : F.IsHomogeneous e) (hG : G.IsHomogeneous t)
    (hgood : GoodChart c F G e t) (P : ProjectiveCommonZero F G) :
    (canonicalEquiv c F G e t he ht hF hG hgood P).val =
      rayPoint (c.affinePoint P.val) := rfl

end Cylinder.ProjectiveIntersectionSchemePoints
end
