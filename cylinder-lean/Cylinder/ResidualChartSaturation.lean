module

public import Cylinder.ResidualSaturation
public import Cylinder.HomogeneousCompleteIntersection
public import Cylinder.ResidualCoordinateTransport

/-! Actual avoiding polynomial coordinates prove saturation of the
original plane complete-intersection ideal and every residual colon. -/

@[expose] public section
noncomputable section

namespace Cylinder.ResidualChartSaturation

open MvPolynomial Cylinder.HilbertEvaluation Cylinder.SaturatedPlaneLine
open Cylinder.ResidualSaturation Cylinder.HomogeneousCompleteIntersection
open Cylinder.ResidualCoordinateTransport Cylinder.CompleteIntersectionKoszul
open Cylinder.CurvePolarLocal
open scoped Classical

variable {K R S : Type*} [Field K] [CommRing R] [CommRing S] [Algebra K R] [Algebra K S]

theorem regular_comap (e : R ≃ₐ[K] S) (J : Ideal S) (a : S) (hregular : J.colon {a} = J) :
    (Ideal.comap e J).colon {e.symm a} = Ideal.comap e J := by
  apply le_antisymm
  · intro P hP
    apply regular_cancel J a (e P) hregular
    have hp := Submodule.mem_colon_singleton.mp hP
    change e (P * e.symm a) ∈ J at hp
    rw [map_mul, e.apply_symm_apply, mul_comm] at hp
    exact hp
  · exact Ideal.le_colon

theorem linear_mem_irrelevant (L : PlaneRing K) (hL : L.IsHomogeneous 1) :
    L ∈ irrelevant (K := K) := by
  have hspan : Submodule.span K (Set.range (X : Fin 3 → PlaneRing K)) ≤
      (irrelevant (K := K)).restrictScalars K :=
    Submodule.span_le.mpr (fun P hP => Ideal.subset_span hP)
  apply hspan
  rw [← homogeneousSubmodule_one_eq_span_X]
  exact hL

/-- The genuine avoiding-chart top forms prove saturation of the actual
original equations; residual ideals consequently are genuinely saturated. -/
theorem equations_residual_saturated (e : PlaneRing K ≃ₐ[K] HomRing (K := K))
    (F G : PlaneRing K) (a b : ℕ)
    (hF : (e F).IsHomogeneous a) (hG : (e G).IsHomogeneous b)
    (hf : (dehomogenize (e F)).totalDegree = a) (hg : (dehomogenize (e G)).totalDegree = b)
    (hfe : homogeneousComponent a (dehomogenize (e F)) ≠ 0)
    (hcop : IsRelPrime (homogeneousComponent a (dehomogenize (e F)))
      (homogeneousComponent b (dehomogenize (e G))))
    (hL : (e.symm (X none)).IsHomogeneous 1) :
    Saturated (equationsIdeal F G) ∧ ∀ D : Ideal (PlaneRing K),
      Saturated ((equationsIdeal F G).colon (D : Set (PlaneRing K))) := by
  have hc := coordinate_colon_eq (e F) (e G) a b hF hG hf hg hfe hcop
  have hreg := regular_comap e (equationsIdeal (e F) (e G)) (X none) hc
  rw [equationsIdeal_comap e F G] at hreg
  have hsat := saturated_of_regular_chart (equationsIdeal F G) (e.symm (X none))
    (linear_mem_irrelevant _ hL) hreg
  exact ⟨hsat, fun D => residual_saturated (equationsIdeal F G) D hsat⟩

#print axioms regular_comap
#print axioms linear_mem_irrelevant
#print axioms equations_residual_saturated

end Cylinder.ResidualChartSaturation

end
