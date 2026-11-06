module

public import Cylinder.CoordinateChartLaurent
public import Cylinder.GlobalTwistCoordinateSections
public import Cylinder.PlaneLaurentCech

/-! Actual sections of the same global twisting sheaf on all three
coordinate charts are identified with their homogeneous Laurent
pieces. The identification keeps the literal homogeneous fractions. -/

@[expose] public section
noncomputable section
open scoped Classical Cylinder.CoordinateChartPermutation
open scoped Cylinder.GlobalTwistChartSections

namespace Cylinder.GlobalTwistChartLaurent

open MvPolynomial AlgebraicGeometry
open Cylinder.CoordinateLaurentLocalization Cylinder.CoordinateTwistChartModule
open Cylinder.CoordinateChartPermutation Cylinder.CoordinateChartLaurent
open Cylinder.PlaneLaurentPieces Cylinder.GlobalTwistChartFrame
open Cylinder.GlobalProjectiveTwist Cylinder.GlobalTwistLocalFractions

set_option autoImplicit false
attribute [local instance] MvPolynomial.gradedAlgebra

variable (K : Type*) [Field K] [Infinite K]

def chartSectionsEquiv (v : ℤ) (i : Index) :
    Γ(twist K v, coordinateOpen K i) ≃ₗ[K] piece (K := K) v {coordinateNumber i} :=
  (GlobalTwistCoordinateSections.sectionLinearEquiv K i v).symm.trans
    (chartLaurentEquiv K v i)

theorem chartSectionsEquiv_coordinateSection (v : ℤ) (i : Index)
    (c : CoordinateChartPermutation.coordinateRing K i) :
    chartSectionsEquiv K v i (GlobalTwistCoordinateSections.coordinateSection K i v c) =
      chartLaurentEquiv K v i c :=
  congrArg (chartLaurentEquiv K v i)
    ((GlobalTwistCoordinateSections.sectionLinearEquiv K i v).symm_apply_apply c)

theorem chartSectionsEquiv_fraction (v : ℤ) (i : Index) (m : ℕ) (H : PlaneRing K)
    (hH : H ∈ grading K (m • (1 : ℕ))) :
    chartSectionsEquiv K v i
      (GlobalTwistCoordinateSections.coordinateSection K i v
        (HomogeneousLocalization.Away.mk (grading K) (isHomogeneous_X K i) m H hH)) =
      chartPiecePermutation K v i ((PlaneLaurentChartBasis.chartPolynomialEquiv v).symm
        (CurvePolarLocal.dehomogenize (MvPolynomial.rename (Equiv.swap i none) H))) := by
  rw [chartSectionsEquiv_coordinateSection, chartLaurentEquiv_mk]

theorem inverse_fraction_value (v : ℤ) (i : Index) (m n : ℕ) (H : PlaneRing K)
    (hH : H ∈ grading K (m • (1 : ℕ))) (hd : (m : ℤ) - n = v)
    (q : coordinateOpen K i) :
    ((chartSectionsEquiv K v i).symm
      (chartLaurentEquiv K v i
        (HomogeneousLocalization.Away.mk (grading K) (isHomogeneous_X K i) m H hH))).val q =
      Localization.mk H ⟨X i ^ n,
        coordinate_power_avoids K i (coordinateOpen K i) le_rfl q n⟩ := by
  change (GlobalTwistCoordinateSections.sectionLinearEquiv K i v
    ((chartLaurentEquiv K v i).symm (chartLaurentEquiv K v i
      (HomogeneousLocalization.Away.mk (grading K) (isHomogeneous_X K i) m H hH)))).val q = _
  rw [LinearEquiv.symm_apply_apply]
  exact GlobalTwistCoordinateSections.sectionLinearEquiv_fraction K i v m n H hH hd q

abbrev OrderedZeroSections (v : ℤ) :=
  Γ(twist K v, coordinateOpen K none) ×
    Γ(twist K v, coordinateOpen K (some 0)) × Γ(twist K v, coordinateOpen K (some 1))

def zeroSectionsEquiv (v : ℤ) :
    OrderedZeroSections K v ≃ₗ[K] PlaneLaurentCech.ZeroCochains (K := K) v :=
  (chartSectionsEquiv K v none).prodCongr
    ((chartSectionsEquiv K v (some 0)).prodCongr (chartSectionsEquiv K v (some 1)))

theorem zeroSectionsEquiv_apply (v : ℤ) (s : OrderedZeroSections K v) :
    zeroSectionsEquiv K v s =
      (chartSectionsEquiv K v none s.1,
        chartSectionsEquiv K v (some 0) s.2.1, chartSectionsEquiv K v (some 1) s.2.2) := rfl

end Cylinder.GlobalTwistChartLaurent

end
