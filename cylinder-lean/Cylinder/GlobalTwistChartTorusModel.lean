module

public import Cylinder.GlobalTwistChartLaurent
public import Cylinder.GlobalTwistTorusCompatibility
public import Cylinder.PlaneLaurentTorusSubstitution

/-! The actual coordinate-chart section model has its literal value
in the common torus. Thus comparison of chart sections uses the same
homogeneous Laurent coefficients as the ordered Čech model. -/

@[expose] public section
noncomputable section
open scoped Classical Cylinder.GlobalTwistChartSections Cylinder.CoordinateChartPermutation
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Cylinder.GlobalTwistChartTorusModel

open AlgebraicGeometry
open Cylinder.CoordinateLaurentLocalization Cylinder.CoordinateChartLaurent
open Cylinder.GlobalProjectiveTwist Cylinder.GlobalTwistChartFrame
open Cylinder.GlobalTwistChartLaurent Cylinder.PlaneLaurentCommonTorus
open Cylinder.GlobalTwistTorusCompatibility Cylinder.ChartTorusEvaluation

attribute [local instance] MvPolynomial.gradedAlgebra

variable (K : Type*) [Field K] [Infinite K]

theorem chartSectionsEquiv_torusValue (v : ℤ) (i : CoordinateChartPermutation.Index)
    (s : Γ(twist K v, coordinateOpen K i)) :
    commonPieceMap K v {coordinateNumber i} (chartSectionsEquiv K v i s) =
      torusValue K i v s := by
  change commonPieceMap K v {coordinateNumber i}
    (chartPiecePermutation K v i
      ((PlaneLaurentChartBasis.chartPolynomialEquiv v).symm
        (affineEquiv K i ((GlobalTwistCoordinateSections.sectionLinearEquiv K i v).symm s)))) = _
  rw [PlaneLaurentTorusSubstitution.commonPieceMap_chartPolynomial]
  unfold torusValue
  rw [coordinateRingMap_eq_normalized]

theorem chartSectionsEquiv_symm_torusValue (v : ℤ) (i : CoordinateChartPermutation.Index)
    (f : PlaneLaurentPieces.piece (K := K) v {coordinateNumber i}) :
    torusValue K i v ((chartSectionsEquiv K v i).symm f) = commonPieceMap K v {coordinateNumber i} f := by
  rw [← chartSectionsEquiv_torusValue, LinearEquiv.apply_symm_apply]

end Cylinder.GlobalTwistChartTorusModel

end
