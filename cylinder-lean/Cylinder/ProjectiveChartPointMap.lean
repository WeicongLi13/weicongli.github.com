module

public import Cylinder.ProjectiveAffineOpen

/-! The point map of the genuine scheme affine-chart isomorphism is
the explicit homogeneous localization prime map used in the construction. -/

@[expose] public section
noncomputable section
open scoped Classical
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Cylinder.ProjectiveChartPointMap

open AlgebraicGeometry CategoryTheory MvPolynomial
open Cylinder.ProjectivePolynomialChart Cylinder.ProjectiveAffineOpen
open Cylinder.CurvePolarLocal

attribute [local instance] MvPolynomial.gradedAlgebra

variable (K : Type*) [Field K] [Infinite K]

omit [Infinite K] in
theorem basicOpenToSpec_toLRSHom :
    (Proj.basicOpenToSpec (grading K) (X none)).toLRSHom =
      ProjectiveSpectrum.Proj.toSpec (grading K) (X none) := by
  refine Eq.trans ?_ (ΓSpec.locallyRingedSpaceAdjunction.homEquiv_apply _ _ _).symm
  dsimp [Proj.basicOpenToSpec, Scheme.Opens.toSpecΓ]
  simp only [Category.assoc, ← Spec.map_comp]
  rfl

theorem basicOpenIsoSpec_apply (p : standardOpen K) :
    (Proj.basicOpenIsoSpec (grading K) (X none) (coordinate_mem K) zero_lt_one).hom p =
      ProjIsoSpecTopComponent.ToSpec.toFun (𝒜 := grading K) (X none) p := by
  have h := congrArg (fun f => f.base p) (basicOpenToSpec_toLRSHom K)
  exact h.trans (ProjectiveSpectrum.Proj.toSpec_base_apply_eq (grading K) p)

theorem affineOpenIso_apply (p : standardOpen K) :
    (affineOpenIso K).hom p =
      PrimeSpectrum.comap (chartEquiv K).symm.toRingHom
        (ProjIsoSpecTopComponent.ToSpec.toFun (𝒜 := grading K) (X none) p) := by
  change PrimeSpectrum.comap (chartEquiv K).symm.toRingHom
      ((Proj.basicOpenIsoSpec (grading K) (X none) (coordinate_mem K) zero_lt_one).hom p) = _
  rw [basicOpenIsoSpec_apply]

end Cylinder.ProjectiveChartPointMap
end
