module

public import Cylinder.ProjectivePointInProj
public import Cylinder.ProjectiveChartPointMap

/-! The canonical ray point is the image of the corresponding affine
point under the actual standard open immersion. The induced stalk
isomorphism therefore compares stalks at the same original point. -/

@[expose] public section
noncomputable section
open scoped Classical
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Cylinder.ProjectiveRayStalk

open MvPolynomial Module AlgebraicGeometry CategoryTheory
open Cylinder.ProjectivePolynomialChart Cylinder.ProjectiveAffineOpen
open Cylinder.ProjectivePointInProj Cylinder.ProjectiveChartPointMap
open Cylinder.AffineAmbientStalkQuotient Cylinder.AffineIntersectionLocalRings

attribute [local instance] MvPolynomial.gradedAlgebra

variable (K : Type*) [Field K] [Infinite K]

theorem affineOpenIso_rayPoint (x : Fin 2 → K) :
    (affineOpenIso K).hom ⟨rayPoint x, rayPoint_mem_standardOpen x⟩ = pointPrime x := by
  rw [affineOpenIso_apply]
  change PrimeSpectrum.comap (chartEquiv K).symm.toRingHom (rayChartPoint x) = pointPrime x
  rw [rayChartPoint_eq_comap]
  apply PrimeSpectrum.ext
  ext P
  change eval x (chartEquiv K ((chartEquiv K).symm P)) = 0 ↔ eval x P = 0
  rw [RingEquiv.apply_symm_apply]

theorem affinePoint_eq_rayPoint (x : Fin 2 → K) :
    ProjectiveAffineOpen.affinePoint K (pointPrime x) = rayPoint x := by
  let q : standardOpen K := ⟨rayPoint x, rayPoint_mem_standardOpen x⟩
  have hq : (affineOpenIso K).inv ((affineOpenIso K).hom q) = q := by
    change ((affineOpenIso K).hom ≫ (affineOpenIso K).inv) q = q
    rw [Iso.hom_inv_id]
    rfl
  change ((affineOpenIso K).inv (pointPrime x)).val = rayPoint x
  rw [← affineOpenIso_rayPoint K x]
  exact congrArg Subtype.val hq

def canonicalStalkEquiv (x : Fin 2 → K) :
    (projectivePlane K).presheaf.stalk (rayPoint x) ≃+* AmbientStalk x := by
  let i := (projectivePlane K).presheaf.stalkCongr (.of_eq (affinePoint_eq_rayPoint K x))
  exact i.symm.commRingCatIsoToRingEquiv.trans (ProjectiveAffineOpen.stalkEquiv K (pointPrime x))

end Cylinder.ProjectiveRayStalk
end
