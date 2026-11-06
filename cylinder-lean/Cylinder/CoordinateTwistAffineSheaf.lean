module

public import Cylinder.CoordinateTwistChartModule
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic

/-! The true homogeneous-fraction module determines a quasicoherent
module sheaf on the actual standard affine open of Proj. These local
objects have not yet been glued to a global twisting sheaf. -/

@[expose] public section
noncomputable section
open scoped Classical

universe u

namespace Cylinder.CoordinateTwistAffineSheaf

open AlgebraicGeometry CategoryTheory Opposite MvPolynomial
open Cylinder.CoordinateLaurentLocalization Cylinder.CoordinateTwistChartModule

set_option autoImplicit false
attribute [local instance] MvPolynomial.gradedAlgebra

variable (K : Type u) [CommRing K]

abbrev coordinateSpec : Scheme.{u} := Spec (CommRingCat.of (chartRing K))

def moduleObject (v : ℤ) : ModuleCat.{u} (chartRing K) :=
  ModuleCat.of (chartRing K) (twistModule K v)

def affineSheaf (v : ℤ) : (coordinateSpec K).Modules :=
  AlgebraicGeometry.tilde (R := CommRingCat.of (chartRing K)) (moduleObject K v)

instance affineSheaf_quasicoherent (v : ℤ) : (affineSheaf K v).IsQuasicoherent := by
  exact inferInstanceAs (AlgebraicGeometry.tilde
    (R := CommRingCat.of (chartRing K)) (moduleObject K v)).IsQuasicoherent

/-- The sections of the actual tilde sheaf recover the genuine local
homogeneous-fraction module with its coordinate-ring action. -/
def globalSectionsEquiv (v : ℤ) :
    twistModule K v ≃ₗ[chartRing K]
      (modulesSpecToSheaf.obj (affineSheaf K v)).presheaf.obj (op ⊤) :=
  (AlgebraicGeometry.tilde.isoTop (R := CommRingCat.of (chartRing K))
    (moduleObject K v)).toLinearEquiv

def toOpen (v : ℤ) (U : (coordinateSpec K).Opens) :
    moduleObject K v ⟶
      (modulesSpecToSheaf.obj (affineSheaf K v)).presheaf.obj (op U) :=
  AlgebraicGeometry.tilde.toOpen (R := CommRingCat.of (chartRing K)) (moduleObject K v) U

theorem toOpen_restrict (v : ℤ) (U V : (coordinateSpec K).Opens) (i : V ⟶ U) :
    toOpen K v U ≫ (modulesSpecToSheaf.obj (affineSheaf K v)).presheaf.map i.op =
      toOpen K v V :=
  AlgebraicGeometry.tilde.toOpen_res (R := CommRingCat.of (chartRing K))
    (moduleObject K v) U V i

set_option backward.isDefEq.respectTransparency.types false in
/-- Restricting the genuine local module to a basic open has the
actual module-localization universal property. -/
instance toBasicOpen_localized (v : ℤ) (f : chartRing K) :
    IsLocalizedModule.Away f (toOpen K v (PrimeSpectrum.basicOpen f)).hom := by
  exact IsLocalizedModule.of_linearEquiv (.powers f)
    (StructureSheaf.toOpenₗ (CommRingCat.of (chartRing K)) (moduleObject K v)
      (PrimeSpectrum.basicOpen f))
    ((AlgebraicGeometry.tilde.modulesSpecToSheafIso
      (R := CommRingCat.of (chartRing K)) (moduleObject K v)).app _).toLinearEquiv.symm

abbrev standardOpen : (Proj (grading K)).Opens :=
  Proj.basicOpen (grading K) (X none)

def standardOpenIso : (standardOpen K).toScheme ≅ coordinateSpec K :=
  Proj.basicOpenIsoSpec (grading K) (X none) (coordinate_mem K) zero_lt_one

/-- This is an actual module sheaf on the standard open of Proj,
obtained by restricting along the genuine affine-chart isomorphism. -/
def standardOpenSheaf (v : ℤ) : (standardOpen K).toScheme.Modules :=
  (affineSheaf K v).restrict (standardOpenIso K).hom

instance standardOpenSheaf_quasicoherent (v : ℤ) :
    (standardOpenSheaf K v).IsQuasicoherent := by
  exact inferInstanceAs
    ((affineSheaf K v).restrict (standardOpenIso K).hom).IsQuasicoherent

end Cylinder.CoordinateTwistAffineSheaf

end
