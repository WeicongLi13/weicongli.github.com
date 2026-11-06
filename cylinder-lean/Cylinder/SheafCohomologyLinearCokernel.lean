module

public import Cylinder.SheafCohomologyScalarAction
public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.LinearAlgebra.Dimension.Finrank

/-! The genuine sheaf-cohomology connecting homomorphism, and hence the
section-cokernel description of H¹, are linear for the canonical scalar
action induced by scalar sheaf endomorphisms. -/

@[expose] public section
noncomputable section

universe w u

namespace Cylinder.SheafCohomologyLinearCokernel

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf Opposite
open Cylinder.SheafCohomologyScalarAction
open scoped Cylinder.SheafCohomologyScalarAction

set_option autoImplicit false

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  {K : Type u} [CommRing K]
  [HasSheafify J AddCommGrpCat.{u}] [HasExt.{w} (Sheaf J AddCommGrpCat.{u})]

/-- The actual underlying short complex of additive sheaves. -/
abbrev additiveComplex (S : ShortComplex (Sheaf J (ModuleCat.{u} K))) :
    ShortComplex (Sheaf J AddCommGrpCat.{u}) :=
  ShortComplex.mk (forgetModules.map S.f) (forgetModules.map S.g) (by
    rw [← Functor.map_comp, S.zero, Functor.map_zero])

/-- Scalar multiplication on all three sheaves is a genuine morphism of
the underlying short complex. -/
def scalarComplexMap (S : ShortComplex (Sheaf J (ModuleCat.{u} K))) (a : K) :
    additiveComplex S ⟶ additiveComplex S where
  τ₁ := scalarMap S.X₁ a
  τ₂ := scalarMap S.X₂ a
  τ₃ := scalarMap S.X₃ a
  comm₁₂ := scalarMap_naturality S.f a
  comm₂₃ := scalarMap_naturality S.g a

/-- Naturality of the true Ext connecting map gives scalar linearity. -/
def connectingLinear {S : ShortComplex (Sheaf J (ModuleCat.{u} K))}
    (hS : (additiveComplex S).ShortExact) (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    Sheaf.H (forgetModules.obj S.X₃) n₀ →ₗ[K] Sheaf.H (forgetModules.obj S.X₁) n₁ where
  toFun := Sheaf.H.δ hS n₀ n₁ h
  map_add' := (Sheaf.H.δ hS n₀ n₁ h).map_add
  map_smul' a x := by
    change Sheaf.H.δ hS n₀ n₁ h (Sheaf.H.map (scalarMap S.X₃ a) n₀ x) =
      Sheaf.H.map (scalarMap S.X₁ a) n₁ (Sheaf.H.δ hS n₀ n₁ h x)
    exact Sheaf.H.δ_naturality n₀ n₁ h hS hS (scalarComplexMap S a) x

def globalSectionsMapLinear (S : ShortComplex (Sheaf J (ModuleCat.{u} K))) (T : C) :
    S.X₂.obj.obj (op T) →ₗ[K] S.X₃.obj.obj (op T) :=
  (S.g.hom.app (op T)).hom

def sectionConnectingLinear {S : ShortComplex (Sheaf J (ModuleCat.{u} K))}
    (hS : (additiveComplex S).ShortExact) {T : C} (hT : IsTerminal T) :
    S.X₃.obj.obj (op T) →ₗ[K] Sheaf.H (forgetModules.obj S.X₁) 1 :=
  (connectingLinear hS 0 1 rfl).comp (cohomologyZeroLinearEquiv S.X₃ hT).symm.toLinearMap

theorem sectionConnectingLinear_apply {S : ShortComplex (Sheaf J (ModuleCat.{u} K))}
    (hS : (additiveComplex S).ShortExact) {T : C} (hT : IsTerminal T)
    (x : S.X₃.obj.obj (op T)) :
    sectionConnectingLinear hS hT x =
      Cylinder.SheafCohomologyCokernel.sectionConnecting hS hT x := rfl

theorem sectionConnectingLinear_ker {S : ShortComplex (Sheaf J (ModuleCat.{u} K))}
    (hS : (additiveComplex S).ShortExact) {T : C} (hT : IsTerminal T) :
    (sectionConnectingLinear hS hT).ker = (globalSectionsMapLinear S T).range := by
  ext x
  change x ∈ (Cylinder.SheafCohomologyCokernel.sectionConnecting hS hT).ker ↔
    x ∈ (Cylinder.SheafCohomologyCokernel.globalSectionsMap
      (S := additiveComplex S) (T := T)).range
  rw [Cylinder.SheafCohomologyCokernel.sectionConnecting_ker hS hT]

theorem sectionConnectingLinear_surjective {S : ShortComplex (Sheaf J (ModuleCat.{u} K))}
    (hS : (additiveComplex S).ShortExact) {T : C} (hT : IsTerminal T)
    [Subsingleton (Sheaf.H (forgetModules.obj S.X₂) 1)] :
    Function.Surjective (sectionConnectingLinear hS hT) :=
  Cylinder.SheafCohomologyCokernel.sectionConnecting_surjective hS hT

/-- A genuine K-linear identification with Ext-defined H¹. The vanishing
assumption concerns H¹ of the middle sheaf, as in the usual long exact
sequence; no cokernel model for cohomology is assumed or defined. -/
def globalSectionsCokernelLinearEquiv {S : ShortComplex (Sheaf J (ModuleCat.{u} K))}
    (hS : (additiveComplex S).ShortExact) {T : C} (hT : IsTerminal T)
    [Subsingleton (Sheaf.H (forgetModules.obj S.X₂) 1)] :
    (S.X₃.obj.obj (op T) ⧸ (globalSectionsMapLinear S T).range) ≃ₗ[K]
      Sheaf.H (forgetModules.obj S.X₁) 1 :=
  (Submodule.quotEquivOfEq _ _ (sectionConnectingLinear_ker hS hT).symm).trans
    ((sectionConnectingLinear hS hT).quotKerEquivOfSurjective
      (sectionConnectingLinear_surjective hS hT))

theorem cohomologyOne_finrank_eq_cokernel {S : ShortComplex (Sheaf J (ModuleCat.{u} K))}
    (hS : (additiveComplex S).ShortExact) {T : C} (hT : IsTerminal T)
    [Subsingleton (Sheaf.H (forgetModules.obj S.X₂) 1)] :
    Module.finrank K (Sheaf.H (forgetModules.obj S.X₁) 1) =
      Module.finrank K (S.X₃.obj.obj (op T) ⧸ (globalSectionsMapLinear S T).range) :=
  (globalSectionsCokernelLinearEquiv hS hT).finrank_eq.symm

end Cylinder.SheafCohomologyLinearCokernel

end
