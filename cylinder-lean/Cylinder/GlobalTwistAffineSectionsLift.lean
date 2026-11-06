module

public import Cylinder.GlobalTwistAdditiveCharts

/-! Any actual global short exact sequence whose kernel is the global
twist has surjective section maps on all three actual coordinate opens.
This is obtained by affine descent, not by restricting injective objects. -/

@[expose] public section
noncomputable section
open scoped Classical
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace Cylinder.GlobalTwistAffineSectionsLift

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopCat TopologicalSpace Opposite
open Cylinder.GlobalTwistLocalFractions Cylinder.GlobalTwistKSheaf
open Cylinder.GlobalTwistAdditiveCharts Cylinder.GlobalTwistChartFrame
open Cylinder.CoordinateChartPermutation Cylinder.CoordinateLaurentLocalization
open Cylinder.SheafCohomologyScalarAction

attribute [local instance] MvPolynomial.gradedAlgebra

variable (K : Type u) [Field K] [Infinite K]

instance coordinateRing_domain (i : Index) : IsDomain (coordinateRing K i) :=
  ((toFirstChart K i).trans (ProjectivePolynomialChart.chartEquiv K)).injective.isDomain
    ((toFirstChart K i).trans (ProjectivePolynomialChart.chartEquiv K)).toRingHom

omit [Infinite K] in
theorem chartEmbedding_image_top (i : Index) :
    (chartEmbedding K i).isOpenEmbedding.functor.obj
      (⊤ : Opens (PrimeSpectrum.Top (coordinateRing K i))) = coordinateOpen K i := by
  change (chartEmbedding K i) ''ᵁ ⊤ = _
  simp [chartEmbedding]

theorem sections_surjective (v : ℤ)
    {S : ShortComplex (CategoryTheory.Sheaf (Opens.grothendieckTopology (plane K).toTopCat)
      AddCommGrpCat.{u})} (hS : S.ShortExact)
    (e : S.X₁ ≅ forgetModules.obj (twistK K v)) (i : Index) :
    Function.Surjective (S.g.hom.app (op (coordinateOpen K i))) := by
  have h := ActualAffineOpenEmbeddingLift.sections_surjective (coordinateRing K i)
    (chartEmbedding K i).base (chartEmbedding K i).isOpenEmbedding hS
    ((ActualAffineOpenEmbeddingLift.pullback (chartEmbedding K i).isOpenEmbedding).mapIso e ≪≫
      chartAdditiveIso K i v)
  rw [chartEmbedding_image_top K i] at h
  exact h

theorem lift_section (v : ℤ)
    {S : ShortComplex (CategoryTheory.Sheaf (Opens.grothendieckTopology (plane K).toTopCat)
      AddCommGrpCat.{u})} (hS : S.ShortExact)
    (e : S.X₁ ≅ forgetModules.obj (twistK K v)) (i : Index)
    (t : S.X₃.obj.obj (op (coordinateOpen K i))) :
    ∃ a : S.X₂.obj.obj (op (coordinateOpen K i)),
      S.g.hom.app (op (coordinateOpen K i)) a = t :=
  sections_surjective K v hS e i t

end Cylinder.GlobalTwistAffineSectionsLift

end
