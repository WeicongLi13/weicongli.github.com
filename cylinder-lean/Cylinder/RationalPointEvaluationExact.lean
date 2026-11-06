module

public import Cylinder.RationalPointIdealSheaf
public import Cylinder.RationalEvaluationSurjectivity
public import Cylinder.SheafCohomologyLinearCokernel
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.Algebra.Category.ModuleCat.Abelian

/-! The actual evaluation-kernel sequence is short exact. -/

@[expose] public section
noncomputable section
open scoped Classical
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Cylinder.RationalPointEvaluationExact

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopCat TopologicalSpace Opposite
open Cylinder.GlobalTwistLocalFractions Cylinder.GlobalTwistKSheaf
open Cylinder.RationalPointEvaluationSheaf Cylinder.RationalPointIdealSheaf

attribute [local instance] MvPolynomial.gradedAlgebra

universe u
variable (K : Type u) [Field K]

local instance moduleSheafZeroMorphisms (X : TopCat.{u}) :
    HasZeroMorphisms (TopCat.Sheaf (ModuleCat.{u} K) X) :=
  RationalPointIdealSheaf.moduleSheafZeroMorphisms K X

abbrev moduleSheaves := CategoryTheory.Sheaf
  (Opens.grothendieckTopology (plane K).toTopCat) (ModuleCat.{u} K)

def sequence {I : Type u} (v : ℤ) (x : I → Fin 2 → K) : ShortComplex (moduleSheaves K) :=
  evaluationSequence K v x

abbrev additiveSequence {I : Type u} (v : ℤ) (x : I → Fin 2 → K) :=
  Cylinder.SheafCohomologyLinearCokernel.additiveComplex (sequence K v x)

theorem additiveSequence_shortExact [Infinite K] {I : Type u} [Fintype I]
    (v : ℤ) (x : I → Fin 2 → K) (hx : Function.Injective x) :
    (additiveSequence K v x).ShortExact := by
  let G := Cylinder.SheafCohomologyScalarAction.forgetModules
    (J := Opens.grothendieckTopology (plane K).toTopCat) (K := K)
  haveI : G.PreservesZeroMorphisms := { map_zero := by intro A B; rfl }
  haveI : PreservesLimitsOfShape WalkingParallelPair G := by
    let J := Opens.grothendieckTopology (plane K).toTopCat
    haveI : PreservesLimitsOfShape WalkingParallelPair
        (G ⋙ sheafToPresheaf J AddCommGrpCat.{u}) := by
      change PreservesLimitsOfShape WalkingParallelPair
        (sheafToPresheaf J (ModuleCat.{u} K) ⋙
          (Functor.whiskeringRight _ _ _).obj (forget₂ (ModuleCat.{u} K) AddCommGrpCat.{u}))
      infer_instance
    exact preservesLimitsOfShape_of_reflects_of_preserves G (sheafToPresheaf J AddCommGrpCat.{u})
  haveI : CategoryTheory.Sheaf.IsLocallySurjective (G.map (evaluationMorphism K v x)) := by
    change TopCat.Presheaf.IsLocallySurjective (G.map (evaluationMorphism K v x)).hom
    apply (TopCat.Presheaf.isLocallySurjective_iff _).mpr
    intro U t q hq
    obtain ⟨V, hVU, ⟨s, hs⟩, hqV⟩ :=
      (TopCat.Presheaf.isLocallySurjective_iff _).mp
        (Cylinder.RationalEvaluationSurjectivity.evaluation_locally_surjective K v x hx) U t q hq
    exact ⟨V, hVU, ⟨s, hs⟩, hqV⟩
  haveI : Epi (G.map (evaluationMorphism K v x)) :=
    CategoryTheory.Sheaf.epi_of_isLocallySurjective _
  have hker := KernelFork.mapIsLimit _ (kernelIsKernel (evaluationMorphism K v x)) G
  exact
    { exact := ShortComplex.exact_of_f_is_kernel _ hker
      mono_f := by
        change Mono (G.map (kernel.ι (evaluationMorphism K v x)))
        exact mono_of_isLimit_fork hker
      epi_g := by
        change Epi (G.map (evaluationMorphism K v x))
        infer_instance }

end Cylinder.RationalPointEvaluationExact
end
