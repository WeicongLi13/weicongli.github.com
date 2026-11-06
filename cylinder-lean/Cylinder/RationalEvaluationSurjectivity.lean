module

public import Cylinder.RationalPointEvaluationLemmas
public import Cylinder.RationalChartEvaluation
public import Cylinder.RationalProjectiveClosedPoints
public import Cylinder.FinitePointOpenSections
public import Cylinder.FinitePointFlasque
public import Mathlib.Topology.Sheaves.LocallySurjective

/-! Actual finite-point evaluation is an epimorphism of sheaves.
Interpolation gives lifts on the standard chart; skyscraper restriction
surjectivity and the open complement of the finite closed support give
the local lifts on the whole projective plane. -/

@[expose] public section
noncomputable section
open scoped Classical Cylinder.GlobalTwistChartSections Cylinder.CoordinateChartPermutation
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Cylinder.RationalEvaluationSurjectivity

open MvPolynomial AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open TopCat TopologicalSpace Opposite
open Cylinder.GlobalTwistLocalFractions Cylinder.GlobalTwistKSheaf Cylinder.GlobalTwistChartFrame
open Cylinder.ProjectivePointInProj Cylinder.RationalTwistEvaluation
open Cylinder.RationalPointEvaluationSheaf Cylinder.RationalPointEvaluationLemmas
open Cylinder.FinitePointSheaf

attribute [local instance] MvPolynomial.gradedAlgebra

universe u
variable (K : Type u) [Field K] [Infinite K]

theorem evaluation_onOpen {I : Type u} (v : ℤ) (x : I → Fin 2 → K)
    (U : (plane K).Opens) (hx : ∀ i, rayPoint (x i) ∈ U)
    (s : sectionsSubmodule K v U) (i : I) :
    FinitePointOpenSections.sectionsLinearEquiv K (plane K).toTopCat
      (fun j => rayPoint (x j)) U hx ((evaluationMorphism K v x).hom.app (op U) s) i =
        evaluation K v (x i) U (hx i) s := by
  rw [FinitePointOpenSections.sectionsLinearEquiv_apply]
  have h := congrArg (fun f => f.hom.app (op U)) (evaluationMorphism_projection K v x i)
  have hs := ConcreteCategory.congr_hom h s
  change (FinitePointOpenSections.pointSectionsIso K (plane K).toTopCat (rayPoint (x i)) U
    (hx i)).hom (((evaluationMorphism K v x ≫ Pi.π _ i).hom.app (op U)) s) = _
  rw [hs]
  exact pointEvaluation_onOpen_apply K v (x i) U (hx i) s

theorem sections_map_surjective_on_chart {I : Type u} [Fintype I]
    (v : ℤ) (x : I → Fin 2 → K) (hx : Function.Injective x) :
    Function.Surjective ((evaluationMorphism K v x).hom.app (op (coordinateOpen K none))) := by
  intro t
  let hpoints (i : I) : rayPoint (x i) ∈ coordinateOpen K none := rayPoint_mem_standardOpen (x i)
  let e := FinitePointOpenSections.sectionsLinearEquiv K (plane K).toTopCat
    (fun i => rayPoint (x i)) (coordinateOpen K none) hpoints
  obtain ⟨s, hs⟩ := Cylinder.RationalChartEvaluation.exists_section_evaluation K v x hx (e t)
  refine ⟨s, e.injective ?_⟩
  funext i
  exact (evaluation_onOpen K v x (coordinateOpen K none) hpoints s i).trans (hs i)

def outsidePoints {I : Type u} [Finite I] (x : I → Fin 2 → K) : (plane K).Opens :=
  ⟨(Set.range (fun i => rayPoint (x i)))ᶜ,
    (Cylinder.RationalProjectiveClosedPoints.isClosed_finite_points K x).isOpen_compl⟩

theorem evaluation_locally_surjective {I : Type u} [Fintype I]
    (v : ℤ) (x : I → Fin 2 → K) (hx : Function.Injective x) :
    TopCat.Presheaf.IsLocallySurjective (evaluationMorphism K v x).hom := by
  apply (TopCat.Presheaf.isLocallySurjective_iff _).mpr
  intro U t q hq
  let T := supportedSheaf K (plane K).toTopCat (fun i => rayPoint (x i))
  by_cases hc : q ∈ coordinateOpen K none
  · obtain ⟨tg, htg⟩ := Cylinder.FinitePointFlasque.restrictions_surjective K (plane K).toTopCat
      (fun i => rayPoint (x i)) (homOfLE (show U ≤ ⊤ from le_top)) t
    let tc := T.obj.map (homOfLE (show coordinateOpen K none ≤ ⊤ from le_top)).op tg
    obtain ⟨s, hs⟩ := sections_map_surjective_on_chart K v x hx tc
    let V := U ⊓ coordinateOpen K none
    let j : V ⟶ coordinateOpen K none := homOfLE inf_le_right
    let i : V ⟶ U := homOfLE inf_le_left
    refine ⟨V, inf_le_left, ⟨(twistK K v).obj.map j.op s, ?_⟩, ⟨hq, hc⟩⟩
    calc
      (evaluationMorphism K v x).hom.app (op V) ((twistK K v).obj.map j.op s) =
          T.obj.map j.op ((evaluationMorphism K v x).hom.app (op (coordinateOpen K none)) s) :=
        ConcreteCategory.congr_hom ((evaluationMorphism K v x).hom.naturality j.op) s
      _ = T.obj.map j.op tc := congrArg (T.obj.map j.op) hs
      _ = T.obj.map i.op t := by
        rw [← htg]
        change T.obj.map j.op
            (T.obj.map (homOfLE (show coordinateOpen K none ≤ ⊤ from le_top)).op tg) =
          T.obj.map i.op (T.obj.map (homOfLE (show U ≤ ⊤ from le_top)).op tg)
        simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp]
        rfl
  · let V := U ⊓ outsidePoints K x
    have hV (i : I) : rayPoint (x i) ∉ V := by
      intro hi
      exact hi.2 ⟨i, rfl⟩
    letI := Cylinder.FinitePointOpenSections.sections_subsingleton_of_not_mem K (plane K).toTopCat
      (fun i => rayPoint (x i)) V hV
    have hqV : q ∈ V := by
      refine ⟨hq, ?_⟩
      rintro ⟨i, rfl⟩
      exact hc (rayPoint_mem_standardOpen (x i))
    exact ⟨V, inf_le_left, ⟨0, Subsingleton.elim _ _⟩, hqV⟩

theorem evaluation_epi {I : Type u} [Fintype I]
    (v : ℤ) (x : I → Fin 2 → K) (hx : Function.Injective x) :
    Epi (evaluationMorphism K v x) := by
  letI : CategoryTheory.Sheaf.IsLocallySurjective (evaluationMorphism K v x) :=
    evaluation_locally_surjective K v x hx
  exact CategoryTheory.Sheaf.epi_of_isLocallySurjective (evaluationMorphism K v x)

end Cylinder.RationalEvaluationSurjectivity
end
