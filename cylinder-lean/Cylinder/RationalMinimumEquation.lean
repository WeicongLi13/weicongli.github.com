module

public import Cylinder.EquationScalarDescent
public import Cylinder.MinimumEquationReduced

/-!
# Minimum-degree equations of actual base-field projective point sets

Initial degree is unchanged by an arbitrary field embedding. A genuine
minimum-degree equation can be chosen over the base field and remains
squarefree over every extension, by the actual point-evaluation argument.
-/

@[expose] public section
noncomputable section

namespace Cylinder.RationalMinimumEquation

open MvPolynomial Cylinder.RationalPlaneLine Cylinder.RationalPlanePointModel
open Cylinder.EquationScalarDescent Cylinder.PlaneBinaryReduction
open scoped Classical

variable {K L : Type*} [Field K] [Field L]

def baseRepresentatives (D : Finset (PlanePoint K)) : D → Fin 3 → K := fun P => P.val.rep

theorem initialDegree_iff (f : K →+* L) (D : Finset (PlanePoint K)) (s : ℕ) :
    InitialDegree (representatives f D) s ↔ InitialDegree (baseRepresentatives D) s := by
  let : Algebra K L := f.toAlgebra
  exact EquationScalarDescent.initialDegree_scalar_extension_iff (baseRepresentatives D) s

theorem hasEquation_iff (f : K →+* L) (D : Finset (PlanePoint K)) (s : ℕ) :
    HasEquation (representatives f D) s ↔ HasEquation (baseRepresentatives D) s := by
  let : Algebra K L := f.toAlgebra
  exact EquationScalarDescent.hasEquation_scalar_extension_iff (baseRepresentatives D) s

theorem exists_base_equation (f : K →+* L) (D : Finset (PlanePoint K)) (s : ℕ)
    (hs : InitialDegree (representatives f D) s) :
    ∃ F : MvPolynomial (Fin 3) K, F.IsHomogeneous s ∧ F ≠ 0 ∧
      (∀ P ∈ D, eval P.rep F = 0) ∧ Squarefree F ∧ Squarefree (MvPolynomial.map f F) := by
  have hsK := (initialDegree_iff f D s).mp hs
  obtain ⟨F, hF, hF0, hzero⟩ := (EquationScalarDescent.idealPiece_ne_bot_iff (baseRepresentatives D) s).mp hsK.1
  refine ⟨F, hF, hF0, ?_, MinimumEquationReduced.squarefree_of_initialDegree
    (baseRepresentatives D) s hsK F hF hF0 hzero, ?_⟩
  · intro P hP
    exact hzero ⟨P, hP⟩
  · let : Algebra K L := f.toAlgebra
    apply MinimumEquationReduced.squarefree_of_initialDegree (representatives f D) s hs
      (MvPolynomial.map f F) (EquationScalarDescent.mapped_homogeneous F s hF)
    · intro hz
      exact hF0 (MvPolynomial.map_injective f f.injective (by simpa only [map_zero] using hz))
    · intro P
      change eval (fun j => f (P.val.rep j)) (MvPolynomial.map f F) = 0
      have hz := hzero P
      change eval P.val.rep F = 0 at hz
      calc
        _ = f (eval P.val.rep F) := (MvPolynomial.map_eval f P.val.rep F).symm
        _ = 0 := by rw [hz, map_zero]

/-- The minimum degree can be selected before or after extension, with the
same genuine base-field equation as a witness. -/
theorem exists_initial_with_base_equation (f : K →+* L) (D : Finset (PlanePoint K)) :
    ∃ s : ℕ, InitialDegree (representatives f D) s ∧
      ∃ F : MvPolynomial (Fin 3) K, F.IsHomogeneous s ∧ F ≠ 0 ∧
        (∀ P ∈ D, eval P.rep F = 0) ∧ Squarefree F ∧ Squarefree (MvPolynomial.map f F) := by
  obtain ⟨s, hs⟩ := InitialDegreeExists.exists_initialDegree (representatives f D)
  exact ⟨s, hs, exists_base_equation f D s hs⟩

end Cylinder.RationalMinimumEquation

end
