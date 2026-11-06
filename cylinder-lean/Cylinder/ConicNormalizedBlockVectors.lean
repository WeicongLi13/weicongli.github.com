module

public import Cylinder.ConicCosetEquivalences
public import Cylinder.BMMBlackLinePointSets

/-! Affine representatives of the literal height fibres recover the
actual normalized vectors with one fixed scalar on each fibre. -/

@[expose] public section
noncomputable section
open scoped Classical

namespace Cylinder.ConicNormalizedBlockVectors
open MvPolynomial Cylinder.RationalPlaneLine Cylinder.PlaneCrossProduct
open Cylinder.ProjectiveFieldEmbedding Cylinder.ConicAffineParametrization
open Cylinder.BMMBlackLineBlocks Cylinder.BMMBlackLinePointSets
open Cylinder.PowerEvaluationRelation

variable {R K : Type*} [Field R] [Field K]

def fiberWhite (N : NormalizedSystem R) (l : Fin 3 → R) (h : R) : pointFiber N l h → N.W :=
  fun P => ⟨P.val, pointFiber_subset N l h P.property⟩

theorem fiberWhite_injective (N : NormalizedSystem R) (l : Fin 3 → R) (h : R) :
    Function.Injective (fiberWhite N l h) := by
  intro P Q heq
  exact Subtype.ext (congrArg (fun T : N.W => T.val) heq)

theorem fiberWhite_height (N : NormalizedSystem R) (l : Fin 3 → R) (h : R)
    (P : pointFiber N l h) : height N l (fiberWhite N l h P) = h := by
  obtain ⟨Q, hQ, heq⟩ := Finset.mem_image.mp P.property
  have he : Q = fiberWhite N l h P := Subtype.ext heq
  exact he ▸ (Finset.mem_filter.mp hQ).2

theorem coordinate_height (ι : R →+* K)
    (g : (Fin 3 → K) ≃ₗ[K] (Fin 3 → K)) (l : Fin 3 → R)
    (hlast : ∀ v, g v 2 = eval v (linearForm (vectorMap ι l))) (v : Fin 3 → R) :
    g (vectorMap ι v) 2 = ι (dot l v) := by
  rw [hlast, eval_linearForm]
  exact (map_dot ι l v).symm

theorem vector_eq_height_smul_affine (ι : R →+* K)
    (g : (Fin 3 → K) ≃ₗ[K] (Fin 3 → K)) (N : NormalizedSystem R) (l : Fin 3 → R)
    (hlast : ∀ v, g v 2 = eval v (linearForm (vectorMap ι l))) (P : N.W)
    (hoff : g (vectorMap ι P.val.rep) 2 ≠ 0) :
    g (vectorMap ι (N.E P)) = ι (height N l P) • affineRepresentative ι g P.val := by
  obtain ⟨a, _ha, hE⟩ := N.representatives P
  have hscaled : g (vectorMap ι (N.E P)) = ι a • g (vectorMap ι P.val.rep) := by
    simp only [hE, map_smulₛₗ, RingHom.id_apply]
  have hh : ι (height N l P) = ι a * g (vectorMap ι P.val.rep) 2 := by
    have h := congrFun hscaled 2
    rw [coordinate_height ι g l hlast] at h
    exact h
  rw [hh, affineRepresentative, smul_smul, mul_assoc, mul_inv_cancel₀ hoff, mul_one]
  exact hscaled

theorem fiber_vector_eq (ι : R →+* K)
    (g : (Fin 3 → K) ≃ₗ[K] (Fin 3 → K)) (N : NormalizedSystem R) (l : Fin 3 → R)
    (hlast : ∀ v, g v 2 = eval v (linearForm (vectorMap ι l))) (h : R) (hh : h ≠ 0)
    (P : pointFiber N l h) :
    g (vectorMap ι (N.E (fiberWhite N l h P))) = ι h • affineRepresentative ι g P.val := by
  have hheight := fiberWhite_height N l h P
  have hdot : dot l P.val.rep ≠ 0 := by
    intro hz
    have hh0 := (height_zero_iff N l (fiberWhite N l h P)).mpr hz
    rw [hheight] at hh0
    exact hh hh0
  have hoff : g (vectorMap ι P.val.rep) 2 ≠ 0 := by
    rw [coordinate_height ι g l hlast]
    exact fun hz => hdot (ι.injective (hz.trans (map_zero ι).symm))
  have heq := vector_eq_height_smul_affine ι g N l hlast (fiberWhite N l h P) hoff
  rwa [hheight] at heq

end Cylinder.ConicNormalizedBlockVectors
end
