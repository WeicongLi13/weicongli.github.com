module

public import Cylinder.ConicAffineDirections
public import Cylinder.ConicFiniteProductMatchings

/-! Actual point blocks on a standard conic. Their genuine secants and
matching equivalences determine the finite slope set and hence subgroup
cosets. No product cardinality or group closure is assumed. -/

@[expose] public section
noncomputable section
open scoped Classical

namespace Cylinder.ConicStandardBlocks
open MvPolynomial Cylinder.RationalPlaneLine Cylinder.ProjectiveFieldEmbedding
open Cylinder.ConicAffineParametrization Cylinder.ConicAffineDirections
open Cylinder.ConicFiniteProductMatchings Cylinder.BMMArcGeometry

variable {R K : Type*} [Field R] [Field K]

def parameter (ι : R →+* K) (g : (Fin 3 → K) ≃ₗ[K] (Fin 3 → K)) (P : PlanePoint R) : K :=
  affineRepresentative ι g P 0

structure StandardBlocks (ι : R →+* K) (g : (Fin 3 → K) ≃ₗ[K] (Fin 3 → K)) (φ : K → K)
    (X Y C : Finset (PlanePoint R)) : Prop where
  disjoint : Disjoint X Y
  cardX : X.card = C.card
  cardY : Y.card = C.card
  off : ∀ P ∈ X ∪ Y, g (vectorMap ι P.rep) 2 ≠ 0
  infinity : ∀ T ∈ C, g (vectorMap ι T.rep) 2 = 0
  shape : ∀ P ∈ X ∪ Y, affineRepresentative ι g P = ![parameter ι g P, φ (parameter ι g P), 1]
  cross : ∀ P ∈ X, ∀ Q ∈ Y, ∃ T ∈ C, Collinear P Q T
  matching : ∀ T : C, ∃ e : X ≃ Y, ∀ P : X, Collinear P.val (e P).val T.val

variable (ι : R →+* K) (g : (Fin 3 → K) ≃ₗ[K] (Fin 3 → K)) (φ : K → K)
variable (X Y C : Finset (PlanePoint R)) (A : StandardBlocks ι g φ X Y C)
include A

theorem parameter_injective : Function.Injective (fun P : ↥(X ∪ Y) => parameter ι g P.val) := by
  intro P Q heq
  apply affineRepresentative_injective ι g (X ∪ Y) A.off
  change affineRepresentative ι g P.val = affineRepresentative ι g Q.val
  change parameter ι g P.val = parameter ι g Q.val at heq
  rw [A.shape P.val P.property, A.shape Q.val Q.property, heq]

theorem left_parameter_injective : Function.Injective (fun P : X => parameter ι g P.val) := by
  intro P Q heq
  have h := parameter_injective ι g φ X Y C A
    (a₁ := ⟨P.val, Finset.mem_union_left _ P.property⟩)
    (a₂ := ⟨Q.val, Finset.mem_union_left _ Q.property⟩) heq
  exact Subtype.ext (congrArg (fun T : ↥(X ∪ Y) => T.val) h)

theorem right_parameter_injective : Function.Injective (fun Q : Y => parameter ι g Q.val) := by
  intro P Q heq
  have h := parameter_injective ι g φ X Y C A
    (a₁ := ⟨P.val, Finset.mem_union_right _ P.property⟩)
    (a₂ := ⟨Q.val, Finset.mem_union_right _ Q.property⟩) heq
  exact Subtype.ext (congrArg (fun T : ↥(X ∪ Y) => T.val) h)

theorem cross_parameter_ne (P : X) (Q : Y) : parameter ι g P.val ≠ parameter ι g Q.val := by
  intro heq
  have h := parameter_injective ι g φ X Y C A
    (a₁ := ⟨P.val, Finset.mem_union_left _ P.property⟩)
    (a₂ := ⟨Q.val, Finset.mem_union_right _ Q.property⟩) heq
  exact Finset.disjoint_left.mp A.disjoint P.property ((congrArg Subtype.val h).symm ▸ Q.property)

theorem collinear_slope (P : X) (Q : Y) (T : C) (hcol : Collinear P.val Q.val T.val) :
    g (vectorMap ι T.val.rep) 0 ≠ 0 ∧ directionSlope ι g T.val =
      (φ (parameter ι g Q.val) - φ (parameter ι g P.val)) /
        (parameter ι g Q.val - parameter ι g P.val) := by
  have hPQ : P.val ≠ Q.val := by
    intro h
    exact Finset.disjoint_left.mp A.disjoint P.property (h.symm ▸ Q.property)
  obtain ⟨hfirst, hslope⟩ := secant_direction_slope ι g P.val Q.val T.val hPQ hcol
    (A.off P.val (Finset.mem_union_left _ P.property))
    (A.off Q.val (Finset.mem_union_right _ Q.property))
    (A.infinity T.val T.property) (cross_parameter_ne ι g φ X Y C A P Q)
  have hp := congrFun (A.shape P.val (Finset.mem_union_left _ P.property)) (1 : Fin 3)
  have hq := congrFun (A.shape Q.val (Finset.mem_union_right _ Q.property)) (1 : Fin 3)
  change affineRepresentative ι g P.val 1 = φ (parameter ι g P.val) at hp
  change affineRepresentative ι g Q.val 1 = φ (parameter ι g Q.val) at hq
  rw [hp, hq] at hslope
  exact ⟨hfirst, hslope⟩

theorem infinity_first_nonzero (anchor : X) : ∀ T ∈ C, g (vectorMap ι T.rep) 0 ≠ 0 := by
  intro T hT
  obtain ⟨e, he⟩ := A.matching ⟨T, hT⟩
  exact (collinear_slope ι g φ X Y C A anchor (e anchor) ⟨T, hT⟩ (he anchor)).1

theorem slope_injective (anchor : X) : Function.Injective (fun T : C => directionSlope ι g T.val) :=
  directionSlope_injective ι g C A.infinity (infinity_first_nonzero ι g φ X Y C A anchor)

theorem cross_slopes : ∀ P : X, ∀ Q : Y, ∃ T : C, directionSlope ι g T.val =
    (φ (parameter ι g Q.val) - φ (parameter ι g P.val)) /
      (parameter ι g Q.val - parameter ι g P.val) := by
  intro P Q
  obtain ⟨T, hT, hcol⟩ := A.cross P.val P.property Q.val Q.property
  exact ⟨⟨T, hT⟩, (collinear_slope ι g φ X Y C A P Q ⟨T, hT⟩ hcol).2⟩

theorem matching_slopes : ∀ T : C, ∃ e : X ≃ Y, ∀ P : X, directionSlope ι g T.val =
    (φ (parameter ι g (e P).val) - φ (parameter ι g P.val)) /
      (parameter ι g (e P).val - parameter ι g P.val) := by
  intro T
  obtain ⟨e, he⟩ := A.matching T
  exact ⟨e, fun P => (collinear_slope ι g φ X Y C A P (e P) T (he P)).2⟩

end Cylinder.ConicStandardBlocks
end
