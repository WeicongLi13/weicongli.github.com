module

public import Cylinder.BMMVectorSecants
public import Cylinder.BMMTriangleBlockers

/-! The secant coefficient is obtained from the actual black blocker
and the fixed representatives of the two white endpoints. -/

@[expose] public section
noncomputable section
open scoped Classical BigOperators

namespace Cylinder.BMMActualCoefficients

open Cylinder.RationalPlaneLine Cylinder.PlaneCrossProduct Cylinder.BMMArcGeometry
open Cylinder.BMMTriangleFrame Cylinder.BMMFrameRatios Cylinder.BMMBlockerPairs
open Cylinder.BMMTriangleBlockers Cylinder.BMMVectorSecants

variable {K : Type*} [Field K]

structure Configuration (K : Type*) [Field K] where
  W : Finset (PlanePoint K)
  B : Finset (PlanePoint K)
  arc : LineCap W 2
  disjoint : Disjoint W B
  blocks : BlocksSecants W B
  card : B.card + 1 = W.card

abbrev blocker (A : Configuration K) (P Q : A.W) (hPQ : P ≠ Q) : A.B :=
  secantBlocker A.W A.B A.arc A.disjoint A.blocks A.card P Q hPQ

theorem exists_blocker_representation (A : Configuration K) (P Q : A.W) (hPQ : P ≠ Q) :
    ∃ b : K, b ≠ 0 ∧ ∃ a : K, a ≠ 0 ∧
      (blocker A P Q hPQ).val.rep = a • (P.val.rep + b • Q.val.rep) := by
  apply exists_secant_representation P.val Q.val (blocker A P Q hPQ).val
    (fun h => hPQ (Subtype.ext h))
  · intro h
    exact Finset.disjoint_left.mp A.disjoint P.property (h ▸ (blocker A P Q hPQ).property)
  · intro h
    exact Finset.disjoint_left.mp A.disjoint Q.property (h ▸ (blocker A P Q hPQ).property)
  · exact secantBlocker_collinear A.W A.B A.arc A.disjoint A.blocks A.card P Q hPQ

def secantCoefficient (A : Configuration K) (P Q : A.W) : K :=
  if hPQ : P ≠ Q then Classical.choose (exists_blocker_representation A P Q hPQ) else 1

@[simp] theorem coefficient_diagonal (A : Configuration K) (P : A.W) :
    secantCoefficient A P P = 1 := by simp [secantCoefficient]

theorem coefficient_spec (A : Configuration K) (P Q : A.W) (hPQ : P ≠ Q) :
    secantCoefficient A P Q ≠ 0 ∧ ∃ a : K, a ≠ 0 ∧
      (blocker A P Q hPQ).val.rep = a • (P.val.rep + secantCoefficient A P Q • Q.val.rep) := by
  simpa only [secantCoefficient, dite_eq_left hPQ] using
    Classical.choose_spec (exists_blocker_representation A P Q hPQ)

theorem coefficient_nonzero (A : Configuration K) (P Q : A.W) :
    secantCoefficient A P Q ≠ 0 := by
  by_cases hPQ : P = Q
  · subst Q
    simp
  · exact (coefficient_spec A P Q hPQ).1

theorem coefficient_unique (A : Configuration K) (P Q : A.W) (hPQ : P ≠ Q)
    (a b : K) (_ha : a ≠ 0)
    (h : (blocker A P Q hPQ).val.rep = a • (P.val.rep + b • Q.val.rep)) :
    secantCoefficient A P Q = b := by
  obtain ⟨_, a', ha', h'⟩ := coefficient_spec A P Q hPQ
  exact secant_representation_unique P.val Q.val (blocker A P Q hPQ).val
    (fun h => hPQ (Subtype.ext h)) a' (secantCoefficient A P Q) a b ha' h' h

theorem coefficient_reverse (A : Configuration K) (P Q : A.W) :
    secantCoefficient A Q P = (secantCoefficient A P Q)⁻¹ := by
  by_cases hPQ : P = Q
  · subst Q
    simp
  obtain ⟨hb, a, ha, hrep⟩ := coefficient_spec A P Q hPQ
  apply coefficient_unique A Q P (Ne.symm hPQ) (a * secantCoefficient A P Q)
    (secantCoefficient A P Q)⁻¹ (mul_ne_zero ha hb)
  have hblock : blocker A P Q hPQ = blocker A Q P (Ne.symm hPQ) :=
    secantBlocker_symm A.W A.B A.arc A.disjoint A.blocks A.card P Q hPQ
  rw [← hblock, hrep]
  simp only [smul_add, smul_smul, mul_assoc, mul_inv_cancel₀ hb, mul_one]
  exact add_comm _ _

theorem coefficient_reverse_product (A : Configuration K) (P Q : A.W) :
    secantCoefficient A P Q * secantCoefficient A Q P = 1 := by
  rw [coefficient_reverse A P Q, mul_inv_cancel₀ (coefficient_nonzero A P Q)]

def triangleConfiguration (T : Triangle K) : Configuration K :=
  ⟨T.W, T.B, T.arc, T.disjoint, T.blocks, T.card⟩

theorem side_coefficient_ratio (T : Triangle K) (i : Fin 3) :
    secantCoefficient (triangleConfiguration T) (T.P (next i)) (T.P (previous i)) =
      blackCoordinates T (sideBlocker T i) (previous i) /
        blackCoordinates T (sideBlocker T i) (next i) := by
  have hPQ : T.P (next i) ≠ T.P (previous i) :=
    fun h => next_ne_previous i (T.injective h)
  obtain ⟨_hb, a, ha, hrep⟩ := coefficient_spec (triangleConfiguration T)
    (T.P (next i)) (T.P (previous i)) hPQ
  change (sideBlocker T i).val.rep =
    a • ((T.P (next i)).val.rep +
      secantCoefficient (triangleConfiguration T) (T.P (next i)) (T.P (previous i)) •
        (T.P (previous i)).val.rep) at hrep
  have heq := congrArg (frame T) hrep
  rw [map_smul, map_add, map_smul] at heq
  have hnext := coordinates_basis (vectors T) (determinant_ne_zero T) (next i)
  have hprev := coordinates_basis (vectors T) (determinant_ne_zero T) (previous i)
  rw [hnext, hprev] at heq
  have hn : blackCoordinates T (sideBlocker T i) (next i) = a := by
    simpa [Pi.single_apply, next_ne_previous i, (next_ne_previous i).symm,
      Pi.smul_apply, smul_eq_mul] using congrFun heq (next i)
  have hp : blackCoordinates T (sideBlocker T i) (previous i) =
      a * secantCoefficient (triangleConfiguration T) (T.P (next i)) (T.P (previous i)) := by
    simpa [Pi.single_apply, next_ne_previous i, (next_ne_previous i).symm,
      Pi.smul_apply, smul_eq_mul] using congrFun heq (previous i)
  rw [hp, hn, mul_div_cancel_left₀ _ ha]

end Cylinder.BMMActualCoefficients

end
