module

public import Cylinder.BMMNormalizedGeometry
public import Cylinder.BMMVectorSecants

/-! Any two Segre normalizations of the same configuration differ by
one scalar. A change of anchor therefore preserves zero sums. -/

@[expose] public section
noncomputable section
open scoped Classical

namespace Cylinder.BMMNormalizationUniqueness

open Cylinder.RationalPlaneLine Cylinder.BMMBlackLineBlocks
open Cylinder.BMMVectorSecants Cylinder.BMMActualCoefficients
open Cylinder.BMMNormalizedGeometry

variable {K : Type*} [Field K]

theorem representative_scalar (N : NormalizedSystem K) (F : N.W → Fin 3 → K)
    (hF : ∀ P, ∃ a : K, a ≠ 0 ∧ F P = a • P.val.rep) (P : N.W) :
    ∃ a : K, a ≠ 0 ∧ F P = a • N.E P := by
  obtain ⟨a, ha, hF⟩ := hF P
  obtain ⟨b, hb, hE⟩ := N.representatives P
  refine ⟨a / b, div_ne_zero ha hb, ?_⟩
  rw [hF, hE, smul_smul, div_mul_cancel₀ _ hb]

theorem equal_pair_scalars (N : NormalizedSystem K) (P Q : N.W) (hPQ : P ≠ Q)
    (a b c : K) (h : a • N.E P + b • N.E Q = c • (N.E P + N.E Q)) : a = b := by
  have hval : P.val ≠ Q.val := fun heq => hPQ (Subtype.ext heq)
  obtain ⟨u, hu, hP⟩ := N.representatives P
  obtain ⟨v, hv, hQ⟩ := N.representatives Q
  have he := congrArg (pairFrame P.val Q.val hval) h
  simp only [hP, hQ, map_add, map_smul, pairFrame_left, pairFrame_right] at he
  have hp : a * u = c * u := by
    simpa [Pi.single_apply, Pi.smul_apply, smul_eq_mul] using congrFun he 0
  have hq : b * v = c * v := by
    simpa [Pi.single_apply, Pi.smul_apply, smul_eq_mul] using congrFun he 1
  exact (mul_right_cancel₀ hu hp).trans (mul_right_cancel₀ hv hq).symm

theorem normalized_vectors_unique (N : NormalizedSystem K) (F : N.W → Fin 3 → K)
    (hFrep : ∀ P, ∃ a : K, a ≠ 0 ∧ F P = a • P.val.rep)
    (hFsum : ∀ P Q (hPQ : P ≠ Q), ∃ a : K, a ≠ 0 ∧
      F P + F Q = a • (Cylinder.BMMBlackLineBlocks.blocker N P Q hPQ).val.rep)
    (anchor : N.W) : ∃ c : K, c ≠ 0 ∧ ∀ P, F P = c • N.E P := by
  choose a ha hE using representative_scalar N F hFrep
  refine ⟨a anchor, ha anchor, ?_⟩
  intro P
  by_cases hPa : P = anchor
  · simpa only [hPa] using hE anchor
  obtain ⟨u, hu, hsum⟩ := N.sums P anchor hPa
  obtain ⟨v, _hv, hF⟩ := hFsum P anchor hPa
  have he : a P • N.E P + a anchor • N.E anchor =
      (v / u) • (N.E P + N.E anchor) := by
    rw [← hE P, ← hE anchor, hF, hsum, smul_smul, div_mul_cancel₀ _ hu]
  rw [hE P, equal_pair_scalars N P anchor hPa _ _ _ he]

theorem change_anchor_is_scalar (N : NormalizedSystem K) (anchor : N.W) :
    let A : Configuration K := ⟨N.W, N.B, N.arc, N.disjoint, N.blocks, N.card⟩
    ∃ c : K, c ≠ 0 ∧ ∀ P, (normalizedSystem A anchor).E P = c • N.E P := by
  let A : Configuration K := ⟨N.W, N.B, N.arc, N.disjoint, N.blocks, N.card⟩
  exact normalized_vectors_unique N (normalizedSystem A anchor).E
    (normalizedSystem A anchor).representatives (normalizedSystem A anchor).sums anchor

end Cylinder.BMMNormalizationUniqueness

end
