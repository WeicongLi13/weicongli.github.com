module

public import Cylinder.BMMSegreLemma
public import Cylinder.BMMSpecialPairs

/-! An actual black point on an arc with more than four white points
has two disjoint matching pairs whose four representatives do not sum
to zero. This is the geometric starting point of the BMM classification. -/

@[expose] public section
noncomputable section
open scoped Classical

namespace Cylinder.BMMSpecialFourTuple

open Cylinder.RationalPlaneLine Cylinder.BMMArcGeometry Cylinder.BMMBlockerPairs
open Cylinder.BMMActualCoefficients Cylinder.BMMSpecialPairs Cylinder.BMMSegreLemma

variable {K : Type*} [Field K]

structure FourTuple (A : Configuration K) (E : A.W → Fin 3 → K) (R : A.B) where
  P : A.W
  Q : A.W
  U : A.W
  V : A.W
  hPQ : P ≠ Q
  hPU : P ≠ U
  hPV : P ≠ V
  hQU : Q ≠ U
  hQV : Q ≠ V
  hUV : U ≠ V
  first_collinear : Collinear P.val Q.val R.val
  second_collinear : Collinear U.val V.val R.val
  nonspecial : E P + E Q + E U + E V ≠ 0

theorem first_blocker (A : Configuration K) (E : A.W → Fin 3 → K) (R : A.B)
    (T : FourTuple A E R) : blocker A T.P T.Q T.hPQ = R :=
  secantBlocker_unique A.W A.B A.arc A.disjoint A.blocks A.card T.P T.Q T.hPQ R T.first_collinear

theorem second_blocker (A : Configuration K) (E : A.W → Fin 3 → K) (R : A.B)
    (T : FourTuple A E R) : blocker A T.U T.V T.hUV = R :=
  secantBlocker_unique A.W A.B A.arc A.disjoint A.blocks A.card T.U T.V T.hUV R T.second_collinear

def matchingFourTuple (A : Configuration K) (E : A.W → Fin 3 → K) (R : A.B)
    (P U : A.W)
    (hUP : U ≠ P)
    (hUQ : U ≠ blackPartner A.W A.B A.arc A.disjoint A.blocks A.card R P)
    (hVP : blackPartner A.W A.B A.arc A.disjoint A.blocks A.card R U ≠ P)
    (hVQ : blackPartner A.W A.B A.arc A.disjoint A.blocks A.card R U ≠
      blackPartner A.W A.B A.arc A.disjoint A.blocks A.card R P)
    (hn : (E P + E (blackPartner A.W A.B A.arc A.disjoint A.blocks A.card R P)) +
      (E U + E (blackPartner A.W A.B A.arc A.disjoint A.blocks A.card R U)) ≠ 0) :
    FourTuple A E R where
  P := P
  Q := blackPartner A.W A.B A.arc A.disjoint A.blocks A.card R P
  U := U
  V := blackPartner A.W A.B A.arc A.disjoint A.blocks A.card R U
  hPQ := (blackPartner_ne A.W A.B A.arc A.disjoint A.blocks A.card R P).symm
  hPU := hUP.symm
  hPV := hVP.symm
  hQU := hUQ.symm
  hQV := hVQ.symm
  hUV := (blackPartner_ne A.W A.B A.arc A.disjoint A.blocks A.card R U).symm
  first_collinear := (blackPartner_spec A.W A.B A.arc A.disjoint A.blocks A.card R P).2
  second_collinear := (blackPartner_spec A.W A.B A.arc A.disjoint A.blocks A.card R U).2
  nonspecial := by simpa only [add_assoc] using hn

theorem exists_actual_nonspecial_fourtuple (A : Configuration K) (E : A.W → Fin 3 → K)
    (hE : ∀ P, ∃ α : K, α ≠ 0 ∧ E P = α • P.val.rep)
    (htwo : (2 : K) ≠ 0) (hlarge : 4 < A.W.card) (R : A.B) :
    Nonempty (FourTuple A E R) := by
  let f := blackPartner A.W A.B A.arc A.disjoint A.blocks A.card R
  obtain ⟨a, b, c, _ha, hb, _hc, hba, hfba, hca, hfca⟩ :=
    actual_black_matching_three_pairs A.W A.B A.arc A.disjoint A.blocks A.card R hlarge
  change b ∉ ({a, f a} : Finset A.W) at hba
  change f b ∉ ({a, f a} : Finset A.W) at hfba
  change c ∉ ({a, f a, b, f b} : Finset A.W) at hca
  change f c ∉ ({a, f a, b, f b} : Finset A.W) at hfca
  have hv : E b + E (f b) ≠ 0 := by
    obtain ⟨α, _hα, hEb⟩ := hE b
    obtain ⟨β, hβ, hEfb⟩ := hE (f b)
    rw [hEb, hEfb]
    exact scaled_representative_sum_ne_zero b.val (f b).val
      (fun h => hb (Subtype.ext h.symm)) α β hβ
  have hcases := exists_nonspecial_pair htwo (E a + E (f a)) (E b + E (f b))
    (E c + E (f c)) hv
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hba hfba hca hfca
  rcases hcases with hab | hac | hbc
  · exact ⟨matchingFourTuple A E R a b hba.1 hba.2 hfba.1 hfba.2 hab⟩
  · exact ⟨matchingFourTuple A E R a c hca.1 hca.2.1 hfca.1 hfca.2.1 hac⟩
  · exact ⟨matchingFourTuple A E R b c hca.2.2.1 hca.2.2.2 hfca.2.2.1 hfca.2.2.2 hbc⟩

theorem normalized_geometry_has_nonspecial_fourtuple (A : Configuration K)
    (anchor : A.W) (htwo : (2 : K) ≠ 0) (hlarge : 4 < A.W.card) :
    ∃ E : A.W → Fin 3 → K,
      (∀ P, ∃ α : K, α ≠ 0 ∧ E P = α • P.val.rep) ∧
      (∀ (P Q : A.W) (hPQ : P ≠ Q), ∃ β : K, β ≠ 0 ∧
        E P + E Q = β • (blocker A P Q hPQ).val.rep) ∧
      ∀ R : A.B, Nonempty (FourTuple A E R) := by
  obtain ⟨E, hE, hsec⟩ := actual_normalized_vector_data A anchor
  exact ⟨E, hE, hsec, fun R => exists_actual_nonspecial_fourtuple A E hE htwo hlarge R⟩

end Cylinder.BMMSpecialFourTuple

end
