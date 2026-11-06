module

public import Cylinder.WeakDirectionMoments
public import Cylinder.LinearFormFactors
public import Cylinder.PrimeLinearFactorCount

/-! At least p undetermined directions force p-divisibility.
The argument proves the required finite-field direction result directly. -/

@[expose] public section
noncomputable section
open scoped Classical

namespace Cylinder.WeakDirectionDivisibility
open MvPolynomial Cylinder.Geometry Cylinder.WeakDirectionsGeometry
open Cylinder.WeakDirectionMoments Cylinder.LinearFormFactors Cylinder.PowerEvaluationRelation

variable (p : ℕ) [Fact p.Prime]

theorem planeMomentPolynomial_eq_zero_of_many_missing {S : Finset (Point p)}
    (hcard : S.card = p ^ 2) (hdirs : p ≤ (nonDeterminedDirections p S).card) :
    planeMomentPolynomial p S = 0 := by
  apply Cylinder.PrimeLinearFactorCount.eq_zero_of_more_prime_linear_factors
    (nonDeterminedDirections p S) (fun D : Direction p => linearForm (Fin.snoc D.rep 0))
  · intro D _
    exact linearForm_prime _ (snoc_zero_ne_zero D.rep D.rep_nonzero)
  · intro D _ E _ hDE
    exact projective_snoc_linearForms_not_associated D E hDE
  · intro D hD
    exact direction_form_dvd_moment p hcard D (Finset.mem_filter.mp hD).2
  · intro D _
    exact linearForm_totalDegree _ (snoc_zero_ne_zero D.rep D.rep_nonzero)
  · exact (planeMomentPolynomial_degree p S).trans_lt
      ((Nat.sub_lt (Fact.out : p.Prime).pos (by decide : 0 < 1)).trans_le hdirs)

theorem pDivisible_of_many_nonDeterminedDirections {S : Finset (Point p)}
    (hcard : S.card = p ^ 2) (hdirs : p ≤ (nonDeterminedDirections p S).card) :
    PDivisible p S := by
  have hzero := planeMomentPolynomial_eq_zero_of_many_missing p hcard hdirs
  intro a _ha b
  apply (ZMod.natCast_eq_zero_iff _ p).mp
  have heval := eval_planeMomentPolynomial_of_card p hcard (Fin.snoc a b)
  rw [hzero, map_zero] at heval
  have hn : normalPart p (Fin.snoc a b) = a := by
    funext j
    exact Fin.snoc_castSucc _ _ _
  have hb : (Fin.snoc a b : Fin 4 → ZMod p) 3 = b := by simp [Fin.snoc]
  rw [hn, hb] at heval
  exact neg_eq_zero.mp heval.symm

end Cylinder.WeakDirectionDivisibility
end
