module

public import Cylinder.WeakDirectionsGeometry
public import Cylinder.PowerEvaluationRelation
public import Cylinder.FiniteFieldHyperplaneDivisibility
public import Mathlib.FieldTheory.Finite.Basic

/-! A plane counting polynomial for the original affine point set.
Its values are the negatives of plane intersection sizes modulo p. -/

@[expose] public section
noncomputable section
open scoped Classical BigOperators

namespace Cylinder.WeakDirectionMoments
open MvPolynomial Cylinder.Geometry Cylinder.WeakDirectionsGeometry

variable (p : ℕ) [Fact p.Prime]

def affineForm (x : Point p) : MvPolynomial (Fin 4) (ZMod p) :=
  C (x 0) * X 0 + C (x 1) * X 1 + C (x 2) * X 2 - X 3

def planeMomentPolynomial (S : Finset (Point p)) : MvPolynomial (Fin 4) (ZMod p) :=
  ∑ x ∈ S, affineForm p x ^ (p - 1)

theorem affineForm_homogeneous (x : Point p) : (affineForm p x).IsHomogeneous 1 :=
  (((isHomogeneous_C_mul_X (x 0) 0).add (isHomogeneous_C_mul_X (x 1) 1)).add
    (isHomogeneous_C_mul_X (x 2) 2)).sub (isHomogeneous_X (ZMod p) 3)

theorem planeMomentPolynomial_homogeneous (S : Finset (Point p)) :
    (planeMomentPolynomial p S).IsHomogeneous (p - 1) := by
  apply IsHomogeneous.sum
  intro x _
  simpa only [one_mul] using (affineForm_homogeneous p x).pow (p - 1)

theorem planeMomentPolynomial_degree (S : Finset (Point p)) :
    (planeMomentPolynomial p S).totalDegree ≤ p - 1 :=
  (planeMomentPolynomial_homogeneous p S).totalDegree_le

def normalPart (w : Fin 4 → ZMod p) : Point p := fun j => w j.castSucc

theorem eval_affineForm (w : Fin 4 → ZMod p) (x : Point p) :
    eval w (affineForm p x) = pairing p (normalPart p w) x - w 3 := by
  simp [affineForm, pairing, normalPart, Fin.sum_univ_three]
  ring

theorem indicator_identity (z : ZMod p) :
    z ^ (p - 1) = 1 - if z = 0 then 1 else 0 := by
  rw [ZMod.pow_card_sub_one]
  by_cases hz : z = 0 <;> simp [hz]

theorem eval_planeMomentPolynomial (S : Finset (Point p)) (w : Fin 4 → ZMod p) :
    eval w (planeMomentPolynomial p S) = (S.card : ZMod p) -
      ((S.filter (fun x => pairing p (normalPart p w) x = w 3)).card : ZMod p) := by
  simp only [planeMomentPolynomial, map_sum, map_pow, eval_affineForm, indicator_identity,
    sub_eq_zero, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_one]
  congr 1
  simp

theorem eval_planeMomentPolynomial_of_card {S : Finset (Point p)}
    (hcard : S.card = p ^ 2) (w : Fin 4 → ZMod p) :
    eval w (planeMomentPolynomial p S) =
      -((S.filter (fun x => pairing p (normalPart p w) x = w 3)).card : ZMod p) := by
  rw [eval_planeMomentPolynomial, hcard, Nat.cast_pow, ZMod.natCast_self, zero_pow (by decide : 2 ≠ 0), zero_sub]

theorem eval_direction_form (D : Direction p) (w : Fin 4 → ZMod p) :
    eval w (Cylinder.PowerEvaluationRelation.linearForm (Fin.snoc D.rep 0)) =
      pairing p (normalPart p w) D.rep := by
  have h : eval w (Cylinder.PowerEvaluationRelation.linearForm (Fin.snoc D.rep 0)) =
      ∑ j : Fin 4, (Fin.snoc D.rep (0 : ZMod p) : Fin 4 → ZMod p) j * w j := by
    simp [Cylinder.PowerEvaluationRelation.linearForm]
  rw [h, Fin.sum_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last, zero_mul, add_zero]
  change (∑ j : Fin 3, D.rep j * w j.castSucc) = ∑ j : Fin 3, w j.castSucc * D.rep j
  apply Finset.sum_congr rfl
  intro j _
  exact mul_comm _ _

theorem moment_vanishes_on_missing_hyperplane {S : Finset (Point p)}
    (hcard : S.card = p ^ 2) (D : Direction p) (hD : ¬ Determines p S D)
    (w : Fin 4 → ZMod p)
    (hw : eval w (Cylinder.PowerEvaluationRelation.linearForm (Fin.snoc D.rep 0)) = 0) :
    eval w (planeMomentPolynomial p S) = 0 := by
  have horth : pairing p (normalPart p w) D.rep = 0 := by
    simpa only [eval_direction_form] using hw
  rw [eval_planeMomentPolynomial_of_card p hcard]
  by_cases ha : normalPart p w = 0
  · by_cases hb : w 3 = 0
    · simp [ha, pairing, hb, hcard]
    · simp [ha, pairing, Ne.symm hb]
  · rw [parallel_plane_intersection_card p hcard hD _ ha _ horth, ZMod.natCast_self, neg_zero]

theorem direction_form_dvd_moment {S : Finset (Point p)} (hcard : S.card = p ^ 2)
    (D : Direction p) (hD : ¬ Determines p S D) :
    Cylinder.PowerEvaluationRelation.linearForm (Fin.snoc D.rep 0) ∣ planeMomentPolynomial p S := by
  apply Cylinder.FiniteFieldHyperplaneDivisibility.zmod_linearForm_dvd_of_vanishing p _ _ _
    (planeMomentPolynomial_degree p S) (moment_vanishes_on_missing_hyperplane p hcard D hD)
  intro hz
  apply D.rep_nonzero
  funext j
  simpa using congrFun hz j.castSucc

end Cylinder.WeakDirectionMoments
end
