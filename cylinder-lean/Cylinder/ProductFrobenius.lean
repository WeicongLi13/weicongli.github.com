module

public import Cylinder.ProjectiveBalance
public import Cylinder.FiniteGrid
public import Mathlib.Algebra.MvPolynomial.Derivation
public import Mathlib.Algebra.CharP.Lemmas

/-!
# Actual homogeneous plane forms and their Frobenius derivation

The plane form is built from the coefficients of an actual nonzero dual
functional. The Frobenius derivation sends `X i` to `(X i)^p`; its action
on rational linear forms and on both products is proved in the actual
four-variable polynomial ring. No product-residue identity is assumed.
-/

@[expose] public section

noncomputable section

namespace Cylinder.ProductFrobenius

open MvPolynomial Cylinder.ProjectiveGeometry Cylinder.ProjectivePointSet Cylinder.ProjectiveBalance
open scoped BigOperators Classical

variable (p : ℕ) [Fact p.Prime]

abbrev Form := MvPolynomial (Fin 4) (ZMod p)

def linearForm (a : ProjectiveGeometry.Vector p) : Form p := ∑ i, C (a i) * X i

def planeForm (H : DualPoint p) : Form p :=
  linearForm p (fun i => H.rep (Pi.single i 1))

@[simp] theorem eval_linearForm (a x : ProjectiveGeometry.Vector p) :
    eval x (linearForm p a) = ProjectiveGeometry.pairing p a x := by
  simp [linearForm, ProjectiveGeometry.pairing]

@[simp] theorem eval_planeForm (H : DualPoint p) (x : ProjectiveGeometry.Vector p) :
    eval x (planeForm p H) = H.rep x := by
  rw [planeForm, eval_linearForm]
  exact (functional_expansion p H.rep x).symm

theorem planeForm_ne_zero (H : DualPoint p) : planeForm p H ≠ 0 := by
  intro h
  obtain ⟨x, hx⟩ := LinearMap.surjective H.rep_nonzero (1 : ZMod p)
  have he := eval_planeForm p H x
  rw [h, map_zero, hx] at he
  exact zero_ne_one he

theorem linearForm_homogeneous (a : ProjectiveGeometry.Vector p) :
    (linearForm p a).IsHomogeneous 1 := by
  apply IsHomogeneous.sum
  intro i _
  exact isHomogeneous_C_mul_X _ _

theorem planeForm_homogeneous (H : DualPoint p) : (planeForm p H).IsHomogeneous 1 :=
  linearForm_homogeneous p _

/-- The actual derivation whose coordinate values are the `p`th powers. -/
def theta : Derivation (ZMod p) (Form p) (Form p) :=
  MvPolynomial.mkDerivation (ZMod p) (fun i : Fin 4 => X i ^ p)

theorem linearForm_pow_char (a : ProjectiveGeometry.Vector p) :
    linearForm p a ^ p = ∑ i : Fin 4, C (a i) * X i ^ p := by
  rw [linearForm, sum_pow_char]
  apply Finset.sum_congr rfl
  intro i _
  rw [mul_pow, ← C_pow, ZMod.pow_card]

/-- The characteristic-`p` derivation of every rational linear form is its `p`th power. -/
theorem theta_linearForm (a : ProjectiveGeometry.Vector p) :
    theta p (linearForm p a) = linearForm p a ^ p := by
  rw [linearForm_pow_char]
  simp [linearForm, theta, map_sum, Derivation.leibniz, smul_eq_mul]

theorem theta_planeForm (H : DualPoint p) : theta p (planeForm p H) = planeForm p H ^ p :=
  theta_linearForm p _

theorem theta_planeForm_power (H : DualPoint p) (n : ℕ) :
    theta p (planeForm p H ^ n) =
      planeForm p H ^ n * (C (n : ZMod p) * planeForm p H ^ (p - 1)) := by
  cases n with
  | zero => simp
  | succ n =>
    have hpow : planeForm p H ^ p = planeForm p H ^ (p - 1) * planeForm p H := by
      rw [← pow_succ]
      congr 1
      have hp := (Fact.out : p.Prime).pos
      omega
    rw [Derivation.leibniz_pow, theta_planeForm, hpow]
    simp only [Nat.add_sub_cancel, nsmul_eq_mul, smul_eq_mul, pow_succ, map_natCast]
    ring

/-- A division-free logarithmic product rule for the genuine polynomial derivation. -/
theorem theta_prod {I : Type*} (s : Finset I) (f g : I → Form p)
    (h : ∀ i ∈ s, theta p (f i) = f i * g i) :
    theta p (∏ i ∈ s, f i) = (∏ i ∈ s, f i) * (∑ i ∈ s, g i) := by
  revert h
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    intro h
    have hs : ∀ j ∈ s, theta p (f j) = f j * g j :=
      fun j hj => h j (Finset.mem_insert_of_mem hj)
    simp only [Finset.prod_insert hi, Finset.sum_insert hi, Derivation.leibniz, smul_eq_mul]
    rw [h i (Finset.mem_insert_self _ _), ih hs]
    ring

def whiteProduct (S : Finset (Geometry.Point p)) : Form p :=
  ∏ H ∈ whitePoints p S, planeForm p H

def blackProduct (S : Finset (Geometry.Point p)) : Form p :=
  ∏ H ∈ blackPoints p S, planeForm p H ^ weight p S H

def whiteLog (S : Finset (Geometry.Point p)) : Form p :=
  ∑ H ∈ whitePoints p S, planeForm p H ^ (p - 1)

def blackLog (S : Finset (Geometry.Point p)) : Form p :=
  ∑ H ∈ blackPoints p S, C (weight p S H : ZMod p) * planeForm p H ^ (p - 1)

def psi (S : Finset (Geometry.Point p)) : Form p := blackLog p S - whiteLog p S

theorem whiteProduct_ne_zero (S : Finset (Geometry.Point p)) : whiteProduct p S ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro H _
  exact planeForm_ne_zero p H

theorem blackProduct_ne_zero (S : Finset (Geometry.Point p)) : blackProduct p S ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro H _
  exact pow_ne_zero _ (planeForm_ne_zero p H)

theorem theta_whiteProduct (S : Finset (Geometry.Point p)) :
    theta p (whiteProduct p S) = whiteProduct p S * whiteLog p S := by
  apply theta_prod
  intro H _
  rw [theta_planeForm, ← pow_succ']
  congr 1
  have hp := (Fact.out : p.Prime).pos
  omega

theorem theta_blackProduct (S : Finset (Geometry.Point p)) :
    theta p (blackProduct p S) = blackProduct p S * blackLog p S := by
  apply theta_prod
  intro H _
  exact theta_planeForm_power p H _

/-- The polynomial numerator of the derivative of `P/N`, with no fraction-field assumption. -/
theorem theta_cross_product (S : Finset (Geometry.Point p)) :
    whiteProduct p S * theta p (blackProduct p S) -
      blackProduct p S * theta p (whiteProduct p S) =
      blackProduct p S * whiteProduct p S * psi p S := by
  rw [theta_blackProduct, theta_whiteProduct, psi]
  ring

#print axioms theta_linearForm
#print axioms theta_planeForm_power
#print axioms theta_cross_product

end Cylinder.ProductFrobenius

end
