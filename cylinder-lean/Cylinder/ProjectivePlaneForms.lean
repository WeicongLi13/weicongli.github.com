module

public import Cylinder.ProductFrobenius
public import Cylinder.FactorDegreeBound
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic

/-! Prime plane equations and the degrees of the actual white and black products. -/

@[expose] public section
noncomputable section
open scoped Classical

namespace Cylinder.ProjectivePlaneForms

open MvPolynomial Finset
open Cylinder.ProjectiveGeometry Cylinder.ProjectiveBalance Cylinder.ProductFrobenius

variable (p : ℕ) [Fact p.Prime]

theorem planeForm_totalDegree (H : DualPoint p) : (planeForm p H).totalDegree = 1 :=
  (planeForm_homogeneous p H).totalDegree (planeForm_ne_zero p H)

theorem planeForm_irreducible (H : DualPoint p) : Irreducible (planeForm p H) := by
  apply irreducible_of_totalDegree_eq_one (planeForm_totalDegree p H)
  intro r hr
  apply isUnit_iff_ne_zero.mpr
  intro hz
  obtain ⟨m, hm⟩ := exists_coeff_ne_zero (planeForm_ne_zero p H)
  have hd := hr m
  rw [hz, zero_dvd_iff] at hd
  exact hm hd

theorem planeForm_prime (H : DualPoint p) : Prime (planeForm p H) :=
  (planeForm_irreducible p H).prime

/-- Divisibility of degree-one equations identifies their actual dual points. -/
theorem planeForm_dvd_iff (H K : DualPoint p) : planeForm p H ∣ planeForm p K ↔ H = K := by
  constructor
  · rintro ⟨Q, hQ⟩
    have hQ0 : Q ≠ 0 := by
      intro hz
      apply planeForm_ne_zero p K
      rw [hQ, hz, mul_zero]
    have hdeg : 1 = 1 + Q.totalDegree := by
      have h := congrArg (fun F : Form p => F.totalDegree) hQ
      rw [planeForm_totalDegree p K,
        totalDegree_mul_of_isDomain (planeForm_ne_zero p H) hQ0,
        planeForm_totalDegree p H] at h
      exact h
    have hQdeg : Q.totalDegree = 0 := by omega
    obtain ⟨q, hqc⟩ : ∃ q : ZMod p, Q = C q :=
      ⟨Q.coeff 0, (totalDegree_eq_zero_iff_eq_C (p := Q)).mp hQdeg⟩
    have hf : K.rep = q • H.rep := by
      apply LinearMap.ext
      intro x
      change K.rep x = q * H.rep x
      rw [← eval_planeForm p K x, hQ, hqc, map_mul, eval_C, eval_planeForm]
      exact mul_comm _ _
    have heq := (Projectivization.mk_eq_mk_iff' (ZMod p) K.rep H.rep
      K.rep_nonzero H.rep_nonzero).mpr ⟨q, hf.symm⟩
    simpa only [Projectivization.mk_rep] using heq.symm
  · rintro rfl
    exact dvd_rfl

theorem planeForm_isRelPrime (H K : DualPoint p) (hHK : H ≠ K) :
    IsRelPrime (planeForm p H) (planeForm p K) := by
  apply (planeForm_irreducible p H).isRelPrime_iff_not_dvd.mpr
  intro hd
  exact hHK ((planeForm_dvd_iff p H K).mp hd)

theorem planeForm_pow_totalDegree (H : DualPoint p) (n : ℕ) :
    (planeForm p H ^ n).totalDegree = n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, totalDegree_mul_of_isDomain
        (pow_ne_zero n (planeForm_ne_zero p H)) (planeForm_ne_zero p H),
        ih, planeForm_totalDegree]

theorem planeForm_product_totalDegree (s : Finset (DualPoint p)) :
    (∏ H ∈ s, planeForm p H).totalDegree = s.card := by
  rw [FactorDegreeBound.totalDegree_prod s (planeForm p)
    (fun H _ => planeForm_ne_zero p H)]
  simp only [planeForm_totalDegree, sum_const, Nat.smul_one_eq_cast, Nat.cast_id]

theorem whiteProduct_totalDegree (S : Finset (Geometry.Point p)) :
    (whiteProduct p S).totalDegree = (whitePoints p S).card :=
  planeForm_product_totalDegree p (whitePoints p S)

theorem white_erase_product_totalDegree (S : Finset (Geometry.Point p))
    (H : DualPoint p) (hH : H ∈ whitePoints p S) :
    (∏ K ∈ (whitePoints p S).erase H, planeForm p K).totalDegree =
      (whitePoints p S).card - 1 := by
  rw [planeForm_product_totalDegree, card_erase_of_mem hH]

theorem blackProduct_totalDegree_sum (S : Finset (Geometry.Point p)) :
    (blackProduct p S).totalDegree = ∑ H ∈ blackPoints p S, weight p S H := by
  rw [blackProduct, FactorDegreeBound.totalDegree_prod _ _
    (fun H _ => pow_ne_zero _ (planeForm_ne_zero p H))]
  simp only [planeForm_pow_totalDegree]

theorem blackProduct_totalDegree {S : Finset (Geometry.Point p)} (hcard : S.card = p ^ 2)
    (hS : Geometry.PDivisible p S) :
    (blackProduct p S).totalDegree = (whitePoints p S).card - 1 := by
  rw [blackProduct_totalDegree_sum, sum_black_weight p hcard hS]

/-- White and black products are coprime in the actual polynomial ring. -/
theorem products_isRelPrime (S : Finset (Geometry.Point p)) :
    IsRelPrime (whiteProduct p S) (blackProduct p S) := by
  unfold whiteProduct blackProduct
  apply IsRelPrime.prod_left
  intro H hH
  apply IsRelPrime.prod_right
  intro K hK
  have hHK : H ≠ K := by
    intro heq
    subst K
    have hw : quotient p S H = 0 := (mem_filter.mp hH).2
    have hb : 2 ≤ quotient p S H := (mem_filter.mp hK).2
    omega
  exact (planeForm_isRelPrime p H K hHK).pow_right

end Cylinder.ProjectivePlaneForms

end
