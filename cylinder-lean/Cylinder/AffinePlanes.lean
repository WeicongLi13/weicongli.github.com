module

public import Cylinder.Geometry
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Tactic.Ring

/-!
# Normalised affine planes in three-dimensional prime-field space

The normal directions are `(1,a,b)`, `(0,1,a)` and `(0,0,1)`.
A plane parameter consists of such a direction and a constant term.  Thus
the parameters are equivalent to the three families of triples, pairs and
single constants.  Incidence is the actual coordinate equation.
-/

@[expose] public section

namespace Cylinder.AffinePlanes

open Cylinder.Geometry
open scoped BigOperators

variable (p : ℕ) [Fact p.Prime]

abbrev NormalParam := (ZMod p × ZMod p) ⊕ ZMod p ⊕ Unit
abbrev PlaneParam := NormalParam p × ZMod p

def normal : NormalParam p → Point p
  | Sum.inl (a, b) => ![1, a, b]
  | Sum.inr (Sum.inl a) => ![0, 1, a]
  | Sum.inr (Sum.inr _) => ![0, 0, 1]

def pivot : NormalParam p → Fin 3
  | Sum.inl _ => 0
  | Sum.inr (Sum.inl _) => 1
  | Sum.inr (Sum.inr _) => 2

abbrev contains (P : PlaneParam p) (x : Point p) : Prop :=
  pairing p (normal p P.1) x = P.2

instance (P : PlaneParam p) (x : Point p) : Decidable (contains p P x) :=
  inferInstanceAs (Decidable (pairing p (normal p P.1) x = P.2))

def plane (P : PlaneParam p) : Finset (Point p) :=
  affinePlane p (normal p P.1) P.2

def planesThrough (x : Point p) : Finset (PlaneParam p) :=
  Finset.univ.filter (fun P => contains p P x)

def planesThroughTwo (x y : Point p) : Finset (PlaneParam p) :=
  Finset.univ.filter (fun P => contains p P x ∧ contains p P y)

def perpendicularNormals (x : Point p) : Finset (NormalParam p) :=
  Finset.univ.filter (fun d => pairing p (normal p d) x = 0)

@[simp] theorem mem_plane (P : PlaneParam p) (x : Point p) :
    x ∈ plane p P ↔ contains p P x := by
  simp [plane, contains]

@[simp] theorem normal_pairing_first (a b : ZMod p) (x : Point p) :
    pairing p (normal p (Sum.inl (a, b))) x = x 0 + a * x 1 + b * x 2 := by
  simp [normal, pairing, Fin.sum_univ_three]

@[simp] theorem normal_pairing_second (a : ZMod p) (x : Point p) :
    pairing p (normal p (Sum.inr (Sum.inl a))) x = x 1 + a * x 2 := by
  simp [normal, pairing, Fin.sum_univ_three]

@[simp] theorem normal_pairing_third (x : Point p) :
    pairing p (normal p (Sum.inr (Sum.inr ()))) x = x 2 := by
  simp [normal, pairing, Fin.sum_univ_three]

@[simp] theorem normal_pivot (d : NormalParam p) : normal p d (pivot p d) = 1 := by
  rcases d with ab | a | u <;> simp [normal, pivot]

theorem normal_ne_zero (d : NormalParam p) : normal p d ≠ 0 := by
  intro h
  have hpivot := congrFun h (pivot p d)
  rw [normal_pivot] at hpivot
  exact one_ne_zero hpivot

@[simp] theorem normalParam_card : Fintype.card (NormalParam p) = p ^ 2 + p + 1 := by
  simp [NormalParam, pow_two, add_assoc]

theorem planeParam_card : Fintype.card (PlaneParam p) = p ^ 3 + p ^ 2 + p := by
  simp only [PlaneParam, Fintype.card_prod, normalParam_card, ZMod.card]
  ring

theorem pairing_sub (a x y : Point p) :
    pairing p a (x - y) = pairing p a x - pairing p a y := by
  simp [pairing, mul_sub, Finset.sum_sub_distrib]

theorem pairing_smul_left (a x : Point p) (t : ZMod p) :
    pairing p (t • a) x = t * pairing p a x := by
  simp [pairing, mul_assoc, Finset.mul_sum]

theorem linear_zero_iff (β d t : ZMod p) (hd : d ≠ 0) :
    β + t * d = 0 ↔ t = -β / d := by
  constructor
  · intro h
    apply mul_right_cancel₀ hd
    rw [div_mul_cancel₀ _ hd]
    exact eq_neg_of_add_eq_zero_left (by simpa only [add_comm] using h)
  · intro ht
    rw [ht, div_mul_cancel₀ _ hd, add_neg_cancel]

theorem sum_linear_zero (β d : ZMod p) (hd : d ≠ 0) :
    (∑ t : ZMod p, if β + t * d = 0 then (1 : ℕ) else 0) = 1 := by
  simp_rw [linear_zero_iff p β d _ hd]
  simp

theorem sum_common_constant (A B : ZMod p) :
    (∑ c : ZMod p, if A = c ∧ B = c then (1 : ℕ) else 0) =
      if A = B then 1 else 0 := by
  by_cases h : A = B
  · subst B
    simp
  · have hn : ∀ c : ZMod p, ¬ (A = c ∧ B = c) := by
      intro c hc
      exact h (hc.1.trans hc.2.symm)
    simp [h, hn]

theorem perpendicularNormals_card {x : Point p} (hx : x ≠ 0) :
    (perpendicularNormals p x).card = p + 1 := by
  change (Finset.univ.filter (fun d : NormalParam p => pairing p (normal p d) x = 0)).card = _
  rw [show (Finset.univ.filter (fun d : NormalParam p => pairing p (normal p d) x = 0)).card =
    ∑ d : NormalParam p, if pairing p (normal p d) x = 0 then (1 : ℕ) else 0 by
      simpa only [Nat.cast_id] using
        (Finset.sum_boole (R := ℕ) (fun d : NormalParam p => pairing p (normal p d) x = 0) Finset.univ).symm]
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_prod_type]
  simp only [normal_pairing_first, normal_pairing_second, Fintype.sum_unique]
  by_cases h2 : x 2 = 0
  · by_cases h1 : x 1 = 0
    · have h0 : x 0 ≠ 0 := by
        intro hz
        apply hx
        funext i
        fin_cases i
        · exact hz
        · exact h1
        · exact h2
      simp [h2, h1, h0]
    · rw [Finset.sum_comm]
      simp only [h2, mul_zero, add_zero]
      simp_rw [sum_linear_zero p (x 0) (x 1) h1]
      simp [h1, h2]
  · simp_rw [sum_linear_zero p (x 0 + _ * x 1) (x 2) h2,
      sum_linear_zero p (x 1) (x 2) h2]
    simp [h2]

theorem planesThrough_card (x : Point p) : (planesThrough p x).card = p ^ 2 + p + 1 := by
  change (Finset.univ.filter (fun P : PlaneParam p => contains p P x)).card = _
  rw [show (Finset.univ.filter (fun P : PlaneParam p => contains p P x)).card =
    ∑ P : PlaneParam p, if contains p P x then (1 : ℕ) else 0 by
      simpa only [Nat.cast_id] using
        (Finset.sum_boole (R := ℕ) (fun P : PlaneParam p => contains p P x) Finset.univ).symm,
    Fintype.sum_prod_type]
  have h : ∀ d : NormalParam p,
      (∑ c : ZMod p, if contains p (d, c) x then (1 : ℕ) else 0) = 1 := by
    intro d
    simp only [contains]
    simp
  simp_rw [h]
  simp [pow_two, add_assoc]

theorem planesThroughTwo_card {x y : Point p} (hxy : x ≠ y) :
    (planesThroughTwo p x y).card = p + 1 := by
  have hdelta : x - y ≠ 0 := by
    intro hzero
    exact hxy (sub_eq_zero.mp hzero)
  have hcond : ∀ d : NormalParam p,
      pairing p (normal p d) x = pairing p (normal p d) y ↔
        pairing p (normal p d) (x - y) = 0 := by
    intro d
    rw [pairing_sub, sub_eq_zero]
  change (Finset.univ.filter (fun P : PlaneParam p => contains p P x ∧ contains p P y)).card = _
  rw [show (Finset.univ.filter (fun P : PlaneParam p => contains p P x ∧ contains p P y)).card =
    ∑ P : PlaneParam p, if contains p P x ∧ contains p P y then (1 : ℕ) else 0 by
      simpa only [Nat.cast_id] using
        (Finset.sum_boole (R := ℕ) (fun P : PlaneParam p => contains p P x ∧ contains p P y) Finset.univ).symm,
    Fintype.sum_prod_type]
  simp only [contains]
  simp_rw [sum_common_constant, hcond]
  rw [show (∑ d : NormalParam p, if pairing p (normal p d) (x - y) = 0 then (1 : ℕ) else 0) =
    (perpendicularNormals p (x - y)).card by
      simpa only [Nat.cast_id, perpendicularNormals] using
        (Finset.sum_boole (R := ℕ) (fun d : NormalParam p => pairing p (normal p d) (x - y) = 0) Finset.univ)]
  exact perpendicularNormals_card p hdelta

theorem scale_div_cancel (t c : ZMod p) (ht : t ≠ 0) : t * (c / t) = c := by
  rw [mul_comm, div_mul_cancel₀ _ ht]

/-- Every nonzero coordinate normal is a nonzero scalar multiple of one normal form. -/
theorem normalisation_exists {a : Point p} (ha : a ≠ 0) :
    ∃ d : NormalParam p, ∃ t : ZMod p, t ≠ 0 ∧ a = t • normal p d := by
  by_cases h0 : a 0 = 0
  · by_cases h1 : a 1 = 0
    · have h2 : a 2 ≠ 0 := by
        intro hz
        apply ha
        funext i
        fin_cases i
        · exact h0
        · exact h1
        · exact hz
      refine ⟨Sum.inr (Sum.inr ()), a 2, h2, ?_⟩
      funext i
      fin_cases i <;> simp [normal, h0, h1, Pi.smul_apply, smul_eq_mul]
    · refine ⟨Sum.inr (Sum.inl (a 2 / a 1)), a 1, h1, ?_⟩
      funext i
      fin_cases i
      · simp [normal, h0, Pi.smul_apply, smul_eq_mul]
      · simp [normal, Pi.smul_apply, smul_eq_mul]
      · simpa [normal, Pi.smul_apply, smul_eq_mul] using (scale_div_cancel p (a 1) (a 2) h1).symm
  · refine ⟨Sum.inl (a 1 / a 0, a 2 / a 0), a 0, h0, ?_⟩
    funext i
    fin_cases i
    · simp [normal, Pi.smul_apply, smul_eq_mul]
    · simpa [normal, Pi.smul_apply, smul_eq_mul] using (scale_div_cancel p (a 0) (a 1) h0).symm
    · simpa [normal, Pi.smul_apply, smul_eq_mul] using (scale_div_cancel p (a 0) (a 2) h0).symm

/-- Every affine plane described by a nonzero normal occurs in the parameter set. -/
theorem plane_coverage {a : Point p} (ha : a ≠ 0) (b : ZMod p) :
    ∃ P : PlaneParam p, plane p P = affinePlane p a b := by
  obtain ⟨d, t, ht, haform⟩ := normalisation_exists p ha
  let c : ZMod p := b / t
  have hconstant : t * c = b := scale_div_cancel p t b ht
  refine ⟨(d, c), ?_⟩
  ext x
  rw [mem_plane, mem_affinePlane]
  change pairing p (normal p d) x = c ↔ pairing p a x = b
  constructor
  · intro hx
    rw [haform, pairing_smul_left, hx]
    exact hconstant
  · intro hx
    apply mul_left_cancel₀ ht
    calc
      t * pairing p (normal p d) x = pairing p a x := by rw [haform, pairing_smul_left]
      _ = b := hx
      _ = t * c := hconstant.symm

theorem normal_proportional_unique {d e : NormalParam p} {t : ZMod p}
    (ht : t ≠ 0) (h : normal p e = t • normal p d) : e = d ∧ t = 1 := by
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  have h2 := congrFun h 2
  clear h
  rcases d with ⟨a, b⟩ | a | ⟨⟩ <;>
    rcases e with ⟨c, d⟩ | c | ⟨⟩ <;>
    simp only [normal, Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail,
      mul_zero, mul_one] at h0 h1 h2
  all_goals simp_all
  all_goals subst t; simp_all

def pivotVector (d : NormalParam p) : Point p := Pi.single (pivot p d) 1

@[simp] theorem pairing_pivotVector (d : NormalParam p) :
    pairing p (normal p d) (pivotVector p d) = 1 := by
  simp [pivotVector]

/-- Equal plane sets have proportional normals and correspondingly scaled constants. -/
theorem proportional_of_plane_eq (P Q : PlaneParam p) (hpq : plane p P = plane p Q) :
    ∃ t : ZMod p, t ≠ 0 ∧ normal p Q.1 = t • normal p P.1 ∧ Q.2 = t * P.2 := by
  let u : Point p := pivotVector p P.1
  have hu : pairing p (normal p P.1) u = 1 := pairing_pivotVector p P.1
  let B : Point p := P.2 • u
  have hBP : B ∈ plane p P := by
    rw [mem_plane]
    change pairing p (normal p P.1) (P.2 • u) = P.2
    rw [pairing_smul, hu, mul_one]
  have hBQ : pairing p (normal p Q.1) B = Q.2 := by
    apply (mem_plane p Q B).mp
    rw [← hpq]
    exact hBP
  let t : ZMod p := pairing p (normal p Q.1) u
  have hkernel : ∀ y : Point p,
      pairing p (normal p Q.1) (y - pairing p (normal p P.1) y • u) = 0 := by
    intro y
    have hkP : pairing p (normal p P.1) (y - pairing p (normal p P.1) y • u) = 0 := by
      rw [pairing_sub, pairing_smul, hu, mul_one, sub_self]
    have hBKP : B + (y - pairing p (normal p P.1) y • u) ∈ plane p P := by
      rw [mem_plane]
      change pairing p (normal p P.1) (B + (y - pairing p (normal p P.1) y • u)) = P.2
      rw [pairing_add, (mem_plane p P B).mp hBP, hkP, add_zero]
    have hBKQ : pairing p (normal p Q.1)
        (B + (y - pairing p (normal p P.1) y • u)) = Q.2 := by
      apply (mem_plane p Q _).mp
      rw [← hpq]
      exact hBKP
    rw [pairing_add, hBQ] at hBKQ
    exact add_left_cancel (hBKQ.trans (add_zero Q.2).symm)
  have hnormal : normal p Q.1 = t • normal p P.1 := by
    funext j
    have hj := hkernel (Pi.single j 1)
    rw [pairing_sub, pairing_smul, pairing_single, pairing_single] at hj
    change normal p Q.1 j = t * normal p P.1 j
    exact (sub_eq_zero.mp hj).trans (mul_comm _ _)
  have ht : t ≠ 0 := by
    intro hzero
    apply normal_ne_zero p Q.1
    rw [hnormal, hzero, zero_smul]
  refine ⟨t, ht, hnormal, ?_⟩
  change pairing p (normal p Q.1) (P.2 • u) = Q.2 at hBQ
  rw [pairing_smul] at hBQ
  exact hBQ.symm.trans (mul_comm _ _)

/-- The parameterisation counts each actual affine plane exactly once. -/
theorem plane_injective : Function.Injective (plane p) := by
  intro P Q hpq
  obtain ⟨t, ht, hnormal, hconstant⟩ := proportional_of_plane_eq p P Q hpq
  obtain ⟨hnormalForm, ht1⟩ := normal_proportional_unique p ht hnormal
  apply Prod.ext hnormalForm.symm
  simpa [ht1] using hconstant.symm

theorem plane_coverage_unique {a : Point p} (ha : a ≠ 0) (b : ZMod p) :
    ∃! P : PlaneParam p, plane p P = affinePlane p a b := by
  obtain ⟨P, hP⟩ := plane_coverage p ha b
  refine ⟨P, hP, ?_⟩
  intro Q hQ
  exact plane_injective p (hQ.trans hP.symm)

end Cylinder.AffinePlanes
