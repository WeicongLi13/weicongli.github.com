module

public import Cylinder.Geometry
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Algebra.BigOperators.Fin
public import Lean.Elab.Tactic.Omega

/-!
# Counting fibres of the coordinate projection

All fibres here are filters of the actual point set.  A full fibre is an
affine line in the third coordinate direction.  Plane divisibility yields
divisibility of the sums along quotient lines.  If the individual fibres
are divisible as well, a set of size `p²` is exactly `p` disjoint full fibres.
-/

@[expose] public section

namespace Cylinder.CoordinateProjection

open Cylinder.Geometry
open scoped BigOperators

variable (p : ℕ) [Fact p.Prime]

abbrev QuotientPoint := Fin 2 → ZMod p

def project (x : Point p) : QuotientPoint p := ![x 0, x 1]

def lift (q : QuotientPoint p) (t : ZMod p) : Point p := ![q 0, q 1, t]

def verticalDirection : Point p := ![0, 0, 1]

def fibre (S : Finset (Point p)) (q : QuotientPoint p) : Finset (Point p) :=
  S.filter (fun x => project p x = q)

def fibreSize (S : Finset (Point p)) (q : QuotientPoint p) : ℕ :=
  (fibre p S q).card

def fullFibre (q : QuotientPoint p) : Finset (Point p) :=
  Finset.univ.filter (fun x => project p x = q)

def quotientPairing (n q : QuotientPoint p) : ZMod p := ∑ i, n i * q i

def quotientLine (n : QuotientPoint p) (b : ZMod p) : Finset (QuotientPoint p) :=
  Finset.univ.filter (fun q => quotientPairing p n q = b)

def liftNormal (n : QuotientPoint p) : Point p := ![n 0, n 1, 0]

def activeProjections (S : Finset (Point p)) : Finset (QuotientPoint p) :=
  Finset.univ.filter (fun q => 0 < fibreSize p S q)

omit [Fact p.Prime] in
@[simp] theorem project_lift (q : QuotientPoint p) (t : ZMod p) :
    project p (lift p q t) = q := by
  funext i
  fin_cases i <;> rfl

omit [Fact p.Prime] in
@[simp] theorem lift_project (x : Point p) : lift p (project p x) (x 2) = x := by
  funext i
  fin_cases i <;> rfl

@[simp] theorem project_zero : project p 0 = 0 := by
  funext i
  fin_cases i <;> rfl

theorem verticalDirection_ne_zero : verticalDirection p ≠ 0 := by
  intro h
  have hlast := congrFun h 2
  simp [verticalDirection] at hlast

theorem lift_as_line (q : QuotientPoint p) (t : ZMod p) :
    lift p q t = lift p q 0 + t • verticalDirection p := by
  funext i
  fin_cases i <;> simp [lift, verticalDirection]

omit [Fact p.Prime] in
@[simp] theorem mem_fibre (S : Finset (Point p)) (q : QuotientPoint p) (x : Point p) :
    x ∈ fibre p S q ↔ x ∈ S ∧ project p x = q := by
  simp [fibre]

@[simp] theorem mem_fullFibre (q : QuotientPoint p) (x : Point p) :
    x ∈ fullFibre p q ↔ project p x = q := by
  simp [fullFibre]

theorem fullFibre_eq_affineLine (q : QuotientPoint p) :
    fullFibre p q = affineLine p (lift p q 0) (verticalDirection p) := by
  ext x
  rw [mem_fullFibre, mem_affineLine]
  constructor
  · intro hx
    refine ⟨x 2, ?_⟩
    rw [← lift_as_line, ← hx, lift_project]
  · rintro ⟨t, ht⟩
    rw [← ht, ← lift_as_line, project_lift]

theorem fullFibre_card (q : QuotientPoint p) : (fullFibre p q).card = p := by
  rw [fullFibre_eq_affineLine]
  exact affineLine_card p _ (verticalDirection_ne_zero p)

theorem fibre_subset_fullFibre (S : Finset (Point p)) (q : QuotientPoint p) :
    fibre p S q ⊆ fullFibre p q := by
  intro x hx
  exact (mem_fullFibre p q x).mpr ((mem_fibre p S q x).mp hx).2

theorem fibreSize_le (S : Finset (Point p)) (q : QuotientPoint p) :
    fibreSize p S q ≤ p := by
  change (fibre p S q).card ≤ p
  calc
    (fibre p S q).card ≤ (fullFibre p q).card :=
      Finset.card_le_card (fibre_subset_fullFibre p S q)
    _ = p := fullFibre_card p q

theorem sum_fibreSize (S : Finset (Point p)) :
    ∑ q : QuotientPoint p, fibreSize p S q = S.card := by
  have hfilter : S.filter (fun x => project p x ∈ (Finset.univ : Finset (QuotientPoint p))) = S := by
    apply Finset.filter_eq_self.mpr
    intro x _
    exact Finset.mem_univ _
  calc
    ∑ q : QuotientPoint p, fibreSize p S q =
        (S.filter (fun x => project p x ∈ (Finset.univ : Finset (QuotientPoint p)))).card :=
      Finset.sum_card_fiberwise_eq_card_filter S Finset.univ (project p)
    _ = S.card := congrArg Finset.card hfilter

@[simp] theorem mem_quotientLine (n q : QuotientPoint p) (b : ZMod p) :
    q ∈ quotientLine p n b ↔ quotientPairing p n q = b := by
  simp [quotientLine]

theorem pairing_liftNormal (n : QuotientPoint p) (x : Point p) :
    pairing p (liftNormal p n) x = quotientPairing p n (project p x) := by
  simp [pairing, quotientPairing, liftNormal, project, Fin.sum_univ_three, Fin.sum_univ_two]

theorem liftNormal_ne_zero {n : QuotientPoint p} (hn : n ≠ 0) : liftNormal p n ≠ 0 := by
  have hproject : project p (liftNormal p n) = n := by
    funext i
    fin_cases i <;> rfl
  intro h
  have hh := congrArg (project p) h
  rw [hproject, project_zero] at hh
  exact hn hh

theorem quotientLine_sum_fibreSize (S : Finset (Point p)) (n : QuotientPoint p) (b : ZMod p) :
    ∑ q ∈ quotientLine p n b, fibreSize p S q =
      (S.filter (fun x => pairing p (liftNormal p n) x = b)).card := by
  have hfilter : S.filter (fun x => project p x ∈ quotientLine p n b) =
      S.filter (fun x => pairing p (liftNormal p n) x = b) := by
    ext x
    rw [Finset.mem_filter, Finset.mem_filter, mem_quotientLine, pairing_liftNormal]
  calc
    ∑ q ∈ quotientLine p n b, fibreSize p S q =
        (S.filter (fun x => project p x ∈ quotientLine p n b)).card :=
      Finset.sum_card_fiberwise_eq_card_filter S (quotientLine p n b) (project p)
    _ = (S.filter (fun x => pairing p (liftNormal p n) x = b)).card :=
      congrArg Finset.card hfilter

theorem quotientLine_sum_dvd {S : Finset (Point p)} (hS : PDivisible p S)
    {n : QuotientPoint p} (hn : n ≠ 0) (b : ZMod p) :
    p ∣ ∑ q ∈ quotientLine p n b, fibreSize p S q := by
  rw [quotientLine_sum_fibreSize]
  exact hS (liftNormal p n) (liftNormal_ne_zero p hn) b

theorem fibreSize_zero_or_full {S : Finset (Point p)} {q : QuotientPoint p}
    (hdiv : p ∣ fibreSize p S q) : fibreSize p S q = 0 ∨ fibreSize p S q = p := by
  have hle := fibreSize_le p S q
  by_cases heq : fibreSize p S q = p
  · exact Or.inr heq
  · exact Or.inl (Nat.eq_zero_of_dvd_of_lt hdiv (by omega))

theorem active_fibreSize {S : Finset (Point p)}
    (hdiv : ∀ q : QuotientPoint p, p ∣ fibreSize p S q) {q : QuotientPoint p}
    (hq : q ∈ activeProjections p S) : fibreSize p S q = p := by
  have hpos := (Finset.mem_filter.mp hq).2
  rcases fibreSize_zero_or_full p (hdiv q) with hzero | hfull
  · omega
  · exact hfull

theorem active_fibre_full {S : Finset (Point p)}
    (hdiv : ∀ q : QuotientPoint p, p ∣ fibreSize p S q) {q : QuotientPoint p}
    (hq : q ∈ activeProjections p S) : fibre p S q = fullFibre p q := by
  apply Finset.eq_of_subset_of_card_le (fibre_subset_fullFibre p S q)
  rw [fullFibre_card]
  exact le_of_eq (active_fibreSize p hdiv hq).symm

theorem sum_active_fibreSize (S : Finset (Point p)) :
    ∑ q ∈ activeProjections p S, fibreSize p S q = S.card := by
  calc
    ∑ q ∈ activeProjections p S, fibreSize p S q =
        ∑ q : QuotientPoint p, fibreSize p S q := by
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro q _ hnot
      have hnotpos : ¬ 0 < fibreSize p S q := by
        intro hpos
        exact hnot (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpos⟩)
      omega
    _ = S.card := sum_fibreSize p S

theorem activeProjections_card {S : Finset (Point p)} (hcard : S.card = p ^ 2)
    (hdiv : ∀ q : QuotientPoint p, p ∣ fibreSize p S q) :
    (activeProjections p S).card = p := by
  apply Nat.eq_of_mul_eq_mul_right (Nat.Prime.pos (Fact.out : p.Prime))
  calc
    (activeProjections p S).card * p =
        ∑ q ∈ activeProjections p S, fibreSize p S q :=
      (Finset.sum_const_nat (fun q hq => active_fibreSize p hdiv hq)).symm
    _ = S.card := sum_active_fibreSize p S
    _ = p * p := by rw [hcard, pow_two]

theorem fullFibres_disjoint {q r : QuotientPoint p} (hqr : q ≠ r) :
    Disjoint (fullFibre p q) (fullFibre p r) := by
  apply Finset.disjoint_left.mpr
  intro x hx hy
  have hxq := (mem_fullFibre p q x).mp hx
  have hxr := (mem_fullFibre p r x).mp hy
  exact hqr (hxq.symm.trans hxr)

/-- Divisible individual fibres of a `p²`-point set are exactly `p` full parallel lines. -/
theorem isCylinder_of_fibreSize_dvd {S : Finset (Point p)} (hcard : S.card = p ^ 2)
    (hdiv : ∀ q : QuotientPoint p, p ∣ fibreSize p S q) : IsCylinder p S := by
  classical
  let e : Fin p ≃ activeProjections p S :=
    (Finset.equivFinOfCardEq (activeProjections_card p hcard hdiv)).symm
  let base : Fin p → Point p := fun i => lift p (e i).val 0
  refine ⟨verticalDirection p, verticalDirection_ne_zero p, base, ?_, ?_⟩
  · intro i j hij
    change Disjoint (affineLine p (lift p (e i).val 0) (verticalDirection p))
      (affineLine p (lift p (e j).val 0) (verticalDirection p))
    rw [← fullFibre_eq_affineLine, ← fullFibre_eq_affineLine]
    apply fullFibres_disjoint
    intro h
    exact hij (e.injective (Subtype.ext h))
  · ext x
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
    constructor
    · intro hx
      have hfibre : x ∈ fibre p S (project p x) :=
        (mem_fibre p S (project p x) x).mpr ⟨hx, rfl⟩
      have hactive : project p x ∈ activeProjections p S :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, Finset.card_pos.mpr ⟨x, hfibre⟩⟩
      let q : activeProjections p S := ⟨project p x, hactive⟩
      refine ⟨e.symm q, ?_⟩
      change x ∈ affineLine p (lift p (e (e.symm q)).val 0) (verticalDirection p)
      rw [e.apply_symm_apply, ← fullFibre_eq_affineLine]
      exact (mem_fullFibre p q.val x).mpr rfl
    · rintro ⟨i, hi⟩
      change x ∈ affineLine p (lift p (e i).val 0) (verticalDirection p) at hi
      rw [← fullFibre_eq_affineLine, ← active_fibre_full p hdiv (e i).property] at hi
      exact ((mem_fibre p S (e i).val x).mp hi).1

#print axioms sum_fibreSize
#print axioms quotientLine_sum_fibreSize
#print axioms quotientLine_sum_dvd
#print axioms isCylinder_of_fibreSize_dvd

end Cylinder.CoordinateProjection
