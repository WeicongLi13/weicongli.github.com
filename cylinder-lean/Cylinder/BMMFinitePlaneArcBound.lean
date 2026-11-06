module

public import Cylinder.BMMTriangleFrame
public import Cylinder.BMMActualBlackLineData
public import Mathlib.LinearAlgebra.Quotient.Basic

/-! Count the genuine quotient directions from one point of a finite
plane arc. Matching parity sharpens the bound for an odd prime, and the
actual black-line blocks then give a strict bound on their size. -/

@[expose] public section
noncomputable section
open scoped Classical BigOperators LinearAlgebra.Projectivization

namespace Cylinder.BMMFinitePlaneArcBound

open Module Cylinder.RationalPlaneLine Cylinder.PlaneCrossProduct Cylinder.BMMArcGeometry
open Cylinder.BMMTriangleFrame Cylinder.BMMActualCoefficients
open Cylinder.BMMBlackLineBlocks Cylinder.BMMBlackLinePartition
open Cylinder.BMMActualBlackLineData Cylinder.BMMNormalizedGeometry
open Cylinder.BlackProjectionRationalLines

variable (p : ℕ) [Fact p.Prime]

abbrev DirectionIndex (P : PlanePoint (ZMod p)) :=
  Projectivization (ZMod p) ((Fin 3 → ZMod p) ⧸ P.submodule)

instance finite_quotient (P : PlanePoint (ZMod p)) :
    Finite ((Fin 3 → ZMod p) ⧸ P.submodule) :=
  Finite.of_surjective P.submodule.mkQ P.submodule.mkQ_surjective

instance directionIndex_fintype (P : PlanePoint (ZMod p)) : Fintype (DirectionIndex p P) :=
  Fintype.ofFinite _

theorem directionIndex_card (P : PlanePoint (ZMod p)) :
    Fintype.card (DirectionIndex p P) = p + 1 := by
  have hv : finrank (ZMod p) (Fin 3 → ZMod p) = 3 := by simp
  have hd := P.submodule.finrank_quotient_add_finrank
  have hq : finrank (ZMod p) ((Fin 3 → ZMod p) ⧸ P.submodule) = 2 := by
    rw [P.finrank_submodule, hv] at hd
    omega
  rw [Fintype.card_eq_nat_card]
  exact (Projectivization.card_of_finrank_two (ZMod p)
    ((Fin 3 → ZMod p) ⧸ P.submodule) hq).trans (by simp [Nat.card_eq_fintype_card])

theorem quotient_rep_nonzero (P Q : PlanePoint (ZMod p)) (hPQ : P ≠ Q) :
    P.submodule.mkQ Q.rep ≠ 0 := by
  intro hz
  have hm := (Submodule.Quotient.mk_eq_zero P.submodule).mp hz
  rw [P.submodule_eq] at hm
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hm
  exact representatives_not_proportional P Q hPQ a ha.symm

def directionOf (P Q : PlanePoint (ZMod p)) (hPQ : P ≠ Q) : DirectionIndex p P :=
  Projectivization.mk (ZMod p) (P.submodule.mkQ Q.rep) (quotient_rep_nonzero p P Q hPQ)

theorem equal_directions_collinear (P Q R : PlanePoint (ZMod p)) (hPQ : P ≠ Q) (hPR : P ≠ R)
    (hdir : directionOf p P Q hPQ = directionOf p P R hPR) : Collinear P Q R := by
  obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff' (ZMod p)
    (P.submodule.mkQ Q.rep) (P.submodule.mkQ R.rep)
    (quotient_rep_nonzero p P Q hPQ) (quotient_rep_nonzero p P R hPR)).mp hdir
  have hz : P.submodule.mkQ (Q.rep - a • R.rep) = 0 := by
    rw [map_sub, map_smul, ← ha, sub_self]
  have hm := (Submodule.Quotient.mk_eq_zero P.submodule).mp hz
  rw [P.submodule_eq] at hm
  obtain ⟨b, hb⟩ := Submodule.mem_span_singleton.mp hm
  have hQ : Q.rep = b • P.rep + a • R.rep := by
    rw [hb]
    abel
  have hd : dotMap (cross P.rep R.rep) Q.rep = 0 := by
    rw [hQ, map_add, map_smul, map_smul]
    change b * dot (cross P.rep R.rep) P.rep + a * dot (cross P.rep R.rep) R.rep = 0
    rw [dot_cross_left, dot_cross_right, mul_zero, mul_zero, add_zero]
  change dot (cross P.rep R.rep) Q.rep = 0 at hd
  exact collinear_line P R Q hd

def arcDirection (W : Finset (PlanePoint (ZMod p))) (P : PlanePoint (ZMod p)) :
    W.erase P → DirectionIndex p P := fun Q =>
  directionOf p P Q.val (Finset.mem_erase.mp Q.property).1.symm

theorem arcDirection_injective (W : Finset (PlanePoint (ZMod p))) (hW : LineCap W 2)
    (P : PlanePoint (ZMod p)) (hP : P ∈ W) : Function.Injective (arcDirection p W P) := by
  intro Q R hdir
  apply Subtype.ext
  by_contra hQR
  have hPQ := (Finset.mem_erase.mp Q.property).1.symm
  have hPR := (Finset.mem_erase.mp R.property).1.symm
  exact white_triple_noncollinear W hW P Q.val R.val hP
    (Finset.mem_erase.mp Q.property).2 (Finset.mem_erase.mp R.property).2 hPQ hPR hQR
    (equal_directions_collinear p P Q.val R.val hPQ hPR hdir)

theorem arc_card_le_prime_add_two (W : Finset (PlanePoint (ZMod p))) (hW : LineCap W 2) :
    W.card ≤ p + 2 := by
  by_cases h0 : W = ∅
  · simp [h0]
  obtain ⟨P, hP⟩ := Finset.nonempty_iff_ne_empty.mpr h0
  have hc := Fintype.card_le_of_injective (arcDirection p W P) (arcDirection_injective p W hW P hP)
  rw [Fintype.card_coe, Finset.card_erase_of_mem hP, directionIndex_card] at hc
  omega

theorem configuration_white_card_le_prime_add_one (A : Configuration (ZMod p)) (hp : 3 ≤ p) :
    A.W.card ≤ p + 1 := by
  have hc := arc_card_le_prime_add_two p A.W A.arc
  by_cases hsmall : A.W.card < 2
  · omega
  obtain ⟨n, hn⟩ := BMMMatchingParity.white_card_even A.W A.B A.arc A.disjoint A.blocks A.card (by omega)
  obtain ⟨k, hk⟩ := (Fact.out : p.Prime).odd_of_ne_two (by omega)
  omega

theorem configuration_black_card_le_prime (A : Configuration (ZMod p)) (hp : 3 ≤ p) :
    A.B.card ≤ p := by
  have hw := configuration_white_card_le_prime_add_one p A hp
  have hc := A.card
  omega

theorem twice_line_card_le_white_card {K : Type*} [Field K] (A : NormalizedSystem K)
    (l : Fin 3 → K) (hl : l ≠ 0) (htwo : (2 : K) ≠ 0) (hm : 2 ≤ (lineBlacks A l).card) :
    2 * (lineBlacks A l).card ≤ A.W.card := by
  obtain ⟨k, hk⟩ := white_card_multiple_twice_line A l hl htwo hm
  have hpos : 0 < A.W.card := by have hc := A.card; omega
  have hkpos : 1 ≤ k := by
    by_contra hz
    have hk0 : k = 0 := by omega
    rw [hk0, mul_zero] at hk
    omega
  calc
    _ = (2 * (lineBlacks A l).card) * 1 := by omega
    _ ≤ (2 * (lineBlacks A l).card) * k := Nat.mul_le_mul_left _ hkpos
    _ = A.W.card := hk.symm

theorem prime_two_nonzero (hp : 3 ≤ p) : (2 : ZMod p) ≠ 0 := by
  intro hz
  have hdiv := (ZMod.natCast_eq_zero_iff 2 p).mp hz
  have hle := Nat.le_of_dvd (by decide : 0 < 2) hdiv
  omega

theorem normalized_black_line_card_lt_prime (A : NormalizedSystem (ZMod p)) (hp : 3 ≤ p)
    (l : Fin 3 → ZMod p) (hl : l ≠ 0) : (lineBlacks A l).card < p := by
  by_cases hsmall : (lineBlacks A l).card < 2
  · omega
  have htwice := twice_line_card_le_white_card A l hl (prime_two_nonzero p hp) (by omega)
  let C : Configuration (ZMod p) := ⟨A.W, A.B, A.arc, A.disjoint, A.blocks, A.card⟩
  have hwhite := configuration_white_card_le_prime_add_one p C hp
  change A.W.card ≤ p + 1 at hwhite
  omega

theorem actual_black_line_card_lt_prime (A : Configuration (ZMod p)) (hp : 3 ≤ p)
    (l : Fin 3 → ZMod p) (hl : l ≠ 0) : (blackLine A l).card < p := by
  have hpos : 0 < A.W.card := by have hc := A.card; omega
  obtain ⟨P, hP⟩ := Finset.card_pos.mp hpos
  let anchor : A.W := ⟨P, hP⟩
  have hm := normalized_black_line_card_lt_prime p (normalizedSystem A anchor) hp l hl
  rwa [normalized_line_card] at hm

end Cylinder.BMMFinitePlaneArcBound

end
