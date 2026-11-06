module

public import Cylinder.BMMNormalizedGeometry

/-! The five actual black points attached to a non-special white
four-tuple. The two opposite pairs give genuine collinear black triples. -/

@[expose] public section
noncomputable section
open scoped Classical BigOperators

namespace Cylinder.BMMFourTupleBlackGeometry

open Cylinder.RationalPlaneLine Cylinder.PlaneCrossProduct Cylinder.BMMArcGeometry
open Cylinder.BMMBlockerPairs Cylinder.BMMActualCoefficients
open Cylinder.BMMBlackLineBlocks Cylinder.BMMSpecialFourTuple
open Cylinder.BlackProjectionRationalLines

variable {K : Type*} [Field K]

abbrev configuration (A : NormalizedSystem K) : Configuration K :=
  ⟨A.W, A.B, A.arc, A.disjoint, A.blocks, A.card⟩

abbrev secant (A : NormalizedSystem K) (P Q : A.W) (hPQ : P ≠ Q) : A.B :=
  secantBlocker A.W A.B A.arc A.disjoint A.blocks A.card P Q hPQ

abbrev firstCross (A : NormalizedSystem K) {R : A.B} (T : FourTuple (configuration A) A.E R) :=
  secant A T.P T.U T.hPU

abbrev secondCross (A : NormalizedSystem K) {R : A.B} (T : FourTuple (configuration A) A.E R) :=
  secant A T.Q T.V T.hQV

abbrev thirdCross (A : NormalizedSystem K) {R : A.B} (T : FourTuple (configuration A) A.E R) :=
  secant A T.P T.V T.hPV

abbrev fourthCross (A : NormalizedSystem K) {R : A.B} (T : FourTuple (configuration A) A.E R) :=
  secant A T.Q T.U T.hQU

theorem base_ne_first (A : NormalizedSystem K) {R : A.B}
    (T : FourTuple (configuration A) A.E R) : R ≠ firstCross A T := by
  intro h
  exact secantBlocker_ne_at A.W A.B A.arc A.disjoint A.blocks A.card T.P T.Q T.U
    T.hPQ T.hPU T.hQU ((first_blocker (configuration A) A.E R T).trans h)

theorem base_ne_second (A : NormalizedSystem K) {R : A.B}
    (T : FourTuple (configuration A) A.E R) : R ≠ secondCross A T := by
  intro h
  have heq : secant A T.Q T.P T.hPQ.symm = R :=
    (secantBlocker_symm A.W A.B A.arc A.disjoint A.blocks A.card T.P T.Q T.hPQ).symm.trans
      (first_blocker (configuration A) A.E R T)
  exact secantBlocker_ne_at A.W A.B A.arc A.disjoint A.blocks A.card T.Q T.P T.V
    T.hPQ.symm T.hQV T.hPV (heq.trans h)

theorem base_ne_third (A : NormalizedSystem K) {R : A.B}
    (T : FourTuple (configuration A) A.E R) : R ≠ thirdCross A T := by
  intro h
  exact secantBlocker_ne_at A.W A.B A.arc A.disjoint A.blocks A.card T.P T.Q T.V
    T.hPQ T.hPV T.hQV ((first_blocker (configuration A) A.E R T).trans h)

theorem base_ne_fourth (A : NormalizedSystem K) {R : A.B}
    (T : FourTuple (configuration A) A.E R) : R ≠ fourthCross A T := by
  intro h
  have heq : secant A T.Q T.P T.hPQ.symm = R :=
    (secantBlocker_symm A.W A.B A.arc A.disjoint A.blocks A.card T.P T.Q T.hPQ).symm.trans
      (first_blocker (configuration A) A.E R T)
  exact secantBlocker_ne_at A.W A.B A.arc A.disjoint A.blocks A.card T.Q T.P T.U
    T.hPQ.symm T.hQU T.hPU (heq.trans h)

theorem points_eq_of_common_nonzero_vector (P Q : PlanePoint K) (v : Fin 3 → K)
    (hv : v ≠ 0) (a b : K) (hP : v = a • P.rep) (hQ : v = b • Q.rep) : P = Q := by
  have hb : b ≠ 0 := by
    intro hz
    exact hv (by rw [hQ, hz, zero_smul])
  by_contra hPQ
  apply representatives_not_proportional P Q hPQ (b⁻¹ * a)
  calc
    Q.rep = b⁻¹ • (b • Q.rep) := by rw [smul_smul, inv_mul_cancel₀ hb, one_smul]
    _ = b⁻¹ • v := by rw [hQ]
    _ = (b⁻¹ * a) • P.rep := by rw [hP, smul_smul]

theorem opposite_secants_ne (A : NormalizedSystem K) {R : A.B}
    (T : FourTuple (configuration A) A.E R) : firstCross A T ≠ secondCross A T := by
  intro heq
  obtain ⟨a, _ha, hab⟩ := A.sums T.P T.Q T.hPQ
  obtain ⟨b, _hb, hcd⟩ := A.sums T.U T.V T.hUV
  obtain ⟨c, _hc, hac⟩ := A.sums T.P T.U T.hPU
  obtain ⟨d, _hd, hbd⟩ := A.sums T.Q T.V T.hQV
  change A.E T.P + A.E T.Q =
    a • (Cylinder.BMMActualCoefficients.blocker (configuration A) T.P T.Q T.hPQ).val.rep at hab
  change A.E T.U + A.E T.V =
    b • (Cylinder.BMMActualCoefficients.blocker (configuration A) T.U T.V T.hUV).val.rep at hcd
  rw [first_blocker (configuration A) A.E R T] at hab
  rw [second_blocker (configuration A) A.E R T] at hcd
  change A.E T.P + A.E T.U = c • (firstCross A T).val.rep at hac
  change A.E T.Q + A.E T.V = d • (secondCross A T).val.rep at hbd
  rw [← heq] at hbd
  have hR : A.E T.P + A.E T.Q + A.E T.U + A.E T.V = (a + b) • R.val.rep := by
    calc
      _ = (A.E T.P + A.E T.Q) + (A.E T.U + A.E T.V) := by abel
      _ = _ := by rw [hab, hcd, add_smul]
  have hC : A.E T.P + A.E T.Q + A.E T.U + A.E T.V =
      (c + d) • (firstCross A T).val.rep := by
    calc
      _ = (A.E T.P + A.E T.U) + (A.E T.Q + A.E T.V) := by abel
      _ = _ := by rw [hac, hbd, add_smul]
  exact base_ne_first A T (Subtype.ext
    (points_eq_of_common_nonzero_vector R.val (firstCross A T).val _ T.nonspecial _ _ hR hC))

def swapLast (A : NormalizedSystem K) {R : A.B}
    (T : FourTuple (configuration A) A.E R) : FourTuple (configuration A) A.E R where
  P := T.P
  Q := T.Q
  U := T.V
  V := T.U
  hPQ := T.hPQ
  hPU := T.hPV
  hPV := T.hPU
  hQU := T.hQV
  hQV := T.hQU
  hUV := T.hUV.symm
  first_collinear := T.first_collinear
  second_collinear := collinear_swap _ _ _ T.second_collinear
  nonspecial := by simpa only [add_assoc, add_left_comm, add_comm] using T.nonspecial

theorem other_opposite_secants_ne (A : NormalizedSystem K) {R : A.B}
    (T : FourTuple (configuration A) A.E R) : thirdCross A T ≠ fourthCross A T :=
  opposite_secants_ne A (swapLast A T)

theorem opposite_black_triple_collinear (A : NormalizedSystem K) {R : A.B}
    (T : FourTuple (configuration A) A.E R) :
    Collinear R.val (firstCross A T).val (secondCross A T).val := by
  obtain ⟨a, _ha, hab⟩ := A.sums T.P T.Q T.hPQ
  obtain ⟨b, _hb, hcd⟩ := A.sums T.U T.V T.hUV
  obtain ⟨c, _hc, hac⟩ := A.sums T.P T.U T.hPU
  obtain ⟨d, _hd, hbd⟩ := A.sums T.Q T.V T.hQV
  change A.E T.P + A.E T.Q =
    a • (Cylinder.BMMActualCoefficients.blocker (configuration A) T.P T.Q T.hPQ).val.rep at hab
  change A.E T.U + A.E T.V =
    b • (Cylinder.BMMActualCoefficients.blocker (configuration A) T.U T.V T.hUV).val.rep at hcd
  rw [first_blocker (configuration A) A.E R T] at hab
  rw [second_blocker (configuration A) A.E R T] at hcd
  have htotal : A.E T.P + A.E T.Q + A.E T.U + A.E T.V = (a + b) • R.val.rep := by
    calc
      _ = (A.E T.P + A.E T.Q) + (A.E T.U + A.E T.V) := by abel
      _ = _ := by rw [hab, hcd, add_smul]
  have hn : a + b ≠ 0 := by
    intro hz
    exact T.nonspecial (by rw [htotal, hz, zero_smul])
  have hcomb : (a + b) • R.val.rep =
      c • (firstCross A T).val.rep + d • (secondCross A T).val.rep := by
    rw [← htotal, ← hac, ← hbd]
    abel
  let l := cross (firstCross A T).val.rep (secondCross A T).val.rep
  have hdot := congrArg (dotMap l) hcomb
  rw [map_smul, map_add, map_smul, map_smul] at hdot
  change (a + b) * dot l R.val.rep =
    c * dot l (firstCross A T).val.rep + d * dot l (secondCross A T).val.rep at hdot
  rw [dot_cross_left, dot_cross_right, mul_zero, mul_zero, add_zero] at hdot
  have hcol : Collinear (firstCross A T).val (secondCross A T).val R.val :=
    (mul_eq_zero.mp hdot).resolve_left hn
  exact collinear_swap _ _ _ (collinear_line _ _ _ hcol)

theorem other_opposite_black_triple_collinear (A : NormalizedSystem K) {R : A.B}
    (T : FourTuple (configuration A) A.E R) :
    Collinear R.val (thirdCross A T).val (fourthCross A T).val :=
  opposite_black_triple_collinear A (swapLast A T)

theorem first_ne_third (A : NormalizedSystem K) {R : A.B}
    (T : FourTuple (configuration A) A.E R) : firstCross A T ≠ thirdCross A T :=
  secantBlocker_ne_at A.W A.B A.arc A.disjoint A.blocks A.card T.P T.U T.V
    T.hPU T.hPV T.hUV

theorem second_ne_fourth (A : NormalizedSystem K) {R : A.B}
    (T : FourTuple (configuration A) A.E R) : secondCross A T ≠ fourthCross A T :=
  secantBlocker_ne_at A.W A.B A.arc A.disjoint A.blocks A.card T.Q T.V T.U
    T.hQV T.hQU T.hUV.symm

theorem first_ne_fourth (A : NormalizedSystem K) {R : A.B}
    (T : FourTuple (configuration A) A.E R) : firstCross A T ≠ fourthCross A T := by
  intro heq
  have hPU := secantBlocker_symm A.W A.B A.arc A.disjoint A.blocks A.card T.P T.U T.hPU
  have hQU := secantBlocker_symm A.W A.B A.arc A.disjoint A.blocks A.card T.Q T.U T.hQU
  exact secantBlocker_ne_at A.W A.B A.arc A.disjoint A.blocks A.card T.U T.P T.Q
    T.hPU.symm T.hQU.symm T.hPQ (hPU.symm.trans (heq.trans hQU))

theorem second_ne_third (A : NormalizedSystem K) {R : A.B}
    (T : FourTuple (configuration A) A.E R) : secondCross A T ≠ thirdCross A T := by
  intro heq
  have hQV := secantBlocker_symm A.W A.B A.arc A.disjoint A.blocks A.card T.Q T.V T.hQV
  have hPV := secantBlocker_symm A.W A.B A.arc A.disjoint A.blocks A.card T.P T.V T.hPV
  exact secantBlocker_ne_at A.W A.B A.arc A.disjoint A.blocks A.card T.V T.Q T.P
    T.hQV.symm T.hPV.symm T.hPQ.symm (hQV.symm.trans (heq.trans hPV))

def fiveBlacks (A : NormalizedSystem K) {R : A.B}
    (T : FourTuple (configuration A) A.E R) : Fin 5 → A.B :=
  ![R, firstCross A T, secondCross A T, thirdCross A T, fourthCross A T]

theorem fiveBlacks_injective (A : NormalizedSystem K) {R : A.B}
    (T : FourTuple (configuration A) A.E R) : Function.Injective (fiveBlacks A T) := by
  have h01 := base_ne_first A T
  have h02 := base_ne_second A T
  have h03 := base_ne_third A T
  have h04 := base_ne_fourth A T
  have h12 := opposite_secants_ne A T
  have h13 := first_ne_third A T
  have h14 := first_ne_fourth A T
  have h23 := second_ne_third A T
  have h24 := second_ne_fourth A T
  have h34 := other_opposite_secants_ne A T
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [fiveBlacks]

theorem fiveBlacks_point_injective (A : NormalizedSystem K) {R : A.B}
    (T : FourTuple (configuration A) A.E R) :
    Function.Injective (fun i => (fiveBlacks A T i).val) :=
  Subtype.val_injective.comp (fiveBlacks_injective A T)

theorem first_line_coefficients_nonzero (A : NormalizedSystem K) {R : A.B}
    (T : FourTuple (configuration A) A.E R) : cross R.val.rep (firstCross A T).val.rep ≠ 0 :=
  cross_ne_zero R.val.rep (firstCross A T).val.rep R.val.rep_nonzero
    (representatives_not_proportional R.val (firstCross A T).val
      (fun h => base_ne_first A T (Subtype.ext h)))

theorem second_line_coefficients_nonzero (A : NormalizedSystem K) {R : A.B}
    (T : FourTuple (configuration A) A.E R) : cross R.val.rep (thirdCross A T).val.rep ≠ 0 :=
  cross_ne_zero R.val.rep (thirdCross A T).val.rep R.val.rep_nonzero
    (representatives_not_proportional R.val (thirdCross A T).val
      (fun h => base_ne_third A T (Subtype.ext h)))

def firstLine (A : NormalizedSystem K) {R : A.B}
    (T : FourTuple (configuration A) A.E R) : PlanePoint K :=
  Projectivization.mk K (cross R.val.rep (firstCross A T).val.rep)
    (first_line_coefficients_nonzero A T)

def secondLine (A : NormalizedSystem K) {R : A.B}
    (T : FourTuple (configuration A) A.E R) : PlanePoint K :=
  Projectivization.mk K (cross R.val.rep (thirdCross A T).val.rep)
    (second_line_coefficients_nonzero A T)

theorem dot_smul_coefficients (l x : Fin 3 → K) (a : K) :
    dot (a • l) x = a * dot l x := by
  simp only [dot, Pi.smul_apply, smul_eq_mul, mul_assoc, Finset.mul_sum]

theorem black_lines_distinct_of_cap_four (A : NormalizedSystem K) {R : A.B}
    (T : FourTuple (configuration A) A.E R) (hcap : LineCap A.B 4) :
    firstLine A T ≠ secondLine A T := by
  intro heq
  obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff' K
    (cross R.val.rep (firstCross A T).val.rep)
    (cross R.val.rep (thirdCross A T).val.rep)
    (first_line_coefficients_nonzero A T) (second_line_coefficients_nonzero A T)).mp heq
  let l := cross R.val.rep (firstCross A T).val.rep
  have hzero : ∀ i, dot l (fiveBlacks A T i).val.rep = 0 := by
    intro i
    fin_cases i
    · exact dot_cross_left _ _
    · exact dot_cross_right _ _
    · exact opposite_black_triple_collinear A T
    · change dot l (thirdCross A T).val.rep = 0
      change a • cross R.val.rep (thirdCross A T).val.rep = l at ha
      rw [← ha, dot_smul_coefficients, dot_cross_right, mul_zero]
    · change dot l (fourthCross A T).val.rep = 0
      have hz := other_opposite_black_triple_collinear A T
      change dot (cross R.val.rep (thirdCross A T).val.rep) (fourthCross A T).val.rep = 0 at hz
      change a • cross R.val.rep (thirdCross A T).val.rep = l at ha
      rw [← ha, dot_smul_coefficients, hz, mul_zero]
  let X := Finset.univ.image (fun i => (fiveBlacks A T i).val)
  have hX : X.card = 5 := by
    rw [Finset.card_image_of_injective _ (fiveBlacks_point_injective A T)]
    simp
  have hsub : X ⊆ A.B.filter (fun P => dot l P.rep = 0) := by
    intro P hP
    obtain ⟨i, _hi, rfl⟩ := Finset.mem_image.mp hP
    exact Finset.mem_filter.mpr ⟨(fiveBlacks A T i).property, hzero i⟩
  have hcount := Finset.card_le_card hsub
  have hbound := hcap l (first_line_coefficients_nonzero A T)
  rw [hX] at hcount
  omega

end Cylinder.BMMFourTupleBlackGeometry

end
