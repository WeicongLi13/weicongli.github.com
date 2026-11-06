module

public import Cylinder.QuadricBlackExclusion
public import Cylinder.QuadricLineAlgebra
public import Cylinder.WhitePlaneHyperfocus

/-! Three actual collinear white dual points force a white quadric to vanish
on their entire actual line. Line balance supplies a black point there,
contradicting the proved black-point exclusion. -/

@[expose] public section
noncomputable section
open scoped Classical

namespace Cylinder.NoWhiteQuadric

open MvPolynomial Cylinder.ProjectiveGeometry Cylinder.ProjectiveBalance
open Cylinder.ProjectiveBlackLine Cylinder.ProjectiveLineCap Cylinder.DualLineBalance
open Cylinder.ProductEvaluationRelation Cylinder.WhitePlaneHyperfocus

variable (p : ℕ) [Fact p.Prime]

theorem pairSpan_coefficients (a b c : DualPoint p) (hc : c.submodule ≤ pairSpan p a b) :
    ∃ x y : ZMod p, x • a.rep + y • b.rep = c.rep := by
  have hmem := (ProjectiveIncidence.submodule_le_iff_rep_mem c (pairSpan p a b)).mp hc
  have hrange : Set.range ![a.rep, b.rep] = ({a.rep, b.rep} : Set (DualSpace p)) := by
    ext f
    simp only [Set.mem_range, Fin.exists_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      Set.mem_insert_iff, Set.mem_singleton_iff, eq_comm]
  unfold pairSpan at hmem
  rw [hrange] at hmem
  exact Submodule.mem_span_pair.mp hmem

theorem pairSpan_coefficients_nonzero (a b c : DualPoint p) (hac : a ≠ c) (hbc : b ≠ c)
    (x y : ZMod p) (h : x • a.rep + y • b.rep = c.rep) : x ≠ 0 ∧ y ≠ 0 := by
  constructor
  · intro hx
    have hrep : y • b.rep = c.rep := by simpa only [hx, zero_smul, zero_add] using h
    have heq := (Projectivization.mk_eq_mk_iff' (ZMod p) c.rep b.rep c.rep_nonzero b.rep_nonzero).mpr
      ⟨y, hrep⟩
    exact hbc (by simpa only [Projectivization.mk_rep] using heq.symm)
  · intro hy
    have hrep : x • a.rep = c.rep := by simpa only [hy, zero_smul, add_zero] using h
    have heq := (Projectivization.mk_eq_mk_iff' (ZMod p) c.rep a.rep c.rep_nonzero a.rep_nonzero).mpr
      ⟨x, hrep⟩
    exact hac (by simpa only [Projectivization.mk_rep] using heq.symm)

def pointVector {K : Type*} [Field K] (f : ZMod p →+* K) (H : DualPoint p) : Fin 4 → K :=
  fun j => f (coefficientVector p H j)

theorem pointVector_combination {K : Type*} [Field K] (f : ZMod p →+* K)
    (a b c : DualPoint p) (x y : ZMod p) (h : x • a.rep + y • b.rep = c.rep) :
    pointVector p f c = f x • pointVector p f a + f y • pointVector p f b := by
  funext j
  have hj := LinearMap.congr_fun h (Pi.single j 1)
  change x * coefficientVector p a j + y * coefficientVector p b j = coefficientVector p c j at hj
  have hm := congrArg f hj
  simpa only [pointVector, Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_add, map_mul] using hm.symm

theorem quadric_zero_on_actual_line {K : Type*} [Field K] [Infinite K]
    (f : ZMod p →+* K) (Q : MvPolynomial (Fin 4) K) (hQ : Q.IsHomogeneous 2)
    (L : Submodule (ZMod p) (DualSpace p)) (hL : Module.finrank (ZMod p) L = 2)
    (a b c : DualPoint p) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (haL : a.submodule ≤ L) (hbL : b.submodule ≤ L) (hcL : c.submodule ≤ L)
    (ha : eval (pointVector p f a) Q = 0) (hb : eval (pointVector p f b) Q = 0)
    (hc : eval (pointVector p f c) Q = 0) :
    ∀ R : DualPoint p, R.submodule ≤ L → eval (pointVector p f R) Q = 0 := by
  have hspan := WhitePlaneHyperfocus.pairSpan_eq_line p a b hab L hL haL hbL
  obtain ⟨x, y, hxy⟩ := pairSpan_coefficients p a b c (by rwa [hspan])
  obtain ⟨hx, hy⟩ := pairSpan_coefficients_nonzero p a b c hac hbc x y hxy
  have hzero := QuadricLineAlgebra.vanish_on_span_of_three Q hQ
    (pointVector p f a) (pointVector p f b) (f x) (f y)
    (fun h => hx (f.injective (by simpa only [map_zero] using h)))
    (fun h => hy (f.injective (by simpa only [map_zero] using h))) ha hb
    (by rwa [← pointVector_combination p f a b c x y hxy])
  intro R hRL
  obtain ⟨u, v, huv⟩ := pairSpan_coefficients p a b R (by rwa [hspan])
  rw [pointVector_combination p f a b R u v huv]
  exact hzero (f u) (f v)

theorem no_quadric_of_not_isArc {K : Type*} [Field K] [Infinite K] [Algebra (ZMod p) K]
    {S : Finset (Geometry.Point p)} (hp : 11 ≤ p)
    (hcard : S.card = p ^ 2) (hS : Geometry.PDivisible p S) (hnon : ¬Geometry.IsCylinder p S)
    (hnotarc : ¬IsArc p S) (Q : MvPolynomial (Fin 4) K) (hQ : Q.IsHomogeneous 2) (hQ0 : Q ≠ 0)
    (hwhite : ∀ H ∈ whitePoints p S, eval (pointVector p (algebraMap (ZMod p) K) H) Q = 0) : False := by
  unfold IsArc at hnotarc
  push Not at hnotarc
  obtain ⟨L, hL, hlarge⟩ := hnotarc
  obtain ⟨a, ha, b, hb, c, hc, hab, hac, hbc⟩ := Finset.two_lt_card.mp hlarge
  have haL := (mem_linePoints p L a).mp (Finset.mem_inter.mp ha).1
  have hbL := (mem_linePoints p L b).mp (Finset.mem_inter.mp hb).1
  have hcL := (mem_linePoints p L c).mp (Finset.mem_inter.mp hc).1
  have haW := (Finset.mem_inter.mp ha).2
  have hbW := (Finset.mem_inter.mp hb).2
  have hcW := (Finset.mem_inter.mp hc).2
  obtain ⟨R, hRB, hRL⟩ := exists_black_of_two_white p hcard hS L hL a b hab haW hbW haL hbL
  have hRzero := quadric_zero_on_actual_line p (algebraMap (ZMod p) K) Q hQ L hL a b c hab hac hbc
    haL hbL hcL (hwhite a haW) (hwhite b hbW) (hwhite c hcW) R hRL
  exact QuadricBlackExclusion.black_not_on_quadric p hp hcard hS hnon Q hQ hQ0 hwhite hRB hRzero

end Cylinder.NoWhiteQuadric

end
