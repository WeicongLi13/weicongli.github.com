module

public import Cylinder.PlaneHomogenization
public import Mathlib.RingTheory.Coprime.Lemmas

/-!
# Degree and irreducibility in the actual homogeneous affine chart

A nonlinear irreducible homogeneous equation cannot have the chart
coordinate as a divisor. Actual homogenization therefore recovers its
degree, and lifts a purported affine factorization back to the original
homogeneous equation. This connects the proved affine self-polar
exclusion to an arbitrary homogeneous plane equation.
-/

@[expose] public section
noncomputable section

namespace Cylinder.HomogeneousCurveChart

open MvPolynomial Cylinder.CurveLocalParameter Cylinder.CurvePolarLocal
open Cylinder.PlaneHomogenization Cylinder.FrobeniusPolar
open scoped Classical

variable {K : Type*} [Field K]

theorem first_coordinate_not_isUnit : ¬ IsUnit (X none : HomogeneousPlanePolynomial (K := K)) := by
  intro hunit
  have hd := (MvPolynomial.isUnit_iff_totalDegree_of_isReduced.mp hunit).2
  rw [totalDegree_X] at hd
  exact Nat.one_ne_zero hd

theorem first_coordinate_not_dvd (n : ℕ) (Q : HomogeneousPlanePolynomial (K := K))
    (hQ : Q.IsHomogeneous n) (hirr : Irreducible Q) (hn : 2 ≤ n) :
    ¬ (X none : HomogeneousPlanePolynomial (K := K)) ∣ Q := by
  intro hd
  have ha := (hirr.dvd_iff.mp hd).resolve_left first_coordinate_not_isUnit
  have hle := MvPolynomial.totalDegree_le_of_dvd_of_isDomain ha.dvd (X_ne_zero none)
  rw [hQ.totalDegree hirr.ne_zero, totalDegree_X] at hle
  omega

variable [Infinite K]

theorem dehomogenize_totalDegree (n : ℕ) (Q : HomogeneousPlanePolynomial (K := K))
    (hQ : Q.IsHomogeneous n) (hirr : Irreducible Q) (hn : 2 ≤ n) :
    (dehomogenize Q).totalDegree = n := by
  have hle := (dehomogenize_totalDegree_le Q).trans hQ.totalDegree_le
  by_contra hne
  have hlt : (dehomogenize Q).totalDegree < n := lt_of_le_of_ne hle hne
  have hd := first_coordinate_dvd_homogenize_of_degree_lt n (dehomogenize Q) hlt
  rw [homogenize_dehomogenize n Q hQ] at hd
  exact first_coordinate_not_dvd n Q hQ hirr hn hd

theorem dehomogenize_irreducible (n : ℕ) (Q : HomogeneousPlanePolynomial (K := K))
    (hQ : Q.IsHomogeneous n) (hirr : Irreducible Q) (hn : 2 ≤ n) :
    Irreducible (dehomogenize Q) := by
  have hdegree := dehomogenize_totalDegree n Q hQ hirr hn
  have hnonzero : dehomogenize Q ≠ 0 := by
    intro hz
    exact hirr.ne_zero (dehomogenize_zero_of_homogeneous n Q hQ hz)
  refine ⟨?_, ?_⟩
  · intro hunit
    have hd := (MvPolynomial.isUnit_iff_totalDegree_of_isReduced.mp hunit).2
    rw [hdegree] at hd
    omega
  · intro f g hfg
    have hf : f ≠ 0 := by
      intro hf
      rw [hf, zero_mul] at hfg
      exact hnonzero hfg
    have hg : g ≠ 0 := by
      intro hg
      rw [hg, mul_zero] at hfg
      exact hnonzero hfg
    have hsum : f.totalDegree + g.totalDegree = n := by
      have h := congrArg MvPolynomial.totalDegree hfg
      rw [hdegree, totalDegree_mul_of_isDomain hf hg] at h
      exact h.symm
    have hhom : (homogenize f.totalDegree f * homogenize g.totalDegree g).IsHomogeneous n := by
      have h := (homogenize_homogeneous f.totalDegree f le_rfl).mul
        (homogenize_homogeneous g.totalDegree g le_rfl)
      simpa only [hsum] using h
    have hlift : Q = homogenize f.totalDegree f * homogenize g.totalDegree g := by
      apply dehomogenize_injective_on_homogeneous n _ _ hQ hhom
      rw [map_mul, dehomogenize_homogenize, dehomogenize_homogenize]
      exact hfg
    rcases hirr.isUnit_or_isUnit hlift with huf | hug
    · left
      simpa only [dehomogenize_homogenize] using huf.map dehomogenize
    · right
      simpa only [dehomogenize_homogenize] using hug.map dehomogenize

omit [Infinite K] in
theorem not_self_polar [IsAlgClosed K] (p n : ℕ) [CharP K p]
    (Q : HomogeneousPlanePolynomial (K := K)) (hQ : Q.IsHomogeneous n)
    (hirr : Irreducible Q) (hn : 2 ≤ n) (hnp : n < p) : ¬ Q ∣ polar p Q := by
  intro hdiv
  have hdegree := dehomogenize_totalDegree n Q hQ hirr hn
  have hirra := dehomogenize_irreducible n Q hQ hirr hn
  have hdiva : dehomogenize Q ∣ CurveSelfPolarParameter.affinePolar p n (dehomogenize Q) := by
    rw [← CurveSelfPolarParameter.dehomogenize_polar p n Q hQ]
    exact map_dvd dehomogenize hdiv
  exact CurveSelfPolarExclusion.not_self_polar p n (dehomogenize Q) hirra
    (by rwa [hdegree]) (by rwa [hdegree]) hdiva

omit [Infinite K] in
theorem polar_ne_zero [IsAlgClosed K] (p n : ℕ) [CharP K p]
    (Q : HomogeneousPlanePolynomial (K := K)) (hQ : Q.IsHomogeneous n)
    (hirr : Irreducible Q) (hn : 2 ≤ n) (hnp : n < p) : polar p Q ≠ 0 := by
  intro hz
  apply not_self_polar p n Q hQ hirr hn hnp
  rw [hz]
  exact dvd_zero Q

omit [Infinite K] in
theorem polar_relPrime [IsAlgClosed K] (p n : ℕ) [CharP K p]
    (Q : HomogeneousPlanePolynomial (K := K)) (hQ : Q.IsHomogeneous n)
    (hirr : Irreducible Q) (hn : 2 ≤ n) (hnp : n < p) : IsRelPrime Q (polar p Q) := by
  intro D hDQ hDH
  rcases hirr.dvd_iff.mp hDQ with hunit | hassoc
  · exact hunit
  · exact False.elim (not_self_polar p n Q hQ hirr hn hnp (hassoc.dvd.trans hDH))

omit [Infinite K] in
theorem polar_totalDegree [IsAlgClosed K] (p n : ℕ) [CharP K p]
    (Q : HomogeneousPlanePolynomial (K := K)) (hQ : Q.IsHomogeneous n)
    (hirr : Irreducible Q) (hn : 2 ≤ n) (hnp : n < p) :
    (polar p Q).totalDegree = n + p - 1 :=
  FrobeniusPolar.polar_totalDegree p n (by omega) Q hQ (polar_ne_zero p n Q hQ hirr hn hnp)

end Cylinder.HomogeneousCurveChart

end
