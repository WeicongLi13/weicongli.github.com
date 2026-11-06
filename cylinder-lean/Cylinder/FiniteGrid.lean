module

public import Mathlib.FieldTheory.Finite.Polynomial
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.Algebra.BigOperators.Fin
public meta import Lean.Elab.Tactic.Omega

/-!
# Reduced polynomials and interpolation on a finite grid

The evaluation map on polynomials of degree less than the field size in
each variable is injective.  In two variables we construct the indicator
interpolation used in Lemma `lem:projectionpoly`, prove that it recovers
the function, and verify its individual-variable degree bounds.

We also prove the nonzero-direction assertion for the highest homogeneous
component, including the constant-polynomial case.
-/

@[expose] public section

noncomputable section

open scoped Classical

namespace Cylinder.FiniteGrid

open MvPolynomial

-- Mathlib's finite-grid rank argument uses a common universe for the
-- variable type and coefficient field. These concrete finite-field
-- interfaces use `Type`, as do `ZMod p` and `Fin 2` in the paper.
variable {K σ : Type} [Field K] [Fintype K]

/-- Convert strict individual-variable degree bounds to the reduced
polynomial submodule used by Mathlib. -/
theorem mem_restrictDegree_of_degreeOf_lt_card (P : MvPolynomial σ K)
    (hdegree : ∀ i, P.degreeOf i < Fintype.card K) :
    P ∈ restrictDegree σ K (Fintype.card K - 1) := by
  rw [mem_restrictDegree_iff_sup]
  intro i
  have hi := hdegree i
  rw [degreeOf_def] at hi
  omega

/-- A reduced polynomial vanishing on the complete finite grid is zero.
The injectivity theorem is proved in Mathlib, not assumed here. -/
theorem eq_zero_of_degreeOf_lt_card [Finite σ] (P : MvPolynomial σ K)
    (hdegree : ∀ i, P.degreeOf i < Fintype.card K)
    (heval : ∀ v : σ → K, eval v P = 0) : P = 0 :=
  MvPolynomial.eq_zero_of_eval_eq_zero σ K P heval
    (mem_restrictDegree_of_degreeOf_lt_card P hdegree)

/-- Every nonzero reduced polynomial has a nonzero value on the grid. -/
theorem exists_eval_ne_zero_of_degreeOf_lt_card [Finite σ] (P : MvPolynomial σ K)
    (hP : P ≠ 0) (hdegree : ∀ i, P.degreeOf i < Fintype.card K) :
    ∃ v : σ → K, eval v P ≠ 0 := by
  by_contra h
  apply hP
  apply eq_zero_of_degreeOf_lt_card P hdegree
  intro v
  by_contra hv
  exact h ⟨v, hv⟩

/-- The two-variable finite-field indicator. -/
def binaryIndicator (a b : K) : MvPolynomial (Fin 2) K :=
  MvPolynomial.indicator ![a, b]

theorem binaryIndicator_formula (a b : K) :
    binaryIndicator a b =
      (1 - (X 0 - C a) ^ (Fintype.card K - 1)) *
        (1 - (X 1 - C b) ^ (Fintype.card K - 1)) := by
  simp [binaryIndicator, MvPolynomial.indicator, Fin.prod_univ_two]

@[simp] theorem eval_binaryIndicator (a b x y : K) :
    eval ![x, y] (binaryIndicator a b) =
      if x = a ∧ y = b then 1 else 0 := by
  by_cases hx : x = a
  · by_cases hy : y = b
    · subst x
      subst y
      simpa [binaryIndicator] using MvPolynomial.eval_indicator_apply_eq_one ![a, b]
    · have hvec : ![x, y] ≠ ![a, b] := by
        intro h
        exact hy (by simpa using congrFun h 1)
      simpa [binaryIndicator, hx, hy] using
        MvPolynomial.eval_indicator_apply_eq_zero ![x, y] ![a, b] hvec
  · have hvec : ![x, y] ≠ ![a, b] := by
      intro h
      exact hx (by simpa using congrFun h 0)
    simpa [binaryIndicator, hx] using
      MvPolynomial.eval_indicator_apply_eq_zero ![x, y] ![a, b] hvec

/-- The explicit indicator interpolation polynomial. -/
def binaryInterpolation (f : K → K → K) : MvPolynomial (Fin 2) K :=
  ∑ a : K, ∑ b : K, f a b • binaryIndicator a b

theorem binaryInterpolation_formula (f : K → K → K) :
    binaryInterpolation f = ∑ a : K, ∑ b : K,
      C (f a b) *
        (1 - (X 0 - C a) ^ (Fintype.card K - 1)) *
        (1 - (X 1 - C b) ^ (Fintype.card K - 1)) := by
  simp only [binaryInterpolation, binaryIndicator_formula, smul_eq_C_mul, mul_assoc]

@[simp] theorem eval_binaryInterpolation (f : K → K → K) (x y : K) :
    eval ![x, y] (binaryInterpolation f) = f x y := by
  simp only [binaryInterpolation, map_sum, smul_eval, eval_binaryIndicator]
  rw [Finset.sum_eq_single x]
  · rw [Finset.sum_eq_single y]
    · simp
    · intro b _ hb
      simp [Ne.symm hb]
    · intro h
      exact (h (Finset.mem_univ y)).elim
  · intro a _ ha
    apply Finset.sum_eq_zero
    intro b _
    simp [Ne.symm ha]
  · intro h
    exact (h (Finset.mem_univ x)).elim

theorem binaryInterpolation_mem_restrictDegree (f : K → K → K) :
    binaryInterpolation f ∈ restrictDegree (Fin 2) K (Fintype.card K - 1) := by
  apply Submodule.sum_mem
  intro a _
  apply Submodule.sum_mem
  intro b _
  exact Submodule.smul_mem _ _ (MvPolynomial.indicator_mem_restrictDegree ![a, b])

theorem binaryInterpolation_degreeOf_le (f : K → K → K) (i : Fin 2) :
    (binaryInterpolation f).degreeOf i ≤ Fintype.card K - 1 := by
  have h := (mem_restrictDegree_iff_sup _ _ _).mp
    (binaryInterpolation_mem_restrictDegree f) i
  simpa only [degreeOf_def] using h

omit [Fintype K] in
/-- The highest homogeneous component of a nonzero polynomial is nonzero. -/
theorem top_homogeneousComponent_ne_zero (P : MvPolynomial σ K) (hP : P ≠ 0) :
    homogeneousComponent P.totalDegree P ≠ 0 := by
  obtain ⟨m, hm, hdegree⟩ := Finset.exists_mem_eq_sup P.support
    (MvPolynomial.support_nonempty.mpr hP) (fun m => m.degree)
  have hmdegree : m.degree = P.totalDegree := by
    simpa only [MvPolynomial.totalDegree, Finsupp.degree_apply, Finsupp.sum] using
      hdegree.symm
  intro hzero
  have hcoeff := congrArg (fun Q : MvPolynomial σ K => Q.coeff m) hzero
  rw [coeff_homogeneousComponent, ite_eq_left hmdegree,
    AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply] at hcoeff
  exact (mem_support_iff.mp hm) hcoeff

/-- A nonzero binary homogeneous polynomial of degree below the field
size is nonzero at a nonzero vector. The degree-zero case is included. -/
theorem exists_nonzero_vector_eval_ne_zero (P : MvPolynomial (Fin 2) K)
    (d : ℕ) (hhom : P.IsHomogeneous d) (hP : P ≠ 0)
    (hdegree : d < Fintype.card K) :
    ∃ v : Fin 2 → K, v ≠ 0 ∧ eval v P ≠ 0 := by
  by_cases hd : d = 0
  · have hconstant : P = C (P.coeff 0) :=
      totalDegree_eq_zero_iff_eq_C.mp (hhom.totalDegree hP |>.trans hd)
    have hc : P.coeff 0 ≠ 0 := by
      intro hz
      apply hP
      rw [hconstant, hz, map_zero]
    refine ⟨![1, 0], ?_, ?_⟩
    · intro hz
      exact one_ne_zero (congrFun hz 0)
    · rw [hconstant, eval_C]
      exact hc
  · have hindividual : ∀ i, P.degreeOf i < Fintype.card K := by
      intro i
      rw [← hhom.totalDegree hP] at hdegree
      exact (degreeOf_le_totalDegree P i).trans_lt hdegree
    obtain ⟨v, hv⟩ := exists_eval_ne_zero_of_degreeOf_lt_card P hP hindividual
    refine ⟨v, ?_, hv⟩
    intro hz
    apply hv
    rw [hz, eval_zero, constantCoeff_eq]
    exact hhom.coeff_eq_zero (by simpa using Ne.symm hd)

/-- The highest-degree homogeneous part used in the projection argument
is nonzero in a nonzero direction when total degree is at most `q - 2`. -/
theorem top_component_has_nonzero_direction (P : MvPolynomial (Fin 2) K)
    (hP : P ≠ 0) (hdegree : P.totalDegree ≤ Fintype.card K - 2) :
    ∃ v : Fin 2 → K, v ≠ 0 ∧ eval v (homogeneousComponent P.totalDegree P) ≠ 0 := by
  apply exists_nonzero_vector_eval_ne_zero _ P.totalDegree
    (homogeneousComponent_isHomogeneous _ _) (top_homogeneousComponent_ne_zero P hP)
  have hcard : 1 < Fintype.card K := Fintype.one_lt_card
  omega

section ZMod

variable {p : ℕ} [Fact p.Prime]

theorem zmod_eq_zero_of_degreeOf_lt (P : MvPolynomial σ (ZMod p)) [Finite σ]
    (hdegree : ∀ i, P.degreeOf i < p)
    (heval : ∀ v : σ → ZMod p, eval v P = 0) : P = 0 := by
  apply eq_zero_of_degreeOf_lt_card P _ heval
  simpa only [ZMod.card] using hdegree

theorem zmod_binaryInterpolation_formula (f : ZMod p → ZMod p → ZMod p) :
    binaryInterpolation f = ∑ a : ZMod p, ∑ b : ZMod p,
      C (f a b) * (1 - (X 0 - C a) ^ (p - 1)) *
        (1 - (X 1 - C b) ^ (p - 1)) := by
  simpa only [ZMod.card] using binaryInterpolation_formula f

theorem zmod_binaryInterpolation_degreeOf_le (f : ZMod p → ZMod p → ZMod p)
    (i : Fin 2) : (binaryInterpolation f).degreeOf i ≤ p - 1 := by
  simpa only [ZMod.card] using binaryInterpolation_degreeOf_le f i

theorem zmod_top_component_has_nonzero_direction (P : MvPolynomial (Fin 2) (ZMod p))
    (hP : P ≠ 0) (hdegree : P.totalDegree ≤ p - 2) :
    ∃ v : Fin 2 → ZMod p, v ≠ 0 ∧
      eval v (homogeneousComponent P.totalDegree P) ≠ 0 := by
  apply top_component_has_nonzero_direction P hP
  simpa only [ZMod.card] using hdegree

end ZMod

end Cylinder.FiniteGrid
