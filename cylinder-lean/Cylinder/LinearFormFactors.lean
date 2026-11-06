module

public import Cylinder.FiniteFieldHyperplaneDivisibility
public import Cylinder.FactorDegreeBound
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
public import Mathlib.LinearAlgebra.Projectivization.Basic

/-! Nonzero linear equations are prime factors. Their association
relation is exactly scalar proportionality of the actual coefficients. -/

@[expose] public section
noncomputable section
open scoped Classical BigOperators

namespace Cylinder.LinearFormFactors

open MvPolynomial Cylinder.PowerEvaluationRelation

variable {K σ : Type} [Field K] [Fintype σ]

theorem eval_linearForm_single (l : σ → K) (i : σ) :
    eval (Pi.single i 1) (linearForm l) = l i := by
  simp [linearForm, Pi.single_apply]

theorem linearForm_ne_zero (l : σ → K) (hl : l ≠ 0) : linearForm l ≠ 0 := by
  intro hz
  apply hl
  funext i
  have hh := congrArg (eval (Pi.single i 1)) hz
  simpa only [eval_linearForm_single, map_zero, Pi.zero_apply] using hh

theorem linearForm_homogeneous (l : σ → K) : (linearForm l).IsHomogeneous 1 :=
  IsHomogeneous.sum Finset.univ _ 1 (fun i _ => isHomogeneous_C_mul_X (l i) i)

theorem linearForm_totalDegree (l : σ → K) (hl : l ≠ 0) : (linearForm l).totalDegree = 1 :=
  (linearForm_homogeneous l).totalDegree (linearForm_ne_zero l hl)

theorem linearForm_irreducible (l : σ → K) (hl : l ≠ 0) : Irreducible (linearForm l) := by
  apply irreducible_of_totalDegree_eq_one (linearForm_totalDegree l hl)
  intro c hc
  apply isUnit_iff_ne_zero.mpr
  intro hz
  apply linearForm_ne_zero l hl
  ext m
  exact zero_dvd_iff.mp (by simpa only [hz] using hc m)

theorem linearForm_prime (l : σ → K) (hl : l ≠ 0) : Prime (linearForm l) :=
  (linearForm_irreducible l hl).prime

theorem coefficients_proportional_of_associated (l m : σ → K)
    (h : Associated (linearForm l) (linearForm m)) :
    ∃ c : K, c ≠ 0 ∧ m = c • l := by
  obtain ⟨u, hu⟩ := h
  obtain ⟨c, hc, he⟩ := MvPolynomial.isUnit_iff_eq_C_of_isReduced.mp u.isUnit
  refine ⟨c, isUnit_iff_ne_zero.mp hc, ?_⟩
  funext i
  have hh := congrArg (eval (Pi.single i 1)) hu
  rw [he, map_mul, eval_linearForm_single, eval_C, eval_linearForm_single] at hh
  change m i = c * l i
  exact hh.symm.trans (mul_comm _ _)

theorem linearForms_not_associated (l m : σ → K) (h : ∀ c : K, m ≠ c • l) :
    ¬Associated (linearForm l) (linearForm m) := by
  intro ha
  obtain ⟨c, _hc, hm⟩ := coefficients_proportional_of_associated l m ha
  exact h c hm

theorem projective_linearForms_not_associated
    (P Q : Projectivization K (σ → K)) (hPQ : P ≠ Q) :
    ¬Associated (linearForm P.rep) (linearForm Q.rep) := by
  intro ha
  obtain ⟨c, _hc, he⟩ := coefficients_proportional_of_associated P.rep Q.rep ha
  apply hPQ
  rw [← Projectivization.mk_rep P, ← Projectivization.mk_rep Q]
  exact ((Projectivization.mk_eq_mk_iff' K Q.rep P.rep Q.rep_nonzero P.rep_nonzero).mpr ⟨c, he.symm⟩).symm

theorem snoc_zero_ne_zero (v : Fin 3 → K) (hv : v ≠ 0) : (Fin.snoc v (0 : K) : Fin 4 → K) ≠ 0 := by
  intro hz
  apply hv
  funext j
  simpa using congrFun hz j.castSucc

theorem projective_snoc_linearForms_not_associated
    (P Q : Projectivization K (Fin 3 → K)) (hPQ : P ≠ Q) :
    ¬Associated (linearForm (Fin.snoc P.rep 0)) (linearForm (Fin.snoc Q.rep 0)) := by
  intro ha
  obtain ⟨c, _hc, he⟩ := coefficients_proportional_of_associated
    (Fin.snoc P.rep 0) (Fin.snoc Q.rep 0) ha
  have hv : Q.rep = c • P.rep := by
    funext j
    simpa using congrFun he j.castSucc
  apply hPQ
  rw [← Projectivization.mk_rep P, ← Projectivization.mk_rep Q]
  exact ((Projectivization.mk_eq_mk_iff' K Q.rep P.rep Q.rep_nonzero P.rep_nonzero).mpr ⟨c, hv.symm⟩).symm

end Cylinder.LinearFormFactors

end
