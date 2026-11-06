module

public import Cylinder.PlaneLinearForms
public import Cylinder.PlaneCrossProduct

/-! Line equations over an extension field and the actual base-field points. -/

@[expose] public section
noncomputable section
open scoped Classical BigOperators

namespace Cylinder.RationalPlaneLine

open MvPolynomial Cylinder.PlaneCrossProduct Cylinder.PlaneLinearForms
open Cylinder.PowerEvaluationRelation

variable {K L : Type*} [Field K] [Field L]

theorem eval_linearForm (a v : Fin 3 → L) : eval v (linearForm a) = dot a v := by
  simp [linearForm, dot]

/-- A true extension-field line through two independent base-field points
is a nonzero scalar multiple of a true base-field line equation. -/
theorem line_equation_descends (f : K →+* L) (F : MvPolynomial (Fin 3) L)
    (hF : F.IsHomogeneous 1) (hF0 : F ≠ 0) (v w : Fin 3 → K)
    (hv : v ≠ 0) (hn : ∀ a : K, w ≠ a • v)
    (hzero_v : eval (fun j => f (v j)) F = 0)
    (hzero_w : eval (fun j => f (w j)) F = 0) :
    ∃ c : Fin 3 → K, c ≠ 0 ∧ ∃ u : L, u ≠ 0 ∧
      F = linearForm (u • (fun j => f (c j))) := by
  obtain ⟨a, hFa⟩ := exists_coefficients F hF
  have ha := coefficients_ne_zero F a hF0 hFa
  have hc := cross_ne_zero v w hv hn
  have hmc : cross (fun j => f (v j)) (fun j => f (w j)) ≠ 0 := by
    rw [← map_cross f v w]
    intro hzero
    apply hc
    funext j
    exact f.injective (by simpa only [map_zero, Pi.zero_apply] using congrFun hzero j)
  obtain ⟨u, hu, hau⟩ := annihilator_proportional a (fun j => f (v j))
    (fun j => f (w j)) ha hmc
    (by simpa only [hFa, eval_linearForm] using hzero_v)
    (by simpa only [hFa, eval_linearForm] using hzero_w)
  rw [← map_cross f v w] at hau
  exact ⟨cross v w, hc, u, hu, hFa.trans (congrArg linearForm hau)⟩

theorem eval_mapped_scalar_linearForm (f : K →+* L) (c v : Fin 3 → K) (u : L) :
    eval (fun j => f (v j)) (linearForm (u • (fun j => f (c j)))) = u * f (dot c v) := by
  simp [linearForm, dot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]

abbrev PlanePoint (K : Type*) [Field K] := Projectivization K (Fin 3 → K)

def zeroSet (f : K →+* L) (D : Finset (PlanePoint K)) (F : MvPolynomial (Fin 3) L) :
    Finset (PlanePoint K) := D.filter (fun P => eval (fun j => f (P.rep j)) F = 0)

def LineCap (D : Finset (PlanePoint K)) (b : ℕ) : Prop :=
  ∀ c : Fin 3 → K, c ≠ 0 → (D.filter (fun P => dot c P.rep = 0)).card ≤ b

theorem representatives_not_proportional (P Q : PlanePoint K) (hPQ : P ≠ Q) :
    ∀ a : K, Q.rep ≠ a • P.rep := by
  intro a ha
  have h := (Projectivization.mk_eq_mk_iff' K Q.rep P.rep Q.rep_nonzero P.rep_nonzero).mpr ⟨a, ha.symm⟩
  exact hPQ (by simpa only [Projectivization.mk_rep] using h.symm)

/-- The line cap over the base field bounds every extension-field linear
factor. A line through at most one base-field point is handled separately. -/
theorem linear_factor_card_bound (f : K →+* L) (D : Finset (PlanePoint K)) (b : ℕ)
    (hb : 1 ≤ b) (hcap : LineCap D b) (F : MvPolynomial (Fin 3) L)
    (hF : F.IsHomogeneous 1) (hF0 : F ≠ 0) : (zeroSet f D F).card ≤ b := by
  by_cases hsmall : (zeroSet f D F).card ≤ 1
  · exact hsmall.trans hb
  · have htwo : 1 < (zeroSet f D F).card := by omega
    obtain ⟨P, hP, Q, hQ, hPQ⟩ := Finset.one_lt_card.mp htwo
    obtain ⟨c, hc, u, hu, hFu⟩ := line_equation_descends f F hF hF0 P.rep Q.rep
      P.rep_nonzero (representatives_not_proportional P Q hPQ)
      (Finset.mem_filter.mp hP).2 (Finset.mem_filter.mp hQ).2
    apply (Finset.card_le_card (show zeroSet f D F ⊆ D.filter (fun R => dot c R.rep = 0) from ?_)).trans
      (hcap c hc)
    intro R hR
    obtain ⟨hRD, hRF⟩ := Finset.mem_filter.mp hR
    refine Finset.mem_filter.mpr ⟨hRD, ?_⟩
    rw [hFu, eval_mapped_scalar_linearForm] at hRF
    exact f.injective (by simpa only [map_zero] using (mul_eq_zero.mp hRF).resolve_left hu)

theorem exists_nonzero_line_through (v : Fin 3 → K) :
    ∃ c : Fin 3 → K, c ≠ 0 ∧ dot c v = 0 := by
  by_cases h0 : v 0 = 0
  · refine ⟨![1, 0, 0], ?_, ?_⟩
    · intro h
      have h' : (1 : K) = 0 := congrFun h 0
      exact one_ne_zero h'
    · simp [dot, Fin.sum_univ_succ, h0]
  · refine ⟨![v 1, -v 0, 0], ?_, ?_⟩
    · intro h
      have h' : -v 0 = 0 := congrFun h 1
      exact h0 (neg_eq_zero.mp h')
    · simp [dot, Fin.sum_univ_succ]
      ring

theorem lineCap_zero_implies_empty (D : Finset (PlanePoint K)) (hcap : LineCap D 0) : D = ∅ := by
  apply Finset.eq_empty_of_forall_notMem
  intro P hP
  obtain ⟨c, hc, hcP⟩ := exists_nonzero_line_through P.rep
  have hpos : 0 < (D.filter (fun R => dot c R.rep = 0)).card :=
    Finset.card_pos.mpr ⟨P, Finset.mem_filter.mpr ⟨hP, hcP⟩⟩
  have h := hcap c hc
  omega

end Cylinder.RationalPlaneLine

end
