module

public import Cylinder.AffineEvaluationDuality

/-! Actual finite complete-intersection point relations vanish once the
genuine affine total-degree filtration spans the quotient. -/

@[expose] public section
noncomputable section

namespace Cylinder.AffineEvaluationHighDegrees

open Module MvPolynomial
open Cylinder.PlaneBinaryReduction Cylinder.CompleteIntersectionKoszul
open Cylinder.CompleteIntersectionFiltered Cylinder.AffinePointEvaluation
open Cylinder.FiniteEvaluationDuality Cylinder.AffineFilteredAlgebra
open scoped Classical BigOperators

variable {K I : Type*} [Field K] [Fintype I]

theorem coefficientRelations_eq_bot (f g : BinaryRing K) (e t : ℕ)
    (he : 0 < e) (ht : 0 < t) (hf : f.totalDegree = e) (hg : g.totalDegree = t)
    (hfe : homogeneousComponent e f ≠ 0) (hge : homogeneousComponent t g ≠ 0)
    (hcop : IsRelPrime (homogeneousComponent e f) (homogeneousComponent t g))
    (v : I → Fin 2 → K) (hv : Function.Injective v)
    (hfv : ∀ i, eval (v i) f = 0) (hgv : ∀ i, eval (v i) g = 0)
    (j : ℕ) (hj : e + t - 2 ≤ j) : coefficientRelations v j = ⊥ := by
  apply eq_bot_iff.mpr
  intro c hc
  apply (Submodule.mem_bot K).mpr
  apply coefficientDualMap_injective
  apply LinearMap.ext
  intro w
  obtain ⟨a, ha⟩ := evaluation_surjective f g v hv hfv hgv w
  obtain ⟨P, hPa⟩ := Ideal.Quotient.mk_surjective a
  obtain ⟨Q, hQdeg, hQP⟩ := exists_low_degree_representative f g e t he ht hf hg hfe hge hcop P
  have hQw : evaluation f g v hfv hgv (Ideal.Quotient.mk (equationsIdeal f g) Q) = w := by
    rw [hQP, hPa, ha]
  have hz := (mem_coefficientRelations v j c).mp hc Q (hQdeg.trans hj)
  change coefficientDualMap c w = coefficientDualMap 0 w
  rw [← hQw]
  rw [evaluation_mk]
  change (∑ i, c i * eval (v i) Q) = ∑ i, (0 : K) * eval (v i) Q
  simpa only [zero_mul, Finset.sum_const_zero] using hz

#print axioms coefficientRelations_eq_bot

end Cylinder.AffineEvaluationHighDegrees

end
