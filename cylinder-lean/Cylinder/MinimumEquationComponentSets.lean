module

public import Cylinder.MinimumEquationComponents

/-! The cofactor filter is precisely the set of points on one component
and on no other component. Degrees of the distinct factors add to the
degree of a reduced equation. -/

@[expose] public section
noncomputable section
open scoped Classical BigOperators

namespace Cylinder.MinimumEquationComponentSets

open MvPolynomial UniqueFactorizationMonoid
open Cylinder.RationalPlaneLine Cylinder.MinimumEquationComponents Cylinder.PlaneCurveFactors

variable {K : Type*} [Field K]

local instance : NormalizedGCDMonoid (MvPolynomial (Fin 3) K) := Classical.arbitrary _

theorem factors_product_associated (F : MvPolynomial (Fin 3) K)
    (hF0 : F ≠ 0) (hF : Squarefree F) :
    Associated (∏ G ∈ PlaneCurveFactors.factors F, G) F := by
  have hnodup := (squarefree_iff_nodup_normalizedFactors hF0).mp hF
  have hprod : (∏ G ∈ PlaneCurveFactors.factors F, G) = (normalizedFactors F).prod := by
    unfold PlaneCurveFactors.factors
    rw [Finset.prod_eq_multiset_prod]
    simp only [Multiset.toFinset_val, hnodup.dedup]
    change (Multiset.map id (normalizedFactors F)).prod = (normalizedFactors F).prod
    rw [Multiset.map_id]
  rw [hprod]
  exact prod_normalizedFactors hF0

theorem factors_degree_sum_eq (F : MvPolynomial (Fin 3) K)
    (hF0 : F ≠ 0) (hF : Squarefree F) :
    (∑ G ∈ PlaneCurveFactors.factors F, G.totalDegree) = F.totalDegree := by
  have hprod := factors_product_associated F hF0 hF
  have hprod0 : (∏ G ∈ PlaneCurveFactors.factors F, G) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun G hG => (factor_irreducible F G hG).ne_zero)
  have hlo := totalDegree_le_of_dvd_of_isDomain hprod.dvd hF0
  have hhi := totalDegree_le_of_dvd_of_isDomain hprod.symm.dvd hprod0
  rw [Cylinder.FactorDegreeBound.totalDegree_prod (PlaneCurveFactors.factors F) (fun G => G)
    (fun G hG => (factor_irreducible F G hG).ne_zero)] at hlo hhi
  exact le_antisymm hlo hhi

theorem eval_cofactor_zero_iff (F G H : MvPolynomial (Fin 3) K)
    (hF0 : F ≠ 0) (hF : Squarefree F) (hG : G ∈ PlaneCurveFactors.factors F) (hGH : F = G * H)
    (v : Fin 3 → K) :
    eval v H = 0 ↔ ∃ Q ∈ (PlaneCurveFactors.factors F).erase G, eval v Q = 0 := by
  have hGirr := factor_irreducible F G hG
  have hH0 : H ≠ 0 := by
    intro hz
    rw [hGH, hz, mul_zero] at hF0
    exact hF0 rfl
  have hHdF : H ∣ F := by rw [hGH]; exact dvd_mul_left H G
  have hmult := (dvd_iff_normalizedFactors_le_normalizedFactors hH0 hF0).mp hHdF
  constructor
  · intro hzero
    obtain ⟨Q, hQ, hQzero⟩ := (eval_zero_iff_factor_zero H hH0 v).mp hzero
    have hQF : Q ∈ PlaneCurveFactors.factors F := Multiset.mem_toFinset.mpr
      (Multiset.mem_of_le hmult (Multiset.mem_toFinset.mp hQ))
    have hQG : Q ≠ G := by
      intro heq
      subst Q
      have hrel : IsRelPrime G H := IsRelPrime.of_squarefree_mul (hGH ▸ hF)
      exact hGirr.not_isUnit (hrel dvd_rfl (factor_dvd H G hQ))
    exact ⟨Q, Finset.mem_erase.mpr ⟨hQG, hQF⟩, hQzero⟩
  · rintro ⟨Q, hQ, hQzero⟩
    obtain ⟨hQG, hQF⟩ := Finset.mem_erase.mp hQ
    have hQdvd := factor_dvd F Q hQF
    rw [hGH] at hQdvd
    have hQH : Q ∣ H := by
      rcases (factor_irreducible F Q hQF).prime.dvd_mul.mp hQdvd with hQGdvd | hQH
      · exact (hQG (normalizedFactors_eq_of_dvd F Q (Multiset.mem_toFinset.mp hQF)
          G (Multiset.mem_toFinset.mp hG) hQGdvd)).elim
      · exact hQH
    obtain ⟨R, hHR⟩ := hQH
    rw [hHR, map_mul, hQzero, zero_mul]

def componentPoints (D : Finset (PlanePoint K)) (F G : MvPolynomial (Fin 3) K) :
    Finset (PlanePoint K) :=
  D.filter (fun P => eval P.rep G = 0 ∧
    ∀ Q ∈ (PlaneCurveFactors.factors F).erase G, eval P.rep Q ≠ 0)

theorem exclusivePoints_eq_componentPoints (D : Finset (PlanePoint K))
    (F G H : MvPolynomial (Fin 3) K) (hF0 : F ≠ 0) (hF : Squarefree F)
    (hG : G ∈ PlaneCurveFactors.factors F) (hGH : F = G * H)
    (hzero : ∀ P ∈ D, eval P.rep F = 0) :
    exclusivePoints D H = componentPoints D F G := by
  ext P
  simp only [exclusivePoints, componentPoints, Finset.mem_filter]
  constructor
  · rintro ⟨hPD, hPH⟩
    refine ⟨hPD, factor_zero_on_exclusive D F G H hGH hzero P
      (Finset.mem_filter.mpr ⟨hPD, hPH⟩), ?_⟩
    intro Q hQ hQzero
    exact hPH ((eval_cofactor_zero_iff F G H hF0 hF hG hGH P.rep).mpr ⟨Q, hQ, hQzero⟩)
  · rintro ⟨hPD, _hPG, hothers⟩
    refine ⟨hPD, ?_⟩
    intro hPH
    obtain ⟨Q, hQ, hQzero⟩ :=
      (eval_cofactor_zero_iff F G H hF0 hF hG hGH P.rep).mp hPH
    exact hothers Q hQ hQzero

theorem componentPoints_disjoint (D : Finset (PlanePoint K))
    (F G Q : MvPolynomial (Fin 3) K) (hQ : Q ∈ PlaneCurveFactors.factors F) (hGQ : G ≠ Q) :
    Disjoint (componentPoints D F G) (componentPoints D F Q) := by
  apply Finset.disjoint_left.mpr
  intro P hPG hPQ
  obtain ⟨_, _, hothers⟩ := Finset.mem_filter.mp hPG
  obtain ⟨_, hQzero, _⟩ := Finset.mem_filter.mp hPQ
  exact hothers Q (Finset.mem_erase.mpr ⟨hGQ.symm, hQ⟩) hQzero

end Cylinder.MinimumEquationComponentSets

end

