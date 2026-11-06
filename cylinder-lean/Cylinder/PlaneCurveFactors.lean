module

public import Cylinder.RationalPlaneLine
public import Cylinder.HomogeneousFactors
public import Cylinder.FactorDegreeBound
public import Mathlib.Algebra.BigOperators.Ring.Multiset

/-! The actual distinct irreducible factors of a homogeneous plane equation. -/

@[expose] public section
noncomputable section
open scoped Classical BigOperators

namespace Cylinder.PlaneCurveFactors

open MvPolynomial UniqueFactorizationMonoid

variable {K : Type*} [Field K]

local instance : NormalizedGCDMonoid (MvPolynomial (Fin 3) K) := Classical.arbitrary _

def factors (F : MvPolynomial (Fin 3) K) : Finset (MvPolynomial (Fin 3) K) :=
  (normalizedFactors F).toFinset

theorem factor_irreducible (F G : MvPolynomial (Fin 3) K) (hG : G ∈ factors F) : Irreducible G :=
  irreducible_of_normalized_factor G (Multiset.mem_toFinset.mp hG)

theorem factor_dvd (F G : MvPolynomial (Fin 3) K) (hG : G ∈ factors F) : G ∣ F :=
  dvd_of_mem_normalizedFactors (Multiset.mem_toFinset.mp hG)

theorem factors_pairwise_relPrime (F : MvPolynomial (Fin 3) K) :
    (factors F : Set (MvPolynomial (Fin 3) K)).Pairwise IsRelPrime := by
  intro G hG H hH hGH
  apply (factor_irreducible F G hG).isRelPrime_iff_not_dvd.mpr
  intro hd
  exact hGH (normalizedFactors_eq_of_dvd F G (Multiset.mem_toFinset.mp hG)
    H (Multiset.mem_toFinset.mp hH) hd)

theorem positive_degree_of_irreducible (G : MvPolynomial (Fin 3) K) (hG : Irreducible G) :
    0 < G.totalDegree := by
  by_contra h
  have hdeg : G.totalDegree = 0 := by omega
  have hC := totalDegree_eq_zero_iff_eq_C.mp hdeg
  have hc : G.coeff 0 ≠ 0 := by
    intro hz
    exact hG.ne_zero (by rw [hC, hz, map_zero])
  exact hG.not_isUnit (hC.symm ▸ (isUnit_iff_ne_zero.mpr hc).map C)

theorem factors_degree_sum_le (F : MvPolynomial (Fin 3) K) (hF0 : F ≠ 0) :
    (∑ G ∈ factors F, G.totalDegree) ≤ F.totalDegree := by
  have hprod : (∏ G ∈ factors F, G) ∣ F :=
    Finset.prod_dvd_of_isRelPrime (factors_pairwise_relPrime F) (fun G hG => factor_dvd F G hG)
  have h := totalDegree_le_of_dvd_of_isDomain hprod hF0
  rw [Cylinder.FactorDegreeBound.totalDegree_prod (factors F) (fun G => G)
    (fun G hG => (factor_irreducible F G hG).ne_zero)] at h
  exact h

theorem factor_homogeneous (F : MvPolynomial (Fin 3) K) (s : ℕ) (hF : F.IsHomogeneous s)
    (hF0 : F ≠ 0) (G : MvPolynomial (Fin 3) K) (hG : G ∈ factors F) :
    G.IsHomogeneous G.totalDegree :=
  Cylinder.HomogeneousFactors.homogeneous_of_dvd G F s hF hF0 (factor_dvd F G hG)

theorem eval_zero_iff_factor_zero (F : MvPolynomial (Fin 3) K) (hF0 : F ≠ 0)
    (v : Fin 3 → K) : eval v F = 0 ↔ ∃ G ∈ factors F, eval v G = 0 := by
  constructor
  · intro hzero
    obtain ⟨Q, hQ⟩ := (prod_normalizedFactors hF0).symm.dvd
    have hprod : ((normalizedFactors F).map (eval v)).prod = 0 := by
      rw [← map_multiset_prod, hQ, map_mul, hzero, zero_mul]
    obtain ⟨G, hG, hzeroG⟩ := Multiset.mem_map.mp (Multiset.prod_eq_zero_iff.mp hprod)
    exact ⟨G, Multiset.mem_toFinset.mpr hG, hzeroG⟩
  · rintro ⟨G, hG, hzeroG⟩
    obtain ⟨Q, rfl⟩ := factor_dvd F G hG
    rw [map_mul, hzeroG, zero_mul]

theorem rational_zeroSet_eq_union {L : Type*} [Field L] (f : K →+* L)
    (D : Finset (RationalPlaneLine.PlanePoint K)) (F : MvPolynomial (Fin 3) L) (hF0 : F ≠ 0) :
    RationalPlaneLine.zeroSet f D F = (factors F).biUnion (RationalPlaneLine.zeroSet f D) := by
  ext P
  simp only [RationalPlaneLine.zeroSet, Finset.mem_filter, Finset.mem_biUnion]
  rw [eval_zero_iff_factor_zero F hF0]
  constructor
  · rintro ⟨hPD, G, hG, hzeroG⟩
    exact ⟨G, hG, hPD, hzeroG⟩
  · rintro ⟨G, hG, hPD, hzeroG⟩
    exact ⟨hPD, G, hG, hzeroG⟩

end Cylinder.PlaneCurveFactors

end
