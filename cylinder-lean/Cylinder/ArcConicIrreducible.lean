module

public import Cylinder.MinimumEquationReduced

/-! A nonzero homogeneous quadric through five points of an actual plane
arc is irreducible over every extension field. A nontrivial factorization
has two homogeneous linear factors, each meeting the rational arc in at
most two points. All degrees and line bounds are derived. -/

@[expose] public section
noncomputable section
open scoped Classical

namespace Cylinder.ArcConicIrreducible
open MvPolynomial Cylinder.RationalPlaneLine Cylinder.HilbertEvaluation
open Cylinder.MinimumEquationReduced

variable {K L : Type*} [Field K] [Field L]

theorem irreducible_quadric_on_arc (ι : K →+* L) (W : Finset (PlanePoint K))
    (hcap : LineCap W 2) (hcard : 5 ≤ W.card) (Q : PlaneRing L)
    (hQ : Q.IsHomogeneous 2) (hQ0 : Q ≠ 0)
    (hzero : ∀ P ∈ W, eval (fun j => ι (P.rep j)) Q = 0) : Irreducible Q := by
  have hdegree : Q.totalDegree = 2 := hQ.totalDegree hQ0
  refine ⟨?_, ?_⟩
  · intro hu
    have hdiv : Q ∣ (1 : PlaneRing L) := hu.dvd
    have hle := totalDegree_le_of_dvd_of_isDomain hdiv (one_ne_zero : (1 : PlaneRing L) ≠ 0)
    rw [hdegree] at hle
    simp at hle
  · intro A B hAB
    by_contra hunit
    obtain ⟨hAunit, hBunit⟩ := not_or.mp hunit
    have hA0 : A ≠ 0 := by
      intro hz
      exact hQ0 (by rw [hAB, hz, zero_mul])
    have hB0 : B ≠ 0 := by
      intro hz
      exact hQ0 (by rw [hAB, hz, mul_zero])
    have hAhom := HomogeneousFactors.homogeneous_of_dvd A Q 2 hQ hQ0 ⟨B, hAB⟩
    have hBdvd : B ∣ Q := by rw [hAB]; exact dvd_mul_left B A
    have hBhom := HomogeneousFactors.homogeneous_of_dvd B Q 2 hQ hQ0 hBdvd
    have hApos := positive_degree_of_nonunit A hA0 hAunit
    have hBpos := positive_degree_of_nonunit B hB0 hBunit
    have hdeg : A.totalDegree + B.totalDegree = 2 := by
      rw [← totalDegree_mul_of_isDomain hA0 hB0, ← hAB, hdegree]
    have hAd : A.totalDegree = 1 := by omega
    have hBd : B.totalDegree = 1 := by omega
    rw [hAd] at hAhom
    rw [hBd] at hBhom
    have hAcard := linear_factor_card_bound ι W 2 (by decide) hcap A hAhom hA0
    have hBcard := linear_factor_card_bound ι W 2 (by decide) hcap B hBhom hB0
    have hsub : W ⊆ zeroSet ι W A ∪ zeroSet ι W B := by
      intro P hP
      have hz := hzero P hP
      rw [hAB, map_mul] at hz
      rcases mul_eq_zero.mp hz with hA | hB
      · exact Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr ⟨hP, hA⟩))
      · exact Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr ⟨hP, hB⟩))
    have hWcard := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
    omega

theorem arc_conic_irreducible (W : Finset (PlanePoint K)) (hcap : LineCap W 2)
    (hcard : 5 ≤ W.card) (Q : PlaneRing K) (hQ : Q.IsHomogeneous 2) (hQ0 : Q ≠ 0)
    (hzero : ∀ P ∈ W, eval P.rep Q = 0) : Irreducible Q := by
  exact irreducible_quadric_on_arc (RingHom.id K) W hcap hcard Q hQ hQ0 hzero

/-- The conic is irreducible after every field embedding, not merely over
the coefficient field in which it was constructed. -/
theorem arc_conic_irreducible_map (ι : K →+* L) (W : Finset (PlanePoint K))
    (hcap : LineCap W 2) (hcard : 5 ≤ W.card) (Q : PlaneRing K)
    (hQ : Q.IsHomogeneous 2) (hQ0 : Q ≠ 0)
    (hzero : ∀ P ∈ W, eval P.rep Q = 0) : Irreducible (MvPolynomial.map ι Q) := by
  apply irreducible_quadric_on_arc ι W hcap hcard (MvPolynomial.map ι Q) (hQ.map ι)
  · intro hz
    exact hQ0 (MvPolynomial.map_injective ι ι.injective (by simpa only [map_zero] using hz))
  · intro P hP
    exact (MvPolynomial.map_eval ι P.rep Q).symm.trans
      (by rw [hzero P hP, map_zero])

theorem arc_conic_prime (W : Finset (PlanePoint K)) (hcap : LineCap W 2)
    (hcard : 5 ≤ W.card) (Q : PlaneRing K) (hQ : Q.IsHomogeneous 2) (hQ0 : Q ≠ 0)
    (hzero : ∀ P ∈ W, eval P.rep Q = 0) : Prime Q :=
  UniqueFactorizationMonoid.irreducible_iff_prime.mp
    (arc_conic_irreducible W hcap hcard Q hQ hQ0 hzero)

end Cylinder.ArcConicIrreducible
end
