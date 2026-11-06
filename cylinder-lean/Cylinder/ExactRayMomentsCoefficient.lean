module

public import Cylinder.ExactRayMomentsLow

/-! The first numerator coefficient and the actual grouped ray moments. -/

@[expose] public section
noncomputable section
open scoped Classical BigOperators
namespace Cylinder.ExactRayMomentsCoefficient
open Cylinder.ExactRayMomentsLow
variable {K R E I : Type*} [Field K] [CommRing R] [IsDomain R] [Algebra K R]
variable [Fintype E] [Fintype I]

def actualDenominator (dir : E → I) (a : I → R) (t : E → K) : Polynomial R :=
  ∏ e, actualFactor (a (dir e)) (t e)

omit [IsDomain R] [Fintype I] in
theorem actualDenominator_constant (dir : E → I) (a : I → R) (t : E → K) :
    (actualDenominator dir a t).coeff 0 = ∏ e, a (dir e) := by
  change Polynomial.constantCoeff (actualDenominator dir a t) = _
  rw [actualDenominator, map_prod]
  simp [actualFactor]

theorem normalized_product_first_coefficient (dir : E → I) (a : I → R)
    (ha : ∀ i, a i ≠ 0) (c t : E → K) (P : Polynomial R)
    (hprod : P = actualNumerator dir a c t) (w : ℕ) (horder : Polynomial.X ^ w ∣ P) :
    algebraMap R (FractionRing R) (P.coeff w) /
        algebraMap R (FractionRing R) ((actualDenominator dir a t).coeff 0) =
      algebraMap R (FractionRing R) ((-1 : R) ^ w) *
        ∑ i, algebraMap R (FractionRing R) (algebraMap K R (moment dir c t i w)) /
          algebraMap R (FractionRing R) (a i) ^ (w + 1) := by
  let F := FractionRing R
  let φ : R →+* F := algebraMap R F
  let aF (e : E) : F := φ (a (dir e))
  let tF (e : E) : F := φ (algebraMap K R (t e))
  let cF (e : E) : F := φ (algebraMap K R (c e))
  have haF : ∀ e, aF e ≠ 0 := by
    intro e h
    exact ha (dir e) (IsFractionRing.injective R F (by simpa [aF, φ] using h))
  have hmap : P.map φ = Cylinder.ExactRayMomentsSeries.residueNumerator aF tF cF := by
    rw [hprod]
    simp [actualNumerator, actualFactor, Cylinder.ExactRayMomentsSeries.residueNumerator,
      Cylinder.ExactRayMomentsSeries.linearFactor, aF, tF, cF,
      Polynomial.map_sum, Polynomial.map_prod]
  have horderF : Polynomial.X ^ w ∣ P.map φ := by
    have h := map_dvd (Polynomial.mapRingHom φ) horder
    simpa using h
  have hden : Cylinder.ExactRayMomentsSeries.denominator aF tF =
      (actualDenominator dir a t).map φ := by
    simp [Cylinder.ExactRayMomentsSeries.denominator, Cylinder.ExactRayMomentsSeries.linearFactor,
      actualDenominator, actualFactor, aF, tF, Polynomial.map_prod]
  have htop := Cylinder.ExactRayMomentsSeries.product_first_moment_sum aF tF cF haF
    (P.map φ) hmap w horderF
  have hfiber : (∑ e, cF e * tF e ^ w / aF e ^ (w + 1)) =
      ∑ i, φ (algebraMap K R (moment dir c t i w)) / φ (a i) ^ (w + 1) := by
    rw [← Finset.sum_fiberwise Finset.univ dir]
    apply Finset.sum_congr rfl
    intro i _
    rw [moment, map_sum, map_sum, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro e he
    have hdir := (Finset.mem_filter.mp he).2
    simp [aF, tF, cF, hdir]
  rw [hfiber, hden, Polynomial.coeff_map, Polynomial.coeff_map] at htop
  simpa only [map_pow, map_neg, map_one] using htop.symm

end Cylinder.ExactRayMomentsCoefficient
end
