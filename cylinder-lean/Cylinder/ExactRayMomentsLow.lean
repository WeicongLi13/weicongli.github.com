module

public import Cylinder.ExactRayMomentsSeries
public import Cylinder.ExactRayMomentsSeparation

/-!
# Actual normalized residue products force low moments to vanish

The numerator is the true cofactor residue sum for the factors
`lambda(direction e) + t(e) T`. Its actual `T^w` divisibility gives the
series vanishing, and different actual prime directions separate the poles.
-/

@[expose] public section
noncomputable section
open scoped Classical BigOperators
namespace Cylinder.ExactRayMomentsLow
variable {K R E I : Type*} [Field K] [CommRing R] [IsDomain R] [Algebra K R]
variable [Fintype E] [Fintype I]

def moment (dir : E → I) (c t : E → K) (i : I) (j : ℕ) : K :=
  ∑ e ∈ Finset.univ.filter (fun e => dir e = i), c e * t e ^ j

def actualFactor (a : R) (t : K) : Polynomial R :=
  Polynomial.C a + Polynomial.C (algebraMap K R t) * Polynomial.X

def actualNumerator (dir : E → I) (a : I → R) (c t : E → K) : Polynomial R :=
  ∑ e, Polynomial.C (algebraMap K R (c e)) *
    ∏ f ∈ Finset.univ.erase e, actualFactor (a (dir f)) (t f)

theorem normalized_product_low_moments (dir : E → I) (a : I → R)
    (ha : ∀ i, Prime (a i)) (hsep : ∀ i k, i ≠ k → ¬a i ∣ a k)
    (c t : E → K) (P : Polynomial R) (hprod : P = actualNumerator dir a c t)
    (w : ℕ) (horder : Polynomial.X ^ w ∣ P) (j : ℕ) (hj : j < w) :
    ∀ i, moment dir c t i j = 0 := by
  let F := FractionRing R
  let φ : R →+* F := algebraMap R F
  let aF (e : E) : F := φ (a (dir e))
  let tF (e : E) : F := φ (algebraMap K R (t e))
  let cF (e : E) : F := φ (algebraMap K R (c e))
  have haF : ∀ e, aF e ≠ 0 := by
    intro e h
    exact (ha (dir e)).ne_zero (IsFractionRing.injective R F (by simpa [aF, φ] using h))
  have hmap : P.map φ = Cylinder.ExactRayMomentsSeries.residueNumerator aF tF cF := by
    rw [hprod]
    simp [actualNumerator, actualFactor, Cylinder.ExactRayMomentsSeries.residueNumerator,
      Cylinder.ExactRayMomentsSeries.linearFactor, aF, tF, cF,
      Polynomial.map_sum, Polynomial.map_prod]
  have horderF : Polynomial.X ^ w ∣ P.map φ := by
    have h := map_dvd (Polynomial.mapRingHom φ) horder
    simpa using h
  have hz := Cylinder.ExactRayMomentsSeries.product_low_moment_sum aF tF cF haF
    (P.map φ) hmap w horderF j hj
  have hfiber : (∑ e, cF e * tF e ^ j / aF e ^ (j + 1)) =
      ∑ i, φ (algebraMap K R (moment dir c t i j)) / φ (a i) ^ (j + 1) := by
    rw [← Finset.sum_fiberwise Finset.univ dir]
    apply Finset.sum_congr rfl
    intro i _
    rw [moment, map_sum, map_sum, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro e he
    have hdir := (Finset.mem_filter.mp he).2
    simp [aF, tF, cF, hdir]
  rw [hfiber] at hz
  exact Cylinder.ExactRayMomentsSeparation.prime_fraction_sum_zero a ha hsep
    (fun i => moment dir c t i j) (j + 1) (by omega) hz

end Cylinder.ExactRayMomentsLow
end
