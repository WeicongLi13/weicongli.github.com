module

public import Cylinder.EquationScalarDescent

/-! Divisibility between actual base-field polynomials descends from any field extension. -/

@[expose] public section
noncomputable section

namespace Cylinder.PolynomialDivisibilityDescent

open MvPolynomial Cylinder.EquationScalarDescent
open scoped Classical

variable {K L σ : Type*} [Field K] [Field L] [Algebra K L]

theorem projection_algebraMap (l : L →ₗ[K] K) (hl : l 1 = 1) (a : K) :
    l (algebraMap K L a) = a := by
  have h := l.map_smul a (1 : L)
  simpa [Algebra.smul_def, hl] using h

theorem coefficientProjection_mapped (l : L →ₗ[K] K) (hl : l 1 = 1) (F : MvPolynomial σ K) :
    coefficientProjection l (MvPolynomial.map (algebraMap K L) F) = F := by
  ext m
  rw [coefficientProjection_coeff, coeff_map, projection_algebraMap l hl]

theorem coefficientProjection_mul_mapped (l : L →ₗ[K] K)
    (F : MvPolynomial σ K) (Q : MvPolynomial σ L) :
    coefficientProjection l (MvPolynomial.map (algebraMap K L) F * Q) = F * coefficientProjection l Q := by
  ext m
  simp only [coefficientProjection_coeff, coeff_mul, coeff_map, map_sum]
  apply Finset.sum_congr rfl
  intro a _ha
  simpa only [Algebra.smul_def, smul_eq_mul, Algebra.algebraMap_self, RingHom.id_apply] using
    l.map_smul (F.coeff a.1) (Q.coeff a.2)

theorem dvd_of_mapped_dvd (F G : MvPolynomial σ K)
    (hdiv : MvPolynomial.map (algebraMap K L) F ∣ MvPolynomial.map (algebraMap K L) G) : F ∣ G := by
  obtain ⟨l, hl⟩ := Module.Projective.exists_dual_eq_one K (one_ne_zero : (1 : L) ≠ 0)
  obtain ⟨Q, hQ⟩ := hdiv
  refine ⟨coefficientProjection l Q, ?_⟩
  have h := congrArg (coefficientProjection l) hQ
  rwa [coefficientProjection_mapped l hl G, coefficientProjection_mul_mapped] at h

theorem mapped_dvd_iff (F G : MvPolynomial σ K) :
    MvPolynomial.map (algebraMap K L) F ∣ MvPolynomial.map (algebraMap K L) G ↔ F ∣ G :=
  ⟨dvd_of_mapped_dvd F G, map_dvd (MvPolynomial.map (algebraMap K L))⟩

end Cylinder.PolynomialDivisibilityDescent

end
