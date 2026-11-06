module

public import Cylinder.PrimitivePlaneSystem
public import Mathlib.Algebra.Polynomial.Degree.TrailingDegree
public import Mathlib.Algebra.MvPolynomial.NoZeroDivisors

/-!
# Actual homogeneous factors

The grading is encoded in a genuine polynomial ring. For a nonzero homogeneous
product, maximal and minimal degrees of this polynomial encoding agree.
Their additivity forces both factors to be homogeneous, without a hypothesis
that the desired gcd or its residual quotients are homogeneous.
-/

@[expose] public section
noncomputable section
namespace Cylinder.HomogeneousFactors
open scoped Polynomial DirectSum
open MvPolynomial
variable {K σ : Type*} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra

def componentEmbedding (n : ℕ) : homogeneousSubmodule σ K n →+ (MvPolynomial σ K)[X] where
  toFun P := Polynomial.monomial n P.val
  map_zero' := by simp
  map_add' P Q := by
    change Polynomial.monomial n (P.val + Q.val) = _
    exact map_add (Polynomial.monomial n) P.val Q.val

def gradingPolynomialHom : (⨁ n : ℕ, homogeneousSubmodule σ K n) →+* (MvPolynomial σ K)[X] :=
  DirectSum.toSemiring componentEmbedding
    (by change Polynomial.monomial 0 (1 : MvPolynomial σ K) = 1; simp)
    (by
      intro i j P Q
      change Polynomial.monomial (i + j) (P.val * Q.val) =
        Polynomial.monomial i P.val * Polynomial.monomial j Q.val
      rw [Polynomial.monomial_mul_monomial])

/-- A true ring homomorphism recording the homogeneous components as coefficients. -/
def degreePolynomial : MvPolynomial σ K →+* (MvPolynomial σ K)[X] :=
  gradingPolynomialHom.comp (DirectSum.decomposeRingEquiv (homogeneousSubmodule σ K)).toRingHom

theorem degreePolynomial_homogeneous (P : MvPolynomial σ K) (n : ℕ)
    (hP : P.IsHomogeneous n) : degreePolynomial P = Polynomial.monomial n P := by
  change gradingPolynomialHom (DirectSum.decompose (homogeneousSubmodule σ K) P) = _
  rw [DirectSum.decompose_of_mem _ hP]
  exact DirectSum.toSemiring_of _ _ _ _ _

theorem degreePolynomial_coeff (P : MvPolynomial σ K) (n : ℕ) :
    (degreePolynomial P).coeff n = homogeneousComponent n P := by
  classical
  induction P using MvPolynomial.induction_on' with
  | monomial d c =>
    rw [degreePolynomial_homogeneous _ d.degree (isHomogeneous_monomial c rfl),
      homogeneousComponent_of_mem (isHomogeneous_monomial c rfl)]
    by_cases h : n = d.degree
    · simp [h]
    · simp [h, Ne.symm h, Polynomial.coeff_monomial]
  | add P Q hP hQ =>
    simp only [map_add, Polynomial.coeff_add, hP, hQ]

theorem degreePolynomial_eval_one (P : MvPolynomial σ K) :
    Polynomial.eval 1 (degreePolynomial P) = P := by
  have he : (Polynomial.evalRingHom (1 : MvPolynomial σ K)).comp degreePolynomial =
      RingHom.id (MvPolynomial σ K) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      rw [RingHom.comp_apply, degreePolynomial_homogeneous _ 0 (isHomogeneous_C σ c)]
      simp
    · intro i
      rw [RingHom.comp_apply, degreePolynomial_homogeneous _ 1 (isHomogeneous_X K i)]
      simp
  exact RingHom.congr_fun he P

theorem degreePolynomial_ne_zero {P : MvPolynomial σ K} (hP : P ≠ 0) : degreePolynomial P ≠ 0 := by
  intro hz
  apply hP
  rw [← degreePolynomial_eval_one P, hz, Polynomial.eval_zero]

/-- If the nonzero product is homogeneous, the actual factors are homogeneous. -/
theorem factors_homogeneous (F G : MvPolynomial σ K) (d : ℕ)
    (hFG : (F * G).IsHomogeneous d) (h0 : F * G ≠ 0) :
    F.IsHomogeneous F.totalDegree ∧ G.IsHomogeneous G.totalDegree := by
  classical
  have hF0 := left_ne_zero_of_mul h0
  have hG0 := right_ne_zero_of_mul h0
  have hf0 := degreePolynomial_ne_zero hF0
  have hg0 := degreePolynomial_ne_zero hG0
  have hmax : (degreePolynomial F).natDegree + (degreePolynomial G).natDegree = d := by
    rw [← Polynomial.natDegree_mul hf0 hg0, ← map_mul,
      degreePolynomial_homogeneous _ d hFG, Polynomial.natDegree_monomial]
    simp [h0]
  have hmin : (degreePolynomial F).natTrailingDegree + (degreePolynomial G).natTrailingDegree = d := by
    rw [← Polynomial.natTrailingDegree_mul hf0 hg0, ← map_mul,
      degreePolynomial_homogeneous _ d hFG, Polynomial.natTrailingDegree_monomial h0]
  have hFl := Polynomial.natTrailingDegree_le_natDegree (degreePolynomial F)
  have hGl := Polynomial.natTrailingDegree_le_natDegree (degreePolynomial G)
  have heF : (degreePolynomial F).natTrailingDegree = (degreePolynomial F).natDegree := by omega
  have heG : (degreePolynomial G).natTrailingDegree = (degreePolynomial G).natDegree := by omega
  have hfactor (P : MvPolynomial σ K)
      (he : (degreePolynomial P).natTrailingDegree = (degreePolynomial P).natDegree) :
      P.IsHomogeneous (degreePolynomial P).natDegree := by
    intro a ha
    have hc : (degreePolynomial P).coeff a.degree ≠ 0 := by
      rw [degreePolynomial_coeff]
      intro hz
      have hh := congrArg (fun Q : MvPolynomial σ K => Q.coeff a) hz
      simp only [coeff_homogeneousComponent] at hh
      change P.coeff a = 0 at hh
      exact ha hh
    have hlo := Polynomial.natTrailingDegree_le_of_ne_zero hc
    have hhi := Polynomial.le_natDegree_of_ne_zero hc
    rw [he] at hlo
    simpa only [Finsupp.degree_eq_weight_one, Pi.one_def] using Nat.le_antisymm hhi hlo
  have hF := hfactor F heF
  have hG := hfactor G heG
  rw [← hF.totalDegree hF0] at hF
  rw [← hG.totalDegree hG0] at hG
  exact ⟨hF, hG⟩

/-- Every divisor of a nonzero homogeneous polynomial is homogeneous. -/
theorem homogeneous_of_dvd (F P : MvPolynomial σ K) (d : ℕ)
    (hP : P.IsHomogeneous d) (hP0 : P ≠ 0) (hFP : F ∣ P) : F.IsHomogeneous F.totalDegree := by
  obtain ⟨Q, rfl⟩ := hFP
  exact (factors_homogeneous F Q d hP hP0).1

/-- Division by a nonzero actual factor has the expected homogeneous degree,
including zero members of the system. -/
theorem quotient_homogeneous (F Q : MvPolynomial σ K) (d : ℕ)
    (hF0 : F ≠ 0) (hP : (F * Q).IsHomogeneous d) :
    Q.IsHomogeneous (d - F.totalDegree) := by
  by_cases hQ0 : Q = 0
  · rw [hQ0]
    exact isHomogeneous_zero σ K _
  have hprod0 := mul_ne_zero hF0 hQ0
  have hQ := (factors_homogeneous F Q d hP hprod0).2
  have hdeg : F.totalDegree + Q.totalDegree = d := by
    rw [← totalDegree_mul_of_isDomain hF0 hQ0]
    exact hP.totalDegree hprod0
  have he : Q.totalDegree = d - F.totalDegree := by omega
  rwa [he] at hQ

end Cylinder.HomogeneousFactors
end
