module

public import Cylinder.HomogeneousFactors

/-!
# Selecting an actual line that preserves a plane system's gcd

The gcd is the actual finite-family gcd. Its homogeneity and the homogeneity
of every residual quotient are proved. A coprime pair in the residual span
then selects an actual line, on which the original and restricted gcds have
exactly the same divisibility property and degree.
-/

@[expose] public section
noncomputable section
namespace Cylinder.GcdPlaneLine
open MvPolynomial
open Cylinder.HilbertEvaluation Cylinder.GenericPlaneLine
open Cylinder.PrimitivePlaneSystem Cylinder.HomogeneousFactors
variable {K I : Type*} [Field K] [Fintype I]

def binaryDivisorSubspace (D : MvPolynomial (Fin 2) K) : Submodule K (MvPolynomial (Fin 2) K) where
  carrier := {P | D ∣ P}
  zero_mem' := dvd_zero D
  add_mem' := dvd_add
  smul_mem' c P hP := by
    rw [smul_eq_C_mul]
    exact dvd_mul_of_dvd_right hP (C c)

/-- Cancellation against a family with no common nonunit factor. -/
theorem product_common_divisor {A T : Type*} [CommRing A] [IsDomain A]
    [UniqueFactorizationMonoid A] (H D : A) (hH0 : H ≠ 0) (q : T → A)
    (hprimitive : ∀ E : A, (∀ i, E ∣ q i) → IsUnit E)
    (hD : ∀ i, D ∣ H * q i) : D ∣ H := by
  obtain ⟨D', H', C, hcop, heD, heH⟩ := UniqueFactorizationMonoid.exists_reduced_factors' D H hH0
  have hC0 : C ≠ 0 := by
    intro hz
    rw [hz, zero_mul] at heH
    exact hH0 heH.symm
  have hD' : ∀ i, D' ∣ q i := by
    intro i
    have hh : C * D' ∣ C * (H' * q i) := by
      rw [heD, ← mul_assoc, heH]
      exact hD i
    exact hcop.dvd_of_dvd_mul_left ((mul_dvd_mul_iff_left hC0).mp hh)
  have hu := hprimitive D' hD'
  rw [← heD, ← heH]
  exact mul_dvd_mul_left C (hu.dvd : D' ∣ H')

theorem familyGcd_homogeneous (f : I → PlaneRing K) (d : ℕ)
    (hhom : ∀ i, (f i).IsHomogeneous d) (hf : ∃ i, f i ≠ 0) :
    (familyGcd f).IsHomogeneous (familyGcd f).totalDegree := by
  obtain ⟨i, hi⟩ := hf
  exact homogeneous_of_dvd _ _ d (hhom i) hi (familyGcd_dvd f i)

theorem residualFamily_homogeneous (f : I → PlaneRing K) (d : ℕ)
    (hhom : ∀ i, (f i).IsHomogeneous d) (hf : ∃ i, f i ≠ 0) (i : I) :
    (residualFamily f i).IsHomogeneous (d - (familyGcd f).totalDegree) := by
  apply quotient_homogeneous _ _ d (familyGcd_ne_zero f hf)
  rw [← family_factorization f i]
  exact hhom i

theorem residual_span_homogeneous (f : I → PlaneRing K) (d : ℕ)
    (hhom : ∀ i, (f i).IsHomogeneous d) (hf : ∃ i, f i ≠ 0) :
    Submodule.span K (Set.range (residualFamily f)) ≤ Forms K (d - (familyGcd f).totalDegree) := by
  apply Submodule.span_le.mpr
  rintro P ⟨i, rfl⟩
  exact residualFamily_homogeneous f d hhom hf i

theorem residual_span_ne_zero (f : I → PlaneRing K) (hf : ∃ i, f i ≠ 0) :
    Submodule.span K (Set.range (residualFamily f)) ≠ ⊥ := by
  obtain ⟨i, hi⟩ := hf
  intro hz
  have hmem : residualFamily f i ∈ Submodule.span K (Set.range (residualFamily f)) :=
    Submodule.subset_span ⟨i, rfl⟩
  rw [hz, Submodule.mem_bot] at hmem
  apply hi
  rw [family_factorization f i, hmem, mul_zero]

/-- Genuine generic-line gcd preservation for a finite homogeneous plane system.
The common-divisor condition and degree are conclusions, not hypotheses. -/
theorem exists_line_preserving_gcd [Infinite K]
    (f : I → PlaneRing K) (d : ℕ) (hhom : ∀ i, (f i).IsHomogeneous d)
    (hf : ∃ i, f i ≠ 0) :
    ∃ p : Fin 3 → K, ∃ w : Fin 2 → K,
      p 0 ≠ 0 ∧ w 0 ≠ 0 ∧ Function.Surjective (lineRestriction p w) ∧
        lineRestriction p w (familyGcd f) ≠ 0 ∧
        (lineRestriction p w (familyGcd f)).totalDegree = (familyGcd f).totalDegree ∧
        ∀ D : MvPolynomial (Fin 2) K,
          (∀ i, D ∣ lineRestriction p w (f i)) ↔ D ∣ lineRestriction p w (familyGcd f) := by
  let U := Submodule.span K (Set.range (residualFamily f))
  have hU := residual_span_ne_zero f hf
  have hhomU := residual_span_homogeneous f d hhom hf
  obtain ⟨F, hFU, G, hGU, hF0, hfg⟩ := exists_relPrime_pair U hU (residual_primitive f hf)
  have hH0 := familyGcd_ne_zero f hf
  obtain ⟨p, hp0, hpFH⟩ := exists_triangular_nonvanishing (F * familyGcd f) (mul_ne_zero hF0 hH0)
  rw [map_mul, map_mul, mul_ne_zero_iff] at hpFH
  obtain ⟨w, hw0, _, hc⟩ := exists_coprime_pencil (triangularMap p F) (triangularMap p G)
    (d - (familyGcd f).totalDegree) (d - (familyGcd f).totalDegree)
    (triangularMap_homogeneous p F _ (hhomU hFU))
    (triangularMap_homogeneous p G _ (hhomU hGU)) hpFH.1
    (relPrime_ringEquiv (triangularEquiv p hp0).toRingEquiv hfg) 1 one_ne_zero
  have hres : ∀ D : MvPolynomial (Fin 2) K,
      (∀ i, D ∣ lineRestriction p w (residualFamily f i)) → IsUnit D := by
    intro D hD
    have hle : U ≤ (binaryDivisorSubspace D).comap (lineRestriction p w).toLinearMap := by
      apply Submodule.span_le.mpr
      rintro P ⟨i, rfl⟩
      exact hD i
    exact hc (hle hFU) (hle hGU)
  have hRH0 : lineRestriction p w (familyGcd f) ≠ 0 := by
    intro hz
    apply hpFH.2
    rw [← pencil_eval_infinity w (triangularMap p (familyGcd f))]
    change eval ![1, 0] (lineRestriction p w (familyGcd f)) = 0
    rw [hz, map_zero]
  refine ⟨p, w, hp0, hw0, lineRestriction_surjective p w hp0 hw0, hRH0,
    (lineRestriction_homogeneous p w _ _ (familyGcd_homogeneous f d hhom hf)).totalDegree hRH0, ?_⟩
  intro D
  constructor
  · intro hD
    apply product_common_divisor _ D hRH0 (fun i => lineRestriction p w (residualFamily f i)) hres
    intro i
    simpa only [family_factorization f i, map_mul] using hD i
  · intro hD i
    rw [family_factorization f i, map_mul]
    exact dvd_mul_of_dvd_left hD _

end Cylinder.GcdPlaneLine
end
