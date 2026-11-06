module

public import Cylinder.GenericPlaneLine
public import Mathlib.Algebra.Module.Submodule.Union
public import Mathlib.Algebra.GCDMonoid.Finset

/-!
# Removing the actual gcd of a plane linear system

An actual system with no nonunit common divisor contains a relatively prime
pair. The pair is constructed by avoiding the finitely many prime-divisibility
subspaces of one nonzero member. Applying the proved line-selection theorem
then gives a binary system with no nonunit common divisor.
-/

@[expose] public section
noncomputable section
namespace Cylinder.PrimitivePlaneSystem
open MvPolynomial
open Cylinder.HilbertEvaluation Cylinder.GenericPlaneLine
variable {K : Type*} [Field K]

local instance planeNormalizedGCD : NormalizedGCDMonoid (PlaneRing K) := Classical.arbitrary _

/-- Actual divisibility defines a linear subspace of the polynomial ring. -/
def divisorSubspace (D : PlaneRing K) : Submodule K (PlaneRing K) where
  carrier := {P | D ∣ P}
  zero_mem' := dvd_zero D
  add_mem' := dvd_add
  smul_mem' c P hP := by
    rw [smul_eq_C_mul]
    exact dvd_mul_of_dvd_right hP (C c)

/-- The system has no common nonunit divisor in the actual polynomial ring. -/
def Primitive (U : Submodule K (PlaneRing K)) : Prop :=
  ∀ D : PlaneRing K, (∀ P ∈ U, D ∣ P) → IsUnit D

/-- A primitive nonzero plane system contains two actual relatively prime members. -/
theorem exists_relPrime_pair [Infinite K] (U : Submodule K (PlaneRing K))
    (hU : U ≠ ⊥) (hprimitive : Primitive U) :
    ∃ F ∈ U, ∃ G ∈ U, F ≠ 0 ∧ IsRelPrime F G := by
  classical
  obtain ⟨F, hFU, hF0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hU
  let T := {D : PlaneRing K // D ∈ UniqueFactorizationMonoid.normalizedFactors F}
  let space (D : T) : Submodule K U := (divisorSubspace D.val).comap U.subtype
  have hproper : ∀ D : T, space D ≠ ⊤ := by
    intro D heq
    have hunit : IsUnit D.val := hprimitive D.val (by
      intro P hPU
      have hm : (⟨P, hPU⟩ : U) ∈ space D := by rw [heq]; trivial
      exact hm)
    exact (UniqueFactorizationMonoid.prime_of_normalized_factor D.val D.property).not_isUnit hunit
  obtain ⟨G, hG⟩ := Submodule.exists_forall_notMem_of_forall_ne_top space hproper
  refine ⟨F, hFU, G.val, G.property, hF0, ?_⟩
  apply (UniqueFactorizationMonoid.isRelPrime_iff_no_prime_factors hF0).mpr
  intro D hDF hDG hDprime
  obtain ⟨E, hE, hDE⟩ := UniqueFactorizationMonoid.exists_mem_normalizedFactors_of_dvd
    hF0 hDprime.irreducible hDF
  apply hG ⟨E, hE⟩
  exact hDE.dvd_iff_dvd_left.mp hDG

/-- A primitive homogeneous system admits an actual nondegenerate line whose
entire binary restriction has no common nonunit factor. -/
theorem exists_primitive_line [Infinite K] (U : Submodule K (PlaneRing K)) (d : ℕ)
    (hU : U ≠ ⊥) (hhom : U ≤ Forms K d) (hprimitive : Primitive U) :
    ∃ p : Fin 3 → K, ∃ w : Fin 2 → K,
      p 0 ≠ 0 ∧ w 0 ≠ 0 ∧ Function.Surjective (lineRestriction p w) ∧
        ∀ D : MvPolynomial (Fin 2) K,
          (∀ P ∈ U, D ∣ lineRestriction p w P) → IsUnit D := by
  obtain ⟨F, hFU, G, hGU, hF0, hfg⟩ := exists_relPrime_pair U hU hprimitive
  obtain ⟨p, w, hp, hw, hsurj, hcop⟩ := exists_coprime_line F G d d (hhom hFU) (hhom hGU) hF0 hfg
  exact ⟨p, w, hp, hw, hsurj, fun D hD => hcop (hD F hFU) (hD G hGU)⟩

section FiniteGcd
variable {I : Type*} [Fintype I]

/-- The actual normalized gcd of a finite family of plane equations. -/
def familyGcd (f : I → PlaneRing K) : PlaneRing K := Finset.univ.gcd f

theorem familyGcd_dvd (f : I → PlaneRing K) (i : I) : familyGcd f ∣ f i :=
  Finset.gcd_dvd (f := f) (Finset.mem_univ i)

theorem familyGcd_ne_zero (f : I → PlaneRing K) (hf : ∃ i, f i ≠ 0) : familyGcd f ≠ 0 := by
  intro hz
  obtain ⟨i, hi⟩ := hf
  have hd := familyGcd_dvd f i
  rw [hz, zero_dvd_iff] at hd
  exact hi hd

/-- Divide by the proved actual gcd; no quotient or factor is postulated. -/
def residualFamily (f : I → PlaneRing K) (i : I) : PlaneRing K :=
  Classical.choose (familyGcd_dvd f i)

theorem family_factorization (f : I → PlaneRing K) (i : I) :
    f i = familyGcd f * residualFamily f i := Classical.choose_spec (familyGcd_dvd f i)

/-- Removing this gcd makes the actual residual span primitive. -/
theorem residual_primitive (f : I → PlaneRing K) (hf : ∃ i, f i ≠ 0) :
    Primitive (Submodule.span K (Set.range (residualFamily f))) := by
  intro D hD
  have hG0 := familyGcd_ne_zero f hf
  have hprod : familyGcd f * D ∣ familyGcd f := by
    change familyGcd f * D ∣ Finset.univ.gcd f
    apply Finset.dvd_gcd
    intro i _
    rw [family_factorization f i]
    exact mul_dvd_mul_left _ (hD _ (Submodule.subset_span ⟨i, rfl⟩))
  have hunit : D ∣ (1 : PlaneRing K) := by
    apply (mul_dvd_mul_iff_left hG0).mp
    simpa using hprod
  exact isUnit_of_dvd_one hunit

end FiniteGcd
end Cylinder.PrimitivePlaneSystem
end
