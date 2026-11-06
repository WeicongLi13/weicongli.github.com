module

public import Cylinder.PlaneIdealRestriction

/-!
# The actual saturated-ideal plane plateau lemma

The construction uses actual finite bases of homogeneous ideal pieces,
the proved regular graph-line/gcd selection, and the proved binary equality
classification. It applies to nonreduced saturated ideals.
-/

@[expose] public section
noncomputable section
namespace Cylinder.GeneralPlanePlateau
open MvPolynomial Module
open Cylinder.HilbertEvaluation Cylinder.PlaneBinaryReduction
open Cylinder.PrimitivePlaneSystem Cylinder.GcdPlaneLine Cylinder.SaturatedPlaneLine
open Cylinder.PlaneIdealRestriction
open Cylinder.BinaryFormLemma (expansion factorSpace binary_growth binary_equality)
open Cylinder.NumericCharacterSequence
variable {K : Type*} [Field K]

def basisFamily (J : Ideal (PlaneRing K)) (d : ℕ) :
    Fin (finrank K (Cylinder.PlanePlateau.piece J d)) → PlaneRing K :=
  fun i => (Module.finBasis K (Cylinder.PlanePlateau.piece J d) i).val

theorem basisFamily_mem (J : Ideal (PlaneRing K)) (d : ℕ)
    (i : Fin (finrank K (Cylinder.PlanePlateau.piece J d))) :
    basisFamily J d i ∈ Cylinder.PlanePlateau.piece J d :=
  (Module.finBasis K (Cylinder.PlanePlateau.piece J d) i).property

theorem basisFamily_homogeneous (J : Ideal (PlaneRing K)) (d : ℕ)
    (i : Fin (finrank K (Cylinder.PlanePlateau.piece J d))) : (basisFamily J d i).IsHomogeneous d :=
  (basisFamily_mem J d i).2

theorem basisFamily_span (J : Ideal (PlaneRing K)) (d : ℕ) :
    Submodule.span K (Set.range (basisFamily J d)) = Cylinder.PlanePlateau.piece J d := by
  let U := Cylinder.PlanePlateau.piece J d
  let b := Module.finBasis K U
  calc
    Submodule.span K (Set.range (basisFamily J d)) = (Submodule.span K (Set.range b)).map U.subtype := by
      rw [Submodule.map_span]
      congr 1
      ext P
      constructor
      · rintro ⟨i, rfl⟩
        exact ⟨b i, ⟨i, rfl⟩, rfl⟩
      · rintro ⟨Q, ⟨i, rfl⟩, rfl⟩
        exact ⟨i, rfl⟩
    _ = U := by rw [b.span_eq, Submodule.map_top, Submodule.range_subtype]

theorem basisFamily_nonzero (J : Ideal (PlaneRing K)) (d : ℕ)
    (hU : Cylinder.PlanePlateau.piece J d ≠ ⊥) : ∃ i, basisFamily J d i ≠ 0 := by
  by_contra! h
  apply hU
  rw [← basisFamily_span]
  apply Submodule.span_eq_bot.mpr
  rintro P ⟨i, rfl⟩
  exact h i

theorem piece_nonzero_of_initial_le (J : Ideal (PlaneRing K)) (z d : ℕ)
    (hz : Cylinder.PlanePlateau.InitialDegree J z) (hd : z ≤ d) :
    Cylinder.PlanePlateau.piece J d ≠ ⊥ := by
  obtain ⟨P, hP, hP0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hz.1
  have hprod : X (0 : Fin 3) ^ (d - z) * P ∈ Cylinder.PlanePlateau.piece J d := by
    refine ⟨J.mul_mem_left _ hP.1, ?_⟩
    have hh := (isHomogeneous_X_pow (R := K) (0 : Fin 3) (d - z)).mul hP.2
    rw [Nat.sub_add_cancel hd] at hh
    exact hh
  intro heq
  rw [heq, Submodule.mem_bot] at hprod
  exact mul_ne_zero (pow_ne_zero _ (X_ne_zero _)) hP0 hprod

theorem basis_restriction_mem (J : Ideal (PlaneRing K)) (a b : K) (d : ℕ)
    (i : Fin (finrank K (Cylinder.PlanePlateau.piece J d))) :
    graphRestriction a b (basisFamily J d i) ∈ restrictionSpace J a b d :=
  (mem_restrictionSpace J a b d _).mpr
    ⟨basisFamily J d i, basisFamily_homogeneous J d i, (basisFamily_mem J d i).1, rfl⟩

theorem restriction_divisor_iff (J : Ideal (PlaneRing K)) (a b : K) (d : ℕ) (D : BinaryRing K) :
    (∀ P ∈ restrictionSpace J a b d, D ∣ P) ↔
      ∀ i, D ∣ graphRestriction a b (basisFamily J d i) := by
  constructor
  · intro h i
    exact h _ (basis_restriction_mem J a b d i)
  · intro h P hP
    obtain ⟨Q, hQ, hQJ, hQP⟩ := (mem_restrictionSpace J a b d P).mp hP
    have hle : Cylinder.PlanePlateau.piece J d ≤
        (binaryDivisorSubspace D).comap (graphRestriction a b).toLinearMap := by
      rw [← basisFamily_span]
      apply Submodule.span_le.mpr
      rintro Q ⟨i, rfl⟩
      exact h i
    rw [← hQP]
    exact hle ⟨hQJ, hQ⟩

theorem restriction_nonzero_of_preserved_gcd (J : Ideal (PlaneRing K)) (a b : K) (d : ℕ)
    (hG0 : graphRestriction a b (familyGcd (basisFamily J d)) ≠ 0)
    (hpres : ∀ D : BinaryRing K,
      (∀ i, D ∣ graphRestriction a b (basisFamily J d i)) ↔
        D ∣ graphRestriction a b (familyGcd (basisFamily J d))) :
    restrictionSpace J a b d ≠ ⊥ := by
  intro hz
  apply hG0
  apply zero_dvd_iff.mp
  apply (hpres 0).mp
  intro i
  have hm := basis_restriction_mem J a b d i
  rw [hz, Submodule.mem_bot] at hm
  rw [hm]

/-- The actual binary equality classification at a plateau, for the restriction
spaces of an actual regular plane ideal. -/
theorem restricted_plateau_factor (J : Ideal (PlaneRing K)) (a b : K) (q c : ℕ)
    (hq : 0 < q) (hregular : J.colon {graphEquation a b} = J)
    (hU0 : restrictionSpace J a b q ≠ ⊥)
    (h0 : firstDifference (Cylinder.PlanePlateau.quotientHilbert J) q = c)
    (h1 : firstDifference (Cylinder.PlanePlateau.quotientHilbert J) (q + 1) = c) :
    ∃ B : BinaryRing K, B ≠ 0 ∧ B.IsHomogeneous c ∧ B.totalDegree = c ∧
      restrictionSpace J a b (q + 1) = factorSpace B (q + 1 - c) := by
  have hr0aux := restriction_rank_add_firstDifference J a b hregular (q - 1)
  have he : q - 1 + 1 = q := Nat.sub_add_cancel hq
  have he' : q - 1 + 2 = q + 1 := by omega
  rw [he, h0, he'] at hr0aux
  have hr0 : finrank K (restrictionSpace J a b q) + c = q + 1 := hr0aux
  have hr1 : finrank K (restrictionSpace J a b (q + 1)) + c = q + 2 := by
    have hh := restriction_rank_add_firstDifference J a b hregular q
    rwa [h1] at hh
  have hgrowth : finrank K (restrictionSpace J a b q) + 1 ≤
      finrank K (expansion (restrictionSpace J a b q)) :=
    binary_growth (restrictionSpace J a b q) q (restrictionSpace_homogeneous J a b q) hU0
  have hle := restriction_expansion_le J a b q
  have hbound : finrank K (expansion (restrictionSpace J a b q)) ≤
      finrank K (restrictionSpace J a b (q + 1)) := Submodule.finrank_mono hle
  have hdim : finrank K (expansion (restrictionSpace J a b q)) = finrank K (restrictionSpace J a b q) + 1 := by omega
  have hrEq : finrank K (expansion (restrictionSpace J a b q)) =
      finrank K (restrictionSpace J a b (q + 1)) := by omega
  have hspace : expansion (restrictionSpace J a b q) = restrictionSpace J a b (q + 1) :=
    Submodule.eq_of_le_of_finrank_eq hle hrEq
  obtain ⟨B, hB0, hB, hfac⟩ := binary_equality (restrictionSpace J a b q) q
    (restrictionSpace_homogeneous J a b q) hU0 hdim
  have hc : q + 1 - finrank K (restrictionSpace J a b q) = c := by omega
  rw [hc] at hB
  have hrpos : 0 < finrank K (restrictionSpace J a b q) := by
    by_contra hn
    exact hU0 (Submodule.finrank_eq_zero.mp (Nat.eq_zero_of_not_pos hn))
  have hefac : finrank K (restrictionSpace J a b q) - 1 = q - c := by omega
  rw [hefac] at hfac
  refine ⟨B, hB0, hB, hB.totalDegree hB0, ?_⟩
  rw [← hspace, hfac, Cylinder.BinaryPlateau.factorSpace_expansion B c (q - c) hB0 hB]
  have hedeg : q - c + 1 = q + 1 - c := by omega
  rw [hedeg]

theorem divisor_of_factorSpace (B D : BinaryRing K) (hB0 : B ≠ 0) (n : ℕ)
    (hD : ∀ P ∈ factorSpace B n, D ∣ P) : D ∣ B := by
  have hmem (i : Fin 2) : B * X i ^ n ∈ factorSpace B n :=
    ⟨X i ^ n, isHomogeneous_X_pow i n, rfl⟩
  have hx := hD _ (hmem 0)
  have hy := hD _ (hmem 1)
  have hD0 : D ≠ 0 := ne_zero_of_dvd_ne_zero (mul_ne_zero hB0 (pow_ne_zero _ (X_ne_zero _))) hx
  exact Cylinder.BinaryPlateau.dvd_of_coprime_multiples D B (X 0 ^ n) (X 1 ^ n) hD0
    Cylinder.BinaryPlateau.variables_isRelPrime.pow (by simpa only [mul_comm] using hx)
      (by simpa only [mul_comm] using hy)

end Cylinder.GeneralPlanePlateau
end
