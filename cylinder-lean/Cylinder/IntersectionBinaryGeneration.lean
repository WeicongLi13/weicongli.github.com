module

public import Cylinder.IntersectionResolution
public import Cylinder.PlaneBinaryReduction
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Full binary generation in degree `s-1`

For actual pairwise relatively prime binary forms of positive degrees,
the cofactor generators span every binary form of degree `s-1`.
Injectivity comes from the proved syzygies and the strict degree bound;
surjectivity follows from the actual equal finite dimensions.
-/

@[expose] public section

noncomputable section

namespace Cylinder.IntersectionBinaryGeneration

open MvPolynomial Module Cylinder.IntersectionResolution Cylinder.PlaneBinaryReduction
open scoped BigOperators Classical

variable {K I : Type*} [Field K] [Fintype I]

abbrev Coefficients (e : I → ℕ) := ∀ i : I, BinaryForms K (e i - 1)

def degreeSum (e : I → ℕ) : ℕ := ∑ i, e i

theorem cofactor_homogeneous (F : I → BinaryRing K) (e : I → ℕ)
    (hF : ∀ i, (F i).IsHomogeneous (e i)) (i : I) :
    (cofactor F i).IsHomogeneous (degreeSum e - e i) := by
  have h := IsHomogeneous.prod (Finset.univ.erase i) F e (fun j _ => hF j)
  have hsum := Finset.sum_erase_add Finset.univ e (Finset.mem_univ i)
  have heq : (∑ j ∈ Finset.univ.erase i, e j) = degreeSum e - e i := by
    unfold degreeSum
    omega
  unfold cofactor
  rw [← heq]
  exact h

theorem degree_le_sum (e : I → ℕ) (i : I) : e i ≤ degreeSum e :=
  Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)

def weightedGeneration (F : I → BinaryRing K) (e : I → ℕ)
    (he : ∀ i, 0 < e i) (hhom : ∀ i, (F i).IsHomogeneous (e i)) :
    Coefficients (K := K) e →ₗ[K] BinaryForms K (degreeSum e - 1) where
  toFun A := ⟨generationMap F (fun i => (A i).val), by
    apply IsHomogeneous.sum
    intro i _
    have h := (A i).property.mul (cofactor_homogeneous F e hhom i)
    have hi := degree_le_sum e i
    have hipos := he i
    have hdegree : (e i - 1) + (degreeSum e - e i) = degreeSum e - 1 := by omega
    rw [hdegree] at h
    exact h⟩
  map_add' A B := by
    apply Subtype.ext
    change (∑ i, ((A i).val + (B i).val) * cofactor F i) =
      (∑ i, (A i).val * cofactor F i) + ∑ i, (B i).val * cofactor F i
    simp [add_mul, Finset.sum_add_distrib]
  map_smul' c A := by
    apply Subtype.ext
    change (∑ i, (c • (A i).val) * cofactor F i) = c • ∑ i, (A i).val * cofactor F i
    simp [smul_mul_assoc, Finset.smul_sum]

theorem weightedGeneration_eq_zero (F : I → BinaryRing K) (e : I → ℕ)
    (he : ∀ i, 0 < e i) (hF0 : ∀ i, F i ≠ 0)
    (hF : Pairwise (fun i j => IsRelPrime (F i) (F j)))
    (hhom : ∀ i, (F i).IsHomogeneous (e i)) (A : Coefficients (K := K) e)
    (hzero : weightedGeneration F e he hhom A = 0) : A = 0 := by
  have hrel : generationMap F (fun i => (A i).val) = 0 := congrArg Subtype.val hzero
  funext i
  apply Subtype.ext
  change (A i).val = 0
  by_contra hAi0
  have hdvd := coefficient_dvd_of_relation F (fun j => (A j).val) hF hrel i
  have hle := totalDegree_le_of_dvd_of_isDomain hdvd hAi0
  rw [(hhom i).totalDegree (hF0 i), (A i).property.totalDegree hAi0] at hle
  have hi := he i
  omega

theorem weightedGeneration_injective (F : I → BinaryRing K) (e : I → ℕ)
    (he : ∀ i, 0 < e i) (hF0 : ∀ i, F i ≠ 0)
    (hF : Pairwise (fun i j => IsRelPrime (F i) (F j)))
    (hhom : ∀ i, (F i).IsHomogeneous (e i)) :
    Function.Injective (weightedGeneration F e he hhom) := by
  intro A B hAB
  apply sub_eq_zero.mp
  apply weightedGeneration_eq_zero F e he hF0 hF hhom
  rw [map_sub, hAB, sub_self]

theorem coefficients_finrank (e : I → ℕ) (he : ∀ i, 0 < e i) :
    finrank K (Coefficients (K := K) e) = degreeSum e := by
  rw [Module.finrank_pi_fintype]
  apply Finset.sum_congr rfl
  intro i _
  rw [binaryForms_finrank]
  have hi := he i
  omega

theorem degreeSum_pos [Nonempty I] (e : I → ℕ) (he : ∀ i, 0 < e i) : 0 < degreeSum e :=
  lt_of_lt_of_le (he (Classical.choice (inferInstance : Nonempty I))) (degree_le_sum e _)

/-- Surjectivity is proved from syzygies and dimensions, never postulated. -/
theorem weightedGeneration_surjective [Nonempty I] (F : I → BinaryRing K) (e : I → ℕ)
    (he : ∀ i, 0 < e i) (hF0 : ∀ i, F i ≠ 0)
    (hF : Pairwise (fun i j => IsRelPrime (F i) (F j)))
    (hhom : ∀ i, (F i).IsHomogeneous (e i)) :
    Function.Surjective (weightedGeneration F e he hhom) := by
  have hdim : finrank K (Coefficients (K := K) e) =
      finrank K (BinaryForms K (degreeSum e - 1)) := by
    rw [coefficients_finrank e he, binaryForms_finrank]
    have hs := degreeSum_pos e he
    omega
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp
    (weightedGeneration_injective F e he hF0 hF hhom)

theorem exists_binary_cofactor_expansion [Nonempty I] (F : I → BinaryRing K) (e : I → ℕ)
    (he : ∀ i, 0 < e i) (hF0 : ∀ i, F i ≠ 0)
    (hF : Pairwise (fun i j => IsRelPrime (F i) (F j)))
    (hhom : ∀ i, (F i).IsHomogeneous (e i))
    (P : BinaryRing K) (hP : P.IsHomogeneous (degreeSum e - 1)) :
    ∃ A : I → BinaryRing K, (∀ i, (A i).IsHomogeneous (e i - 1)) ∧
      P = ∑ i, A i * cofactor F i := by
  obtain ⟨A, hA⟩ := weightedGeneration_surjective F e he hF0 hF hhom ⟨P, hP⟩
  exact ⟨fun i => (A i).val, fun i => (A i).property, (congrArg Subtype.val hA).symm⟩

#print axioms weightedGeneration_injective
#print axioms weightedGeneration_surjective
#print axioms exists_binary_cofactor_expansion

end Cylinder.IntersectionBinaryGeneration

end
