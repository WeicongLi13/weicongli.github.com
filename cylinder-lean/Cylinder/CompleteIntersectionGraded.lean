module

public import Cylinder.CompleteIntersectionKoszul
public import Cylinder.HomogeneousDivision
public import Cylinder.PlaneBinaryReduction

/-!
# Degree pieces of the actual complete-intersection quotient

Shifted coefficient spaces include their zero pieces below degree zero.
Homogeneous projection gives the actual degree part of the ideal `(F,G)`;
the proved Koszul syzygy gives its real relation space.
-/

@[expose] public section
noncomputable section

namespace Cylinder.CompleteIntersectionGraded

open Module MvPolynomial
open Cylinder.HilbertEvaluation Cylinder.CompleteIntersectionKoszul
open scoped Classical

variable {K : Type*} [Field K]

local instance : GradedAlgebra (Forms K) := MvPolynomial.gradedAlgebra

def shiftedForms (e d : ℕ) : Submodule K (PlaneRing K) :=
  if e ≤ d then Forms K (d - e) else ⊥

theorem mem_shiftedForms (e d : ℕ) (P : PlaneRing K) :
    P ∈ shiftedForms (K := K) e d ↔
      if e ≤ d then P.IsHomogeneous (d - e) else P = 0 := by
  by_cases h : e ≤ d <;> simp [shiftedForms, h]

instance shiftedForms_finite (e d : ℕ) : FiniteDimensional K (shiftedForms (K := K) e d) := by
  by_cases h : e ≤ d
  · rw [shiftedForms, if_pos h]; infer_instance
  · rw [shiftedForms, if_neg h]; infer_instance

theorem shiftedForms_homogeneous (e d : ℕ) (P : shiftedForms (K := K) e d) :
    P.val.IsHomogeneous (d - e) := by
  have h := (mem_shiftedForms e d P.val).mp P.property
  by_cases he : e ≤ d
  · simpa only [he, ite_true] using h
  · have hP : P.val = 0 := by simpa only [he, ite_false] using h
    rw [hP]
    exact isHomogeneous_zero _ _ _

theorem shiftedForms_zero_of_not_le (e d : ℕ) (P : shiftedForms (K := K) e d)
    (h : ¬e ≤ d) : P.val = 0 := by
  simpa only [h, ite_false] using (mem_shiftedForms e d P.val).mp P.property

def shiftedProjection (e d : ℕ) : PlaneRing K →ₗ[K] shiftedForms (K := K) e d :=
  if h : e ≤ d then
    (MvPolynomial.homogeneousComponent (d - e)).codRestrict _
      (fun P => (mem_shiftedForms e d _).mpr (by
        simp only [h, ite_true]
        exact homogeneousComponent_isHomogeneous _ _))
  else 0

theorem shiftedProjection_mul (F A : PlaneRing K) (e d : ℕ) (hF : F.IsHomogeneous e) :
    (DirectSum.decompose (Forms K) (A * F) d : PlaneRing K) =
      (shiftedProjection (K := K) e d A).val * F := by
  rw [DirectSum.coe_decompose_mul_of_right_mem (Forms K) d hF]
  by_cases h : e ≤ d
  · simp only [h, ite_true, shiftedProjection, dif_pos]
    congr 1
    exact MvPolynomial.decomposition.decompose'_apply _ _
  · simp [h, shiftedProjection]

theorem shiftedForms_mul_mem (F : PlaneRing K) (r e d : ℕ)
    (hF : F.IsHomogeneous r) (hre : r ≤ e) (P : shiftedForms (K := K) e d) :
    F * P.val ∈ shiftedForms (K := K) (e - r) d := by
  apply (mem_shiftedForms _ _ _).mpr
  by_cases hed : e ≤ d
  · have hsmall : e - r ≤ d := by omega
    simp only [hsmall, ite_true]
    have hh := hF.mul (shiftedForms_homogeneous e d P)
    convert hh using 1 <;> omega
  · rw [shiftedForms_zero_of_not_le e d P hed, mul_zero]
    split <;> simp [isHomogeneous_zero]

def gradedGenerator (F G : PlaneRing K) (e t d : ℕ)
    (hF : F.IsHomogeneous e) (hG : G.IsHomogeneous t) :
    (shiftedForms (K := K) e d × shiftedForms (K := K) t d) →ₗ[K] Forms K d where
  toFun A := ⟨A.1.val * F + A.2.val * G, by
    have hmul (P : PlaneRing K) (r : ℕ) (hP : P.IsHomogeneous r)
        (B : shiftedForms (K := K) r d) : (B.val * P).IsHomogeneous d := by
      by_cases hrd : r ≤ d
      · have hh := (shiftedForms_homogeneous r d B).mul hP
        convert hh using 1 <;> omega
      · rw [shiftedForms_zero_of_not_le r d B hrd, zero_mul]
        exact isHomogeneous_zero _ _ _
    exact (hmul F e hF A.1).add (hmul G t hG A.2)⟩
  map_add' A B := by apply Subtype.ext; simp only [Prod.fst_add, Prod.snd_add,
    Submodule.coe_add, add_mul]; ring
  map_smul' c A := by apply Subtype.ext; simp [smul_add, smul_mul_assoc]

def quotientPieceMap (F G : PlaneRing K) (d : ℕ) :
    Forms K d →ₗ[K] QuotientRing F G :=
  (Ideal.Quotient.mkₐ K (equationsIdeal F G)).toLinearMap.comp (Forms K d).subtype

def quotientPiece (F G : PlaneRing K) (d : ℕ) : Submodule K (QuotientRing F G) :=
  LinearMap.range (quotientPieceMap F G d)

def idealPiece (F G : PlaneRing K) (d : ℕ) : Submodule K (Forms K d) :=
  ((equationsIdeal F G).restrictScalars K).comap (Forms K d).subtype

theorem quotientPieceMap_kernel (F G : PlaneRing K) (d : ℕ) :
    LinearMap.ker (quotientPieceMap F G d) = idealPiece F G d := by
  ext P
  exact Ideal.Quotient.eq_zero_iff_mem

theorem gradedGenerator_range (F G : PlaneRing K) (e t d : ℕ)
    (hF : F.IsHomogeneous e) (hG : G.IsHomogeneous t) :
    LinearMap.range (gradedGenerator F G e t d hF hG) = idealPiece F G d := by
  ext P
  constructor
  · rintro ⟨A, rfl⟩
    exact Ideal.mem_span_pair.mpr ⟨A.1.val, A.2.val, rfl⟩
  · intro hP
    obtain ⟨A, B, hAB⟩ := Ideal.mem_span_pair.mp hP
    refine ⟨(shiftedProjection e d A, shiftedProjection t d B), ?_⟩
    apply Subtype.ext
    have hp := congrArg (fun Q : PlaneRing K =>
      (DirectSum.decompose (Forms K) Q d : PlaneRing K)) hAB
    change (DirectSum.decompose (Forms K) (A * F + B * G) d : PlaneRing K) =
      (DirectSum.decompose (Forms K) P.val d : PlaneRing K) at hp
    rw [DirectSum.decompose_add, DirectSum.add_apply, Submodule.coe_add,
      DirectSum.decompose_of_mem_same (Forms K) P.property,
      shiftedProjection_mul F A e d hF, shiftedProjection_mul G B t d hG] at hp
    exact hp

def gradedKoszul (F G : PlaneRing K) (e t d : ℕ)
    (hF : F.IsHomogeneous e) (hG : G.IsHomogeneous t) :
    shiftedForms (K := K) (e + t) d →ₗ[K]
      (shiftedForms (K := K) e d × shiftedForms (K := K) t d) where
  toFun c := (⟨-G * c.val, by
    have h := shiftedForms_mul_mem G t (e + t) d hG (by omega) c
    simpa using (shiftedForms (K := K) e d).neg_mem (by simpa using h)⟩,
    ⟨F * c.val, by
      simpa using shiftedForms_mul_mem F e (e + t) d hF (by omega) c⟩)
  map_add' c z := by apply Prod.ext <;> apply Subtype.ext <;> simp [mul_add]
  map_smul' a c := by apply Prod.ext <;> apply Subtype.ext <;> simp [smul_mul_assoc, mul_smul_comm]

theorem gradedKoszul_injective (F G : PlaneRing K) (e t d : ℕ)
    (hF : F.IsHomogeneous e) (hG : G.IsHomogeneous t) (hF0 : F ≠ 0) :
    Function.Injective (gradedKoszul F G e t d hF hG) := by
  intro c z hcz
  apply Subtype.ext
  exact mul_left_cancel₀ hF0 (congrArg (fun A => A.2.val) hcz)

theorem koszul_coefficient_mem (F G B c : PlaneRing K) (e t d : ℕ)
    (hF : F.IsHomogeneous e) (hF0 : F ≠ 0)
    (hB : B ∈ shiftedForms (K := K) t d) (hBc : B = F * c) :
    c ∈ shiftedForms (K := K) (e + t) d := by
  apply (mem_shiftedForms _ _ _).mpr
  by_cases hs : e + t ≤ d
  · simp only [hs, ite_true]
    have htd : t ≤ d := by omega
    have hBh : B.IsHomogeneous (d - t) := by
      simpa only [htd, ite_true] using (mem_shiftedForms t d B).mp hB
    have heq : e + (d - (e + t)) = d - t := by omega
    exact HomogeneousDivision.quotient_isHomogeneous F B c e (d - (e + t))
      hF0 hF (heq.symm ▸ hBh) hBc.symm
  · simp only [hs, ite_false]
    have hB0 : B = 0 := by
      by_cases htd : t ≤ d
      · have hBh : B.IsHomogeneous (d - t) := by
          simpa only [htd, ite_true] using (mem_shiftedForms t d B).mp hB
        by_contra hBn
        have hdeg := totalDegree_le_of_dvd_of_isDomain (show F ∣ B from ⟨c, hBc⟩) hBn
        rw [hF.totalDegree hF0, hBh.totalDegree hBn] at hdeg
        omega
      · simpa only [htd, ite_false] using (mem_shiftedForms t d B).mp hB
    exact (mul_eq_zero.mp (hBc.symm.trans hB0)).resolve_left hF0

theorem gradedKoszul_range (F G : PlaneRing K) (e t d : ℕ)
    (hF : F.IsHomogeneous e) (hG : G.IsHomogeneous t)
    (hF0 : F ≠ 0) (hcop : IsRelPrime F G) :
    LinearMap.range (gradedKoszul F G e t d hF hG) =
      LinearMap.ker (gradedGenerator F G e t d hF hG) := by
  ext A
  constructor
  · rintro ⟨c, rfl⟩
    apply Subtype.ext
    change (-G * c.val) * F + (F * c.val) * G = 0
    ring
  · intro hA
    have hrel : A.1.val * F + A.2.val * G = 0 := congrArg Subtype.val hA
    obtain ⟨c, hcA, hcB⟩ := (koszul_syzygy_iff F G hF0 hcop A.1.val A.2.val).mp hrel
    have hcm := koszul_coefficient_mem F G A.2.val c e t d hF hF0 A.2.property hcB
    exact ⟨⟨c, hcm⟩, Prod.ext (Subtype.ext hcA.symm) (Subtype.ext hcB.symm)⟩

theorem gradedKoszul_kernel_finrank (F G : PlaneRing K) (e t d : ℕ)
    (hF : F.IsHomogeneous e) (hG : G.IsHomogeneous t)
    (hF0 : F ≠ 0) (hcop : IsRelPrime F G) :
    finrank K (LinearMap.ker (gradedGenerator F G e t d hF hG)) =
      finrank K (shiftedForms (K := K) (e + t) d) := by
  rw [← gradedKoszul_range F G e t d hF hG hF0 hcop]
  exact LinearMap.finrank_range_of_inj (gradedKoszul_injective F G e t d hF hG hF0)

theorem quotientPiece_rank_formula (F G : PlaneRing K) (e t d : ℕ)
    (hF : F.IsHomogeneous e) (hG : G.IsHomogeneous t)
    (hF0 : F ≠ 0) (hcop : IsRelPrime F G) :
    finrank K (quotientPiece F G d) +
      finrank K (shiftedForms (K := K) e d) + finrank K (shiftedForms (K := K) t d) =
      finrank K (Forms K d) + finrank K (shiftedForms (K := K) (e + t) d) := by
  have hq := (quotientPieceMap F G d).finrank_range_add_finrank_ker
  have hg := (gradedGenerator F G e t d hF hG).finrank_range_add_finrank_ker
  rw [quotientPieceMap_kernel] at hq
  rw [gradedGenerator_range, gradedKoszul_kernel_finrank F G e t d hF hG hF0 hcop,
    Module.finrank_prod] at hg
  change finrank K (quotientPiece F G d) + finrank K (idealPiece F G d) = _ at hq
  omega

#print axioms gradedGenerator_range
#print axioms gradedKoszul_range
#print axioms quotientPiece_rank_formula

end Cylinder.CompleteIntersectionGraded

end
