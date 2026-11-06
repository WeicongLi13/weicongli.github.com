module

public import Cylinder.FinalAssociatedPieces
public import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal

/-! The direct sum of all degree quotients of a homogeneous two-generator
ideal is its actual polynomial quotient, including its degree-zero part. -/

@[expose] public section
noncomputable section

namespace Cylinder.FinalHomogeneousQuotient

open Module MvPolynomial
open Cylinder.PlaneBinaryReduction Cylinder.CompleteIntersectionKoszul
open Cylinder.BinaryCompleteIntersectionGraded
open scoped Classical DirectSum

variable {K : Type*} [Field K]
local instance : GradedAlgebra (BinaryForms K) := MvPolynomial.gradedAlgebra

abbrev DegreeQuotient (F G : BinaryRing K) (n : ℕ) :=
  BinaryForms K n ⧸ idealPiece F G n

instance degreeQuotientAddCommGroup (F G : BinaryRing K) (n : ℕ) :
    AddCommGroup (DegreeQuotient F G n) :=
  Submodule.Quotient.addCommGroup (idealPiece F G n)

abbrev Sum (F G : BinaryRing K) := ⨁ n : ℕ, DegreeQuotient F G n

instance sumAddCommGroup (F G : BinaryRing K) : AddCommGroup (Sum F G) :=
  inferInstanceAs (AddCommGroup (Π₀ n : ℕ, DegreeQuotient F G n))

def polynomialToSum (F G : BinaryRing K) : BinaryRing K →ₗ[K] Sum F G :=
  (DFinsupp.mapRange.linearMap (fun n => (idealPiece F G n).mkQ)).comp
    (DirectSum.decomposeLinearEquiv (BinaryForms K)).toLinearMap

theorem polynomialToSum_apply (F G P : BinaryRing K) (n : ℕ) :
    polynomialToSum F G P n =
      Submodule.Quotient.mk (DirectSum.decompose (BinaryForms K) P n) := rfl

theorem polynomialToSum_homogeneous (F G : BinaryRing K) (n : ℕ) (P : BinaryForms K n) :
    polynomialToSum F G P.val =
      DirectSum.lof K ℕ (DegreeQuotient F G) n (Submodule.Quotient.mk P) := by
  simp only [polynomialToSum, LinearMap.comp_apply, LinearEquiv.coe_coe,
    DirectSum.decomposeLinearEquiv_apply_coe]
  exact DFinsupp.mapRange_single (hf := fun n => (idealPiece F G n).mkQ.map_zero)

theorem equationsIdeal_homogeneous (F G : BinaryRing K) (e t : ℕ)
    (hF : F.IsHomogeneous e) (hG : G.IsHomogeneous t) :
    (equationsIdeal F G).IsHomogeneous (BinaryForms K) := by
  apply Ideal.homogeneous_span
  intro P hP
  rcases hP with rfl | hP
  · exact ⟨e, hF⟩
  · have hPG := Set.mem_singleton_iff.mp hP
    subst P
    exact ⟨t, hG⟩

theorem polynomialToSum_kernel (F G : BinaryRing K) (e t : ℕ)
    (hF : F.IsHomogeneous e) (hG : G.IsHomogeneous t) :
    LinearMap.ker (polynomialToSum F G) = (equationsIdeal F G).restrictScalars K := by
  ext P
  change polynomialToSum F G P = 0 ↔ P ∈ equationsIdeal F G
  rw [(equationsIdeal_homogeneous F G e t hF hG).mem_iff]
  constructor
  · intro h n
    have hn := congrArg (fun a : Sum F G => a n) h
    change Submodule.Quotient.mk (DirectSum.decompose (BinaryForms K) P n) =
      (0 : DegreeQuotient F G n) at hn
    exact (Submodule.Quotient.mk_eq_zero (idealPiece F G n)).mp hn
  · intro h
    apply DFinsupp.ext
    intro n
    change Submodule.Quotient.mk (DirectSum.decompose (BinaryForms K) P n) =
      (0 : DegreeQuotient F G n)
    exact (Submodule.Quotient.mk_eq_zero (idealPiece F G n)).mpr (h n)

theorem polynomialToSum_surjective (F G : BinaryRing K) :
    Function.Surjective (polynomialToSum F G) := by
  have hmap : Function.Surjective
      (DFinsupp.mapRange.linearMap (fun n => (idealPiece F G n).mkQ)) :=
    (DFinsupp.mapRange_surjective _ (fun n => (idealPiece F G n).mkQ.map_zero)).mpr
      (fun n => (idealPiece F G n).mkQ_surjective)
  exact hmap.comp (DirectSum.decomposeLinearEquiv (BinaryForms K)).surjective

def quotientToSum (F G : BinaryRing K) (e t : ℕ)
    (hF : F.IsHomogeneous e) (hG : G.IsHomogeneous t) :
    QuotientRing F G →ₗ[K] Sum F G where
  toFun x := Quotient.liftOn' x (polynomialToSum F G) (by
    intro P Q h
    apply sub_eq_zero.mp
    rw [← map_sub]
    apply LinearMap.mem_ker.mp
    rw [polynomialToSum_kernel F G e t hF hG]
    exact (Submodule.quotientRel_def (equationsIdeal F G)).mp h)
  map_add' := by
    rintro ⟨P⟩ ⟨Q⟩
    exact (polynomialToSum F G).map_add P Q
  map_smul' := by
    intro c
    rintro ⟨P⟩
    exact (polynomialToSum F G).map_smul c P

theorem quotientToSum_mk (F G : BinaryRing K) (e t : ℕ)
    (hF : F.IsHomogeneous e) (hG : G.IsHomogeneous t) (P : BinaryRing K) :
    quotientToSum F G e t hF hG (Ideal.Quotient.mk (equationsIdeal F G) P) =
      polynomialToSum F G P := rfl

def quotientEquiv (F G : BinaryRing K) (e t : ℕ)
    (hF : F.IsHomogeneous e) (hG : G.IsHomogeneous t) :
    QuotientRing F G ≃ₗ[K] Sum F G :=
  LinearEquiv.ofBijective (quotientToSum F G e t hF hG) ⟨by
    rintro ⟨P⟩ ⟨Q⟩ h
    apply (Submodule.Quotient.eq _).mpr
    change P - Q ∈ equationsIdeal F G
    have hker : P - Q ∈ LinearMap.ker (polynomialToSum F G) := by
      change polynomialToSum F G (P - Q) = 0
      change polynomialToSum F G P = polynomialToSum F G Q at h
      rw [map_sub, h, sub_self]
    rwa [polynomialToSum_kernel F G e t hF hG] at hker,
    by
      intro z
      obtain ⟨P, hP⟩ := polynomialToSum_surjective F G z
      exact ⟨Ideal.Quotient.mk (equationsIdeal F G) P, hP⟩⟩

theorem quotientEquiv_mk (F G : BinaryRing K) (e t : ℕ)
    (hF : F.IsHomogeneous e) (hG : G.IsHomogeneous t) (P : BinaryRing K) :
    quotientEquiv F G e t hF hG (Ideal.Quotient.mk (equationsIdeal F G) P) =
      polynomialToSum F G P := rfl

theorem quotientEquiv_symm_lof (F G : BinaryRing K) (e t n : ℕ)
    (hF : F.IsHomogeneous e) (hG : G.IsHomogeneous t) (P : BinaryForms K n) :
    (quotientEquiv F G e t hF hG).symm
      (DirectSum.lof K ℕ (DegreeQuotient F G) n (Submodule.Quotient.mk P)) =
        Ideal.Quotient.mk (equationsIdeal F G) P.val := by
  apply (quotientEquiv F G e t hF hG).injective
  rw [LinearEquiv.apply_symm_apply, quotientEquiv_mk, polynomialToSum_homogeneous]

end Cylinder.FinalHomogeneousQuotient

end
