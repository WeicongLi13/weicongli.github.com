module

public import Cylinder.IntegerEvaluationDuality

/-! A single residue-defined isomorphism in every integer degree. This
choice gives literal compatibility with multiplication, including when
the target relation degree is negative. -/

@[expose] public section
noncomputable section

namespace Cylinder.IntegerResidualDuality

open Module MvPolynomial
open Cylinder.PlaneBinaryReduction Cylinder.CompleteIntersectionKoszul
open Cylinder.FiniteEvaluationDuality Cylinder.CurvePolarLocal Cylinder.PlaneHomogenization
open Cylinder.HomogeneousCompleteIntersection Cylinder.ResidualEvaluation Cylinder.ResidualQuotientPieces
open Cylinder.ResidualIntegerPieces Cylinder.FullEvaluationDuality Cylinder.IntegerEvaluationDuality
open Cylinder.AffinePointEvaluation Cylinder.AffineEvaluationHighDegrees
open Cylinder.CompleteIntersectionFiltered Cylinder.AffineFilteredDuality Cylinder.AffineResidueFunctional
open scoped Classical BigOperators

variable {K I : Type*} [Field K] [Fintype I]

structure ValidSystem (F G : HomRing (K := K)) (e t : ℕ) (v : I → Fin 2 → K) : Prop where
  he : 0 < e
  ht : 0 < t
  hF : F.IsHomogeneous e
  hG : G.IsHomogeneous t
  hf : (dehomogenize F).totalDegree = e
  hg : (dehomogenize G).totalDegree = t
  hfe : homogeneousComponent e (dehomogenize F) ≠ 0
  hge : homogeneousComponent t (dehomogenize G) ≠ 0
  hcop : IsRelPrime (homogeneousComponent e (dehomogenize F)) (homogeneousComponent t (dehomogenize G))
  hv : Function.Injective v
  hfv : ∀ i, eval (v i) (dehomogenize F) = 0
  hgv : ∀ i, eval (v i) (dehomogenize G) = 0

variable (F G : HomRing (K := K)) (e t : ℕ) (v : I → Fin 2 → K) (s : ValidSystem F G e t v)

def pieceToAnnihilator (d : ℤ) : integerResidualPiece F G v d →ₗ[K]
    (pointIdeal (dehomogenize F) (dehomogenize G) v s.hfv s.hgv).annihilator.restrictScalars K :=
  (((Ideal.Quotient.mkₐ K (equationsIdeal (dehomogenize F) (dehomogenize G))).toLinearMap.comp
    dehomogenizeLinear).comp (integerResidualPiece F G v d).subtype).codRestrict _ (by
      intro H
      by_cases hd : 0 ≤ d
      · have hHhom : H.val.IsHomogeneous d.toNat := by
          have hmem : H.val ∈ integerForms K d := H.property.2
          rw [integerForms, if_pos hd] at hmem
          exact (mem_homogeneousSubmodule d.toNat H.val).mp hmem
        exact (homogeneous_mem_residual_iff_annihilator F G H.val e t d.toNat s.hF s.hG hHhom
          s.hf s.hg s.hfe s.hcop v s.hfv s.hgv).mp H.property.1
      · have hH0 : H.val = 0 := by
          have hmem : H.val ∈ integerForms K d := H.property.2
          simpa only [integerForms, if_neg hd, Submodule.mem_bot] using hmem
        change Ideal.Quotient.mk (equationsIdeal (dehomogenize F) (dehomogenize G))
          (dehomogenize H.val) ∈ _
        rw [hH0, map_zero, map_zero]
        exact Submodule.zero_mem _)

def quotientToAnnihilator (d : ℤ) : IntegerResidualQuotient F G v d →ₗ[K]
    (pointIdeal (dehomogenize F) (dehomogenize G) v s.hfv s.hgv).annihilator.restrictScalars K :=
  (integerEquationPiece F G v d).liftQ (pieceToAnnihilator F G e t v s d) (by
    intro H hH
    apply Subtype.ext
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (dehomogenize_mem_equations F G H.val hH))

def quotientCoefficients (d : ℤ) : IntegerResidualQuotient F G v d →ₗ[K] (I → K) :=
  (fullEvaluationDuality (dehomogenize F) (dehomogenize G) e t s.he s.ht s.hf s.hg s.hfe s.hge s.hcop
    v s.hv s.hfv s.hgv).toLinearMap.comp (quotientToAnnihilator F G e t v s d)

theorem quotient_formula (d : ℤ) (a : IntegerResidualQuotient F G v d)
    (b : QuotientRing (dehomogenize F) (dehomogenize G)) :
    residueFunctional (dehomogenize F) (dehomogenize G) e t s.he s.ht s.hf s.hg s.hfe s.hge s.hcop
      ((quotientToAnnihilator F G e t v s d a).val * b) =
    ∑ i, quotientCoefficients F G e t v s d a i * evaluation (dehomogenize F) (dehomogenize G) v s.hfv s.hgv b i :=
  full_duality_formula _ _ e t s.he s.ht s.hf s.hg s.hfe s.hge s.hcop v s.hv s.hfv s.hgv _ b

theorem quotientCoefficients_mem (j : ℤ) (a : IntegerResidualQuotient F G v ((e : ℤ) + t - 3 - j)) :
    quotientCoefficients F G e t v s _ a ∈ integerCoefficientRelations v j := by
  by_cases hj : 0 ≤ j
  · by_cases hd : 0 ≤ (e : ℤ) + t - 3 - j
    · obtain ⟨H, rfl⟩ := Submodule.Quotient.mk_surjective (integerEquationPiece F G v _) a
      rw [integerCoefficientRelations, if_pos hj]
      apply (mem_coefficientRelations v j.toNat _).mpr
      intro P hP
      have hformula := quotient_formula F G e t v s _ (Submodule.Quotient.mk H)
        (Ideal.Quotient.mk (equationsIdeal (dehomogenize F) (dehomogenize G)) P)
      rw [evaluation_mk] at hformula
      have heval (i : I) : polynomialEvaluation v P i = eval (v i) P := rfl
      simp only [heval] at hformula
      rw [← hformula]
      change residueFunctional (dehomogenize F) (dehomogenize G) e t s.he s.ht s.hf s.hg s.hfe s.hge s.hcop
        (Ideal.Quotient.mk (equationsIdeal (dehomogenize F) (dehomogenize G)) (dehomogenize H.val) *
          Ideal.Quotient.mk (equationsIdeal (dehomogenize F) (dehomogenize G)) P) = 0
      rw [← map_mul]
      apply residue_zero_of_low_degree _ _ e t s.he s.ht s.hf s.hg s.hfe s.hge s.hcop
      have hHhom : H.val.IsHomogeneous ((e : ℤ) + t - 3 - j).toNat := by
        have hmem : H.val ∈ integerForms K ((e : ℤ) + t - 3 - j) := H.property.2
        rw [integerForms, if_pos hd] at hmem
        exact (mem_homogeneousSubmodule _ _).mp hmem
      have hdeg := (dehomogenize_totalDegree_le H.val).trans hHhom.totalDegree_le
      have hmul := totalDegree_mul (dehomogenize H.val) P
      omega
    · rw [integerResidualQuotient_eq_zero F G v _ (by omega) a, map_zero]
      exact Submodule.zero_mem _
  · simp only [integerCoefficientRelations, if_neg hj, Submodule.mem_top]

def quotientRelationMap (j : ℤ) : IntegerResidualQuotient F G v ((e : ℤ) + t - 3 - j) →ₗ[K]
    integerCoefficientRelations v j :=
  (quotientCoefficients F G e t v s _).codRestrict _ (quotientCoefficients_mem F G e t v s j)

theorem quotientToAnnihilator_injective (d : ℤ) : Function.Injective (quotientToAnnihilator F G e t v s d) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro a ha
  by_cases hd : 0 ≤ d
  · obtain ⟨H, rfl⟩ := Submodule.Quotient.mk_surjective (integerEquationPiece F G v d) a
    apply (Submodule.Quotient.mk_eq_zero (integerEquationPiece F G v d) (x := H)).mpr
    have hHz := congrArg Subtype.val ha
    have hHhom : H.val.IsHomogeneous d.toNat := by
      have hmem : H.val ∈ integerForms K d := H.property.2
      rw [integerForms, if_pos hd] at hmem
      exact (mem_homogeneousSubmodule _ _).mp hmem
    exact (homogeneous_mem_iff_dehomogenize_mem F G H.val e t d.toNat s.hF s.hG hHhom
      s.hf s.hg s.hfe s.hcop).mpr (Ideal.Quotient.eq_zero_iff_mem.mp hHz)
  · exact integerResidualQuotient_eq_zero F G v d (by omega) a

theorem quotientRelationMap_injective (j : ℤ) : Function.Injective (quotientRelationMap F G e t v s j) := by
  intro a b hab
  apply quotientToAnnihilator_injective F G e t v s _
  apply (fullEvaluationDuality _ _ e t s.he s.ht s.hf s.hg s.hfe s.hge s.hcop v s.hv s.hfv s.hgv).injective
  exact congrArg Subtype.val hab

theorem quotientRelationMap_surjective (j : ℤ) : Function.Surjective (quotientRelationMap F G e t v s j) := by
  intro c
  let d : ℤ := (e : ℤ) + t - 3 - j
  by_cases hd : 0 ≤ d
  · let a := (fullEvaluationDuality (dehomogenize F) (dehomogenize G) e t s.he s.ht s.hf s.hg s.hfe s.hge s.hcop
      v s.hv s.hfv s.hgv).symm c.val
    have hca := (fullEvaluationDuality (dehomogenize F) (dehomogenize G) e t s.he s.ht s.hf s.hg s.hfe s.hge s.hcop
      v s.hv s.hfv s.hgv).apply_symm_apply c.val
    have haf : a.val ∈ filteredPiece (dehomogenize F) (dehomogenize G) d.toNat := by
      by_cases hj : 0 ≤ j
      · have hjσ : j.toNat < e + t - 2 := by dsimp [d] at hd; omega
        have hn : d.toNat = e + t - 2 - j.toNat - 1 := by dsimp [d]; omega
        rw [hn, ← filtered_orthogonal _ _ e t s.he s.ht s.hf s.hg s.hfe s.hge s.hcop j.toNat hjσ]
        apply (Submodule.mem_dualAnnihilator _).mpr
        intro b hb
        obtain ⟨P, hP, hPb⟩ := (mem_filteredPiece _ _ j.toNat b).mp hb
        change residueFunctional _ _ e t s.he s.ht s.hf s.hg s.hfe s.hge s.hcop (a.val * b) = 0
        rw [full_duality_formula _ _ e t s.he s.ht s.hf s.hg s.hfe s.hge s.hcop v s.hv s.hfv s.hgv a b,
          hca, ← hPb]
        have hc : c.val ∈ coefficientRelations v j.toNat := by
          simpa only [integerCoefficientRelations, if_pos hj] using c.property
        exact (mem_coefficientRelations v j.toNat c.val).mp hc P hP
      · rw [filteredPiece_eq_top _ _ e t s.he s.ht s.hf s.hg s.hfe s.hge s.hcop d.toNat (by dsimp [d] at *; omega)]
        trivial
    obtain ⟨H, hH⟩ := residualToAffine_surjective F G e t d.toNat s.hF s.hG s.hf s.hg s.hfe s.hcop v s.hfv s.hgv ⟨a.val, a.property, haf⟩
    let Hi := residualPieceEquivInteger F G v d.toNat d (Int.toNat_of_nonneg hd).symm H
    refine ⟨Submodule.Quotient.mk Hi, ?_⟩
    apply Subtype.ext
    change fullEvaluationDuality _ _ e t s.he s.ht s.hf s.hg s.hfe s.hge s.hcop v s.hv s.hfv s.hgv
      (pieceToAnnihilator F G e t v s d Hi) = c.val
    have heq : pieceToAnnihilator F G e t v s d Hi = a := by
      apply Subtype.ext
      change Ideal.Quotient.mk (equationsIdeal (dehomogenize F) (dehomogenize G)) (dehomogenize H.val.val) = a.val
      exact congrArg Subtype.val hH
    rw [heq]
    exact hca
  · have hj : 0 ≤ j := by
      have he := s.he
      have ht := s.ht
      dsimp [d] at hd
      omega
    have hhigh : e + t - 2 ≤ j.toNat := by dsimp [d] at hd; omega
    have hz := coefficientRelations_eq_bot _ _ e t s.he s.ht s.hf s.hg s.hfe s.hge s.hcop v s.hv s.hfv s.hgv j.toNat hhigh
    have hc : c.val = 0 := by
      simpa only [integerCoefficientRelations, if_pos hj, hz, Submodule.mem_bot] using c.property
    refine ⟨0, ?_⟩
    apply Subtype.ext
    change (quotientCoefficients F G e t v s _ 0) = c.val
    rw [map_zero]
    exact hc.symm

/-- One fixed residue functional gives the actual relation/residual
isomorphisms for all integer j, with no changing choice of pairing. -/
def relationResidualEquiv (j : ℤ) : integerCoefficientRelations v j ≃ₗ[K]
    IntegerResidualQuotient F G v ((e : ℤ) + t - 3 - j) :=
  (LinearEquiv.ofBijective (quotientRelationMap F G e t v s j)
    ⟨quotientRelationMap_injective F G e t v s j, quotientRelationMap_surjective F G e t v s j⟩).symm

#print axioms quotient_formula
#print axioms quotientRelationMap_surjective
#print axioms relationResidualEquiv

end Cylinder.IntegerResidualDuality

end
