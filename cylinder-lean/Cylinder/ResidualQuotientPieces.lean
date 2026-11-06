module

public import Cylinder.ResidualEvaluation

/-! Actual homogeneous residual quotient pieces are the complementary
filtered affine annihilator pieces. The maps, kernels and surjectivity are
proved on the actual colon ideal and actual dehomogenization. -/

@[expose] public section
noncomputable section

namespace Cylinder.ResidualQuotientPieces

open Module MvPolynomial
open Cylinder.PlaneBinaryReduction Cylinder.CompleteIntersectionKoszul
open Cylinder.CompleteIntersectionFiltered Cylinder.AffinePointEvaluation
open Cylinder.AffineEvaluationDuality Cylinder.FiniteEvaluationDuality
open Cylinder.CurvePolarLocal Cylinder.PlaneHomogenization
open Cylinder.HomogeneousCompleteIntersection Cylinder.ResidualEvaluation
open scoped Classical

variable {K I : Type*} [Field K] [Fintype I]

def dehomogenizeLinear : HomRing (K := K) →ₗ[K] BinaryRing K where
  toFun := dehomogenize
  map_add' H J := map_add _ _ _
  map_smul' c H := by simp [smul_eq_C_mul, map_mul]

def residualPiece (F G : HomRing (K := K)) (v : I → Fin 2 → K) (n : ℕ) :
    Submodule K (HomForms K n) :=
  ((residualIdeal F G v).restrictScalars K).comap (HomForms K n).subtype

def equationInResidualPiece (F G : HomRing (K := K)) (v : I → Fin 2 → K) (n : ℕ) :
    Submodule K (residualPiece F G v n) :=
  ((equationsIdeal F G).restrictScalars K).comap
    ((HomForms K n).subtype.comp (residualPiece F G v n).subtype)

abbrev ResidualQuotientPiece (F G : HomRing (K := K)) (v : I → Fin 2 → K) (n : ℕ) : Type _ :=
  @HasQuotient.Quotient ↥(residualPiece F G v n) _
    (Submodule.hasQuotient (R := K)) (equationInResidualPiece F G v n)

def residualToAffine (F G : HomRing (K := K)) (e t n : ℕ)
    (hF : F.IsHomogeneous e) (hG : G.IsHomogeneous t)
    (hf : (dehomogenize F).totalDegree = e) (hg : (dehomogenize G).totalDegree = t)
    (hfe : homogeneousComponent e (dehomogenize F) ≠ 0)
    (hcop : IsRelPrime (homogeneousComponent e (dehomogenize F))
      (homogeneousComponent t (dehomogenize G)))
    (v : I → Fin 2 → K)
    (hfv : ∀ i, eval (v i) (dehomogenize F) = 0)
    (hgv : ∀ i, eval (v i) (dehomogenize G) = 0) :
    residualPiece F G v n →ₗ[K]
      ↥((pointIdeal (dehomogenize F) (dehomogenize G) v hfv hgv).annihilator.restrictScalars K ⊓
        filteredPiece (dehomogenize F) (dehomogenize G) n) :=
  (((Ideal.Quotient.mkₐ K (equationsIdeal (dehomogenize F) (dehomogenize G))).toLinearMap.comp
    dehomogenizeLinear).comp ((HomForms K n).subtype.comp (residualPiece F G v n).subtype)).codRestrict _ (by
      intro H
      constructor
      · exact (homogeneous_mem_residual_iff_annihilator F G H.val.val e t n hF hG H.val.property
          hf hg hfe hcop v hfv hgv).mp H.property
      · exact (mem_filteredPiece _ _ n _).mpr ⟨dehomogenize H.val.val,
          (dehomogenize_totalDegree_le H.val.val).trans H.val.property.totalDegree_le, rfl⟩)

theorem residualToAffine_kernel (F G : HomRing (K := K)) (e t n : ℕ)
    (hF : F.IsHomogeneous e) (hG : G.IsHomogeneous t)
    (hf : (dehomogenize F).totalDegree = e) (hg : (dehomogenize G).totalDegree = t)
    (hfe : homogeneousComponent e (dehomogenize F) ≠ 0)
    (hcop : IsRelPrime (homogeneousComponent e (dehomogenize F))
      (homogeneousComponent t (dehomogenize G)))
    (v : I → Fin 2 → K)
    (hfv : ∀ i, eval (v i) (dehomogenize F) = 0)
    (hgv : ∀ i, eval (v i) (dehomogenize G) = 0) :
    LinearMap.ker (residualToAffine F G e t n hF hG hf hg hfe hcop v hfv hgv) =
      equationInResidualPiece F G v n := by
  ext H
  constructor
  · intro hH
    have hz := congrArg Subtype.val hH
    have hHI := Ideal.Quotient.eq_zero_iff_mem.mp hz
    exact (homogeneous_mem_iff_dehomogenize_mem F G H.val.val e t n hF hG H.val.property hf hg hfe hcop).mpr hHI
  · intro hH
    apply Subtype.ext
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    exact (homogeneous_mem_iff_dehomogenize_mem F G H.val.val e t n hF hG H.val.property hf hg hfe hcop).mp hH

theorem residualToAffine_surjective (F G : HomRing (K := K)) (e t n : ℕ)
    (hF : F.IsHomogeneous e) (hG : G.IsHomogeneous t)
    (hf : (dehomogenize F).totalDegree = e) (hg : (dehomogenize G).totalDegree = t)
    (hfe : homogeneousComponent e (dehomogenize F) ≠ 0)
    (hcop : IsRelPrime (homogeneousComponent e (dehomogenize F))
      (homogeneousComponent t (dehomogenize G)))
    (v : I → Fin 2 → K)
    (hfv : ∀ i, eval (v i) (dehomogenize F) = 0)
    (hgv : ∀ i, eval (v i) (dehomogenize G) = 0) :
    Function.Surjective (residualToAffine F G e t n hF hG hf hg hfe hcop v hfv hgv) := by
  intro a
  obtain ⟨P, hPdeg, hPa⟩ := (mem_filteredPiece _ _ n a.val).mp a.property.2
  let H : HomForms K n := ⟨homogenize n P, homogenize_homogeneous n P hPdeg⟩
  have hHI : H ∈ residualPiece F G v n := by
    apply (homogeneous_mem_residual_iff_annihilator F G H.val e t n hF hG H.property
      hf hg hfe hcop v hfv hgv).mpr
    rw [dehomogenize_homogenize, hPa]
    exact a.property.1
  refine ⟨⟨H, hHI⟩, ?_⟩
  apply Subtype.ext
  change Ideal.Quotient.mk (equationsIdeal (dehomogenize F) (dehomogenize G))
    (dehomogenize (homogenize n P)) = a.val
  rw [dehomogenize_homogenize]
  exact hPa

/-- The geometric residual quotient is isomorphic to the actual affine
annihilator filtration piece. -/
def residualQuotientEquiv (F G : HomRing (K := K)) (e t n : ℕ)
    (hF : F.IsHomogeneous e) (hG : G.IsHomogeneous t)
    (hf : (dehomogenize F).totalDegree = e) (hg : (dehomogenize G).totalDegree = t)
    (hfe : homogeneousComponent e (dehomogenize F) ≠ 0)
    (hcop : IsRelPrime (homogeneousComponent e (dehomogenize F))
      (homogeneousComponent t (dehomogenize G)))
    (v : I → Fin 2 → K)
    (hfv : ∀ i, eval (v i) (dehomogenize F) = 0)
    (hgv : ∀ i, eval (v i) (dehomogenize G) = 0) :
    ResidualQuotientPiece F G v n ≃ₗ[K]
      ↥((pointIdeal (dehomogenize F) (dehomogenize G) v hfv hgv).annihilator.restrictScalars K ⊓
        filteredPiece (dehomogenize F) (dehomogenize G) n) :=
  (Submodule.quotEquivOfEq _ _
    (residualToAffine_kernel F G e t n hF hG hf hg hfe hcop v hfv hgv).symm).trans
      (LinearMap.quotKerEquivOfSurjective (R := K)
        (residualToAffine F G e t n hF hG hf hg hfe hcop v hfv hgv)
        (residualToAffine_surjective F G e t n hF hG hf hg hfe hcop v hfv hgv))

#print axioms residualToAffine_kernel
#print axioms residualToAffine_surjective
#print axioms residualQuotientEquiv

end Cylinder.ResidualQuotientPieces

end
