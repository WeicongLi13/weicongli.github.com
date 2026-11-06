module

public import Cylinder.CompleteIntersectionGraded
public import Cylinder.ResidualCoordinateTransport
public import Cylinder.PlanePlateau

/-! Low-degree actual complete-intersection pieces vanish. Consequently
the actual relative residual quotient piece is the actual residual ideal
piece, with an explicit isomorphism rather than a dimension assumption. -/

@[expose] public section
noncomputable section

namespace Cylinder.CompleteIntersectionLowPieces

open Module MvPolynomial Cylinder.HilbertEvaluation Cylinder.CompleteIntersectionKoszul
open Cylinder.CompleteIntersectionGraded Cylinder.ResidualCoordinateTransport
open scoped Classical

variable {K : Type*} [Field K]

theorem homogeneous_eq_zero_of_mem_equations (F G H : PlaneRing K) (e t n : ℕ)
    (hF : F.IsHomogeneous e) (hG : G.IsHomogeneous t) (hH : H.IsHomogeneous n)
    (hne : n < e) (hnt : n < t) (hHI : H ∈ equationsIdeal F G) : H = 0 := by
  have hmem : (⟨H, hH⟩ : Forms K n) ∈ idealPiece F G n := hHI
  rw [← gradedGenerator_range F G e t n hF hG] at hmem
  obtain ⟨A, hA⟩ := hmem
  have hzF := shiftedForms_zero_of_not_le e n A.1 (by omega)
  have hzG := shiftedForms_zero_of_not_le t n A.2 (by omega)
  have hv := congrArg Subtype.val hA
  change A.1.val * F + A.2.val * G = H at hv
  simpa only [hzF, hzG, zero_mul, zero_add] using hv.symm

theorem equation_piece_eq_bot (F G : PlaneRing K) (e t n : ℕ)
    (hF : F.IsHomogeneous e) (hG : G.IsHomogeneous t) (hne : n < e) (hnt : n < t) :
    Cylinder.PlanePlateau.piece (equationsIdeal F G) n = ⊥ := by
  apply eq_bot_iff.mpr
  intro H hH
  exact homogeneous_eq_zero_of_mem_equations F G H e t n hF hG hH.2 hne hnt hH.1

def integerPlaneForms (K : Type*) [Field K] (d : ℤ) : Submodule K (PlaneRing K) :=
  if 0 ≤ d then Forms K d.toNat else ⊥

abbrev RelativePiece (F G : PlaneRing K) (D : Ideal (PlaneRing K)) (n : ℕ) :=
  ResidualQuotient (equationsIdeal F G) D (integerPlaneForms K) (n : ℤ)

theorem relative_equation_piece_eq_bot (F G : PlaneRing K) (D : Ideal (PlaneRing K)) (e t n : ℕ)
    (hF : F.IsHomogeneous e) (hG : G.IsHomogeneous t) (hne : n < e) (hnt : n < t) :
    equationPiece (equationsIdeal F G) D (integerPlaneForms K) (n : ℤ) = ⊥ := by
  apply eq_bot_iff.mpr
  intro H hH
  change H = 0
  apply Subtype.ext
  change H.val = (0 : PlaneRing K)
  apply homogeneous_eq_zero_of_mem_equations F G H.val e t n hF hG _ hne hnt hH
  have hmem : H.val ∈ integerPlaneForms K (n : ℤ) := H.property.2
  have hh : H.val ∈ Forms K n := by
    simpa only [integerPlaneForms, Int.natCast_nonneg, ite_true, Int.toNat_natCast] using hmem
  exact (mem_homogeneousSubmodule _ _).mp hh

/-- Low-degree residual quotients are actual residual ideal pieces. -/
def relativePieceEquiv (F G : PlaneRing K) (D : Ideal (PlaneRing K)) (e t n : ℕ)
    (hF : F.IsHomogeneous e) (hG : G.IsHomogeneous t) (hne : n < e) (hnt : n < t) :
    RelativePiece F G D n ≃ₗ[K]
      Cylinder.PlanePlateau.piece ((equationsIdeal F G).colon (D : Set (PlaneRing K))) n :=
  ((equationPiece (equationsIdeal F G) D (integerPlaneForms K) (n : ℤ)).quotEquivOfEqBot
    (relative_equation_piece_eq_bot F G D e t n hF hG hne hnt)).trans
      (LinearEquiv.ofEq _ _ (by simp only [residualPiece, integerPlaneForms,
        Int.natCast_nonneg, ite_true, Int.toNat_natCast, Cylinder.PlanePlateau.piece]))

theorem residual_piece_finrank (F G : PlaneRing K) (D : Ideal (PlaneRing K)) (e t n : ℕ)
    (hF : F.IsHomogeneous e) (hG : G.IsHomogeneous t) (hne : n < e) (hnt : n < t) :
    finrank K (RelativePiece F G D n) =
      finrank K (Cylinder.PlanePlateau.piece ((equationsIdeal F G).colon (D : Set (PlaneRing K))) n) :=
  (relativePieceEquiv F G D e t n hF hG hne hnt).finrank_eq

#print axioms homogeneous_eq_zero_of_mem_equations
#print axioms relativePieceEquiv
#print axioms residual_piece_finrank

end Cylinder.CompleteIntersectionLowPieces

end
