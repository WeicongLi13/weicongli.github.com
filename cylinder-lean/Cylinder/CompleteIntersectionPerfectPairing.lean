module

public import Cylinder.CompleteIntersectionAdjoint
public import Mathlib.LinearAlgebra.PerfectPairing.Basic

/-! The actual homogeneous binary complete-intersection multiplication
pairing is perfect. Its nondegeneracy follows from the proved socle and
constructed complementary products, rather than a pairing hypothesis. -/

@[expose] public section
noncomputable section

namespace Cylinder.CompleteIntersectionPerfectPairing

open Module MvPolynomial
open Cylinder.PlaneBinaryReduction Cylinder.CompleteIntersectionKoszul
open Cylinder.BinaryCompleteIntersectionGraded Cylinder.CompleteIntersectionSocle
open Cylinder.CompleteIntersectionAdjoint
open scoped Classical

variable {K : Type*} [Field K]

instance quotientPiece_finite (F G : BinaryRing K) (d : ℕ) :
    FiniteDimensional K (quotientPiece F G d) := by
  unfold quotientPiece
  infer_instance

def topCoordinate (F G : BinaryRing K) (e t : ℕ) (he : 0 < e) (ht : 0 < t)
    (hF : F.IsHomogeneous e) (hG : G.IsHomogeneous t)
    (hF0 : F ≠ 0) (hcop : IsRelPrime F G) :
    quotientPiece F G (e + t - 2) ≃ₗ[K] K :=
  LinearEquiv.ofFinrankEq _ _ (by
    rw [top_quotientPiece_finrank F G e t he ht hF hG hF0 hcop, Module.finrank_self])

/-- Multiply two actual quotient classes, then read the coordinate of their
one-dimensional top quotient piece. -/
def soclePairing (F G : BinaryRing K) (e t i j : ℕ)
    (he : 0 < e) (ht : 0 < t)
    (hF : F.IsHomogeneous e) (hG : G.IsHomogeneous t)
    (hF0 : F ≠ 0) (hcop : IsRelPrime F G) (hij : i + j = e + t - 2) :
    quotientPiece F G i →ₗ[K] quotientPiece F G j →ₗ[K] K :=
  (pieceMultiplication F G i j (e + t - 2) hij).compr₂
    (topCoordinate F G e t he ht hF hG hF0 hcop).toLinearMap

theorem soclePairing_injective (F G : BinaryRing K) (e t i j : ℕ)
    (he : 0 < e) (ht : 0 < t)
    (hF : F.IsHomogeneous e) (hG : G.IsHomogeneous t)
    (hF0 : F ≠ 0) (hcop : IsRelPrime F G) (hij : i + j = e + t - 2) :
    Function.Injective (soclePairing F G e t i j he ht hF hG hF0 hcop hij) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro a ha
  by_contra han
  obtain ⟨b, hb⟩ := pieceMultiplication_separates F G e t i j hF hG hF0 hcop hij a han
  have hab := congrArg (fun f : quotientPiece F G j →ₗ[K] K => f b) ha
  change topCoordinate F G e t he ht hF hG hF0 hcop
    (pieceMultiplication F G i j (e + t - 2) hij a b) = 0 at hab
  exact hb ((topCoordinate F G e t he ht hF hG hF0 hcop).injective
    (hab.trans (map_zero _).symm))

theorem soclePairing_flip (F G : BinaryRing K) (e t i j : ℕ)
    (he : 0 < e) (ht : 0 < t)
    (hF : F.IsHomogeneous e) (hG : G.IsHomogeneous t)
    (hF0 : F ≠ 0) (hcop : IsRelPrime F G) (hij : i + j = e + t - 2) :
    (soclePairing F G e t i j he ht hF hG hF0 hcop hij).flip =
      soclePairing F G e t j i he ht hF hG hF0 hcop (by omega) := by
  ext a b
  apply congrArg (topCoordinate F G e t he ht hF hG hF0 hcop)
  apply Subtype.ext
  exact mul_comm b.val a.val

/-- Perfectness is proved for multiplication on the genuine quotient pieces. -/
theorem soclePairing_isPerfPair (F G : BinaryRing K) (e t i j : ℕ)
    (he : 0 < e) (ht : 0 < t)
    (hF : F.IsHomogeneous e) (hG : G.IsHomogeneous t)
    (hF0 : F ≠ 0) (hcop : IsRelPrime F G) (hij : i + j = e + t - 2) :
    (soclePairing F G e t i j he ht hF hG hF0 hcop hij).IsPerfPair := by
  apply LinearMap.IsPerfPair.of_injective
    (soclePairing_injective F G e t i j he ht hF hG hF0 hcop hij)
  rw [soclePairing_flip]
  exact soclePairing_injective F G e t j i he ht hF hG hF0 hcop (by omega)

/-- The complementary homogeneous pieces are actual dual vector spaces. -/
def complementaryPieceEquivDual (F G : BinaryRing K) (e t i j : ℕ)
    (he : 0 < e) (ht : 0 < t)
    (hF : F.IsHomogeneous e) (hG : G.IsHomogeneous t)
    (hF0 : F ≠ 0) (hcop : IsRelPrime F G) (hij : i + j = e + t - 2) :
    quotientPiece F G i ≃ₗ[K] Dual K (quotientPiece F G j) := by
  let p := soclePairing F G e t i j he ht hF hG hF0 hcop hij
  letI : p.IsPerfPair := soclePairing_isPerfPair F G e t i j he ht hF hG hF0 hcop hij
  exact p.toPerfPair

#print axioms soclePairing_isPerfPair
#print axioms complementaryPieceEquivDual

end Cylinder.CompleteIntersectionPerfectPairing

end
