module

public import Cylinder.CompleteIntersectionSocle

/-! Every nonzero homogeneous complete-intersection class has a genuine
nonzero product in the one-dimensional socle degree. -/

@[expose] public section
noncomputable section

namespace Cylinder.CompleteIntersectionAdjoint

open MvPolynomial Module
open Cylinder.PlaneBinaryReduction Cylinder.CompleteIntersectionKoszul
open Cylinder.CompleteIntersectionSocle Cylinder.BinaryCompleteIntersectionGraded
open scoped Classical

variable {K : Type*} [Field K]

private theorem exists_top_product_aux (F G : BinaryRing K) (e t : ℕ)
    (hF : F.IsHomogeneous e) (hG : G.IsHomogeneous t)
    (hF0 : F ≠ 0) (hcop : IsRelPrime F G) (r : ℕ) :
    ∀ d : ℕ, d + r = e + t - 2 → ∀ P : BinaryRing K,
      P.IsHomogeneous d → P ∉ equationsIdeal F G →
      ∃ Q : BinaryRing K, Q.IsHomogeneous r ∧ P * Q ∉ equationsIdeal F G := by
  induction r with
  | zero =>
    intro d hd P hP hPn
    refine ⟨1, isHomogeneous_one _ _, ?_⟩
    simpa only [mul_one] using hPn
  | succ r ih =>
    intro d hd P hP hPn
    have hbelow : d < e + t - 2 := by omega
    have hnot : ¬(X (0 : Fin 2) * P ∈ equationsIdeal F G ∧
        X (1 : Fin 2) * P ∈ equationsIdeal F G) := by
      rintro ⟨hX, hY⟩
      exact hPn (homogeneous_socle_below F G e t d hF hG hF0 hcop P hP hbelow hX hY)
    obtain ⟨i, hi⟩ : ∃ i : Fin 2, X i * P ∉ equationsIdeal F G := by
      by_cases hX : X (0 : Fin 2) * P ∈ equationsIdeal F G
      · exact ⟨1, fun hY => hnot ⟨hX, hY⟩⟩
      · exact ⟨0, hX⟩
    have hXP : (X i * P).IsHomogeneous (d + 1) := by
      simpa [Nat.add_comm] using (isHomogeneous_X K i).mul hP
    obtain ⟨Q, hQ, hPQ⟩ := ih (d + 1) (by omega) (X i * P) hXP hi
    refine ⟨X i * Q, ?_, ?_⟩
    · simpa [Nat.add_comm] using (isHomogeneous_X K i).mul hQ
    · convert hPQ using 1 <;> ring

/-- The complementary factor is constructed by successive variable
multiplications; no nondegenerate-pairing hypothesis occurs. -/
theorem exists_top_product (F G : BinaryRing K) (e t d : ℕ)
    (hF : F.IsHomogeneous e) (hG : G.IsHomogeneous t)
    (hF0 : F ≠ 0) (hcop : IsRelPrime F G)
    (P : BinaryRing K) (hP : P.IsHomogeneous d) (hPn : P ∉ equationsIdeal F G)
    (hd : d ≤ e + t - 2) :
    ∃ Q : BinaryRing K, Q.IsHomogeneous (e + t - 2 - d) ∧
      P * Q ∉ equationsIdeal F G :=
  exists_top_product_aux F G e t hF hG hF0 hcop (e + t - 2 - d)
    d (by omega) P hP hPn

theorem quotientPiece_mul_mem (F G : BinaryRing K) (i j n : ℕ) (hij : i + j = n)
    (a : quotientPiece F G i) (b : quotientPiece F G j) :
    a.val * b.val ∈ quotientPiece F G n := by
  obtain ⟨P, hP⟩ := a.property
  obtain ⟨Q, hQ⟩ := b.property
  refine ⟨⟨P.val * Q.val, hij ▸ P.property.mul Q.property⟩, ?_⟩
  change Ideal.Quotient.mk (equationsIdeal F G) (P.val * Q.val) = a.val * b.val
  rw [map_mul]
  exact congrArg₂ (fun x y => x * y) hP hQ

def pieceMultiplication (F G : BinaryRing K) (i j n : ℕ) (hij : i + j = n) :
    quotientPiece F G i →ₗ[K] quotientPiece F G j →ₗ[K] quotientPiece F G n where
  toFun a :=
    { toFun := fun b => ⟨a.val * b.val, quotientPiece_mul_mem F G i j n hij a b⟩
      map_add' := by intro b c; apply Subtype.ext; exact mul_add _ _ _
      map_smul' := by intro k b; apply Subtype.ext; exact mul_smul_comm _ _ _ }
  map_add' := by intro a b; ext c; exact add_mul _ _ _
  map_smul' := by intro k a; ext b; exact smul_mul_assoc _ _ _

theorem pieceMultiplication_separates (F G : BinaryRing K) (e t i j : ℕ)
    (hF : F.IsHomogeneous e) (hG : G.IsHomogeneous t)
    (hF0 : F ≠ 0) (hcop : IsRelPrime F G) (hij : i + j = e + t - 2)
    (a : quotientPiece F G i) (ha : a ≠ 0) :
    ∃ b : quotientPiece F G j,
      pieceMultiplication F G i j (e + t - 2) hij a b ≠ 0 := by
  obtain ⟨P, hP⟩ := a.property
  have hPn : P.val ∉ equationsIdeal F G := by
    intro hPI
    have hzero : a.val = 0 := hP.symm.trans (Ideal.Quotient.eq_zero_iff_mem.mpr hPI)
    exact ha (Subtype.ext hzero)
  obtain ⟨Q, hQ, hPQ⟩ := exists_top_product F G e t i hF hG hF0 hcop P.val P.property hPn
    (by omega)
  have hj : e + t - 2 - i = j := by omega
  let Qh : BinaryForms K j := ⟨Q, hj ▸ hQ⟩
  let b : quotientPiece F G j := ⟨quotientPieceMap F G j Qh, ⟨Qh, rfl⟩⟩
  refine ⟨b, ?_⟩
  intro hz
  apply hPQ
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  have hzero := congrArg Subtype.val hz
  change a.val * Ideal.Quotient.mk (equationsIdeal F G) Q = 0 at hzero
  change Ideal.Quotient.mk (equationsIdeal F G) P.val = a.val at hP
  rw [map_mul, hP]
  exact hzero

#print axioms exists_top_product
#print axioms pieceMultiplication_separates

end Cylinder.CompleteIntersectionAdjoint

end

