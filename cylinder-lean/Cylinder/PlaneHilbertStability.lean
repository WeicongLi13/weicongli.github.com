module

public import Cylinder.PlaneBinaryReduction

/-! A zero actual Hilbert first difference forces all higher first differences
to vanish. The proof uses true binary-ideal growth and actual interpolation. -/

@[expose] public section
noncomputable section
namespace Cylinder.PlaneHilbertStability
open Module
open Cylinder.HilbertEvaluation Cylinder.PlaneNumericalCharacter Cylinder.PlaneBinaryReduction
variable {K I : Type*} [Field K] [Fintype I]

omit [Fintype I] in
theorem equal_succ_propagates (v : I → Fin 3 → K) (a b : K)
    (hLv : ∀ i, MvPolynomial.eval (v i) (graphEquation a b) ≠ 0) (d : ℕ)
    (heq : hilbert v (d + 1) = hilbert v d) :
    hilbert v (d + 2) = hilbert v (d + 1) := by
  have hdim := artinComponent_add_binaryIdealPiece v a b d
  have hart := artinComponent_rank_add v (graphEquation a b) (graphEquation_homogeneous a b) hLv d
  have hr : finrank K (binaryIdealPiece v a b (d + 1)) = d + 2 := by omega
  have hne : binaryIdealPiece v a b (d + 1) ≠ ⊥ := by
    intro hz
    rw [hz, finrank_bot] at hr
    omega
  have hg := binaryIdealPiece_growth v a b (d + 1) hne
  have hdim' := artinComponent_add_binaryIdealPiece v a b (d + 1)
  have hart' := artinComponent_rank_add v (graphEquation a b) (graphEquation_homogeneous a b) hLv (d + 1)
  have hn : d + 1 + 1 = d + 2 := by omega
  rw [hn] at hg hdim' hart'
  omega

theorem hilbert_eq_card_of_equal_succ [Infinite K] (v : I → Fin 3 → K)
    (hv : ∀ i, v i ≠ 0) (hsep : ProjectivelyDistinct v) (d : ℕ)
    (heq : hilbert v (d + 1) = hilbert v d) :
    ∀ w, d ≤ w → hilbert v w = Fintype.card I := by
  obtain ⟨a, b, hLv⟩ := exists_graph_avoiding v hv
  have hstep : ∀ n, hilbert v (d + n + 1) = hilbert v (d + n) := by
    intro n
    induction n with
    | zero => simpa using heq
    | succ n ih =>
      have h := equal_succ_propagates v a b hLv (d + n) ih
      simpa only [Nat.succ_eq_add_one, Nat.add_assoc] using h
  have htail : ∀ n, hilbert v (d + n) = hilbert v d := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      simpa only [Nat.succ_eq_add_one, ← Nat.add_assoc] using (hstep n).trans ih
  have hcard : hilbert v d = Fintype.card I := by
    rw [← htail (Fintype.card I)]
    exact hilbert_eq_card_of_card_sub_one_le v hv hsep _ (by omega)
  intro w hw
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hw
  exact (htail n).trans hcard

end Cylinder.PlaneHilbertStability
end
