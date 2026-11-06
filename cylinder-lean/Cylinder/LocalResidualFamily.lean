module

public import Cylinder.LocalResidualCross

/-! The full family of actual residual representatives, including their
nonzero initial term and cross identities, is constructed from duality. -/

@[expose] public section
noncomputable section
open scoped Classical

namespace Cylinder.LocalResidualFamily
open Module MvPolynomial Cylinder.HilbertEvaluation Cylinder.ProjectiveChartData
open Cylinder.ProjectivePointIdealTransport Cylinder.ProjectiveIntegerRelations
open Cylinder.ProjectiveCompleteIntersectionDuality Cylinder.LocalResidualRepresentatives
open Cylinder.ResidualCoordinateTransport Cylinder.LocalResidualCross

variable {K : Type*} [Field K]

theorem exists_residual_family (c : Chart K) (F G : PlaneRing K) (e t d β M : ℕ)
    (he : 0 < e) (ht : 0 < t) (hF : F.IsHomogeneous e) (hG : G.IsHomogeneous t)
    (hgood : GoodChart c F G e t) (D : Finset (PlanePointModel.Plane K)) [Nonempty D]
    (hpoints : ∀ P : D, eval P.val.rep F = 0 ∧ eval P.val.rep G = 0)
    (hdegree : (e : ℤ) + t - 3 - d = β) (hMd : M ≤ d)
    (u : D → K) (hu : ∀ P, u P ≠ 0) (μ : ℕ → D → K) (hμ0 : μ 0 = u)
    (hrel : ∀ q ≤ M, PowerEvaluationRelation.Relation (fun P : D => c.normalizedPoint P.val) (μ q) (d - q)) :
    ∃ Q : ℕ → PlaneRing K,
      (∀ q ≤ M, (Q q).IsHomogeneous (β + q)) ∧
      (∀ q ≤ M, Q q ∈ ResidualIdeal F G D) ∧ Q 0 ≠ 0 ∧
      ∀ q ≤ M, ∀ P : D,
        eval (c.normalizedPoint P.val) (Q 0) * μ q P =
          eval (c.normalizedPoint P.val) (Q q) * u P := by
  let a (q : ℕ) (hq : q ≤ M) : originalRelations c D ((d : ℤ) - q) :=
    ⟨μ q, by
      have hcast : (d : ℤ) - q = (d - q : ℕ) := by omega
      rw [hcast]
      simp only [originalRelations, Int.natCast_nonneg, ite_true, Int.toNat_natCast]
      exact (PlaneRelationSpaces.mem_relationSpace _ _ _).mpr (hrel q hq)⟩
  let E (q : ℕ) := projectiveRelationResidualEquiv c F G e t he ht hF hG hgood D hpoints ((d : ℤ) - q)
  have hex (q : ℕ) (hq : q ≤ M) :
      ∃ R : residualPiece (CompleteIntersectionKoszul.equationsIdeal F G) (originalPointIdeal D)
        (integerPlaneForms K) ((e : ℤ) + t - 3 - ((d : ℤ) - q)),
          Submodule.Quotient.mk R = E q (a q hq) :=
    Submodule.Quotient.mk_surjective _ (E q (a q hq))
  let R (q : ℕ) (hq : q ≤ M) := (hex q hq).choose
  have hclass (q : ℕ) (hq : q ≤ M) : E q (a q hq) = Submodule.Quotient.mk (R q hq) :=
    (hex q hq).choose_spec.symm
  have hhom (q : ℕ) (hq : q ≤ M) : (R q hq).val.IsHomogeneous (β + q) := by
    have hmem := (R q hq).property.2
    have hn : (e : ℤ) + t - 3 - ((d : ℤ) - q) = (β + q : ℕ) := by omega
    have hnonneg : 0 ≤ (e : ℤ) + t - 3 - ((d : ℤ) - q) := by omega
    have hh : (R q hq).val.IsHomogeneous ((e : ℤ) + t - 3 - ((d : ℤ) - q)).toNat := by
      have hhmem : (R q hq).val ∈ HilbertEvaluation.Forms K
          ((e : ℤ) + t - 3 - ((d : ℤ) - q)).toNat := by
        change (R q hq).val ∈ integerPlaneForms K ((e : ℤ) + t - 3 - ((d : ℤ) - q)) at hmem
        rw [integerPlaneForms, if_pos hnonneg] at hmem
        exact hmem
      exact (mem_homogeneousSubmodule _ _).mp hhmem
    convert hh using 1
    omega
  let Q (q : ℕ) : PlaneRing K := if hq : q ≤ M then (R q hq).val else 0
  have hQhom : ∀ q ≤ M, (Q q).IsHomogeneous (β + q) := by
    intro q hq
    simpa only [Q, dif_pos hq] using hhom q hq
  have hQmem : ∀ q ≤ M, Q q ∈ ResidualIdeal F G D := by
    intro q hq
    simp only [Q, dif_pos hq]
    exact (R q hq).property.1
  have hQ0 : Q 0 ≠ 0 := by
    intro hz
    have hR0 : R 0 (by omega) = 0 := by
      apply Subtype.ext
      change (R 0 (by omega)).val = (0 : PlaneRing K)
      simpa only [Q, dif_pos (show 0 ≤ M by omega)] using hz
    have hE0 := hclass 0 (by omega)
    rw [hR0] at hE0
    have ha0 : a 0 (by omega) = 0 := E 0 |>.injective (by simpa using hE0)
    have hμzero : μ 0 = 0 := congrArg Subtype.val ha0
    obtain ⟨P⟩ := ‹Nonempty D›
    exact hu P (by simpa only [← hμ0, Pi.zero_apply] using congrFun hμzero P)
  refine ⟨Q, hQhom, hQmem, hQ0, ?_⟩
  intro q hq P
  have hh := cross_of_residual_representatives c F G e t he ht hF hG hgood D hpoints
    ((d : ℤ) - 0) ((d : ℤ) - q) β (β + q) (by omega)
    (a 0 (by omega)) (a q hq) (R 0 (by omega)) (R q hq)
    (by simpa only [Nat.add_zero] using hhom 0 (by omega)) (hhom q hq)
    (hclass 0 (by omega)) (hclass q hq) P
  simpa only [a, Q, dif_pos (show 0 ≤ M by omega), dif_pos hq, hμ0] using hh

#print axioms exists_residual_family

end Cylinder.LocalResidualFamily
end
