module

public import Cylinder.LineAffineCoordinates
public import Cylinder.LinearEvaluationTransport
public import Mathlib.Algebra.MvPolynomial.Funext

/-! Actual collinear bijections indexed by a finite set on one line become
the projection matchings of the proved moment argument. The resulting
nonzero conic is pulled back to the original projective coordinates. -/

@[expose] public section
noncomputable section
open scoped Classical

namespace Cylinder.BMMBlackLineConic

open MvPolynomial Cylinder.RationalPlaneLine Cylinder.PlaneCrossProduct Cylinder.BMMArcGeometry
open Cylinder.LineAffineCoordinates Cylinder.ThreeNetFullSupportRelations
open Cylinder.LinearEvaluationTransport Cylinder.HilbertEvaluation

variable {K : Type*} [Field K]

theorem eq_of_affine_vectors_proportional (g : (Fin 3 → K) ≃ₗ[K] (Fin 3 → K))
    (P Q : PlanePoint K) (hP : g P.rep 0 ≠ 0) (hQ : g Q.rep 0 ≠ 0)
    (c : K) (heq : affineVector (affineCoordinates g Q) = c • affineVector (affineCoordinates g P)) :
    P = Q := by
  have hzero := congrFun heq (0 : Fin 3)
  have hc : c = 1 := by
    simpa only [affineVector, Matrix.cons_val_zero, Pi.smul_apply, smul_eq_mul, mul_one] using hzero.symm
  have hv : (g Q.rep 0)⁻¹ • g Q.rep = (g P.rep 0)⁻¹ • g P.rep := by
    rw [← normalized_affine_vector g Q hQ, ← normalized_affine_vector g P hP]
    simpa only [hc, one_smul] using heq
  have hs := congrArg (fun x : Fin 3 → K => g Q.rep 0 • x) hv
  simp only [smul_smul, mul_inv_cancel₀ hQ, one_smul] at hs
  have hrep : (g Q.rep 0 * (g P.rep 0)⁻¹) • P.rep = Q.rep := by
    apply g.injective
    rw [map_smul]
    exact hs.symm
  have hpq := (Projectivization.mk_eq_mk_iff' K Q.rep P.rep Q.rep_nonzero P.rep_nonzero).mpr
    ⟨g Q.rep 0 * (g P.rep 0)⁻¹, hrep⟩
  simpa only [Projectivization.mk_rep] using hpq.symm

def familyPoint (X Y : Finset (PlanePoint K)) : X ⊕ Y → PlanePoint K :=
  Sum.elim (fun P => P.val) (fun Q => Q.val)

theorem familyPoint_injective (X Y : Finset (PlanePoint K)) (hdisj : Disjoint X Y) :
    Function.Injective (familyPoint X Y) := by
  intro i j hij
  cases i with
  | inl P =>
    cases j with
    | inl Q => exact congrArg Sum.inl (Subtype.ext hij)
    | inr Q =>
      change P.val = Q.val at hij
      exact False.elim (Finset.disjoint_left.mp hdisj P.property (hij.symm ▸ Q.property))
  | inr P =>
    cases j with
    | inl Q =>
      change P.val = Q.val at hij
      exact False.elim (Finset.disjoint_left.mp hdisj Q.property (hij ▸ P.property))
    | inr Q => exact congrArg Sum.inr (Subtype.ext hij)

theorem affine_representatives_distinct (g : (Fin 3 → K) ≃ₗ[K] (Fin 3 → K))
    (X Y : Finset (PlanePoint K)) (hdisj : Disjoint X Y)
    (hX : ∀ P ∈ X, g P.rep 0 ≠ 0) (hY : ∀ Q ∈ Y, g Q.rep 0 ≠ 0) :
    ProjectivelyDistinct (representatives (fun P : X => affineCoordinates g P.val)
      (fun Q : Y => affineCoordinates g Q.val)) := by
  have hnon : ∀ i : X ⊕ Y, g (familyPoint X Y i).rep 0 ≠ 0 := by
    intro i
    cases i with
    | inl P => exact hX P.val P.property
    | inr Q => exact hY Q.val Q.property
  intro i j hij c heq
  apply hij
  apply familyPoint_injective X Y hdisj
  apply eq_of_affine_vectors_proportional g (familyPoint X Y i) (familyPoint X Y j)
    (hnon i) (hnon j) c
  cases i <;> cases j <;> exact heq

theorem infinite_pullback_nonzero [Infinite K] (g : (Fin 3 → K) ≃ₗ[K] (Fin 3 → K))
    (Q : MvPolynomial (Fin 3) K) (hQ : Q ≠ 0) : linearPullback g Q ≠ 0 := by
  intro hz
  apply hQ
  apply MvPolynomial.funext
  intro x
  have heval := congrArg (eval (g.symm x)) hz
  simpa only [linearPullback_eval, LinearEquiv.apply_symm_apply, map_zero] using heval

theorem vanishing_at_affine_vector_implies_pullback_zero
    (g : (Fin 3 → K) ≃ₗ[K] (Fin 3 → K)) (Q : MvPolynomial (Fin 3) K)
    (hQ : Q.IsHomogeneous 2) (P : PlanePoint K) (hP : g P.rep 0 ≠ 0)
    (hzero : eval (affineVector (affineCoordinates g P)) Q = 0) :
    eval P.rep (linearPullback g Q) = 0 := by
  rw [normalized_affine_vector g P hP, homogeneous_eval_smul Q 2 hQ] at hzero
  rw [linearPullback_eval]
  exact (mul_eq_zero.mp hzero).resolve_left (pow_ne_zero 2 (inv_ne_zero hP))

theorem conic_of_collinear_matchings [Infinite K] (p : ℕ) [Fact p.Prime] [CharP K p]
    (l : Fin 3 → K) (hl : l ≠ 0) (X Y C : Finset (PlanePoint K))
    (hdisj : Disjoint X Y) (hXcard : X.card = C.card) (hYcard : Y.card = C.card)
    (hCnon : C.Nonempty) (hCp : C.card ≤ p)
    (hXoff : ∀ P ∈ X, dot l P.rep ≠ 0) (hYoff : ∀ Q ∈ Y, dot l Q.rep ≠ 0)
    (hCline : ∀ R ∈ C, dot l R.rep = 0)
    (hmatch : ∀ R : C, ∃ e : X ≃ Y, ∀ P : X, Collinear P.val (e P).val R.val) :
    ∃ Q : MvPolynomial (Fin 3) K, Q.IsHomogeneous 2 ∧ Q ≠ 0 ∧ ∀ P ∈ X ∪ Y, eval P.rep Q = 0 := by
  obtain ⟨g, hgzero, hgone⟩ := exists_line_affine_coordinates l hl C hCline
  have hXzero : ∀ P ∈ X, g P.rep 0 ≠ 0 := fun P hP => by rw [hgzero]; exact hXoff P hP
  have hYzero : ∀ P ∈ Y, g P.rep 0 ≠ 0 := fun P hP => by rw [hgzero]; exact hYoff P hP
  have hCzero : ∀ R ∈ C, g R.rep 0 = 0 := fun R hR => (hgzero R.rep).trans (hCline R hR)
  let D : Finset K := Finset.univ.image (fun R : C => lineParameter g R.val)
  have hDcard : D.card = C.card := by
    dsimp only [D]
    rw [Finset.card_image_of_injective _ (lineParameter_injective g C hCzero hgone),
      Finset.card_univ, Fintype.card_coe]
  have hDnon : D.Nonempty := Finset.card_pos.mp (by
    rw [hDcard]
    exact Finset.card_pos.mpr hCnon)
  have hDp : D.card ≤ p := hDcard.trans_le hCp
  let a : X → Fin 2 → K := fun P => affineCoordinates g P.val
  let b : Y → Fin 2 → K := fun Q => affineCoordinates g Q.val
  have hsep : ProjectivelyDistinct (representatives a b) :=
    affine_representatives_distinct g X Y hdisj hXzero hYzero
  have hprojection : ∀ t ∈ D, ∃ e : X ≃ Y,
      ∀ P, t * a P 0 + a P 1 = t * b (e P) 0 + b (e P) 1 := by
    intro t ht
    obtain ⟨R, _hR, rfl⟩ := Finset.mem_image.mp ht
    obtain ⟨e, he⟩ := hmatch R
    refine ⟨e, fun P => ?_⟩
    have hPQ : P.val ≠ (e P).val := by
      intro h
      exact Finset.disjoint_left.mp hdisj P.property (h.symm ▸ (e P).property)
    exact collinear_projection_equal g P.val (e P).val R.val hPQ (he P)
      (hXzero P.val P.property) (hYzero (e P).val (e P).property)
      (hCzero R.val R.property) (hgone R.val R.property)
  have hcard : Fintype.card X + Fintype.card Y = 2 * D.card := by
    simp only [Fintype.card_coe, hXcard, hYcard, hDcard]
    omega
  obtain ⟨Q, hQ, hQ0, hQa, hQb⟩ := conic_of_projection_matchings p a b D hcard hDnon hDp hsep hprojection
  refine ⟨linearPullback g Q, linearPullback_homogeneous g Q 2 hQ,
    infinite_pullback_nonzero g Q hQ0, ?_⟩
  intro P hP
  rcases Finset.mem_union.mp hP with hPX | hPY
  · exact vanishing_at_affine_vector_implies_pullback_zero g Q hQ P (hXzero P hPX) (hQa ⟨P, hPX⟩)
  · exact vanishing_at_affine_vector_implies_pullback_zero g Q hQ P (hYzero P hPY) (hQb ⟨P, hPY⟩)

end Cylinder.BMMBlackLineConic

end
