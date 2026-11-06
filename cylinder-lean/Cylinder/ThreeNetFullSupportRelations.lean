module

public import Cylinder.ThreeNetMomentPolynomials
public import Cylinder.ThreeNetConicSupport

/-! Projection matchings give an actual full-support homogeneous evaluation
relation on the two affine point families, and hence a genuine conic. -/

@[expose] public section
noncomputable section
open scoped Classical BigOperators

namespace Cylinder.ThreeNetFullSupportRelations

open MvPolynomial Cylinder.HilbertEvaluation Cylinder.PowerEvaluationRelation
open Cylinder.ThreeNetMomentPolynomials

variable {K I J : Type*} [Field K] [Fintype I] [Fintype J]

def affineVector (a : Fin 2 → K) : Fin 3 → K := ![1, a 0, a 1]

def representatives (a : I → Fin 2 → K) (b : J → Fin 2 → K) : I ⊕ J → Fin 3 → K :=
  Sum.elim (fun i => affineVector (a i)) (fun j => affineVector (b j))

def coefficients : I ⊕ J → K := Sum.elim (fun _ => 1) (fun _ => -1)

omit [Fintype I] [Fintype J] in
theorem coefficients_nonzero : ∀ x : I ⊕ J, coefficients (K := K) x ≠ 0 := by
  intro x
  cases x <;> simp [coefficients]

omit [Fintype I] [Fintype J] in
theorem representatives_nonzero (a : I → Fin 2 → K) (b : J → Fin 2 → K) :
    ∀ x, representatives a b x ≠ 0 := by
  intro x hz
  have hzero := congrFun hz (0 : Fin 3)
  cases x <;> apply one_ne_zero (α := K) <;> simpa only [representatives, Sum.elim_inl, Sum.elim_inr,
    affineVector, Matrix.cons_val_zero, Pi.zero_apply] using hzero

theorem monomial_value (a : Fin 2 → K) (m : Fin 3 →₀ ℕ) :
    m.prod (fun j n => affineVector a j ^ n) = a 0 ^ m 1 * a 1 ^ m 2 := by
  rw [m.prod_fintype _ (fun _ => pow_zero _)]
  simp [affineVector, Fin.prod_univ_succ]

theorem homogeneous_evaluation_sums_equal (p : ℕ) [Fact p.Prime] [CharP K p]
    (a : I → Fin 2 → K) (b : J → Fin 2 → K) (D : Finset K) (hDp : D.card ≤ p)
    (hmatch : ∀ t ∈ D, ∃ e : I ≃ J,
      ∀ i, t * a i 0 + a i 1 = t * b (e i) 0 + b (e i) 1)
    (d : ℕ) (hd : d < D.card) (F : MvPolynomial (Fin 3) K) (hF : F.IsHomogeneous d) :
    (∑ i, eval (affineVector (a i)) F) = ∑ j, eval (affineVector (b j)) F := by
  have hmon : ∀ m ∈ F.support,
      (∑ i, m.prod (fun j n => affineVector (a i) j ^ n)) =
        ∑ i, m.prod (fun j n => affineVector (b i) j ^ n) := by
    intro m hm
    have hsum : m.sum (fun _ n => n) = d := by
      simpa only [Finsupp.sum] using (hF.degree_eq_sum_deg_support hm).symm
    have hdegree : m 0 + m 1 + m 2 = d := by
      rw [m.sum_fintype _ (fun _ => rfl)] at hsum
      simpa [Fin.sum_univ_succ, add_assoc] using hsum
    simp_rw [monomial_value]
    exact mixed_moments_equal p a b D hDp hmatch (m 1) (m 2) (by omega)
  have heval (v : Fin 3 → K) : eval v F =
      ∑ m ∈ F.support, F.coeff m * m.prod (fun j n => v j ^ n) := by
    calc
      eval v F = eval v (∑ m ∈ F.support, monomial m (F.coeff m)) := congrArg (eval v) F.as_sum
      _ = _ := by simp only [map_sum, eval_monomial]
  calc
    _ = ∑ m ∈ F.support, F.coeff m * ∑ i, m.prod (fun j n => affineVector (a i) j ^ n) := by
      simp only [heval, Finset.mul_sum]
      exact Finset.sum_comm
    _ = ∑ m ∈ F.support, F.coeff m * ∑ i, m.prod (fun j n => affineVector (b i) j ^ n) :=
      Finset.sum_congr rfl (fun m hm => congrArg (F.coeff m * ·) (hmon m hm))
    _ = _ := by
      simp only [heval, Finset.mul_sum]
      exact Finset.sum_comm

theorem full_support_relation (p : ℕ) [Fact p.Prime] [CharP K p]
    (a : I → Fin 2 → K) (b : J → Fin 2 → K) (D : Finset K) (hDp : D.card ≤ p)
    (hmatch : ∀ t ∈ D, ∃ e : I ≃ J,
      ∀ i, t * a i 0 + a i 1 = t * b (e i) 0 + b (e i) 1)
    (d : ℕ) (hd : d < D.card) :
    Relation (representatives a b) coefficients d := by
  intro F hF
  have hs := homogeneous_evaluation_sums_equal p a b D hDp hmatch d hd F hF
  simpa only [Fintype.sum_sum_type, representatives, coefficients, Sum.elim_inl,
    Sum.elim_inr, one_mul, neg_one_mul, Finset.sum_neg_distrib, add_neg_eq_zero] using hs

theorem conic_of_projection_matchings [Infinite K] (p : ℕ) [Fact p.Prime] [CharP K p]
    (a : I → Fin 2 → K) (b : J → Fin 2 → K) (D : Finset K)
    (hcard : Fintype.card I + Fintype.card J = 2 * D.card) (hDnon : D.Nonempty)
    (hDp : D.card ≤ p) (hsep : ProjectivelyDistinct (representatives a b))
    (hmatch : ∀ t ∈ D, ∃ e : I ≃ J,
      ∀ i, t * a i 0 + a i 1 = t * b (e i) 0 + b (e i) 1) :
    ∃ Q : PlaneRing K, Q.IsHomogeneous 2 ∧ Q ≠ 0 ∧
      (∀ i, eval (affineVector (a i)) Q = 0) ∧ ∀ j, eval (affineVector (b j)) Q = 0 := by
  obtain ⟨Q, hQ, hQ0, hvan⟩ := ThreeNetConicSupport.conic_of_full_support_relation
    (representatives a b) (representatives_nonzero a b) hsep D.card
    (by simpa only [Fintype.card_sum] using hcard) coefficients coefficients_nonzero
    (full_support_relation p a b D hDp hmatch (D.card - 1)
      (by have hpos := Finset.card_pos.mpr hDnon; omega))
  exact ⟨Q, hQ, hQ0, fun i => hvan (Sum.inl i), fun j => hvan (Sum.inr j)⟩

end Cylinder.ThreeNetFullSupportRelations

end
