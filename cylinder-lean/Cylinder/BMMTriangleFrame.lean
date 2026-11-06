module

public import Cylinder.BMMArcGeometry

/-! Actual coordinates based on three distinct white points of an arc.
The coordinate equivalence is given by explicit Cramer numerators. -/

@[expose] public section
noncomputable section
open scoped Classical BigOperators

namespace Cylinder.BMMTriangleFrame

open Cylinder.RationalPlaneLine Cylinder.PlaneCrossProduct Cylinder.BMMArcGeometry

variable {K : Type*} [Field K]

theorem white_triple_noncollinear (W : Finset (PlanePoint K)) (hW : LineCap W 2)
    (P Q R : PlanePoint K) (hP : P ∈ W) (hQ : Q ∈ W) (hR : R ∈ W)
    (hPQ : P ≠ Q) (hPR : P ≠ R) (hQR : Q ≠ R) : ¬Collinear P Q R := by
  intro hcol
  let c := cross P.rep Q.rep
  have hc : c ≠ 0 := cross_ne_zero P.rep Q.rep P.rep_nonzero
    (representatives_not_proportional P Q hPQ)
  have hsub : ({P, Q, R} : Finset (PlanePoint K)) ⊆ W.filter (fun X => dot c X.rep = 0) := by
    intro X hX
    rcases Finset.mem_insert.mp hX with hXP | hX
    · subst X
      exact Finset.mem_filter.mpr ⟨hP, dot_cross_left P.rep Q.rep⟩
    rcases Finset.mem_insert.mp hX with hXQ | hX
    · subst X
      exact Finset.mem_filter.mpr ⟨hQ, dot_cross_right P.rep Q.rep⟩
    have hx := Finset.mem_singleton.mp hX
    subst X
    exact Finset.mem_filter.mpr ⟨hR, hcol⟩
  have hcard : ({P, Q, R} : Finset (PlanePoint K)).card = 3 := by simp [hPQ, hPR, hQR]
  have hcount := Finset.card_le_card hsub
  rw [hcard] at hcount
  have hcap := hW c hc
  omega

def determinant (v : Fin 3 → Fin 3 → K) : K := dot (cross (v 0) (v 1)) (v 2)

def numerators (v : Fin 3 → Fin 3 → K) (x : Fin 3 → K) : Fin 3 → K :=
  ![dot (cross (v 1) (v 2)) x, dot (cross (v 2) (v 0)) x, dot (cross (v 0) (v 1)) x]

def synthesis (v : Fin 3 → Fin 3 → K) : (Fin 3 → K) →ₗ[K] (Fin 3 → K) where
  toFun c := ∑ i, c i • v i
  map_add' c d := by
    simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' a c := by
    simp only [Pi.smul_apply, smul_smul, Finset.smul_sum, smul_eq_mul, RingHom.id_apply]

def numeratorMap (v : Fin 3 → Fin 3 → K) : (Fin 3 → K) →ₗ[K] (Fin 3 → K) where
  toFun := numerators v
  map_add' x y := by
    funext i
    fin_cases i <;> simp [numerators, dot, Finset.mul_sum, mul_add, Finset.sum_add_distrib]
  map_smul' a x := by
    funext i
    fin_cases i <;> simp [numerators, dot, Finset.mul_sum, mul_left_comm, mul_assoc]

theorem numerator_synthesis (v : Fin 3 → Fin 3 → K) (c : Fin 3 → K) :
    numeratorMap v (synthesis v c) = determinant v • c := by
  funext i
  fin_cases i <;> simp [numeratorMap, numerators, synthesis, determinant, dot, cross,
    Fin.sum_univ_succ, Finset.sum_apply] <;> ring

theorem synthesis_numerator (v : Fin 3 → Fin 3 → K) (x : Fin 3 → K) :
    synthesis v (numeratorMap v x) = determinant v • x := by
  funext i
  fin_cases i <;> simp [numeratorMap, numerators, synthesis, determinant, dot, cross,
    Fin.sum_univ_succ, Finset.sum_apply] <;> ring

def coordinates (v : Fin 3 → Fin 3 → K) (hd : determinant v ≠ 0) :
    (Fin 3 → K) ≃ₗ[K] (Fin 3 → K) where
  toLinearMap := (determinant v)⁻¹ • numeratorMap v
  invFun := synthesis v
  left_inv x := by
    change synthesis v ((determinant v)⁻¹ • numeratorMap v x) = x
    rw [map_smul, synthesis_numerator, smul_smul, inv_mul_cancel₀ hd, one_smul]
  right_inv c := by
    change (determinant v)⁻¹ • numeratorMap v (synthesis v c) = c
    rw [numerator_synthesis, smul_smul, inv_mul_cancel₀ hd, one_smul]

theorem coordinates_apply (v : Fin 3 → Fin 3 → K) (hd : determinant v ≠ 0)
    (x : Fin 3 → K) (i : Fin 3) : coordinates v hd x i = (determinant v)⁻¹ * numerators v x i := rfl

theorem numerators_basis (v : Fin 3 → Fin 3 → K) (i : Fin 3) :
    numerators v (v i) = determinant v • (Pi.single i 1 : Fin 3 → K) := by
  funext j
  fin_cases i <;> fin_cases j <;> simp [numerators, determinant, dot, cross,
    Fin.sum_univ_succ, Pi.single_apply] <;> ring

theorem coordinates_basis (v : Fin 3 → Fin 3 → K) (hd : determinant v ≠ 0) (i : Fin 3) :
    coordinates v hd (v i) = (Pi.single i 1 : Fin 3 → K) := by
  change (determinant v)⁻¹ • numerators v (v i) = _
  rw [numerators_basis, smul_smul, inv_mul_cancel₀ hd, one_smul]

theorem white_frame_determinant_ne_zero (W : Finset (PlanePoint K)) (hW : LineCap W 2)
    (P : Fin 3 → PlanePoint K) (hP : ∀ i, P i ∈ W) (hinj : Function.Injective P) :
    determinant (fun i => (P i).rep) ≠ 0 :=
  white_triple_noncollinear W hW (P 0) (P 1) (P 2) (hP 0) (hP 1) (hP 2)
    (fun h => (by decide : (0 : Fin 3) ≠ 1) (hinj h))
    (fun h => (by decide : (0 : Fin 3) ≠ 2) (hinj h))
    (fun h => (by decide : (1 : Fin 3) ≠ 2) (hinj h))

theorem white_off_triangle_coordinates_nonzero (W : Finset (PlanePoint K)) (hW : LineCap W 2)
    (P : Fin 3 → PlanePoint K) (hP : ∀ i, P i ∈ W) (hinj : Function.Injective P)
    (R : PlanePoint K) (hR : R ∈ W) (hRP : ∀ i, R ≠ P i) :
    ∀ i, coordinates (fun j => (P j).rep) (white_frame_determinant_ne_zero W hW P hP hinj) R.rep i ≠ 0 := by
  intro i
  rw [coordinates_apply]
  apply mul_ne_zero (inv_ne_zero (white_frame_determinant_ne_zero W hW P hP hinj))
  fin_cases i
  · exact white_triple_noncollinear W hW (P 1) (P 2) R (hP 1) (hP 2) hR
      (fun h => (by decide : (1 : Fin 3) ≠ 2) (hinj h)) (hRP 1).symm (hRP 2).symm
  · exact white_triple_noncollinear W hW (P 2) (P 0) R (hP 2) (hP 0) hR
      (fun h => (by decide : (2 : Fin 3) ≠ 0) (hinj h)) (hRP 2).symm (hRP 0).symm
  · exact white_triple_noncollinear W hW (P 0) (P 1) R (hP 0) (hP 1) hR
      (fun h => (by decide : (0 : Fin 3) ≠ 1) (hinj h)) (hRP 0).symm (hRP 1).symm

end Cylinder.BMMTriangleFrame

end
