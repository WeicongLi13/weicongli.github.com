module

public import Cylinder.GcdPlaneLine

/-!
# Simultaneous actual line selection

An actual finite collection of coprime homogeneous pairs has a single line
on which every pair remains coprime. The line simultaneously avoids any
specified finite set of nonzero projective representatives.
-/

@[expose] public section
noncomputable section
namespace Cylinder.SimultaneousPlaneLine
open scoped Classical BigOperators
open MvPolynomial
open Cylinder.HilbertEvaluation Cylinder.GenericPlaneLine Cylinder.BinaryHomogenization
variable {K : Type*} [Field K]

/-- A genuine resultant polynomial certifies every good pencil parameter. -/
theorem coprime_pencil_certificate
    (F G : PlaneRing K) (m n : ℕ) (hF : F.IsHomogeneous m) (hG : G.IsHomogeneous n)
    (hinf : eval (Fin.cons 1 0) F ≠ 0) (hfg : IsRelPrime F G) :
    ∃ A : MvPolynomial (Fin 2) K, A ≠ 0 ∧
      ∀ w : Fin 2 → K, eval w A ≠ 0 → IsRelPrime (pencilRestriction w F) (pencilRestriction w G) := by
  let f := MvPolynomial.finSuccEquiv K 2 F
  let g := MvPolynomial.finSuccEquiv K 2 G
  let c := eval (Fin.cons 1 0) F
  let f' := Polynomial.C (MvPolynomial.C c⁻¹) * f
  have hf' : f'.Monic := by
    apply Polynomial.monic_of_natDegree_le_of_coeff_eq_one m
    · exact (Polynomial.natDegree_C_mul_le _ _).trans (nested_natDegree_le F m hF)
    · change (Polynomial.C (MvPolynomial.C c⁻¹) * f).coeff m = 1
      rw [Polynomial.coeff_C_mul, nested_top_coefficient F m hF, ← MvPolynomial.C_mul]
      simp only [c, inv_mul_cancel₀ hinf, MvPolynomial.C_1]
  have hfg' : IsRelPrime f' g := by
    have hnested := relPrime_ringEquiv (MvPolynomial.finSuccEquiv K 2).toRingEquiv hfg
    have hu : IsUnit (Polynomial.C (MvPolynomial.C c⁻¹ : MvPolynomial (Fin 2) K)) := by
      apply IsUnit.map Polynomial.C
      apply IsUnit.map MvPolynomial.C
      exact (inv_ne_zero hinf).isUnit
    exact (associated_unit_mul_left f (Polynomial.C (MvPolynomial.C c⁻¹)) hu).symm.isRelPrime_left hnested
  refine ⟨f'.resultant g, resultant_ne_zero_of_monic
    (FractionRing (MvPolynomial (Fin 2) K)) hf' hfg', ?_⟩
  intro w hw
  have hc := specialization_coprime hf' (eval w) hw
  have hcop : IsCoprime (f.map (eval w)) (g.map (eval w)) := by
    change IsCoprime ((Polynomial.C (MvPolynomial.C c⁻¹) * f).map (eval w)) _ at hc
    rw [Polynomial.map_mul, Polynomial.map_C, MvPolynomial.eval_C] at hc
    exact (isCoprime_mul_unit_left_left (Polynomial.isUnit_C.mpr (inv_ne_zero hinf).isUnit) _ _).mp hc
  apply binary_relPrime_of_dehomogenize_coprime _ _ m n
    (pencilRestriction_homogeneous w F m hF) (pencilRestriction_homogeneous w G n hG)
  · rwa [pencil_eval_infinity]
  · simpa only [pencil_dehomogenize] using hcop

/-- A nonzero linear polynomial vanishing at a prescribed representative. -/
def pointAvoidPolynomial (v : Fin 3 → K) : PlaneRing K :=
  if v 0 = 0 then X 0 else C (v 0) * X 1 - C (v 1) * X 0

theorem pointAvoidPolynomial_ne_zero (v : Fin 3 → K) : pointAvoidPolynomial v ≠ 0 := by
  by_cases hv : v 0 = 0
  · simp [pointAvoidPolynomial, hv]
  · intro hz
    have he := congrArg (eval ![0, 1, 0]) hz
    simp [pointAvoidPolynomial, hv] at he

/-- The last two coordinates of a representative in the triangular chart. -/
def transverseCoordinates (p v : Fin 3 → K) : Fin 2 → K :=
  ![v 1 - p 1 * (p 0)⁻¹ * v 0, v 2 - p 2 * (p 0)⁻¹ * v 0]

theorem transverseCoordinates_ne_zero (p v : Fin 3 → K)
    (hp : p 0 ≠ 0) (hv : v ≠ 0) (havoid : eval p (pointAvoidPolynomial v) ≠ 0) :
    transverseCoordinates p v ≠ 0 := by
  intro hz
  have h1 := congrFun hz (0 : Fin 2)
  have h2 := congrFun hz (1 : Fin 2)
  simp only [transverseCoordinates, Matrix.cons_val_zero, Matrix.cons_val_one, Pi.zero_apply] at h1 h2
  by_cases hv0 : v 0 = 0
  · apply hv
    have hv1 : v 1 = 0 := by simpa [hv0] using h1
    have hv2 : v 2 = 0 := by simpa [hv0] using h2
    funext i
    fin_cases i <;> simp [hv0, hv1, hv2]
  · apply havoid
    simp only [pointAvoidPolynomial, ite_eq_right hv0, map_sub, map_mul, eval_C, eval_X]
    have he1 : v 1 = p 1 * (p 0)⁻¹ * v 0 := sub_eq_zero.mp h1
    rw [he1]
    field_simp [hp]
    ring

def lineParameterPolynomial (u : Fin 2 → K) : MvPolynomial (Fin 2) K :=
  C (u 0) * X 1 - C (u 1) * X 0

theorem lineParameterPolynomial_ne_zero (u : Fin 2 → K) (hu : u ≠ 0) : lineParameterPolynomial u ≠ 0 := by
  intro hz
  have h0 := congrArg (eval ![0, 1]) hz
  have h1 := congrArg (eval ![1, 0]) hz
  simp only [lineParameterPolynomial, map_sub, map_mul, eval_C, eval_X,
    Matrix.cons_val_zero, Matrix.cons_val_one, mul_one, mul_zero, sub_zero, zero_sub, map_zero] at h0 h1
  apply hu
  funext i
  fin_cases i
  · exact h0
  · exact neg_eq_zero.mp h1

/-- The actual linear equation of the selected line in the original coordinates. -/
def lineEquation (p : Fin 3 → K) (w : Fin 2 → K) : PlaneRing K :=
  C (w 1) * (X 1 - C (p 1 * (p 0)⁻¹) * X 0) -
    C (w 0) * (X 2 - C (p 2 * (p 0)⁻¹) * X 0)

theorem lineEquation_homogeneous (p : Fin 3 → K) (w : Fin 2 → K) :
    (lineEquation p w).IsHomogeneous 1 := by
  exact ((isHomogeneous_X K 1).sub ((isHomogeneous_X K 0).C_mul _)).C_mul _ |>.sub
    (((isHomogeneous_X K 2).sub ((isHomogeneous_X K 0).C_mul _)).C_mul _)

theorem lineEquation_ne_zero (p : Fin 3 → K) (w : Fin 2 → K) (hw : w 0 ≠ 0) :
    lineEquation p w ≠ 0 := by
  intro hz
  have h := congrArg (eval ![0, 0, 1]) hz
  apply hw
  simpa [lineEquation] using h

theorem lineEquation_eval (p v : Fin 3 → K) (w : Fin 2 → K) :
    eval v (lineEquation p w) = eval w (lineParameterPolynomial (transverseCoordinates p v)) := by
  simp [lineEquation, lineParameterPolynomial, transverseCoordinates]
  ring

theorem lineEquation_restriction (p : Fin 3 → K) (w : Fin 2 → K) (hp : p 0 ≠ 0) :
    lineRestriction p w (lineEquation p w) = 0 := by
  have h0 : lineRestriction p w (X 0) = C (p 0) * X 0 := by
    change pencilRestriction w (triangularMap p (X 0)) = _
    rw [triangularMap_X_zero, map_mul, pencilRestriction_C, pencilRestriction_X]
    rfl
  have h1 : lineRestriction p w (X 1) = C (w 0) * X 1 + C (p 1) * X 0 := by
    change pencilRestriction w (triangularMap p (X 1)) = _
    rw [triangularMap_X_one, map_add, map_mul, pencilRestriction_C, pencilRestriction_X, pencilRestriction_X]
    rfl
  have h2 : lineRestriction p w (X 2) = C (w 1) * X 1 + C (p 2) * X 0 := by
    change pencilRestriction w (triangularMap p (X 2)) = _
    rw [triangularMap_X_two, map_add, map_mul, pencilRestriction_C, pencilRestriction_X, pencilRestriction_X]
    rfl
  have hC (c : K) : lineRestriction p w (C c) = C c := (lineRestriction p w).commutes c
  simp only [lineEquation, map_sub (lineRestriction p w), map_mul (lineRestriction p w), hC, h0, h1, h2]
  have hs (a : K) : (C (a * (p 0)⁻¹) : MvPolynomial (Fin 2) K) * C (p 0) = C a := by
    rw [← C_mul, mul_assoc, inv_mul_cancel₀ hp, mul_one]
  simp only [← mul_assoc, hs]
  ring

/-- A single actual line preserves every coprime pair and avoids every given
projective representative. The nonzero determinant also permits graph coordinates. -/
theorem exists_simultaneous_line [Infinite K] {J T : Type*} [Fintype J] [Fintype T]
    (F G : J → PlaneRing K) (m n : J → ℕ)
    (hF : ∀ j, (F j).IsHomogeneous (m j)) (hG : ∀ j, (G j).IsHomogeneous (n j))
    (hF0 : ∀ j, F j ≠ 0) (hcop : ∀ j, IsRelPrime (F j) (G j))
    (v : T → Fin 3 → K) (hv : ∀ i, v i ≠ 0)
    (B : PlaneRing K) (hB : B ≠ 0) :
    ∃ p : Fin 3 → K, ∃ w : Fin 2 → K,
      p 0 ≠ 0 ∧ p 2 ≠ 0 ∧ w 0 ≠ 0 ∧ p 1 * w 1 - p 2 * w 0 ≠ 0 ∧
        eval p B ≠ 0 ∧
        (∀ j, IsRelPrime (lineRestriction p w (F j)) (lineRestriction p w (G j))) ∧
        ∀ i, eval (v i) (lineEquation p w) ≠ 0 := by
  classical
  let P := (∏ j, F j) * (∏ i, pointAvoidPolynomial (v i)) * B * X (0 : Fin 3) * X 2
  have hP0 : P ≠ 0 := by
    apply mul_ne_zero
    · apply mul_ne_zero
      · apply mul_ne_zero
        · apply mul_ne_zero
          · exact Finset.prod_ne_zero_iff.mpr (fun j _ => hF0 j)
          · exact Finset.prod_ne_zero_iff.mpr (fun i _ => pointAvoidPolynomial_ne_zero (v i))
        · exact hB
      · exact X_ne_zero 0
    · exact X_ne_zero 2
  obtain ⟨p, hp⟩ := exists_eval_ne_zero P hP0
  simp only [P, map_mul, map_prod, eval_X, mul_ne_zero_iff, Finset.prod_ne_zero_iff,
    Finset.mem_univ, forall_const] at hp
  obtain ⟨⟨⟨⟨hPF, hPA⟩, hPB⟩, hp0⟩, hp2⟩ := hp
  have hPF' (j : J) : eval (Fin.cons 1 0) (triangularMap p (F j)) ≠ 0 := by
    rw [triangularMap_eval_origin]
    exact hPF j
  choose A hA hcertificate using fun j : J => coprime_pencil_certificate
    (triangularMap p (F j)) (triangularMap p (G j)) (m j) (n j)
    (triangularMap_homogeneous p (F j) (m j) (hF j))
    (triangularMap_homogeneous p (G j) (n j) (hG j)) (hPF' j)
    (relPrime_ringEquiv (triangularEquiv p hp0).toRingEquiv (hcop j))
  have hu (i : T) : transverseCoordinates p (v i) ≠ 0 :=
    transverseCoordinates_ne_zero p (v i) hp0 (hv i) (hPA i)
  have hdetvec : (![p 1, p 2] : Fin 2 → K) ≠ 0 := by
    intro hz
    have h := congrFun hz (1 : Fin 2)
    exact hp2 h
  let Q := (∏ j, A j) * (∏ i, lineParameterPolynomial (transverseCoordinates p (v i))) *
    X (0 : Fin 2) * lineParameterPolynomial ![p 1, p 2]
  have hQ0 : Q ≠ 0 := by
    apply mul_ne_zero
    · apply mul_ne_zero
      · apply mul_ne_zero
        · exact Finset.prod_ne_zero_iff.mpr (fun j _ => hA j)
        · exact Finset.prod_ne_zero_iff.mpr (fun i _ => lineParameterPolynomial_ne_zero _ (hu i))
      · exact X_ne_zero 0
    · exact lineParameterPolynomial_ne_zero _ hdetvec
  obtain ⟨w, hw⟩ := exists_eval_ne_zero Q hQ0
  simp only [Q, map_mul, map_prod, eval_X, mul_ne_zero_iff, Finset.prod_ne_zero_iff,
    Finset.mem_univ, forall_const] at hw
  obtain ⟨⟨⟨hWA, hWP⟩, hw0⟩, hwdet⟩ := hw
  have hdet : p 1 * w 1 - p 2 * w 0 ≠ 0 := by
    simpa [lineParameterPolynomial] using hwdet
  refine ⟨p, w, hp0, hp2, hw0, hdet, hPB, fun j => hcertificate j w (hWA j), ?_⟩
  intro i
  rw [lineEquation_eval]
  exact hWP i

end Cylinder.SimultaneousPlaneLine
end
