module

public import Cylinder.SimultaneousPlaneLine

/-!
# Actual graph coordinates on the selected line

The binary reparameterization is a genuine invertible linear substitution.
This converts simultaneous line selection into the existing graphRestriction
and graphEquation interfaces used in the Artin reduction.
-/

@[expose] public section
noncomputable section
namespace Cylinder.GraphPlaneLine
open MvPolynomial
open Cylinder.HilbertEvaluation Cylinder.GenericPlaneLine Cylinder.SimultaneousPlaneLine
open Cylinder.PlaneBinaryReduction
variable {K : Type*} [Field K]

def matrixMap (a b c d : K) : BinaryRing K →ₐ[K] BinaryRing K :=
  MvPolynomial.aeval ![C a * X 0 + C b * X 1, C c * X 0 + C d * X 1]

theorem matrixMap_X_zero (a b c d : K) : matrixMap a b c d (X 0) = C a * X 0 + C b * X 1 := by
  simp [matrixMap]
theorem matrixMap_X_one (a b c d : K) : matrixMap a b c d (X 1) = C c * X 0 + C d * X 1 := by
  simp [matrixMap]
theorem matrixMap_C (a b c d e : K) : matrixMap a b c d (C e) = C e :=
  (matrixMap a b c d).commutes e

theorem matrixMap_inverse_left (a b c d : K) (hdet : a * d - b * c ≠ 0) :
    (matrixMap (d * (a * d - b * c)⁻¹) (-(b * (a * d - b * c)⁻¹))
      (-(c * (a * d - b * c)⁻¹)) (a * (a * d - b * c)⁻¹)).comp (matrixMap a b c d) =
      AlgHom.id K (BinaryRing K) := by
  have hu : ((C a * C d - C b * C c) * C (a * d - b * c)⁻¹ : BinaryRing K) = 1 := by
    rw [← C_mul, ← C_mul, ← C_sub, ← C_mul, mul_inv_cancel₀ hdet, C_1]
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i
  · change matrixMap _ _ _ _ (matrixMap a b c d (X (0 : Fin 2))) = X 0
    rw [matrixMap_X_zero, map_add, map_mul, map_mul, matrixMap_C, matrixMap_C,
      matrixMap_X_zero, matrixMap_X_one]
    simp only [C_mul, C_neg]
    linear_combination (X (0 : Fin 2) : BinaryRing K) * hu
  · change matrixMap _ _ _ _ (matrixMap a b c d (X (1 : Fin 2))) = X 1
    rw [matrixMap_X_one, map_add, map_mul, map_mul, matrixMap_C, matrixMap_C,
      matrixMap_X_zero, matrixMap_X_one]
    simp only [C_mul, C_neg]
    linear_combination (X (1 : Fin 2) : BinaryRing K) * hu

theorem matrixMap_inverse_right (a b c d : K) (hdet : a * d - b * c ≠ 0) :
    (matrixMap a b c d).comp
      (matrixMap (d * (a * d - b * c)⁻¹) (-(b * (a * d - b * c)⁻¹))
        (-(c * (a * d - b * c)⁻¹)) (a * (a * d - b * c)⁻¹)) =
      AlgHom.id K (BinaryRing K) := by
  have hu : ((C a * C d - C b * C c) * C (a * d - b * c)⁻¹ : BinaryRing K) = 1 := by
    rw [← C_mul, ← C_mul, ← C_sub, ← C_mul, mul_inv_cancel₀ hdet, C_1]
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i
  · change matrixMap a b c d (matrixMap _ _ _ _ (X (0 : Fin 2))) = X 0
    rw [matrixMap_X_zero]
    simp only [map_add (matrixMap a b c d), map_mul (matrixMap a b c d),
      matrixMap_C, matrixMap_X_zero, matrixMap_X_one]
    simp only [C_mul, C_neg]
    linear_combination (X (0 : Fin 2) : BinaryRing K) * hu
  · change matrixMap a b c d (matrixMap _ _ _ _ (X (1 : Fin 2))) = X 1
    rw [matrixMap_X_one]
    simp only [map_add (matrixMap a b c d), map_mul (matrixMap a b c d),
      matrixMap_C, matrixMap_X_zero, matrixMap_X_one]
    simp only [C_mul, C_neg]
    linear_combination (X (1 : Fin 2) : BinaryRing K) * hu

def matrixEquiv (a b c d : K) (hdet : a * d - b * c ≠ 0) : BinaryRing K ≃ₐ[K] BinaryRing K :=
  AlgEquiv.ofAlgHom (matrixMap a b c d)
    (matrixMap (d * (a * d - b * c)⁻¹) (-(b * (a * d - b * c)⁻¹))
      (-(c * (a * d - b * c)⁻¹)) (a * (a * d - b * c)⁻¹))
    (matrixMap_inverse_right a b c d hdet) (matrixMap_inverse_left a b c d hdet)

def graphA (p : Fin 3 → K) (w : Fin 2 → K) : K :=
  p 0 * w 1 * (p 1 * w 1 - w 0 * p 2)⁻¹
def graphB (p : Fin 3 → K) (w : Fin 2 → K) : K :=
  -(p 0 * w 0 * (p 1 * w 1 - w 0 * p 2)⁻¹)

theorem graph_reparameterization (p : Fin 3 → K) (w : Fin 2 → K)
    (hdet : p 1 * w 1 - w 0 * p 2 ≠ 0) (P : PlaneRing K) :
    matrixMap (p 1) (w 0) (p 2) (w 1) (graphRestriction (graphA p w) (graphB p w) P) =
      lineRestriction p w P := by
  have he : (matrixMap (p 1) (w 0) (p 2) (w 1)).comp
      (graphRestriction (graphA p w) (graphB p w)) = lineRestriction p w := by
    have hu : ((C (p 1) * C (w 1) - C (w 0) * C (p 2)) *
        C (p 1 * w 1 - w 0 * p 2)⁻¹ : BinaryRing K) = 1 := by
      rw [← C_mul, ← C_mul, ← C_sub, ← C_mul, mul_inv_cancel₀ hdet, C_1]
    apply MvPolynomial.algHom_ext
    intro i
    have g0 : graphRestriction (graphA p w) (graphB p w) (X (0 : Fin 3)) =
        C (graphA p w) * X 0 + C (graphB p w) * X 1 := by simp [graphRestriction, innerGraph]
    have g1 : graphRestriction (graphA p w) (graphB p w) (X (1 : Fin 3)) = X (0 : Fin 2) :=
      graphRestriction_X_succ _ _ (0 : Fin 2)
    have g2 : graphRestriction (graphA p w) (graphB p w) (X (2 : Fin 3)) = X (1 : Fin 2) :=
      graphRestriction_X_succ _ _ (1 : Fin 2)
    fin_cases i
    · change matrixMap _ _ _ _ (graphRestriction (graphA p w) (graphB p w) (X (0 : Fin 3))) =
        pencilRestriction w (triangularMap p (X (0 : Fin 3)))
      rw [g0]
      rw [triangularMap_X_zero, map_mul, pencilRestriction_C, pencilRestriction_X]
      change matrixMap _ _ _ _ (C (graphA p w) * X 0 + C (graphB p w) * X 1) = C (p 0) * X 0
      rw [map_add, map_mul, map_mul, matrixMap_C, matrixMap_C, matrixMap_X_zero, matrixMap_X_one]
      simp only [graphA, graphB, C_mul, C_neg]
      linear_combination (C (p 0) * X (0 : Fin 2) : BinaryRing K) * hu
    · change matrixMap _ _ _ _ (graphRestriction (graphA p w) (graphB p w) (X (1 : Fin 3))) =
        pencilRestriction w (triangularMap p (X (1 : Fin 3)))
      rw [g1]
      rw [matrixMap_X_zero, triangularMap_X_one, map_add, map_mul, pencilRestriction_C,
        pencilRestriction_X, pencilRestriction_X]
      simp
      ring
    · change matrixMap _ _ _ _ (graphRestriction (graphA p w) (graphB p w) (X (2 : Fin 3))) =
        pencilRestriction w (triangularMap p (X (2 : Fin 3)))
      rw [g2]
      rw [matrixMap_X_one, triangularMap_X_two, map_add, map_mul, pencilRestriction_C,
        pencilRestriction_X, pencilRestriction_X]
      simp
      ring
  exact AlgHom.congr_fun he P

theorem lineEquation_normalized [Infinite K] (p : Fin 3 → K) (w : Fin 2 → K)
    (hp : p 0 ≠ 0) (hdet : p 1 * w 1 - w 0 * p 2 ≠ 0) :
    lineEquation p w = C (-(p 1 * w 1 - w 0 * p 2) * (p 0)⁻¹) *
      graphEquation (graphA p w) (graphB p w) := by
  apply MvPolynomial.funext
  intro v
  simp [lineEquation, graphEquation, graphA, graphB]
  have hdet2 : w 1 * p 1 - w 0 * p 2 ≠ 0 := by simpa only [mul_comm (w 1) (p 1)] using hdet
  field_simp [hp, hdet, hdet2]
  ring

/-- One actual graph line simultaneously preserves every coprime pair and
avoids the specified finite projective representatives. -/
theorem exists_graph_coprime_avoiding [Infinite K] {J T : Type*} [Fintype J] [Fintype T]
    (F G : J → PlaneRing K) (m n : J → ℕ)
    (hF : ∀ j, (F j).IsHomogeneous (m j)) (hG : ∀ j, (G j).IsHomogeneous (n j))
    (hF0 : ∀ j, F j ≠ 0) (hcop : ∀ j, IsRelPrime (F j) (G j))
    (v : T → Fin 3 → K) (hv : ∀ i, v i ≠ 0) :
    ∃ a b : K,
      (∀ j, IsRelPrime (graphRestriction a b (F j)) (graphRestriction a b (G j))) ∧
        ∀ i, eval (v i) (graphEquation a b) ≠ 0 := by
  obtain ⟨p, w, hp0, _, _, hdet, _, hcopR, havoid⟩ :=
    exists_simultaneous_line F G m n hF hG hF0 hcop v hv 1 one_ne_zero
  have hdet' : p 1 * w 1 - w 0 * p 2 ≠ 0 := by simpa only [mul_comm (w 0) (p 2)] using hdet
  let e := matrixEquiv (p 1) (w 0) (p 2) (w 1) hdet'
  refine ⟨graphA p w, graphB p w, ?_, ?_⟩
  · intro j
    have hcopE : IsRelPrime (e (graphRestriction (graphA p w) (graphB p w) (F j)))
        (e (graphRestriction (graphA p w) (graphB p w) (G j))) := by
      simpa only [e, matrixEquiv, AlgEquiv.ofAlgHom_apply, graph_reparameterization p w hdet'] using hcopR j
    have h := relPrime_ringEquiv e.symm.toRingEquiv hcopE
    simpa using h
  · intro i hz
    apply havoid i
    rw [lineEquation_normalized p w hp0 hdet', map_mul, eval_C, hz, mul_zero]

theorem graphRestriction_ne_zero_of_eval (p : Fin 3 → K) (w : Fin 2 → K)
    (hdet : p 1 * w 1 - w 0 * p 2 ≠ 0) (P : PlaneRing K) (hP : eval p P ≠ 0) :
    graphRestriction (graphA p w) (graphB p w) P ≠ 0 := by
  intro hz
  have hR : lineRestriction p w P = 0 := by
    rw [← graph_reparameterization p w hdet P, hz, map_zero]
  have hh : eval ![1, 0] (lineRestriction p w P) = eval p P := by
    change eval ![1, 0] (pencilRestriction w (triangularMap p P)) = eval p P
    rw [pencil_eval_infinity, triangularMap_eval_origin]
  apply hP
  rw [← hh, hR, map_zero]

/-- The same selected graph line preserves the coprime pairs, avoids the points,
and does not annihilate any of a further finite family of actual polynomials. -/
theorem exists_graph_coprime_avoiding_with_nonzero [Infinite K]
    {J T S : Type*} [Fintype J] [Fintype T] [Fintype S]
    (F G : J → PlaneRing K) (m n : J → ℕ)
    (hF : ∀ j, (F j).IsHomogeneous (m j)) (hG : ∀ j, (G j).IsHomogeneous (n j))
    (hF0 : ∀ j, F j ≠ 0) (hcop : ∀ j, IsRelPrime (F j) (G j))
    (v : T → Fin 3 → K) (hv : ∀ i, v i ≠ 0)
    (H : S → PlaneRing K) (hH0 : ∀ i, H i ≠ 0) :
    ∃ a b : K,
      (∀ j, IsRelPrime (graphRestriction a b (F j)) (graphRestriction a b (G j))) ∧
        (∀ i, eval (v i) (graphEquation a b) ≠ 0) ∧
          ∀ i, graphRestriction a b (H i) ≠ 0 := by
  classical
  obtain ⟨p, w, hp0, _, _, hdet, hPB, hcopR, havoid⟩ := exists_simultaneous_line
    F G m n hF hG hF0 hcop v hv (∏ i, H i)
      (Finset.prod_ne_zero_iff.mpr (fun i _ => hH0 i))
  have hdet' : p 1 * w 1 - w 0 * p 2 ≠ 0 := by simpa only [mul_comm (w 0) (p 2)] using hdet
  let e := matrixEquiv (p 1) (w 0) (p 2) (w 1) hdet'
  refine ⟨graphA p w, graphB p w, ?_, ?_, ?_⟩
  · intro j
    have hcopE : IsRelPrime (e (graphRestriction (graphA p w) (graphB p w) (F j)))
        (e (graphRestriction (graphA p w) (graphB p w) (G j))) := by
      simpa only [e, matrixEquiv, AlgEquiv.ofAlgHom_apply, graph_reparameterization p w hdet'] using hcopR j
    have h := relPrime_ringEquiv e.symm.toRingEquiv hcopE
    simpa using h
  · intro i hz
    apply havoid i
    rw [lineEquation_normalized p w hp0 hdet', map_mul, eval_C, hz, mul_zero]
  · intro i
    apply graphRestriction_ne_zero_of_eval p w hdet' (H i)
    rw [map_prod] at hPB
    exact (Finset.prod_ne_zero_iff.mp hPB) i (Finset.mem_univ i)

/-- The requested common graph line for an actual pairwise relatively prime
finite family. No restriction nonvanishing or coprimality is assumed. -/
theorem exists_graph_pairwise_coprime_avoiding [Infinite K]
    {S T : Type*} [Fintype S] [Fintype T]
    (F : S → PlaneRing K) (d : S → ℕ) (hF : ∀ i, (F i).IsHomogeneous (d i))
    (hF0 : ∀ i, F i ≠ 0) (hcop : Pairwise (fun i j => IsRelPrime (F i) (F j)))
    (v : T → Fin 3 → K) (hv : ∀ i, v i ≠ 0) :
    ∃ a b : K, (∀ i, eval (v i) (graphEquation a b) ≠ 0) ∧
      (∀ i, graphRestriction a b (F i) ≠ 0) ∧
        Pairwise (fun i j => IsRelPrime (graphRestriction a b (F i)) (graphRestriction a b (F j))) := by
  classical
  let J := {ij : S × S // ij.1 ≠ ij.2}
  obtain ⟨a, b, hpair, havoid, hnonzero⟩ := exists_graph_coprime_avoiding_with_nonzero
    (fun j : J => F j.val.1) (fun j : J => F j.val.2)
    (fun j : J => d j.val.1) (fun j : J => d j.val.2)
    (fun j => hF j.val.1) (fun j => hF j.val.2) (fun j => hF0 j.val.1)
    (fun j => hcop j.property) v hv F hF0
  exact ⟨a, b, havoid, hnonzero, fun i j hij => hpair ⟨(i, j), hij⟩⟩

end Cylinder.GraphPlaneLine
end
