module

public import Cylinder.HomogeneousCompleteIntersection

/-! The actual homogeneous residual colon ideal and the actual ideal
annihilator in the affine chart have the same homogeneous classes. -/

@[expose] public section
noncomputable section

namespace Cylinder.ResidualEvaluation

open Module MvPolynomial
open Cylinder.PlaneBinaryReduction Cylinder.CompleteIntersectionKoszul
open Cylinder.AffinePointEvaluation Cylinder.FiniteEvaluationDuality
open Cylinder.CurvePolarLocal Cylinder.PlaneHomogenization
open Cylinder.HomogeneousCompleteIntersection
open scoped Classical BigOperators

variable {K I : Type*} [Field K] [Fintype I]

local instance : GradedAlgebra (HomForms K) := MvPolynomial.gradedAlgebra

def homogeneousPointIdeal (v : I → Fin 2 → K) : HomogeneousIdeal (HomForms K) :=
  (Ideal.comap dehomogenize (polynomialPointIdeal v)).homogeneousCore (HomForms K)

theorem homogeneous_mem_pointIdeal (v : I → Fin 2 → K) (H : HomRing (K := K))
    (n : ℕ) (hH : H.IsHomogeneous n) :
    H ∈ (homogeneousPointIdeal v).toIdeal ↔ dehomogenize H ∈ polynomialPointIdeal v := by
  constructor
  · intro h
    exact Ideal.toIdeal_homogeneousCore_le (HomForms K)
      (Ideal.comap dehomogenize (polynomialPointIdeal v)) h
  · intro h
    exact Ideal.mem_homogeneousCore_of_homogeneous_of_mem ⟨n, hH⟩ h

theorem dehomogenize_mem_pointIdeal (v : I → Fin 2 → K) (H : HomRing (K := K))
    (hH : H ∈ (homogeneousPointIdeal v).toIdeal) :
    dehomogenize H ∈ polynomialPointIdeal v :=
  Ideal.toIdeal_homogeneousCore_le (HomForms K)
    (Ideal.comap dehomogenize (polynomialPointIdeal v)) hH

theorem exists_homogeneous_pointIdeal_lift (v : I → Fin 2 → K) (P : BinaryRing K)
    (hP : P ∈ polynomialPointIdeal v) :
    ∃ H : HomRing (K := K), H ∈ (homogeneousPointIdeal v).toIdeal ∧ dehomogenize H = P := by
  refine ⟨homogenize P.totalDegree P, ?_, dehomogenize_homogenize _ _⟩
  apply (homogeneous_mem_pointIdeal v _ P.totalDegree (homogenize_homogeneous _ _ (le_refl _))).mpr
  rwa [dehomogenize_homogenize]

def residualIdeal (F G : HomRing (K := K)) (v : I → Fin 2 → K) : Ideal (HomRing (K := K)) :=
  (equationsIdeal F G).colon ((homogeneousPointIdeal v).toIdeal : Set (HomRing (K := K)))

theorem homogeneous_mem_residual_iff_annihilator (F G H : HomRing (K := K)) (e t n : ℕ)
    (hF : F.IsHomogeneous e) (hG : G.IsHomogeneous t) (hH : H.IsHomogeneous n)
    (hf : (dehomogenize F).totalDegree = e) (hg : (dehomogenize G).totalDegree = t)
    (hfe : homogeneousComponent e (dehomogenize F) ≠ 0)
    (hcop : IsRelPrime (homogeneousComponent e (dehomogenize F))
      (homogeneousComponent t (dehomogenize G)))
    (v : I → Fin 2 → K)
    (hfv : ∀ i, eval (v i) (dehomogenize F) = 0)
    (hgv : ∀ i, eval (v i) (dehomogenize G) = 0) :
    H ∈ residualIdeal F G v ↔
      Ideal.Quotient.mk (equationsIdeal (dehomogenize F) (dehomogenize G)) (dehomogenize H) ∈
        (pointIdeal (dehomogenize F) (dehomogenize G) v hfv hgv).annihilator := by
  constructor
  · intro hRes
    apply Submodule.mem_annihilator.mpr
    intro b hb
    obtain ⟨P, rfl⟩ := Ideal.Quotient.mk_surjective b
    have hPI : P ∈ polynomialPointIdeal v := hb
    obtain ⟨E, hE, hEP⟩ := exists_homogeneous_pointIdeal_lift v P hPI
    have hHE := Submodule.mem_colon.mp hRes E hE
    change H * E ∈ equationsIdeal F G at hHE
    have hdeh := dehomogenize_mem_equations F G (H * E) hHE
    rw [map_mul, hEP] at hdeh
    change Ideal.Quotient.mk (equationsIdeal (dehomogenize F) (dehomogenize G)) (dehomogenize H) *
      Ideal.Quotient.mk (equationsIdeal (dehomogenize F) (dehomogenize G)) P = 0
    rw [← map_mul]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hdeh
  · intro hAnn
    apply Submodule.mem_colon.mpr
    intro E hE
    change H * E ∈ equationsIdeal F G
    rw [← sum_homogeneousComponent E, Finset.mul_sum]
    apply Ideal.sum_mem
    intro d hd
    have hEd : homogeneousComponent d E ∈ (homogeneousPointIdeal v).toIdeal :=
      homogeneousComponent_mem_of_mem (homogeneousPointIdeal v).isHomogeneous hE d
    have hdehEd := dehomogenize_mem_pointIdeal v _ hEd
    have hclass : Ideal.Quotient.mk (equationsIdeal (dehomogenize F) (dehomogenize G))
        (dehomogenize (homogeneousComponent d E)) ∈
      pointIdeal (dehomogenize F) (dehomogenize G) v hfv hgv := hdehEd
    have hprod := Submodule.mem_annihilator.mp hAnn _ hclass
    change Ideal.Quotient.mk (equationsIdeal (dehomogenize F) (dehomogenize G)) (dehomogenize H) *
      Ideal.Quotient.mk (equationsIdeal (dehomogenize F) (dehomogenize G))
        (dehomogenize (homogeneousComponent d E)) = 0 at hprod
    rw [← map_mul] at hprod
    apply (homogeneous_mem_iff_dehomogenize_mem F G _ e t (n + d) hF hG
      (hH.mul (homogeneousComponent_isHomogeneous d E)) hf hg hfe hcop).mpr
    rw [map_mul]
    exact Ideal.Quotient.eq_zero_iff_mem.mp hprod

#print axioms exists_homogeneous_pointIdeal_lift
#print axioms homogeneous_mem_residual_iff_annihilator

end Cylinder.ResidualEvaluation

end
