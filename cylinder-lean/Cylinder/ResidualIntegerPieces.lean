module

public import Cylinder.CompleteIntersectionDuality
public import Cylinder.AffineEvaluationHighDegrees

/-! Integer homogeneous residual quotient pieces, including the actual
zero components in negative degrees. -/

@[expose] public section
noncomputable section

namespace Cylinder.ResidualIntegerPieces

open Module MvPolynomial
open Cylinder.PlaneBinaryReduction Cylinder.CompleteIntersectionKoszul
open Cylinder.FiniteEvaluationDuality Cylinder.CurvePolarLocal Cylinder.PlaneHomogenization
open Cylinder.HomogeneousCompleteIntersection Cylinder.ResidualEvaluation Cylinder.ResidualQuotientPieces
open Cylinder.CompleteIntersectionDuality Cylinder.AffineEvaluationHighDegrees
open scoped Classical

variable {K I : Type*} [Field K] [Fintype I]

def integerForms (K : Type*) [Field K] (d : ℤ) : Submodule K (HomRing (K := K)) :=
  if 0 ≤ d then HomForms K d.toNat else ⊥

def integerResidualPiece (F G : HomRing (K := K)) (v : I → Fin 2 → K) (d : ℤ) :
    Submodule K (HomRing (K := K)) :=
  (residualIdeal F G v).restrictScalars K ⊓ integerForms K d

def integerEquationPiece (F G : HomRing (K := K)) (v : I → Fin 2 → K) (d : ℤ) :
    Submodule K (integerResidualPiece F G v d) :=
  ((equationsIdeal F G).restrictScalars K).comap (integerResidualPiece F G v d).subtype

abbrev IntegerResidualQuotient (F G : HomRing (K := K)) (v : I → Fin 2 → K) (d : ℤ) : Type _ :=
  @HasQuotient.Quotient ↥(integerResidualPiece F G v d) _
    (Submodule.hasQuotient (R := K)) (integerEquationPiece F G v d)

def residualPieceEquivInteger (F G : HomRing (K := K)) (v : I → Fin 2 → K)
    (n : ℕ) (d : ℤ) (hd : d = (n : ℤ)) :
    residualPiece F G v n ≃ₗ[K] integerResidualPiece F G v d where
  toFun H := ⟨H.val.val, H.property, by simpa [integerForms, hd] using H.val.property⟩
  invFun H := ⟨⟨H.val, by simpa [integerForms, hd] using H.property.2⟩, H.property.1⟩
  left_inv H := rfl
  right_inv H := rfl
  map_add' H J := rfl
  map_smul' a H := rfl

theorem equationPiece_map_integer (F G : HomRing (K := K)) (v : I → Fin 2 → K)
    (n : ℕ) (d : ℤ) (hd : d = (n : ℤ)) :
    (equationInResidualPiece F G v n).map (residualPieceEquivInteger F G v n d hd).toLinearMap =
      integerEquationPiece F G v d := by
  apply le_antisymm
  · intro H hH
    obtain ⟨J, hJ, rfl⟩ := hH
    exact hJ
  · intro H hH
    refine ⟨(residualPieceEquivInteger F G v n d hd).symm H, ?_,
      (residualPieceEquivInteger F G v n d hd).apply_symm_apply H⟩
    exact hH

def residualQuotientEquivInteger (F G : HomRing (K := K)) (v : I → Fin 2 → K)
    (n : ℕ) (d : ℤ) (hd : d = (n : ℤ)) :
    ResidualQuotientPiece F G v n ≃ₗ[K] IntegerResidualQuotient F G v d :=
  Submodule.Quotient.equiv _ _ (residualPieceEquivInteger F G v n d hd)
    (equationPiece_map_integer F G v n d hd)

theorem integerResidualPiece_eq_bot (F G : HomRing (K := K)) (v : I → Fin 2 → K)
    (d : ℤ) (hd : d < 0) : integerResidualPiece F G v d = ⊥ := by
  simp [integerResidualPiece, integerForms, not_le.mpr hd]

theorem integerResidualQuotient_eq_zero (F G : HomRing (K := K)) (v : I → Fin 2 → K)
    (d : ℤ) (hd : d < 0) (a : IntegerResidualQuotient F G v d) : a = 0 := by
  obtain ⟨H, rfl⟩ := Submodule.Quotient.mk_surjective (integerEquationPiece F G v d) a
  have hH : H = 0 := by
    apply Subtype.ext
    change H.val = (0 : HomRing (K := K))
    simpa only [integerResidualPiece_eq_bot F G v d hd, Submodule.mem_bot] using H.property
  rw [hH]
  rfl

/-- Finite degree-j relations and the actual integer-graded residual
quotient are isomorphic for every nonnegative j. -/
def relationResidualIntegerEquiv (F G : HomRing (K := K)) (e t : ℕ)
    (he : 0 < e) (ht : 0 < t)
    (hF : F.IsHomogeneous e) (hG : G.IsHomogeneous t)
    (hf : (dehomogenize F).totalDegree = e) (hg : (dehomogenize G).totalDegree = t)
    (hfe : homogeneousComponent e (dehomogenize F) ≠ 0)
    (hge : homogeneousComponent t (dehomogenize G) ≠ 0)
    (hcop : IsRelPrime (homogeneousComponent e (dehomogenize F))
      (homogeneousComponent t (dehomogenize G)))
    (v : I → Fin 2 → K) (hv : Function.Injective v)
    (hfv : ∀ i, eval (v i) (dehomogenize F) = 0)
    (hgv : ∀ i, eval (v i) (dehomogenize G) = 0) (j : ℕ) :
    coefficientRelations v j ≃ₗ[K]
      IntegerResidualQuotient F G v ((e : ℤ) + t - 3 - j) := by
  by_cases hj : j < e + t - 2
  · exact (relationResidualEquiv F G e t he ht hF hG hf hg hfe hge hcop v hv hfv hgv j hj).trans
      (residualQuotientEquivInteger F G v (e + t - 2 - j - 1) _ (by omega))
  · have hzero := coefficientRelations_eq_bot (dehomogenize F) (dehomogenize G) e t
      he ht hf hg hfe hge hcop v hv hfv hgv j (by omega)
    letI : Subsingleton (coefficientRelations v j) := ⟨by
      intro c c'
      apply Subtype.ext
      have hc : c.val = 0 := by simpa only [hzero, Submodule.mem_bot] using c.property
      have hc' : c'.val = 0 := by simpa only [hzero, Submodule.mem_bot] using c'.property
      exact hc.trans hc'.symm⟩
    letI : Subsingleton (IntegerResidualQuotient F G v ((e : ℤ) + t - 3 - j)) := ⟨by
      intro a b
      rw [integerResidualQuotient_eq_zero F G v _ (by omega) a,
        integerResidualQuotient_eq_zero F G v _ (by omega) b]⟩
    exact LinearEquiv.ofSubsingleton _ _

#print axioms residualQuotientEquivInteger
#print axioms integerResidualQuotient_eq_zero
#print axioms relationResidualIntegerEquiv

end Cylinder.ResidualIntegerPieces

end
