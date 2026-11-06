module

public import Cylinder.ActualIdealCharacter
public import Cylinder.IntegerRepresentativeRelations

/-! The numerical-character defect formulas in every integer degree,
including the last nonzero degree -1 for a single point. -/

@[expose] public section
noncomputable section
open scoped Classical BigOperators
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Cylinder.IntegerCharacterFormulas

open Module Finset
open Cylinder.HilbertEvaluation Cylinder.HilbertCharacterFormulas
open Cylinder.PlaneBinaryReduction Cylinder.IntegerRepresentativeRelations

variable {K I : Type*} [Field K] [Fintype I]

def integerDefect (x : I → Fin 3 → K) (v : ℤ) : ℕ :=
  if 0 ≤ v then Fintype.card I - hilbert x v.toNat else Fintype.card I

def characterTerm (n i : ℕ) (v : ℤ) : ℕ :=
  ((n : ℤ) - v - 1).toNat - ((i : ℤ) - v - 1).toNat

theorem characterTerm_nonnegative (n i : ℕ) (v : ℤ) (hv : 0 ≤ v) :
    characterTerm n i v = (n - (v.toNat + 1)) - (i - (v.toNat + 1)) := by
  dsimp [characterTerm]
  omega

theorem characterTerm_negative (n i : ℕ) (v : ℤ) (hv : v < 0) (hi : i ≤ n) :
    characterTerm n i v = n - i := by
  dsimp [characterTerm]
  omega

theorem integerDefect_eq_relations (x : I → Fin 3 → K) (v : ℤ) :
    integerDefect x v = finrank K (integerRelations x v) := by
  by_cases hv : 0 ≤ v
  · have he : integerRelations x v = PlaneRelationSpaces.relationSpace x v.toNat := by
      simp only [integerRelations, ite_eq_left hv]
    calc
      _ = Fintype.card I - hilbert x v.toNat := by simp only [integerDefect, ite_eq_left hv]
      _ = finrank K (PlaneRelationSpaces.relationSpace x v.toNat) :=
        (PlaneRelationSpaces.relationSpace_finrank x v.toNat).symm
      _ = finrank K (integerRelations x v) := (LinearEquiv.ofEq _ _ he).finrank_eq.symm
  · have he : integerRelations x v = ⊤ := by simp only [integerRelations, ite_eq_right hv]
    calc
      _ = Fintype.card I := by simp only [integerDefect, ite_eq_right hv]
      _ = finrank K (I → K) := (Module.finrank_fintype_fun_eq_card K).symm
      _ = finrank K (integerRelations x v) :=
        ((LinearEquiv.ofEq _ _ he).trans Submodule.topEquiv).finrank_eq.symm

variable [Infinite K] [Nonempty I]

theorem integerDefect_character_formula (x : I → Fin 3 → K)
    (hx : ∀ i, x i ≠ 0) (hsep : ProjectivelyDistinct x)
    (s : ℕ) (hs : InitialDegree x s) (v : ℤ) :
    integerDefect x v = ∑ i ∈ range s, characterTerm (numericalCharacter x i) i v := by
  have hc := ActualIdealCharacter.character_formulas x hx hsep s hs
  by_cases hv : 0 ≤ v
  · simp only [integerDefect, ite_eq_left hv]
    rw [hc.2.2.2 v.toNat]
    apply sum_congr rfl
    intro i _
    exact (characterTerm_nonnegative _ _ v hv).symm
  · simp only [integerDefect, ite_eq_right hv]
    rw [hc.2.2.1]
    apply sum_congr rfl
    intro i hi
    exact (characterTerm_negative _ _ v (lt_of_not_ge hv)
      (le_trans (Nat.le_of_lt (mem_range.mp hi)) (hc.1 i (mem_range.mp hi)))).symm

theorem integerDefect_positive_iff (x : I → Fin 3 → K)
    (hx : ∀ i, x i ≠ 0) (hsep : ProjectivelyDistinct x)
    (s : ℕ) (hs : InitialDegree x s) (v : ℤ) :
    0 < integerDefect x v ↔ v < (numericalCharacter x 0 : ℤ) - 1 := by
  have hshape := derivationShape x hx hsep s hs
  by_cases hv : 0 ≤ v
  · simp only [integerDefect, ite_eq_left hv]
    rw [defect_positive_iff x hx hsep s hshape v.toNat]
    omega
  · have hspos := hshape.positive
    have hn : s ≤ numericalCharacter x 0 :=
      NumericCharacterSequence.character_ge_initial_size hshape (by omega : 0 < s)
    have hcard := Fintype.card_pos (α := I)
    simp only [integerDefect, ite_eq_right hv]
    omega

theorem last_positive_degree (x : I → Fin 3 → K)
    (hx : ∀ i, x i ≠ 0) (hsep : ProjectivelyDistinct x)
    (s : ℕ) (hs : InitialDegree x s) :
    0 < integerDefect x ((numericalCharacter x 0 : ℤ) - 2) ∧
      ∀ v : ℤ, (numericalCharacter x 0 : ℤ) - 2 < v → integerDefect x v = 0 := by
  constructor
  · rw [integerDefect_positive_iff x hx hsep s hs]
    omega
  · intro v hv
    have h := integerDefect_positive_iff x hx hsep s hs v
    omega

end Cylinder.IntegerCharacterFormulas
end
