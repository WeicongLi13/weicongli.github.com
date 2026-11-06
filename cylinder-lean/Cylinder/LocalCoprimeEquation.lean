module

public import Cylinder.ActualIdealCharacter
public import Cylinder.HomogeneousFactors

/-! The degree of the last numerical character produces a genuine equation
coprime to an irreducible initial equation. The strict dimension inequality
is derived from the actual ideal-dimension formula, with its last correction
term equal to one. -/

@[expose] public section
noncomputable section
open scoped Classical BigOperators
namespace Cylinder.LocalCoprimeEquation
open MvPolynomial Module Finset
open Cylinder.HilbertEvaluation Cylinder.PlaneNumericalCharacter
open Cylinder.PlaneBinaryReduction Cylinder.HilbertCharacterFormulas
open Cylinder.ActualIdealCharacter Cylinder.NumericCharacterSequence
open Cylinder.HomogeneousFactors
variable {K I : Type*} [Field K] [Fintype I]
local instance planeGradedAlgebra : GradedAlgebra (Forms K) := MvPolynomial.gradedAlgebra

def factorMap (v : I → Fin 3 → K) (F : PlaneRing K) (e r : ℕ)
    (hF : F.IsHomogeneous e) (hvan : ∀ i, eval (v i) F = 0) :
    Forms K r →ₗ[K] idealPiece v (r + e) :=
  LinearMap.codRestrict (idealPiece v (r + e))
    (LinearMap.codRestrict (Forms K (r + e))
      ((LinearMap.mul K (PlaneRing K) F).comp (Forms K r).subtype)
      (fun Q => by
        change (F * Q.val).IsHomogeneous (r + e)
        simpa only [add_comm e r] using hF.mul Q.property))
    (fun Q => by
      change F * Q.val ∈ (vanishingIdeal v).toIdeal
      apply (homogeneous_mem_vanishingIdeal v (F * Q.val) (e + r) (hF.mul Q.property)).mpr
      intro i
      rw [map_mul, hvan i, zero_mul])

omit [Fintype I] in
theorem factorMap_injective (v : I → Fin 3 → K) (F : PlaneRing K) (e r : ℕ)
    (hF : F.IsHomogeneous e) (hF0 : F ≠ 0) (hvan : ∀ i, eval (v i) F = 0) :
    Function.Injective (factorMap v F e r hF hvan) := by
  intro P Q h
  apply Subtype.ext
  exact mul_left_cancel₀ hF0 (congrArg (fun H => H.val.val) h)

omit [Fintype I] in
theorem factorMap_range_finrank (v : I → Fin 3 → K) (F : PlaneRing K) (e r : ℕ)
    (hF : F.IsHomogeneous e) (hF0 : F ≠ 0) (hvan : ∀ i, eval (v i) F = 0) :
    finrank K (LinearMap.range (factorMap v F e r hF hvan)) = finrank K (Forms K r) :=
  LinearMap.finrank_range_of_inj (factorMap_injective v F e r hF hF0 hvan)

omit [Fintype I] in
theorem factorMap_range_iff_dvd (v : I → Fin 3 → K) (F : PlaneRing K) (e r : ℕ)
    (hF : F.IsHomogeneous e) (hF0 : F ≠ 0) (hvan : ∀ i, eval (v i) F = 0)
    (P : idealPiece v (r + e)) :
    P ∈ LinearMap.range (factorMap v F e r hF hvan) ↔ F ∣ P.val.val := by
  constructor
  · rintro ⟨Q, hQ⟩
    exact ⟨Q.val, (congrArg (fun H => H.val.val) hQ).symm⟩
  · rintro ⟨Q, hQ⟩
    have hhom : Q.IsHomogeneous r := by
      have hh := quotient_homogeneous F Q (r + e) hF0 (hQ ▸ P.val.property)
      simpa only [hF.totalDegree hF0, Nat.add_sub_cancel] using hh
    refine ⟨⟨Q, hhom⟩, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    exact hQ.symm

theorem last_character_correction_positive [Infinite K] [Nonempty I]
    (v : I → Fin 3 → K) (e : ℕ) (hinitial : InitialDegree v e) :
    0 < ∑ i ∈ range e, (numericalCharacter v (e - 1) + 1 - numericalCharacter v i) := by
  have he0 := initialDegree_pos v e hinitial
  have hi : e - 1 ∈ range e := mem_range.mpr (by omega)
  have hle := Finset.single_le_sum (fun i (_ : i ∈ range e) =>
    Nat.zero_le (numericalCharacter v (e - 1) + 1 - numericalCharacter v i)) hi
  have hterm : numericalCharacter v (e - 1) + 1 - numericalCharacter v (e - 1) = 1 := by omega
  rw [hterm] at hle
  omega

theorem last_character_piece_strictly_larger [Infinite K] [Nonempty I]
    (v : I → Fin 3 → K) (hv : ∀ i, v i ≠ 0) (hsep : ProjectivelyDistinct v)
    (e : ℕ) (hinitial : InitialDegree v e) :
    e ≤ numericalCharacter v (e - 1) ∧
      finrank K (Forms K (numericalCharacter v (e - 1) - e)) <
        finrank K (idealPiece v (numericalCharacter v (e - 1))) := by
  have he0 := initialDegree_pos v e hinitial
  have ht := (character_formulas v hv hsep e hinitial).1 (e - 1) (by omega)
  refine ⟨ht, ?_⟩
  have hdim := ideal_dimension v hv hsep e hinitial (numericalCharacter v (e - 1)) (by omega)
  have hc := last_character_correction_positive v e hinitial
  rw [forms_dimension]
  have harith : numericalCharacter v (e - 1) + 1 - e =
      (numericalCharacter v (e - 1) - e) + 1 := by omega
  rw [harith] at hdim
  omega

/-- The actual coprime equation needed by the local curve theorem. -/
theorem exists_coprime_equation [Infinite K] [Nonempty I]
    (v : I → Fin 3 → K) (hv : ∀ i, v i ≠ 0) (hsep : ProjectivelyDistinct v)
    (e : ℕ) (hinitial : InitialDegree v e) (F : PlaneRing K)
    (hFirr : Irreducible F) (hFhom : F.IsHomogeneous e) (hFvan : ∀ i, eval (v i) F = 0) :
    e ≤ numericalCharacter v (e - 1) ∧ ∃ G : PlaneRing K,
      G ≠ 0 ∧ G.IsHomogeneous (numericalCharacter v (e - 1)) ∧
        (∀ i, eval (v i) G = 0) ∧ IsRelPrime F G := by
  let t := numericalCharacter v (e - 1)
  let r := t - e
  obtain ⟨hte, hdim⟩ := last_character_piece_strictly_larger v hv hsep e hinitial
  have hrt : r + e = t := by dsimp only [r, t]; omega
  have hnotall : ¬∀ P : idealPiece v (r + e), F ∣ P.val.val := by
    intro hall
    have hrange : LinearMap.range (factorMap v F e r hFhom hFvan) = ⊤ := by
      apply top_unique
      intro P _
      exact (factorMap_range_iff_dvd v F e r hFhom hFirr.ne_zero hFvan P).mpr (hall P)
    have hrank := factorMap_range_finrank v F e r hFhom hFirr.ne_zero hFvan
    rw [hrange, finrank_top, hrt] at hrank
    dsimp only [r, t] at hrank
    omega
  push Not at hnotall
  obtain ⟨P, hP⟩ := hnotall
  refine ⟨hte, P.val.val, ?_, ?_, ?_, hFirr.isRelPrime_iff_not_dvd.mpr hP⟩
  · intro hz
    exact hP (hz ▸ dvd_zero F)
  · change P.val.val.IsHomogeneous t
    rw [← hrt]
    exact P.val.property
  · exact (homogeneous_mem_vanishingIdeal v P.val.val (r + e) P.val.property).mp P.property

end Cylinder.LocalCoprimeEquation
end
