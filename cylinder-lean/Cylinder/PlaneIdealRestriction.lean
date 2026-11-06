module

public import Cylinder.SaturatedPlaneLine

/-!
# Actual homogeneous ideal restriction ranks

For a regular graph line, restriction of an actual ideal has kernel exactly
the line times the preceding homogeneous ideal piece. Rank-nullity then gives
the first-difference dimension used in the plane plateau proof.
-/

@[expose] public section
noncomputable section
namespace Cylinder.PlaneIdealRestriction
open MvPolynomial Module
open Cylinder.HilbertEvaluation Cylinder.PlaneNumericalCharacter Cylinder.PlaneBinaryReduction
open Cylinder.NumericCharacterSequence
variable {K : Type*} [Field K]

def idealForms (J : Ideal (PlaneRing K)) (d : ℕ) : Submodule K (Forms K d) :=
  (J.restrictScalars K).comap (Forms K d).subtype

instance idealForms_addCommGroup (J : Ideal (PlaneRing K)) (d : ℕ) :
    AddCommGroup (idealForms J d) := Submodule.addCommGroup (idealForms J d)

instance idealForms_finiteDimensional (J : Ideal (PlaneRing K)) (d : ℕ) :
    FiniteDimensional K (idealForms J d) :=
  Module.Finite.of_injective (idealForms J d).subtype Subtype.val_injective

theorem idealForms_finrank (J : Ideal (PlaneRing K)) (d : ℕ) :
    finrank K (idealForms J d) = finrank K (Cylinder.PlanePlateau.piece J d) := by
  have he : idealForms J d = (Cylinder.PlanePlateau.piece J d).comap (Forms K d).subtype := by
    ext P
    change P.val ∈ J ↔ P.val ∈ J ∧ P.val ∈ Forms K d
    exact ⟨fun h => ⟨h, P.property⟩, fun h => h.1⟩
  rw [he]
  exact (Submodule.comapSubtypeEquivOfLe
    (show Cylinder.PlanePlateau.piece J d ≤ Forms K d from inf_le_right)).finrank_eq

def restrictionSpace (J : Ideal (PlaneRing K)) (a b : K) (d : ℕ) : Submodule K (BinaryRing K) :=
  (idealForms J d).map ((graphRestriction a b).toLinearMap.comp (Forms K d).subtype)

theorem mem_restrictionSpace (J : Ideal (PlaneRing K)) (a b : K) (d : ℕ) (F : BinaryRing K) :
    F ∈ restrictionSpace J a b d ↔
      ∃ P : PlaneRing K, P.IsHomogeneous d ∧ P ∈ J ∧ graphRestriction a b P = F := by
  constructor
  · rintro ⟨P, hP, rfl⟩
    exact ⟨P.val, P.property, hP, rfl⟩
  · rintro ⟨P, hP, hPI, hF⟩
    exact ⟨⟨P, hP⟩, hPI, hF⟩

theorem restrictionSpace_homogeneous (J : Ideal (PlaneRing K)) (a b : K) (d : ℕ) :
    restrictionSpace J a b d ≤ BinaryForms K d := by
  intro F hF
  obtain ⟨P, hP, _, rfl⟩ := (mem_restrictionSpace J a b d F).mp hF
  exact graphRestriction_homogeneous a b P d hP

instance restrictionSpace_finiteDimensional (J : Ideal (PlaneRing K)) (a b : K) (d : ℕ) :
    FiniteDimensional K (restrictionSpace J a b d) :=
  Submodule.finiteDimensional_of_le (restrictionSpace_homogeneous J a b d)

def restrictionMap (J : Ideal (PlaneRing K)) (a b : K) (d : ℕ) :
    idealForms J d →ₗ[K] BinaryRing K :=
  ((graphRestriction a b).toLinearMap.comp (Forms K d).subtype).domRestrict (idealForms J d)

theorem restrictionMap_range (J : Ideal (PlaneRing K)) (a b : K) (d : ℕ) :
    LinearMap.range (restrictionMap J a b d) = restrictionSpace J a b d :=
  LinearMap.range_domRestrict _ _

def idealMultiplication (J : Ideal (PlaneRing K)) (a b : K) (d : ℕ) :
    idealForms J d →ₗ[K] idealForms J (d + 1) :=
  LinearMap.codRestrict (idealForms J (d + 1))
    ((multiplicationForm (graphEquation a b) (graphEquation_homogeneous a b) d).comp (idealForms J d).subtype)
    (fun P => by
      change graphEquation a b * P.val.val ∈ J
      exact J.mul_mem_left _ P.property)

theorem idealMultiplication_injective (J : Ideal (PlaneRing K)) (a b : K) (d : ℕ) :
    Function.Injective (idealMultiplication J a b d) := by
  intro P Q he
  apply Subtype.ext
  apply Subtype.ext
  exact mul_left_cancel₀ (graphEquation_ne_zero a b) (congrArg (fun P => P.val.val) he)

theorem restrictionMap_kernel (J : Ideal (PlaneRing K)) (a b : K)
    (hregular : J.colon {graphEquation a b} = J) (d : ℕ) :
    LinearMap.ker (restrictionMap J a b (d + 1)) = LinearMap.range (idealMultiplication J a b d) := by
  ext P
  constructor
  · intro hP
    have hz := LinearMap.mem_ker.mp hP
    change graphRestriction a b P.val.val = 0 at hz
    obtain ⟨Q, hQ⟩ := (graphRestriction_zero_iff_dvd a b P.val.val).mp hz
    have hQhom : Q.IsHomogeneous d :=
      Cylinder.HomogeneousDivision.quotient_isHomogeneous (graphEquation a b) P.val.val Q 1 d
        (graphEquation_ne_zero a b) (graphEquation_homogeneous a b)
        (by
          have hh : P.val.val.IsHomogeneous (d + 1) := P.val.property
          simpa only [Nat.add_comm] using hh) hQ.symm
    have hQJ : Q ∈ J := by
      rw [← hregular, Submodule.mem_colon_singleton, smul_eq_mul, mul_comm Q, ← hQ]
      exact P.property
    exact ⟨⟨⟨Q, hQhom⟩, hQJ⟩, Subtype.ext (Subtype.ext hQ.symm)⟩
  · rintro ⟨Q, rfl⟩
    apply LinearMap.mem_ker.mpr
    change graphRestriction a b (graphEquation a b * Q.val.val) = 0
    rw [map_mul, graphRestriction_equation, zero_mul]

set_option backward.isDefEq.respectTransparency false in
theorem restriction_dimension (J : Ideal (PlaneRing K)) (a b : K)
    (hregular : J.colon {graphEquation a b} = J) (d : ℕ) :
    finrank K (restrictionSpace J a b (d + 1)) + finrank K (Cylinder.PlanePlateau.piece J d) =
      finrank K (Cylinder.PlanePlateau.piece J (d + 1)) := by
  have hr := LinearMap.finrank_range_add_finrank_ker (K := K) (restrictionMap J a b (d + 1))
  rw [restrictionMap_range, restrictionMap_kernel J a b hregular,
    LinearMap.finrank_range_of_inj (idealMultiplication_injective J a b d), idealForms_finrank,
    idealForms_finrank] at hr
  exact hr

/-- The actual restriction rank is complementary to the true Hilbert first difference. -/
theorem restriction_rank_add_firstDifference (J : Ideal (PlaneRing K)) (a b : K)
    (hregular : J.colon {graphEquation a b} = J) (d : ℕ) :
    finrank K (restrictionSpace J a b (d + 1)) +
      firstDifference (Cylinder.PlanePlateau.quotientHilbert J) (d + 1) = d + 2 := by
  have hres := restriction_dimension J a b hregular d
  have h0 := Cylinder.PlanePlateau.quotient_dimension J d
  have h1 := Cylinder.PlanePlateau.quotient_dimension J (d + 1)
  have hforms := forms_rank_succ (K := K) d
  have hbound := (Submodule.finrank_mono (restrictionSpace_homogeneous J a b (d + 1)))
  rw [binaryForms_finrank] at hbound
  change finrank K (restrictionSpace J a b (d + 1)) +
    (Cylinder.PlanePlateau.quotientHilbert J (d + 1) - Cylinder.PlanePlateau.quotientHilbert J d) = d + 2
  omega

theorem restriction_expansion_le (J : Ideal (PlaneRing K)) (a b : K) (d : ℕ) :
    Cylinder.BinaryFormLemma.expansion (restrictionSpace J a b d) ≤ restrictionSpace J a b (d + 1) := by
  have hmul (j : Fin 2) : (restrictionSpace J a b d).map (Cylinder.BinaryFormLemma.mulVar j) ≤
      restrictionSpace J a b (d + 1) := by
    intro F hF
    obtain ⟨G, hG, rfl⟩ := Submodule.mem_map.mp hF
    obtain ⟨P, hP, hPI, hPG⟩ := (mem_restrictionSpace J a b d G).mp hG
    apply (mem_restrictionSpace J a b (d + 1) _).mpr
    refine ⟨X j.succ * P, ?_, J.mul_mem_left _ hPI, ?_⟩
    · convert (isHomogeneous_X K j.succ).mul hP using 1; omega
    · rw [map_mul, graphRestriction_X_succ, hPG]
      rfl
  exact sup_le (hmul 0) (hmul 1)

end Cylinder.PlaneIdealRestriction
end
