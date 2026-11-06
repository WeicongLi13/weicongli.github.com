import NSDensity.CodeSemantics

namespace NSDensity.Concrete

variable {F E : Type*} [Field F] [Field E] [Algebra F E]

/-- Replace the abstract coefficient field by its image in the ambient field. -/
noncomputable def coefficientEquiv : F ≃+* (algebraMap F E).fieldRange :=
  (algebraMap F E).rangeRestrictFieldEquiv

@[simp] theorem coefficientEquiv_coe (x : F) :
    (coefficientEquiv (E := E) x : E) = algebraMap F E x := rfl

noncomputable def functionalToCoefficientImage (φ : E →ₗ[F] F) :
    E →ₗ[(algebraMap F E).fieldRange] (algebraMap F E).fieldRange where
  toFun x := coefficientEquiv (E := E) (φ x)
  map_add' x y := by simp
  map_smul' r x := by
    obtain ⟨s, rfl⟩ := (coefficientEquiv (F := F) (E := E)).surjective r
    change coefficientEquiv (E := E) (φ ((algebraMap F E s) * x)) = _
    rw [← Algebra.smul_def, map_smul]
    exact map_mul (coefficientEquiv (E := E)) s (φ x)

noncomputable def functionalFromCoefficientImage
    (φ : E →ₗ[(algebraMap F E).fieldRange] (algebraMap F E).fieldRange) : E →ₗ[F] F where
  toFun x := (coefficientEquiv (E := E)).symm (φ x)
  map_add' x y := by simp
  map_smul' r x := by
    apply (coefficientEquiv (E := E)).injective
    simp only [RingEquiv.apply_symm_apply, RingHom.id_apply, smul_eq_mul, map_mul]
    have hs : r • x = coefficientEquiv (E := E) r • x := by
      simp only [Algebra.smul_def]
      rfl
    rw [hs, φ.map_smul]
    simp only [smul_eq_mul]

theorem mem_functionalCode_coefficient_image {I : Type*} (v : I → E) (c : I → F) :
    c ∈ functionalCodeOver (F := F) v ↔
      (fun i => coefficientEquiv (E := E) (c i)) ∈
        functionalCode (algebraMap F E).fieldRange v := by
  constructor
  · rintro ⟨φ, rfl⟩
    exact ⟨functionalToCoefficientImage φ, rfl⟩
  · rintro ⟨φ, hφ⟩
    refine ⟨functionalFromCoefficientImage φ, ?_⟩
    funext i
    apply (coefficientEquiv (E := E)).injective
    simpa [functionalFromCoefficientImage, functionalEvaluationOver,
      functionalEvaluation] using congrFun hφ i

/-- Coordinate permutations commute with the coefficient-field identification. -/
theorem preserves_functionalCode_coefficient_image {I : Type*} [Fintype I]
    (v : I → E) (σ : Equiv.Perm I) :
    (∀ c : I → F, c ∈ functionalCodeOver (F := F) v ↔
      (c ∘ σ) ∈ functionalCodeOver (F := F) v) ↔
      preservesCode (algebraMap F E).fieldRange
        (functionalCode (algebraMap F E).fieldRange v) σ := by
  constructor
  · intro h c
    let d : I → F := fun i => (coefficientEquiv (E := E)).symm (c i)
    have hd : (fun i => coefficientEquiv (E := E) (d i)) = c := by
      funext i; exact RingEquiv.apply_symm_apply _ _
    have hdσ : (fun i => coefficientEquiv (E := E) ((d ∘ σ) i)) = c ∘ σ := by
      funext i; exact RingEquiv.apply_symm_apply _ _
    rw [← hd, ← mem_functionalCode_coefficient_image]
    have hh := h d
    rw [mem_functionalCode_coefficient_image v (d ∘ σ), hdσ] at hh
    simpa only [hd] using hh
  · intro h c
    rw [mem_functionalCode_coefficient_image, mem_functionalCode_coefficient_image]
    exact h _

#print axioms mem_functionalCode_coefficient_image
#print axioms preserves_functionalCode_coefficient_image

/-- Changing the finite extension by an algebra isomorphism changes no words. -/
theorem functionalCodeOver_algEquiv {K : Type*} [Field K] [Algebra F K]
    {I : Type*} (e : E ≃ₐ[F] K) (v : I → E) :
    functionalCodeOver (F := F) (fun i => e (v i)) = functionalCodeOver (F := F) v :=
  functionalCodeOver_embedding e.toLinearMap e.injective v

theorem rootFunctionalCodeOver_algEquiv {K : Type*} [Field K] [Algebra F K]
    (e : E ≃ₐ[F] K) (n : ℕ) (a : E) :
    functionalCodeOver (F := F) (fun i : Fin n => (e a) ^ i.val) =
      functionalCodeOver (F := F) (fun i : Fin n => a ^ i.val) := by
  simpa only [map_pow] using functionalCodeOver_algEquiv e (fun i : Fin n => a ^ i.val)

#print axioms rootFunctionalCodeOver_algEquiv

end NSDensity.Concrete
