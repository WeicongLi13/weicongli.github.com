import NSDensity.ConcreteDescent
import NSDensity.CodeModelColumns
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
The generator-matrix code associated with root columns, and its dual.
The generator code is the range of all linear functionals on the column
space. This description is independent of a basis or a choice of trace.
-/

open scoped BigOperators

namespace NSDensity.Concrete

variable {E : Type*} [Field E] {I : Type*} [Fintype I]

/-- The row-vector obtained by applying a linear functional to all columns. -/
def functionalEvaluation (F : Subfield E) (v : I → E) :
    (E →ₗ[F] F) →ₗ[F] (I → F) where
  toFun φ i := φ (v i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [Fintype I] in
@[simp]
theorem functionalEvaluation_apply (F : Subfield E) (v : I → E)
    (φ : E →ₗ[F] F) (i : I) : functionalEvaluation F v φ i = φ (v i) := rfl

/-- The concrete generator-matrix code with columns `v i`. -/
def functionalCode (F : Subfield E) (v : I → E) : Submodule F (I → F) :=
  LinearMap.range (functionalEvaluation F v)

omit [Fintype I] in
theorem mem_functionalCode (F : Subfield E) (v : I → E) (w : I → F) :
    w ∈ functionalCode F v ↔ ∃ φ : E →ₗ[F] F, ∀ i, φ (v i) = w i := by
  constructor
  · rintro ⟨φ, rfl⟩
    exact ⟨φ, fun _ => rfl⟩
  · rintro ⟨φ, hφ⟩
    exact ⟨φ, funext hφ⟩

private theorem functional_sum (F : Subfield E) (v : I → E) (c : I → F)
    (φ : E →ₗ[F] F) :
    φ (∑ i, (c i : E) * v i) = ∑ i, c i * φ (v i) := by
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  change φ (c i • v i) = c i • φ (v i)
  exact map_smul φ (c i) (v i)

/-- The root-relation code is exactly the ordinary dot-product dual of the
generator-matrix code. Thus it is not an extra abstract exceptional set. -/
theorem mem_relationCode_iff_orthogonal_functionalCode
    (F : Subfield E) (v : I → E) (c : I → F) :
    c ∈ relationCode F v ↔
      ∀ w ∈ functionalCode F v, ∑ i, c i * w i = 0 := by
  rw [mem_relationCode, ← Module.forall_dual_apply_eq_zero_iff F]
  constructor
  · intro h w hw
    obtain ⟨φ, rfl⟩ := hw
    exact (functional_sum F v c φ).symm.trans (h φ)
  · intro h φ
    rw [functional_sum]
    exact h _ ⟨φ, rfl⟩

/-- Preservation of an actual linear code by a coordinate permutation. -/
def preservesCode (F : Subfield E) (C : Submodule F (I → F))
    (σ : Equiv.Perm I) : Prop :=
  ∀ c : I → F, c ∈ C ↔ (c ∘ σ) ∈ C

private theorem preservesCode_functionalCode_of_relations [Finite E]
    (F : Subfield E) (v : I → E)
    (hspan : Function.Surjective (columnEval F v)) (σ : Equiv.Perm I)
    (hσ : preservesRelations F v σ) : preservesCode F (functionalCode F v) σ := by
  obtain ⟨T, hT⟩ := exists_column_linearEquiv_apply F v hspan σ hσ
  have hTinv (i : I) : T.symm (v i) = v (σ i) := by
    apply T.injective
    rw [T.apply_symm_apply, hT]
    simp
  intro c
  constructor
  · intro hc
    obtain ⟨φ, hφ⟩ := (mem_functionalCode F v c).1 hc
    refine (mem_functionalCode F v (c ∘ σ)).2 ⟨φ.comp T.symm.toLinearMap, ?_⟩
    intro i
    change φ (T.symm (v i)) = c (σ i)
    rw [hTinv, hφ]
  · intro hc
    obtain ⟨φ, hφ⟩ := (mem_functionalCode F v (c ∘ σ)).1 hc
    refine (mem_functionalCode F v c).2 ⟨φ.comp T.toLinearMap, ?_⟩
    intro i
    change φ (T (v i)) = c i
    rw [hT, hφ]
    exact congrArg c (σ.apply_symm_apply i)

/-- A functional on the column space factors through the evaluation map
whenever it annihilates its kernel. Extending from the image removes every
spanning assumption on the chosen ambient field. -/
private theorem exists_functional_factor (F : Subfield E) (v : I → E)
    (σ : Equiv.Perm I) (hσ : preservesRelations F v σ) (φ : E →ₗ[F] F) :
    ∃ ψ : E →ₗ[F] F, ∀ c : I → F,
      ψ (columnEval F v c) = φ (columnEval F v (c ∘ σ)) := by
  let f := columnEval F v
  let g := (φ.comp f).comp (permuteCoeffs F σ)
  have hker : LinearMap.ker f.rangeRestrict ≤ LinearMap.ker g := by
    rw [LinearMap.ker_rangeRestrict]
    intro c hc
    have hc' : c ∈ relationCode F v := hc
    have hd : (c ∘ σ) ∈ relationCode F v := (hσ c).1 hc'
    change f (c ∘ σ) = 0 at hd
    change φ (f (c ∘ σ)) = 0
    rw [hd, map_zero]
  let ψ₀ : LinearMap.range f →ₗ[F] F :=
    f.rangeRestrict.liftOfSurjective
      (LinearMap.range_eq_top.mp f.range_rangeRestrict) ⟨g, hker⟩
  have hψ₀ (c : I → F) : ψ₀ (f.rangeRestrict c) = g c :=
    LinearMap.equivOfSurjective_apply _ _
  obtain ⟨ψ, hψ⟩ := ψ₀.exists_extend
  refine ⟨ψ, fun c => ?_⟩
  have hh := LinearMap.congr_fun hψ (f.rangeRestrict c)
  exact hh.trans (hψ₀ c)

private theorem preservesCode_functionalCode_of_relations_general
    (F : Subfield E) (v : I → E) (σ : Equiv.Perm I)
    (hσ : preservesRelations F v σ) : preservesCode F (functionalCode F v) σ := by
  classical
  have hfwd {τ : Equiv.Perm I} (hτ : preservesRelations F v τ)
      {c : I → F} (hc : c ∈ functionalCode F v) :
      (c ∘ τ.symm) ∈ functionalCode F v := by
    obtain ⟨φ, hφ⟩ := (mem_functionalCode F v c).1 hc
    obtain ⟨ψ, hψ⟩ := exists_functional_factor F v τ hτ φ
    refine (mem_functionalCode F v (c ∘ τ.symm)).2 ⟨ψ, fun i => ?_⟩
    have hh := hψ (Pi.single i 1)
    rw [columnEval_single, columnEval_permute] at hh
    change ψ (v i) = φ (columnEval F (fun j => v (τ.symm j)) (Pi.single i 1)) at hh
    rw [columnEval_single] at hh
    exact hh.trans (hφ (τ.symm i))
  have hσinv : preservesRelations F v σ.symm := by
    intro c
    simpa [Function.comp_def] using (hσ (c ∘ σ.symm)).symm
  intro c
  constructor
  · intro hc
    simpa using hfwd hσinv hc
  · intro hc
    simpa [Function.comp_def] using hfwd hσ hc

private theorem preservesRelations_of_functionalCode
    (F : Subfield E) (v : I → E) (σ : Equiv.Perm I)
    (hσ : preservesCode F (functionalCode F v) σ) : preservesRelations F v σ := by
  have hfwd {τ : Equiv.Perm I}
      (hτ : preservesCode F (functionalCode F v) τ)
      {c : I → F} (hc : c ∈ relationCode F v) : (c ∘ τ) ∈ relationCode F v := by
    rw [mem_relationCode_iff_orthogonal_functionalCode] at hc ⊢
    intro w hw
    have hw' : (w ∘ τ.symm) ∈ functionalCode F v := by
      apply (hτ (w ∘ τ.symm)).2
      simpa [Function.comp_def] using hw
    have hsum := hc (w ∘ τ.symm) hw'
    have hreindex := Equiv.sum_comp τ (fun i : I => c i * w (τ.symm i))
    simpa [Function.comp_def] using hreindex.trans hsum
  intro c
  constructor
  · exact hfwd hσ
  · intro hc
    have hσinv : preservesCode F (functionalCode F v) σ.symm := by
      intro w
      simpa [Function.comp_def] using (hσ (w ∘ σ.symm)).symm
    simpa [Function.comp_def] using hfwd hσinv hc

/-- A code and its root-relation dual have exactly the same permutation
automorphisms. The spanning condition states that the chosen columns
generate their ambient column space. -/
theorem preservesRelations_iff_preserves_functionalCode [Finite E]
    (F : Subfield E) (v : I → E)
    (hspan : Function.Surjective (columnEval F v)) (σ : Equiv.Perm I) :
    preservesRelations F v σ ↔ preservesCode F (functionalCode F v) σ :=
  ⟨preservesCode_functionalCode_of_relations F v hspan σ,
    preservesRelations_of_functionalCode F v σ⟩

/-- Ambient-independent duality for permutation automorphism groups. -/
theorem preservesRelations_iff_preserves_functionalCode_general
    (F : Subfield E) (v : I → E) (σ : Equiv.Perm I) :
    preservesRelations F v σ ↔ preservesCode F (functionalCode F v) σ :=
  ⟨preservesCode_functionalCode_of_relations_general F v σ,
    preservesRelations_of_functionalCode F v σ⟩

end NSDensity.Concrete
