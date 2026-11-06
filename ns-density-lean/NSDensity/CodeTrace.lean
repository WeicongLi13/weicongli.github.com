import NSDensity.CodePolynomial
import NSDensity.ConcreteCyclic
import Mathlib.RingTheory.Trace.Basic

/-! The finite-field trace description of the actual generator code.
The final inverse-root identity matches the negative-power convention in
the paper without making any unproved identification of reciprocal
check polynomials. -/

namespace NSDensity.Concrete

variable {E : Type*} [Field E] [Finite E] {I : Type*} [Fintype I]

/-- Every linear functional on a finite field extension is a trace pairing
with a field element; this is a proved theorem, not an input. -/
theorem exists_trace_functional (F : Subfield E) (φ : E →ₗ[F] F) :
    ∃ b : E, ∀ x : E, φ x = Algebra.trace F E (b * x) := by
  let e := (Algebra.traceForm F E).toDual (traceForm_nondegenerate F E)
  obtain ⟨b, hb⟩ := e.surjective φ
  refine ⟨b, fun x => ?_⟩
  have hx := congrArg (fun ψ : E →ₗ[F] F => ψ x) hb
  exact hx.symm

/-- The actual trace word associated with a field element and its columns. -/
noncomputable def traceEvaluation (F : Subfield E) (v : I → E) :
    E →ₗ[F] (I → F) := (functionalEvaluation F v).comp (Algebra.traceForm F E)

omit [Finite E] [Fintype I] in
@[simp]
theorem traceEvaluation_apply (F : Subfield E) (v : I → E) (b : E) (i : I) :
    traceEvaluation F v b i = Algebra.trace F E (b * v i) := rfl

/-- The finite-field trace code, as an actual linear code. -/
noncomputable def traceCode (F : Subfield E) (v : I → E) : Submodule F (I → F) :=
  LinearMap.range (traceEvaluation F v)

omit [Finite E] [Fintype I] in
theorem mem_traceCode (F : Subfield E) (v : I → E) (w : I → F) :
    w ∈ traceCode F v ↔ ∃ b : E, ∀ i : I, Algebra.trace F E (b * v i) = w i := by
  constructor
  · rintro ⟨b, rfl⟩
    exact ⟨b, fun _ => rfl⟩
  · rintro ⟨b, hb⟩
    exact ⟨b, funext hb⟩

omit [Fintype I] in
theorem functionalCode_eq_traceCode (F : Subfield E) (v : I → E) :
    functionalCode F v = traceCode F v := by
  ext w
  constructor
  · intro hw
    obtain ⟨φ, hφ⟩ := (mem_functionalCode F v w).1 hw
    obtain ⟨b, hb⟩ := exists_trace_functional F φ
    refine ⟨b, funext fun i => ?_⟩
    exact (hb (v i)).symm.trans (hφ i)
  · rintro ⟨b, rfl⟩
    exact ⟨Algebra.traceForm F E b, rfl⟩

/-- The negative-power trace convention used for the polynomial code
in the paper. -/
noncomputable def inverseRootTraceCode (F : Subfield E) (n : ℕ) (a : E) :
    Submodule F (Fin n → F) :=
  traceCode F (fun i : Fin n => a ^ (-(i.val : ℤ)))

theorem rootFunctionalCode_eq_positive_trace (F : Subfield E) (n : ℕ) (a : E) :
    rootFunctionalCode F n a = traceCode F (fun i : Fin n => a ^ i.val) :=
  functionalCode_eq_traceCode F _

/-- The positive-power generator convention and the paper's negative-power
trace convention give precisely the same code after taking the inverse
root. This is equality of code submodules, so their permutation groups
are identical. -/
theorem rootFunctionalCode_eq_inverse_trace (F : Subfield E) (n : ℕ) (a : E) :
    rootFunctionalCode F n a = inverseRootTraceCode F n a⁻¹ := by
  rw [rootFunctionalCode_eq_positive_trace]
  congr 1
  funext i
  simp [zpow_neg, zpow_natCast]

theorem inverseRootTraceCode_eq_rootFunctionalCode (F : Subfield E) (n : ℕ) (a : E) :
    inverseRootTraceCode F n a = rootFunctionalCode F n a⁻¹ := by
  simpa using (rootFunctionalCode_eq_inverse_trace F n a⁻¹).symm

/-- The inverse-root convention has exactly the same length. -/
theorem inverse_trace_root_exact_order (F : Subfield E) {n : ℕ} {a : E}
    (ha : orderOf a = n) :
    orderOf a⁻¹ = n ∧ rootFunctionalCode F n a = inverseRootTraceCode F n a⁻¹ :=
  ⟨(inverse_root_orderOf a).trans ha, rootFunctionalCode_eq_inverse_trace F n a⟩

end NSDensity.Concrete
