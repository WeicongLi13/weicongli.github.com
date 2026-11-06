module

public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.LinearAlgebra.Finsupp.Supported
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.FinCases

/-! The homogeneous Laurent pieces used by the three standard charts
of the projective plane, and an explicit primitive for every degree-v
one-cocycle. These are genuine Laurent polynomials; no identification
with Ext-defined sheaf cohomology is made here. -/

@[expose] public section
noncomputable section
open scoped Classical

namespace Cylinder.PlaneLaurentPieces

set_option autoImplicit false

abbrev Exponent := Fin 3 → ℤ
/-- The coefficient module of Laurent polynomials in three variables. -/
abbrev Laurent (K : Type*) [Zero K] := Exponent →₀ K

def totalDegree (a : Exponent) : ℤ := a 0 + a 1 + a 2

/-- Inverting the coordinates in I allows negative exponents exactly
at those coordinates. All monomials have total degree v. -/
def Allowed (v : ℤ) (I : Finset (Fin 3)) (a : Exponent) : Prop :=
  totalDegree a = v ∧ ∀ i, i ∉ I → 0 ≤ a i

variable {K : Type*} [CommRing K]

/-- This coefficient module is the actual additive module of the
three-variable Laurent group algebra. -/
def coefficientEquiv : AddMonoidAlgebra K Exponent ≃ₗ[K] Laurent K :=
  AddMonoidAlgebra.coeffLinearEquiv K

def piece (v : ℤ) (I : Finset (Fin 3)) : Submodule K (Laurent K) :=
  Finsupp.supported K K {a | Allowed v I a}

theorem mem_piece_iff (v : ℤ) (I : Finset (Fin 3)) (f : Laurent K) :
    f ∈ piece v I ↔ ∀ a, f a ≠ 0 → Allowed v I a := by
  change (↑f.support : Set Exponent) ⊆ {a | Allowed v I a} ↔ _
  constructor
  · intro hf a ha
    exact hf (Finsupp.mem_support_iff.mpr ha)
  · intro hf a ha
    exact hf a (Finsupp.mem_support_iff.mp ha)

theorem coeff_zero_of_negative {v : ℤ} {I : Finset (Fin 3)} {f : Laurent K}
    (hf : f ∈ piece v I) (a : Exponent) (i : Fin 3) (hi : i ∉ I)
    (ha : a i < 0) : f a = 0 := by
  by_contra h
  have hn := ((mem_piece_iff v I f).mp hf a h).2 i hi
  omega

theorem piece_mono (v : ℤ) {I J : Finset (Fin 3)} (hIJ : I ⊆ J) :
    (piece (K := K) v I) ≤ piece v J := by
  intro f hf
  apply (mem_piece_iff v J f).mpr
  intro a ha
  obtain ⟨hd, hn⟩ := (mem_piece_iff v I f).mp hf a ha
  exact ⟨hd, fun i hi => hn i (fun h => hi (hIJ h))⟩

theorem cycle_coeff {f₀₁ f₀₂ f₁₂ : Laurent K} (h : f₁₂ - f₀₂ + f₀₁ = 0)
    (a : Exponent) : f₁₂ a - f₀₂ a + f₀₁ a = 0 := by
  exact congrArg (fun f : Laurent K => f a) h

theorem negative_zero_agrees {v : ℤ} {f₀₁ f₀₂ f₁₂ : Laurent K}
    (h₁₂ : f₁₂ ∈ piece v {1, 2}) (hc : f₁₂ - f₀₂ + f₀₁ = 0)
    (a : Exponent) (ha : a 0 < 0) : f₀₂ a = f₀₁ a := by
  have hz := coeff_zero_of_negative h₁₂ a 0 (by simp) ha
  have h := cycle_coeff hc a
  have he : f₀₁ a - f₀₂ a = 0 := by
    simpa [hz, sub_eq_add_neg, add_comm] using h
  exact (sub_eq_zero.mp he).symm

theorem double_negative_zero {v : ℤ} {f₀₁ f₀₂ f₁₂ : Laurent K}
    (h₀₂ : f₀₂ ∈ piece v {0, 2}) (h₁₂ : f₁₂ ∈ piece v {1, 2})
    (hc : f₁₂ - f₀₂ + f₀₁ = 0) (a : Exponent)
    (ha₀ : a 0 < 0) (ha₁ : a 1 < 0) : f₀₁ a = 0 := by
  have hz₀₂ := coeff_zero_of_negative h₀₂ a 1 (by simp) ha₁
  have hz₁₂ := coeff_zero_of_negative h₁₂ a 0 (by simp) ha₀
  simpa [hz₀₂, hz₁₂] using cycle_coeff hc a

/-- The part of a Laurent polynomial with a pole in the first coordinate. -/
def polePart (f : Laurent K) : Laurent K := f.filter (fun a => a 0 < 0)

theorem polePart_apply (f : Laurent K) (a : Exponent) :
    polePart f a = if a 0 < 0 then f a else 0 := rfl

theorem polePart_mem_first {v : ℤ} {f₀₁ f₀₂ f₁₂ : Laurent K}
    (h₀₁ : f₀₁ ∈ piece v {0, 1}) (h₀₂ : f₀₂ ∈ piece v {0, 2})
    (h₁₂ : f₁₂ ∈ piece v {1, 2}) (hc : f₁₂ - f₀₂ + f₀₁ = 0) :
    polePart f₀₁ ∈ piece v {0} := by
  apply (mem_piece_iff v {0} _).mpr
  intro a ha
  by_cases hneg : a 0 < 0
  · have hne : f₀₁ a ≠ 0 := by simpa [polePart_apply, hneg] using ha
    obtain ⟨hd, hn⟩ := (mem_piece_iff v {0, 1} _).mp h₀₁ a hne
    have ha₁ : 0 ≤ a 1 := by
      by_contra h
      exact hne (double_negative_zero h₀₂ h₁₂ hc a hneg (by omega))
    refine ⟨hd, ?_⟩
    intro i hi
    fin_cases i
    · simp at hi
    · exact ha₁
    · exact hn 2 (by simp)
  · simp [polePart_apply, hneg] at ha

theorem remainder_mem_second {v : ℤ} {f₀₁ : Laurent K}
    (h₀₁ : f₀₁ ∈ piece v {0, 1}) : f₀₁ - polePart f₀₁ ∈ piece v {1} := by
  apply (mem_piece_iff v {1} _).mpr
  intro a ha
  by_cases hneg : a 0 < 0
  · simp [Finsupp.sub_apply, polePart_apply, hneg] at ha
  · have hne : f₀₁ a ≠ 0 := by
      simpa [Finsupp.sub_apply, polePart_apply, hneg] using ha
    obtain ⟨hd, hn⟩ := (mem_piece_iff v {0, 1} _).mp h₀₁ a hne
    refine ⟨hd, ?_⟩
    intro i hi
    fin_cases i
    · change 0 ≤ a 0
      omega
    · simp at hi
    · exact hn 2 (by simp)

theorem adjusted_mem_third {v : ℤ} {f₀₁ f₀₂ f₁₂ : Laurent K}
    (h₀₂ : f₀₂ ∈ piece v {0, 2}) (h₁₂ : f₁₂ ∈ piece v {1, 2})
    (hc : f₁₂ - f₀₂ + f₀₁ = 0) : f₀₂ - polePart f₀₁ ∈ piece v {2} := by
  apply (mem_piece_iff v {2} _).mpr
  intro a ha
  by_cases hneg : a 0 < 0
  · have he := negative_zero_agrees h₁₂ hc a hneg
    simp [Finsupp.sub_apply, polePart_apply, hneg, he] at ha
  · have hne : f₀₂ a ≠ 0 := by
      simpa [Finsupp.sub_apply, polePart_apply, hneg] using ha
    obtain ⟨hd, hn⟩ := (mem_piece_iff v {0, 2} _).mp h₀₂ a hne
    refine ⟨hd, ?_⟩
    intro i hi
    fin_cases i
    · change 0 ≤ a 0
      omega
    · exact hn 1 (by simp)
    · simp at hi

/-- An explicit primitive for every one-cocycle in the standard
degree-v Laurent model, for every integer v. -/
theorem one_cocycle_has_primitive (v : ℤ) (f₀₁ f₀₂ f₁₂ : Laurent K)
    (h₀₁ : f₀₁ ∈ piece v {0, 1}) (h₀₂ : f₀₂ ∈ piece v {0, 2})
    (h₁₂ : f₁₂ ∈ piece v {1, 2}) (hc : f₁₂ - f₀₂ + f₀₁ = 0) :
    ∃ (s₀ : piece (K := K) v {0}) (s₁ : piece (K := K) v {1})
      (s₂ : piece (K := K) v {2}),
      f₀₁ = s₁.val - s₀.val ∧ f₀₂ = s₂.val - s₀.val ∧ f₁₂ = s₂.val - s₁.val := by
  refine ⟨⟨-polePart f₀₁, (piece (K := K) v {0}).neg_mem (polePart_mem_first h₀₁ h₀₂ h₁₂ hc)⟩,
    ⟨f₀₁ - polePart f₀₁, remainder_mem_second h₀₁⟩,
    ⟨f₀₂ - polePart f₀₁, adjusted_mem_third h₀₂ h₁₂ hc⟩, ?_, ?_, ?_⟩
  · change f₀₁ = (f₀₁ - polePart f₀₁) - -polePart f₀₁
    abel
  · change f₀₂ = (f₀₂ - polePart f₀₁) - -polePart f₀₁
    abel
  · change f₁₂ = (f₀₂ - polePart f₀₁) - (f₀₁ - polePart f₀₁)
    apply sub_eq_zero.mp
    calc
      f₁₂ - ((f₀₂ - polePart f₀₁) - (f₀₁ - polePart f₀₁)) = f₁₂ - f₀₂ + f₀₁ := by abel
      _ = 0 := hc

end Cylinder.PlaneLaurentPieces

end
