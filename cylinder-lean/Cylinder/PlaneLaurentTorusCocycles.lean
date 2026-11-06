module

public import Cylinder.PlaneLaurentCommonTorus

/-! A cocycle identity in the actual common torus has the same
homogeneous coefficient identity. Its primitive therefore comes from
the three genuine single-coordinate Laurent pieces. -/

@[expose] public section
noncomputable section
open scoped Classical
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Cylinder.PlaneLaurentTorusCocycles

open Cylinder.PlaneLaurentPieces Cylinder.PlaneLaurentCommonTorus

variable (K : Type*) [Field K]

theorem fullInclusion_value (v : ℤ) (I : Finset (Fin 3)) (f : piece (K := K) v I) :
    commonPieceMap K v {0, 1, 2} (fullInclusion K v I f) = commonPieceMap K v I f := rfl

theorem torus_sub_of_coefficients (v : ℤ) {I J L : Finset (Fin 3)}
    (f : piece (K := K) v I) (g : piece (K := K) v J) (h : piece (K := K) v L)
    (he : f.val - g.val = h.val) :
    commonPieceMap K v I f - commonPieceMap K v J g = commonPieceMap K v L h := by
  have hv : fullInclusion K v I f = fullInclusion K v L h + fullInclusion K v J g :=
    Subtype.ext ((sub_eq_iff_eq_add).mp he)
  have hm := congrArg (commonPieceMap K v {0, 1, 2}) hv
  rw [(commonPieceMap K v {0, 1, 2}).map_add,
    fullInclusion_value, fullInclusion_value, fullInclusion_value] at hm
  exact (sub_eq_iff_eq_add).mpr hm

theorem coefficient_cocycle_of_torus (v : ℤ)
    (f₀₁ : piece (K := K) v {0, 1}) (f₀₂ : piece (K := K) v {0, 2})
    (f₁₂ : piece (K := K) v {1, 2})
    (hc : commonPieceMap K v {0, 2} f₀₂ - commonPieceMap K v {1, 2} f₁₂ =
      commonPieceMap K v {0, 1} f₀₁) :
    f₁₂.val - f₀₂.val + f₀₁.val = 0 := by
  have he : fullInclusion K v {0, 2} f₀₂ =
      fullInclusion K v {0, 1} f₀₁ + fullInclusion K v {1, 2} f₁₂ := by
    apply commonPieceMap_injective K v {0, 1, 2}
    rw [(commonPieceMap K v {0, 1, 2}).map_add,
      fullInclusion_value, fullInclusion_value, fullInclusion_value]
    exact (sub_eq_iff_eq_add).mp hc
  have hv : f₀₂.val = f₀₁.val + f₁₂.val := congrArg Subtype.val he
  rw [hv]
  abel

theorem exists_torus_primitive (v : ℤ)
    (f₀₁ : piece (K := K) v {0, 1}) (f₀₂ : piece (K := K) v {0, 2})
    (f₁₂ : piece (K := K) v {1, 2})
    (hc : commonPieceMap K v {0, 2} f₀₂ - commonPieceMap K v {1, 2} f₁₂ =
      commonPieceMap K v {0, 1} f₀₁) :
    ∃ (s₀ : piece (K := K) v {0}) (s₁ : piece (K := K) v {1})
      (s₂ : piece (K := K) v {2}),
      commonPieceMap K v {0} s₀ - commonPieceMap K v {1} s₁ = commonPieceMap K v {0, 1} f₀₁ ∧
      commonPieceMap K v {0} s₀ - commonPieceMap K v {2} s₂ = commonPieceMap K v {0, 2} f₀₂ ∧
      commonPieceMap K v {1} s₁ - commonPieceMap K v {2} s₂ = commonPieceMap K v {1, 2} f₁₂ := by
  obtain ⟨s₀, s₁, s₂, h₀₁, h₀₂, h₁₂⟩ := one_cocycle_has_primitive v
    f₀₁.val f₀₂.val f₁₂.val f₀₁.property f₀₂.property f₁₂.property
      (coefficient_cocycle_of_torus K v f₀₁ f₀₂ f₁₂ hc)
  refine ⟨-s₀, -s₁, -s₂, ?_, ?_, ?_⟩
  all_goals apply torus_sub_of_coefficients
  · change -s₀.val - -s₁.val = f₀₁.val
    rw [h₀₁]
    abel
  · change -s₀.val - -s₂.val = f₀₂.val
    rw [h₀₂]
    abel
  · change -s₁.val - -s₂.val = f₁₂.val
    rw [h₁₂]
    abel

end Cylinder.PlaneLaurentTorusCocycles

end
