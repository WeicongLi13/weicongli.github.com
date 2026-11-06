module

public import Cylinder.PlaneLaurentCech

/-! The kernel in degree zero of the actual Laurent chart complex is
the polynomial Laurent piece: all exponents are nonnegative. This is an
algebraic kernel calculation, not a definition of sheaf cohomology. -/

@[expose] public section
noncomputable section
open scoped Classical
set_option autoImplicit false

namespace Cylinder.PlaneLaurentH0

open Cylinder.PlaneLaurentPieces Cylinder.PlaneLaurentCech

variable {K : Type*} [CommRing K]

theorem compatible_first_second (v : ℤ) (s : LinearMap.ker (differentialZero (K := K) v)) :
    s.val.2.1.val = s.val.1.val := by
  have he := congrArg (fun t : OneCochains (K := K) v => t.1.val)
    (LinearMap.mem_ker.mp s.property)
  change s.val.2.1.val - s.val.1.val = 0 at he
  exact sub_eq_zero.mp he

theorem compatible_first_third (v : ℤ) (s : LinearMap.ker (differentialZero (K := K) v)) :
    s.val.2.2.val = s.val.1.val := by
  have he := congrArg (fun t : OneCochains (K := K) v => t.2.1.val)
    (LinearMap.mem_ker.mp s.property)
  change s.val.2.2.val - s.val.1.val = 0 at he
  exact sub_eq_zero.mp he

theorem compatible_has_no_poles (v : ℤ) (s : LinearMap.ker (differentialZero (K := K) v)) :
    s.val.1.val ∈ piece (K := K) v ∅ := by
  apply (mem_piece_iff v ∅ _).mpr
  intro a ha
  have h0 := (mem_piece_iff v {0} _).mp s.val.1.property a ha
  have h1 := (mem_piece_iff v {1} _).mp s.val.2.1.property a
    (by rw [compatible_first_second]; exact ha)
  refine ⟨h0.1, fun i _ => ?_⟩
  by_cases hi : i = 0
  · subst i
    exact h1.2 0 (by decide)
  · exact h0.2 i (by simpa using hi)

def diagonal (v : ℤ) (f : piece (K := K) v ∅) :
    LinearMap.ker (differentialZero (K := K) v) :=
  ⟨(⟨f.val, piece_mono v (by simp) f.property⟩,
    ⟨f.val, piece_mono v (by simp) f.property⟩,
    ⟨f.val, piece_mono v (by simp) f.property⟩), by
      apply LinearMap.mem_ker.mpr
      apply Prod.ext
      · exact Subtype.ext (sub_self f.val)
      · apply Prod.ext
        · exact Subtype.ext (sub_self f.val)
        · exact Subtype.ext (sub_self f.val)⟩

def globalPieceEquivKernel (v : ℤ) :
    piece (K := K) v ∅ ≃ₗ[K] LinearMap.ker (differentialZero (K := K) v) where
  toFun := diagonal v
  invFun s := ⟨s.val.1.val, compatible_has_no_poles v s⟩
  left_inv _ := rfl
  right_inv s := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · apply Prod.ext
      · exact Subtype.ext (compatible_first_second v s).symm
      · exact Subtype.ext (compatible_first_third v s).symm
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem globalPiece_eq_bot_of_negative (v : ℤ) (hv : v < 0) :
    piece (K := K) v ∅ = ⊥ := by
  apply le_antisymm
  · intro f hf
    change f = 0
    apply Finsupp.ext
    intro a
    by_contra ha
    have h := (mem_piece_iff v ∅ f).mp hf a ha
    have h0 := h.2 0 (by simp)
    have h1 := h.2 1 (by simp)
    have h2 := h.2 2 (by simp)
    have hd := h.1
    dsimp [totalDegree] at hd
    omega
  · exact bot_le

end Cylinder.PlaneLaurentH0
end
