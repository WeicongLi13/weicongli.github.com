module

public import Cylinder.HilbertEvaluation
public import Mathlib.LinearAlgebra.Projectivization.Basic

/-! The homogeneous evaluation model attached to an actual finite plane point set. -/

@[expose] public section
noncomputable section
open scoped Classical

namespace Cylinder.PlanePointModel

open Cylinder.HilbertEvaluation

variable {K : Type*} [Field K]

abbrev Plane (K : Type*) [Field K] := Projectivization K (Fin 3 → K)

def representatives (D : Finset (Plane K)) : D → Fin 3 → K := fun x => x.val.rep

theorem representatives_nonzero (D : Finset (Plane K)) :
    ∀ x, representatives D x ≠ 0 := fun x => x.val.rep_nonzero

theorem representatives_distinct (D : Finset (Plane K)) :
    ProjectivelyDistinct (representatives D) := by
  intro x y hxy c hrep
  apply hxy
  apply Subtype.ext
  have hproj := (Projectivization.mk_eq_mk_iff' K y.val.rep x.val.rep
    y.val.rep_nonzero x.val.rep_nonzero).mpr ⟨c, hrep.symm⟩
  simpa only [Projectivization.mk_rep] using hproj.symm

/-- Interpolation for the actual finite projective point set. -/
theorem hilbert_eq_card [Infinite K] (D : Finset (Plane K)) (d : ℕ)
    (hd : D.card - 1 ≤ d) : hilbert (representatives D) d = D.card := by
  have h := hilbert_eq_card_of_card_sub_one_le (representatives D)
    (representatives_nonzero D) (representatives_distinct D) d
  have hd' : Fintype.card D - 1 ≤ d := by simpa only [Fintype.card_coe] using hd
  simpa only [Fintype.card_coe] using h hd'

end Cylinder.PlanePointModel

end
