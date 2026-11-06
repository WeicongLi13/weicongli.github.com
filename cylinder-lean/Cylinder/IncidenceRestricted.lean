module

public import Cylinder.IncidenceDoubleCount

/-!
# Incidence sums over an actual finite set of planes
-/

@[expose] public section

noncomputable section

namespace Cylinder.IncidenceRestricted

open scoped BigOperators Classical

variable {A B : Type*}

theorem sum_card_on (R : A → B → Prop) (S : Finset A) (T : Finset B) :
    (∑ H ∈ T, (S.filter (fun x => R x H)).card) =
      ∑ x ∈ S, (T.filter (R x)).card := by
  have hcard (H : B) : (S.filter (fun x => R x H)).card =
      ∑ x ∈ S, if R x H then 1 else 0 := by
    simp only [Finset.sum_boole, Nat.cast_id]
  simp_rw [hcard]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  simp only [Finset.sum_boole, Nat.cast_id]

end Cylinder.IncidenceRestricted

end
