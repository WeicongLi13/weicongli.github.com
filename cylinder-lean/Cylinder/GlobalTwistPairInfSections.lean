module

public import Cylinder.GlobalTwistPairSections

/-! Changing between the literal intersection of two coordinate
opens and the equal basic open of their product uses actual sheaf
restriction. It preserves values and subtraction and is injective. -/

@[expose] public section
noncomputable section
open scoped Classical Cylinder.GlobalTwistChartSections
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Cylinder.GlobalTwistPairInfSections

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open Cylinder.CoordinateChartPermutation Cylinder.GlobalProjectiveTwist
open Cylinder.GlobalTwistChartFrame Cylinder.GlobalTwistPairSections

variable (K : Type*) [Field K]

def infToPair (v : ℤ) (i j : Index)
    (s : Γ(twist K v, coordinateOpen K i ⊓ coordinateOpen K j)) :
    Γ(twist K v, pairOpen K i j) :=
  (twist K v).presheaf.map (homOfLE (le_of_eq (pairOpen_eq K i j))).op s

theorem infToPair_value (v : ℤ) (i j : Index)
    (s : Γ(twist K v, coordinateOpen K i ⊓ coordinateOpen K j)) (q : pairOpen K i j) :
    (infToPair K v i j s).val q =
      s.val ⟨q.val, (le_of_eq (pairOpen_eq K i j)) q.property⟩ := rfl

theorem infToPair_injective (v : ℤ) (i j : Index) :
    Function.Injective (infToPair K v i j) := by
  intro s t he
  apply Subtype.ext
  funext q
  let q' : pairOpen K i j := ⟨q.val, by rw [pairOpen_eq]; exact q.property⟩
  exact congrArg (fun x : Γ(twist K v, pairOpen K i j) => x.val q') he

theorem infToPair_sub (v : ℤ) (i j : Index)
    (s t : Γ(twist K v, coordinateOpen K i ⊓ coordinateOpen K j)) :
    infToPair K v i j (s - t) = infToPair K v i j s - infToPair K v i j t :=
  map_sub _ s t

theorem infToPair_chart_left (v : ℤ) (i j : Index)
    (s : Γ(twist K v, coordinateOpen K i)) :
    infToPair K v i j ((twist K v).presheaf.map (homOfLE (inf_le_left :
      coordinateOpen K i ⊓ coordinateOpen K j ≤ coordinateOpen K i)).op s) =
      (twist K v).presheaf.map (homOfLE (pairOpen_le_first K i j)).op s := by
  apply Subtype.ext
  funext q
  rfl

theorem infToPair_chart_right (v : ℤ) (i j : Index)
    (s : Γ(twist K v, coordinateOpen K j)) :
    infToPair K v i j ((twist K v).presheaf.map (homOfLE (inf_le_right :
      coordinateOpen K i ⊓ coordinateOpen K j ≤ coordinateOpen K j)).op s) =
      (twist K v).presheaf.map
        (homOfLE ((le_of_eq (pairOpen_eq K i j)).trans inf_le_right)).op s := by
  apply Subtype.ext
  funext q
  rfl

end Cylinder.GlobalTwistPairInfSections

end
