module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Tactic.Push

/-!
# The geometric statement of the strong cylinder conjecture

The definitions in this file use finite sets of actual coordinate vectors.
In particular, `IsCylinder` means an exact union of `p` pairwise disjoint
affine lines with a common nonzero direction.  Defining the conjecture does
not prove it.  The lemmas below are elementary facts about this model.
-/

@[expose] public section

namespace Cylinder.Geometry

open scoped BigOperators

variable (p : ℕ) [Fact p.Prime]

/-- The affine three-space over the prime field. -/
abbrev Point := Fin 3 → ZMod p

/-- The coordinate pairing used to describe affine planes. -/
def pairing (a x : Point p) : ZMod p := ∑ i, a i * x i

/-- The plane with normal `a` and constant term `b`.
The normal is required to be nonzero in the divisibility condition below. -/
def affinePlane (a : Point p) (b : ZMod p) : Finset (Point p) :=
  Finset.univ.filter (fun x => pairing p a x = b)

/-- A line consists of the points `base + t • direction`, for `t` in the field. -/
def affineLine (base direction : Point p) : Finset (Point p) :=
  Finset.univ.image (fun t : ZMod p => base + t • direction)

/-- Every affine plane meets the point set in a multiple of `p`. -/
def PDivisible (S : Finset (Point p)) : Prop :=
  ∀ a : Point p, a ≠ 0 → ∀ b : ZMod p,
    p ∣ (S.filter (fun x => pairing p a x = b)).card

/-- An exact union of `p` pairwise disjoint lines with one common direction. -/
def IsCylinder (S : Finset (Point p)) : Prop :=
  ∃ direction : Point p, direction ≠ 0 ∧
    ∃ base : Fin p → Point p,
      Pairwise (fun i j =>
        Disjoint (affineLine p (base i) direction)
          (affineLine p (base j) direction)) ∧
      S = Finset.univ.biUnion (fun i => affineLine p (base i) direction)

/-- The assertion requiring a proof for the selected prime `p`. -/
def StrongCylinderConjecture : Prop :=
  ∀ S : Finset (Point p), S.card = p ^ 2 → PDivisible p S → IsCylinder p S

@[simp] theorem mem_affinePlane (a x : Point p) (b : ZMod p) :
    x ∈ affinePlane p a b ↔ pairing p a x = b := by
  simp [affinePlane]

@[simp] theorem mem_affineLine (base direction x : Point p) :
    x ∈ affineLine p base direction ↔
      ∃ t : ZMod p, base + t • direction = x := by
  simp [affineLine]

theorem base_mem_affineLine (base direction : Point p) :
    base ∈ affineLine p base direction := by
  rw [mem_affineLine]
  exact ⟨0, by simp⟩

theorem nonzero_coordinate {v : Point p} (hv : v ≠ 0) :
    ∃ i : Fin 3, v i ≠ 0 := by
  by_contra h
  push Not at h
  apply hv
  funext i
  exact h i

@[simp] theorem pairing_zero (a : Point p) : pairing p a 0 = 0 := by
  simp [pairing]

theorem pairing_add (a x y : Point p) :
    pairing p a (x + y) = pairing p a x + pairing p a y := by
  simp [pairing, mul_add, Finset.sum_add_distrib]

theorem pairing_smul (a x : Point p) (t : ZMod p) :
    pairing p a (t • x) = t * pairing p a x := by
  simp [pairing, mul_left_comm, Finset.mul_sum]

@[simp] theorem pairing_single (a : Point p) (i : Fin 3) :
    pairing p a (Pi.single i 1) = a i := by
  simp [pairing, Pi.single_apply]

/-- A nonzero normal defines a nonzero linear functional. -/
theorem nonzero_normal_pairing {a : Point p} (ha : a ≠ 0) :
    ∃ x : Point p, pairing p a x ≠ 0 := by
  obtain ⟨i, hi⟩ := nonzero_coordinate p ha
  exact ⟨Pi.single i 1, by simpa using hi⟩

theorem pairing_on_line (a base direction : Point p) (t : ZMod p) :
    pairing p a (base + t • direction) =
      pairing p a base + t * pairing p a direction := by
  rw [pairing_add, pairing_smul]

theorem line_parameter_injective (base : Point p) {direction : Point p}
    (hd : direction ≠ 0) :
    Function.Injective (fun t : ZMod p => base + t • direction) := by
  obtain ⟨i, hi⟩ := nonzero_coordinate p hd
  intro s t h
  have hcoord := congrFun h i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hcoord
  exact mul_right_cancel₀ hi (add_left_cancel hcoord)

theorem affineLine_card (base : Point p) {direction : Point p}
    (hd : direction ≠ 0) :
    (affineLine p base direction).card = p := by
  rw [affineLine, Finset.card_image_of_injective _
    (line_parameter_injective p base hd)]
  simp

theorem cylinder_exact_membership {S : Finset (Point p)} (hS : IsCylinder p S) :
    ∃ direction : Point p, direction ≠ 0 ∧
      ∃ base : Fin p → Point p,
        Pairwise (fun i j =>
          Disjoint (affineLine p (base i) direction)
            (affineLine p (base j) direction)) ∧
        ∀ x : Point p, x ∈ S ↔
          ∃ i : Fin p, ∃ t : ZMod p, base i + t • direction = x := by
  obtain ⟨direction, hd, base, hdisjoint, hUnion⟩ := hS
  refine ⟨direction, hd, base, hdisjoint, ?_⟩
  intro x
  rw [hUnion]
  simp [mem_affineLine]

end Cylinder.Geometry
