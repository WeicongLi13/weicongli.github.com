module

public import Cylinder.Geometry
public import Mathlib.LinearAlgebra.Projectivization.Cardinality
public import Mathlib.LinearAlgebra.Projectivization.Subspace
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-!
# Actual finite projective three-space

Points are nonzero homogeneous four-vectors modulo nonzero scalar
multiplication. Dual points are homogeneous plane equations modulo scale.
The affine embedding is the chart with first coordinate equal to one.
-/

@[expose] public section

namespace Cylinder.ProjectiveGeometry

open scoped BigOperators LinearAlgebra.Projectivization

variable (p : ℕ) [Fact p.Prime]

/-- Homogeneous coordinate vectors for projective three-space. -/
abbrev Vector := Fin 4 → ZMod p

/-- The actual finite projective three-space over the prime field. -/
abbrev PG3 := Projectivization (ZMod p) (Vector p)

/-- Dual projective points parameterize homogeneous plane equations. -/
abbrev DualPoint := Projectivization (ZMod p) (Module.Dual (ZMod p) (Vector p))

noncomputable instance : Fintype (PG3 p) := Fintype.ofFinite _
noncomputable instance : DecidableEq (PG3 p) := Classical.decEq _
instance : Finite (Module.Dual (ZMod p) (Vector p)) :=
  Finite.of_injective (fun f : Module.Dual (ZMod p) (Vector p) =>
    (f : Vector p → ZMod p)) DFunLike.coe_injective
noncomputable instance : Fintype (DualPoint p) := Fintype.ofFinite _
noncomputable instance : DecidableEq (DualPoint p) := Classical.decEq _

def pairing (a x : Vector p) : ZMod p := ∑ i, a i * x i

theorem pairing_add (a x y : Vector p) :
    pairing p a (x + y) = pairing p a x + pairing p a y := by
  simp [pairing, mul_add, Finset.sum_add_distrib]

theorem pairing_smul_right (a x : Vector p) (t : ZMod p) :
    pairing p a (t • x) = t * pairing p a x := by
  simp [pairing, mul_left_comm, Finset.mul_sum]

theorem pairing_smul_left (a x : Vector p) (t : ZMod p) :
    pairing p (t • a) x = t * pairing p a x := by
  simp [pairing, mul_assoc, Finset.mul_sum]

theorem pairing_comm (a x : Vector p) : pairing p a x = pairing p x a := by
  simp [pairing, mul_comm]

/-- A homogeneous coefficient vector defines a genuine linear functional. -/
def pairingMap (a : Vector p) : Module.Dual (ZMod p) (Vector p) where
  toFun := pairing p a
  map_add' := pairing_add p a
  map_smul' t x := by
    simpa only [smul_eq_mul, RingHom.id_apply] using pairing_smul_right p a x t

theorem pairingMap_ne_zero {a : Vector p} (ha : a ≠ 0) : pairingMap p a ≠ 0 := by
  intro h
  apply ha
  funext i
  have := LinearMap.congr_fun h (Pi.single i 1)
  simpa [pairingMap, pairing, Pi.single_apply] using this

theorem vector_eq_sum_single (x : Vector p) :
    x = ∑ i : Fin 4, x i • Pi.single i 1 := by
  funext j
  simp [Finset.sum_apply, Pi.single_apply]

theorem functional_expansion (f : Module.Dual (ZMod p) (Vector p)) (x : Vector p) :
    f x = pairing p (fun i => f (Pi.single i 1)) x := by
  calc
    f x = f (∑ i : Fin 4, x i • Pi.single i 1) :=
      congrArg f (vector_eq_sum_single p x)
    _ = ∑ i : Fin 4, x i * f (Pi.single i 1) := by simp [map_sum, map_smul, smul_eq_mul]
    _ = pairing p (fun i => f (Pi.single i 1)) x := by simp [pairing, mul_comm]

/-- Coordinate normal vectors are exactly all homogeneous plane functionals. -/
def pairingEquiv : Vector p ≃ₗ[ZMod p] Module.Dual (ZMod p) (Vector p) where
  toFun := pairingMap p
  invFun f i := f (Pi.single i 1)
  left_inv a := by
    funext i
    simp [pairingMap, pairing, Pi.single_apply]
  right_inv f := by
    apply LinearMap.ext
    intro x
    exact (functional_expansion p f x).symm
  map_add' a b := by
    apply LinearMap.ext
    intro x
    simp [pairingMap, pairing, add_mul, Finset.sum_add_distrib]
  map_smul' t a := by
    apply LinearMap.ext
    intro x
    exact pairing_smul_left p a x t

/-- A point is on a plane precisely when its homogeneous equation vanishes. -/
noncomputable def Incident (x : PG3 p) (H : DualPoint p) : Prop :=
  H.rep x.rep = 0

/-- Incidence is independent of the nonzero representatives used. -/
@[simp] theorem incident_mk_mk (x : Vector p) (a : Module.Dual (ZMod p) (Vector p))
    (hx : x ≠ 0) (ha : a ≠ 0) :
    Incident p (Projectivization.mk (ZMod p) x hx)
      (Projectivization.mk (ZMod p) a ha) ↔ a x = 0 := by
  obtain ⟨c, hc⟩ := Projectivization.exists_smul_eq_mk_rep (ZMod p) a ha
  obtain ⟨d, hd⟩ := Projectivization.exists_smul_eq_mk_rep (ZMod p) x hx
  simp only [Units.smul_def] at hc hd
  unfold Incident
  rw [← hc, ← hd]
  simp [map_smul, smul_eq_mul]

/-- There are `p³+p²+p+1` points (and equally many dual points). -/
theorem card_pg3 : Fintype.card (PG3 p) = p ^ 3 + p ^ 2 + p + 1 := by
  rw [Fintype.card_eq_nat_card]
  have h := Projectivization.card_of_finrank (ZMod p) (Vector p)
    (n := 4) (by simp [Vector, Module.finrank_fintype_fun_eq_card])
  simpa [Finset.sum_range_succ, ZMod.card, Nat.card_eq_fintype_card,
    Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h

theorem card_dualPoint : Fintype.card (DualPoint p) = p ^ 3 + p ^ 2 + p + 1 :=
  by
    rw [Fintype.card_eq_nat_card]
    have h := Projectivization.card_of_finrank (ZMod p)
      (Module.Dual (ZMod p) (Vector p)) (n := 4)
      (by simp [Vector, Subspace.dual_finrank_eq])
    simpa [Finset.sum_range_succ, ZMod.card, Nat.card_eq_fintype_card,
      Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h

/-- Normalize an affine point into the standard projective chart. -/
def affineVector (x : Geometry.Point p) : Vector p := Fin.cons 1 x

@[simp] theorem affineVector_zero (x : Geometry.Point p) : affineVector p x 0 = 1 := rfl

@[simp] theorem affineVector_succ (x : Geometry.Point p) (i : Fin 3) :
    affineVector p x i.succ = x i := rfl

theorem affineVector_ne_zero (x : Geometry.Point p) : affineVector p x ≠ 0 := by
  intro h
  have := congrFun h 0
  simpa using this

/-- The standard affine chart embeds injectively into projective space. -/
def affineEmbed (x : Geometry.Point p) : PG3 p :=
  Projectivization.mk (ZMod p) (affineVector p x) (affineVector_ne_zero p x)

theorem affineEmbed_injective : Function.Injective (affineEmbed p) := by
  intro x y h
  obtain ⟨t, ht⟩ := (Projectivization.mk_eq_mk_iff' (ZMod p)
    (affineVector p x) (affineVector p y)
    (affineVector_ne_zero p x) (affineVector_ne_zero p y)).mp h
  have htone : t = 1 := by
    have := congrFun ht 0
    simpa [affineVector] using this
  subst t
  funext i
  have := congrFun ht i.succ
  simpa using this.symm

/-- The standard plane at infinity has homogeneous equation `X₀=0`. -/
def infinity : DualPoint p :=
  Projectivization.mk (ZMod p) (LinearMap.proj (0 : Fin 4))
    (by intro h; have := LinearMap.congr_fun h (Pi.single (0 : Fin 4) 1); simpa using this)

theorem affineEmbed_not_incident_infinity (x : Geometry.Point p) :
    ¬ Incident p (affineEmbed p x) (infinity p) := by
  simp [affineEmbed, infinity, affineVector]

/-- Homogenize an affine plane equation `a·x=b`. -/
def affinePlaneFunctional (a : Geometry.Point p) (b : ZMod p) :
    Module.Dual (ZMod p) (Vector p) := pairingMap p (Fin.cons (-b) a)

@[simp] theorem affinePlaneFunctional_apply (a : Geometry.Point p) (b : ZMod p)
    (x : Geometry.Point p) :
    affinePlaneFunctional p a b (affineVector p x) = Geometry.pairing p a x - b := by
  simp [affinePlaneFunctional, pairingMap, pairing, affineVector, Fin.sum_univ_succ,
    Geometry.pairing, sub_eq_add_neg, add_comm]

theorem affinePlaneFunctional_ne_zero {a : Geometry.Point p} (ha : a ≠ 0) (b : ZMod p) :
    affinePlaneFunctional p a b ≠ 0 := by
  apply pairingMap_ne_zero p
  intro h
  apply ha
  funext i
  have := congrFun h i.succ
  simpa using this

/-- The dual point of a genuine affine plane. -/
def affinePlaneDual (a : Geometry.Point p) (b : ZMod p) (ha : a ≠ 0) : DualPoint p :=
  Projectivization.mk (ZMod p) (affinePlaneFunctional p a b)
    (affinePlaneFunctional_ne_zero p ha b)

@[simp] theorem affineEmbed_incident_affinePlaneDual (a : Geometry.Point p) (b : ZMod p)
    (ha : a ≠ 0) (x : Geometry.Point p) :
    Incident p (affineEmbed p x) (affinePlaneDual p a b ha) ↔ Geometry.pairing p a x = b := by
  simp [affineEmbed, affinePlaneDual, sub_eq_zero]

#print axioms card_pg3
#print axioms incident_mk_mk
#print axioms affineEmbed_injective
#print axioms affineEmbed_not_incident_infinity
#print axioms pairingEquiv
#print axioms affineEmbed_incident_affinePlaneDual

end Cylinder.ProjectiveGeometry
