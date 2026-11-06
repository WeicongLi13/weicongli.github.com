module

public import Cylinder.Geometry
public import Cylinder.CoordinateProjection
public import Cylinder.LinearTransport
public import Cylinder.ConicLineCoordinates
public import Mathlib.LinearAlgebra.Projectivization.Cardinality

/-! Genuine undetermined affine directions. A p²-set meets every line
in such a direction once, and each parallel affine plane contains p of
its points. All cardinalities refer to the original finite point set. -/

@[expose] public section
noncomputable section
open scoped Classical

namespace Cylinder.WeakDirectionsGeometry
open Cylinder.Geometry Cylinder.CoordinateProjection

variable (p : ℕ) [Fact p.Prime]

abbrev Direction := Projectivization (ZMod p) (Point p)
instance : Fintype (Direction p) := Fintype.ofFinite _

def Determines (S : Finset (Point p)) (D : Direction p) : Prop :=
  ∃ x ∈ S, ∃ y ∈ S, x ≠ y ∧ ∃ t : ZMod p, x + t • D.rep = y

def nonDeterminedDirections (S : Finset (Point p)) : Finset (Direction p) :=
  Finset.univ.filter (fun D => ¬ Determines p S D)

theorem points_eq_of_same_missing_line {S : Finset (Point p)} {D : Direction p}
    (hD : ¬ Determines p S D) (x y : S) (t : ZMod p) (ht : x.val + t • D.rep = y.val) : x = y := by
  apply Subtype.ext
  by_contra hne
  exact hD ⟨x.val, x.property, y.val, y.property, hne, t, ht⟩

def translate (S : Finset (Point p)) (D : Direction p) (z : S × ZMod p) : Point p :=
  z.1.val + z.2 • D.rep

theorem translate_injective {S : Finset (Point p)} {D : Direction p}
    (hD : ¬ Determines p S D) : Function.Injective (translate p S D) := by
  intro x y heq
  have hxy : x.1.val + (x.2 - y.2) • D.rep = y.1.val := by
    calc
      _ = (x.1.val + x.2 • D.rep) - y.2 • D.rep := by rw [sub_smul]; abel
      _ = (y.1.val + y.2 • D.rep) - y.2 • D.rep := congrArg (fun v : Point p => v - y.2 • D.rep) heq
      _ = _ := add_sub_cancel_right _ _
  have hbase := points_eq_of_same_missing_line p hD x.1 y.1 (x.2 - y.2) hxy
  refine Prod.ext hbase ?_
  apply line_parameter_injective p x.1.val D.rep_nonzero
  change x.1.val + x.2 • D.rep = x.1.val + y.2 • D.rep
  change x.1.val + x.2 • D.rep = y.1.val + y.2 • D.rep at heq
  simpa only [hbase] using heq

theorem translate_bijective {S : Finset (Point p)} (hcard : S.card = p ^ 2)
    {D : Direction p} (hD : ¬ Determines p S D) : Function.Bijective (translate p S D) := by
  have hinj := translate_injective p hD
  have hcards : Fintype.card (S × ZMod p) = Fintype.card (Point p) := by
    simp only [Fintype.card_prod, Fintype.card_coe, ZMod.card, Point, Fintype.card_fun,
      Fintype.card_fin, hcard]
    ring
  let e : (S × ZMod p) ≃ Point p := Fintype.equivOfCardEq hcards
  have hsurj : Function.Surjective (fun x : Point p => translate p S D (e.symm x)) :=
    Finite.surjective_of_injective (hinj.comp e.symm.injective)
  exact ⟨hinj, fun x => by obtain ⟨y, hy⟩ := hsurj x; exact ⟨e.symm y, hy⟩⟩

theorem affinePlane_card (a : Point p) (ha : a ≠ 0) (b : ZMod p) :
    (affinePlane p a b).card = p ^ 2 := by
  let ell := LinearTransport.pairingMap p a
  have hell : ell ≠ 0 := by
    intro hz
    obtain ⟨x, hx⟩ := nonzero_normal_pairing p ha
    exact hx (congrArg (fun f : Point p →ₗ[ZMod p] ZMod p => f x) hz)
  obtain ⟨g, hg⟩ := ConicLineCoordinates.exists_functional_coordinates ell hell
  let f : QuotientPoint p → Point p := fun q => g (lift p q b)
  have hf : Function.Injective f := by
    intro q r hqr
    have he := congrArg (project p) (g.injective hqr)
    simpa only [project_lift] using he
  have himage : Finset.univ.image f = affinePlane p a b := by
    ext x
    constructor
    · intro hx
      obtain ⟨q, _hq, rfl⟩ := Finset.mem_image.mp hx
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ _, hg (lift p q b)⟩
    · intro hx
      have hxplane := (Finset.mem_filter.mp hx).2
      have hz : g.symm x 2 = b := by
        have h := hg (g.symm x)
        rw [LinearEquiv.apply_symm_apply] at h
        exact h.symm.trans hxplane
      refine Finset.mem_image.mpr ⟨project p (g.symm x), Finset.mem_univ _, ?_⟩
      change g (lift p (project p (g.symm x)) b) = x
      rw [← hz, lift_project, LinearEquiv.apply_symm_apply]
  rw [← himage, Finset.card_image_of_injective _ hf, Finset.card_univ]
  simp [QuotientPoint]

def planeTranslation {S : Finset (Point p)} (D : Direction p) (a : Point p) (b : ZMod p)
    (horth : pairing p a D.rep = 0) : (S.filter (fun x => pairing p a x = b)) × ZMod p → affinePlane p a b :=
  fun z => ⟨z.1.val + z.2 • D.rep, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
    rw [pairing_on_line, horth, mul_zero, add_zero]
    exact (Finset.mem_filter.mp z.1.property).2⟩⟩

theorem planeTranslation_bijective {S : Finset (Point p)} (hcard : S.card = p ^ 2)
    {D : Direction p} (hD : ¬ Determines p S D) (a : Point p) (b : ZMod p)
    (horth : pairing p a D.rep = 0) : Function.Bijective (planeTranslation p D a b horth (S := S)) := by
  constructor
  · intro x y heq
    let x' : S × ZMod p := (⟨x.1.val, (Finset.mem_filter.mp x.1.property).1⟩, x.2)
    let y' : S × ZMod p := (⟨y.1.val, (Finset.mem_filter.mp y.1.property).1⟩, y.2)
    have hxy : x' = y' := (translate_injective p hD) (congrArg Subtype.val heq)
    exact Prod.ext (Subtype.ext (congrArg (fun z : S × ZMod p => z.1.val) hxy))
      (congrArg (fun z : S × ZMod p => z.2) hxy)
  · intro x
    obtain ⟨z, hz⟩ := (translate_bijective p hcard hD).2 x.val
    have hs : pairing p a z.1.val = b := by
      have hxplane := (Finset.mem_filter.mp x.property).2
      rw [← hz, translate, pairing_on_line, horth, mul_zero, add_zero] at hxplane
      exact hxplane
    refine ⟨(⟨z.1.val, Finset.mem_filter.mpr ⟨z.1.property, hs⟩⟩, z.2), Subtype.ext hz⟩

theorem parallel_plane_intersection_card {S : Finset (Point p)} (hcard : S.card = p ^ 2)
    {D : Direction p} (hD : ¬ Determines p S D) (a : Point p) (ha : a ≠ 0)
    (b : ZMod p) (horth : pairing p a D.rep = 0) :
    (S.filter (fun x => pairing p a x = b)).card = p := by
  have hc := Fintype.card_of_bijective (planeTranslation_bijective p hcard hD a b horth)
  rw [Fintype.card_prod, Fintype.card_coe, ZMod.card, Fintype.card_coe, affinePlane_card p a ha b] at hc
  have hp : 0 < p := (Fact.out : p.Prime).pos
  apply Nat.eq_of_mul_eq_mul_right hp
  simpa only [pow_two] using hc

end Cylinder.WeakDirectionsGeometry
end
