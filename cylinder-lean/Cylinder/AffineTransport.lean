module

public import Cylinder.DirectionCylinder
public import Mathlib.LinearAlgebra.AffineSpace.AffineEquiv

/-!
# Affine changes of coordinates

The map `x ↦ g x + shift` is bundled as an actual affine equivalence, with
inverse `y ↦ g.symm (y - shift)`.  The results also apply to any affine
equivalence of the coordinate space.  In a plane equation the normal is
pulled back by the linear part, and the constant term is translated by
the pairing with the image of zero.
-/

@[expose] public section

namespace Cylinder.AffineTransport

open Cylinder.Geometry

variable (p : ℕ) [Fact p.Prime]

def coordinateEquiv (g : Point p ≃ₗ[ZMod p] Point p) (shift : Point p) :
    Point p ≃ᵃ[ZMod p] Point p where
  toFun x := g x + shift
  invFun y := g.symm (y - shift)
  left_inv x := by simp
  right_inv y := by simp
  linear := g
  map_vadd' x v := by
    change g (v + x) + shift = g v + (g x + shift)
    rw [map_add, add_assoc]

@[simp] theorem coordinateEquiv_apply (g : Point p ≃ₗ[ZMod p] Point p)
    (shift x : Point p) : coordinateEquiv p g shift x = g x + shift := rfl

@[simp] theorem coordinateEquiv_linear (g : Point p ≃ₗ[ZMod p] Point p) (shift : Point p) :
    (coordinateEquiv p g shift).linear = g := rfl

@[simp] theorem coordinateEquiv_zero (g : Point p ≃ₗ[ZMod p] Point p) (shift : Point p) :
    coordinateEquiv p g shift 0 = shift := by simp

theorem apply_eq_linear_add_zero (e : Point p ≃ᵃ[ZMod p] Point p) (x : Point p) :
    e x = e.linear x + e 0 := by
  have h := e.map_vadd 0 x
  change e (x + 0) = e.linear x + e 0 at h
  simpa only [add_zero] using h

theorem image_card (e : Point p ≃ᵃ[ZMod p] Point p) (S : Finset (Point p)) :
    (S.image e).card = S.card := Finset.card_image_of_injective _ e.injective

theorem image_symm_image (e : Point p ≃ᵃ[ZMod p] Point p) (S : Finset (Point p)) :
    (S.image e).image e.symm = S := by
  simp [Finset.image_image, Function.comp_def]

theorem pairing_affine (e : Point p ≃ᵃ[ZMod p] Point p) (a x : Point p) :
    pairing p a (e x) =
      pairing p (LinearTransport.pullbackNormal p e.linear a) x + pairing p a (e 0) := by
  rw [apply_eq_linear_add_zero, pairing_add, ← LinearTransport.pairing_pullbackNormal]

/-- Pull back both the normal and the constant term of an actual plane filter. -/
theorem filter_image_plane (e : Point p ≃ᵃ[ZMod p] Point p) (S : Finset (Point p))
    (a : Point p) (c : ZMod p) :
    (S.image e).filter (fun y => pairing p a y = c) =
      (S.filter (fun x => pairing p (LinearTransport.pullbackNormal p e.linear a) x =
        c - pairing p a (e 0))).image e := by
  ext y
  constructor
  · intro hy
    obtain ⟨himage, hplane⟩ := Finset.mem_filter.mp hy
    obtain ⟨x, hx, hxy⟩ := Finset.mem_image.mp himage
    apply Finset.mem_image.mpr
    refine ⟨x, Finset.mem_filter.mpr ⟨hx, ?_⟩, hxy⟩
    apply (eq_sub_iff_add_eq).mpr
    rw [← pairing_affine, hxy]
    exact hplane
  · intro hy
    obtain ⟨x, hx, hxy⟩ := Finset.mem_image.mp hy
    obtain ⟨hxS, hxplane⟩ := Finset.mem_filter.mp hx
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_image.mpr ⟨x, hxS, hxy⟩, ?_⟩
    rw [← hxy, pairing_affine, hxplane, sub_add_cancel]

theorem plane_image_card (e : Point p ≃ᵃ[ZMod p] Point p) (S : Finset (Point p))
    (a : Point p) (c : ZMod p) :
    ((S.image e).filter (fun y => pairing p a y = c)).card =
      (S.filter (fun x => pairing p (LinearTransport.pullbackNormal p e.linear a) x =
        c - pairing p a (e 0))).card := by
  rw [filter_image_plane, Finset.card_image_of_injective _ e.injective]

theorem coordinate_plane_image_card (g : Point p ≃ₗ[ZMod p] Point p)
    (shift : Point p) (S : Finset (Point p)) (a : Point p) (c : ZMod p) :
    ((S.image (coordinateEquiv p g shift)).filter (fun y => pairing p a y = c)).card =
      (S.filter (fun x => pairing p (LinearTransport.pullbackNormal p g a) x =
        c - pairing p a shift)).card := by
  simpa only [coordinateEquiv_linear, coordinateEquiv_zero] using
    plane_image_card p (coordinateEquiv p g shift) S a c

theorem pDivisible_image (e : Point p ≃ᵃ[ZMod p] Point p) {S : Finset (Point p)}
    (hS : PDivisible p S) : PDivisible p (S.image e) := by
  intro a ha c
  rw [plane_image_card]
  exact hS (LinearTransport.pullbackNormal p e.linear a)
    (LinearTransport.pullbackNormal_ne_zero p e.linear ha) (c - pairing p a (e 0))

theorem pDivisible_image_iff (e : Point p ≃ᵃ[ZMod p] Point p) (S : Finset (Point p)) :
    PDivisible p (S.image e) ↔ PDivisible p S := by
  constructor
  · intro h
    have hback := pDivisible_image p e.symm h
    simpa only [image_symm_image] using hback
  · exact pDivisible_image p e

theorem affineLine_param (e : Point p ≃ᵃ[ZMod p] Point p) (base direction : Point p)
    (t : ZMod p) : e (base + t • direction) = e base + t • e.linear direction := by
  have h := e.map_vadd base (t • direction)
  change e (t • direction + base) = e.linear (t • direction) + e base at h
  simpa only [add_comm, map_smul] using h

theorem image_affineLine (e : Point p ≃ᵃ[ZMod p] Point p) (base direction : Point p) :
    (affineLine p base direction).image e = affineLine p (e base) (e.linear direction) := by
  simp only [affineLine, Finset.image_image, Function.comp_def, affineLine_param]

theorem inDirection_image (e : Point p ≃ᵃ[ZMod p] Point p) {S : Finset (Point p)}
    {direction : Point p} (hS : IsCylinderInDirection p S direction) :
    IsCylinderInDirection p (S.image e) (e.linear direction) := by
  obtain ⟨hd, base, hdisjoint, hUnion⟩ := hS
  have hed : e.linear direction ≠ 0 := by
    intro hzero
    apply hd
    exact e.linear.injective (by simpa using hzero)
  refine ⟨hed, (fun i => e (base i)), ?_, ?_⟩
  · intro i j hij
    rw [← image_affineLine p e (base i) direction,
      ← image_affineLine p e (base j) direction]
    exact (Finset.disjoint_image e.injective).mpr (hdisjoint hij)
  · rw [hUnion, Finset.biUnion_image]
    simp only [image_affineLine]

theorem inDirection_image_iff (e : Point p ≃ᵃ[ZMod p] Point p)
    (S : Finset (Point p)) (direction : Point p) :
    IsCylinderInDirection p (S.image e) (e.linear direction) ↔
      IsCylinderInDirection p S direction := by
  constructor
  · intro h
    have hback := inDirection_image p e.symm h
    simpa [image_symm_image] using hback
  · exact inDirection_image p e

theorem isCylinder_image (e : Point p ≃ᵃ[ZMod p] Point p) {S : Finset (Point p)}
    (hS : IsCylinder p S) : IsCylinder p (S.image e) := by
  obtain ⟨direction, hdir⟩ := (isCylinder_iff_exists_direction p S).mp hS
  exact isCylinder_of_inDirection p (inDirection_image p e hdir)

theorem isCylinder_image_iff (e : Point p ≃ᵃ[ZMod p] Point p) (S : Finset (Point p)) :
    IsCylinder p (S.image e) ↔ IsCylinder p S := by
  constructor
  · intro h
    have hback := isCylinder_image p e.symm h
    simpa only [image_symm_image] using hback
  · exact isCylinder_image p e

#print axioms coordinateEquiv
#print axioms plane_image_card
#print axioms pDivisible_image_iff
#print axioms inDirection_image_iff
#print axioms isCylinder_image_iff

end Cylinder.AffineTransport
