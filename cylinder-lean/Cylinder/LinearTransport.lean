module

public import Cylinder.CoordinateProjection
public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Linear changes of coordinates

These results use actual linear equivalences of the coordinate space.
Plane intersection counts and exact unions of parallel lines are preserved.
An isomorphism of two one-dimensional spans extends to the whole space,
allowing any nonzero direction to be sent to the standard third direction.
-/

@[expose] public section

namespace Cylinder.LinearTransport

open Cylinder.Geometry
open scoped BigOperators

variable (p : ℕ) [Fact p.Prime]

def pairingMap (a : Point p) : Point p →ₗ[ZMod p] ZMod p where
  toFun := pairing p a
  map_add' x y := pairing_add p a x y
  map_smul' t x := by
    simpa only [smul_eq_mul, RingHom.id_apply] using pairing_smul p a x t

theorem point_eq_sum_single (x : Point p) :
    x = ∑ i : Fin 3, x i • Pi.single i 1 := by
  funext j
  simp [Finset.sum_apply, Pi.single_apply]

theorem functional_expansion (L : Point p →ₗ[ZMod p] ZMod p) (x : Point p) :
    L x = ∑ i : Fin 3, x i * L (Pi.single i 1) := by
  calc
    L x = L (∑ i : Fin 3, x i • Pi.single i 1) :=
      congrArg L (point_eq_sum_single p x)
    _ = ∑ i : Fin 3, L (x i • Pi.single i 1) := map_sum L _ _
    _ = ∑ i : Fin 3, x i * L (Pi.single i 1) := by
      apply Finset.sum_congr rfl
      intro i _
      simp [map_smul, smul_eq_mul]

def pullbackNormal (g : Point p ≃ₗ[ZMod p] Point p) (a : Point p) : Point p :=
  fun i => pairing p a (g (Pi.single i 1))

theorem pairing_pullbackNormal (g : Point p ≃ₗ[ZMod p] Point p) (a x : Point p) :
    pairing p (pullbackNormal p g a) x = pairing p a (g x) := by
  have h := functional_expansion p ((pairingMap p a).comp g.toLinearMap) x
  change pairing p a (g x) = ∑ i : Fin 3, x i * pairing p a (g (Pi.single i 1)) at h
  calc
    pairing p (pullbackNormal p g a) x =
        ∑ i : Fin 3, x i * pairing p a (g (Pi.single i 1)) := by
      simp [pairing, pullbackNormal, mul_comm]
    _ = pairing p a (g x) := h.symm

theorem pullbackNormal_ne_zero (g : Point p ≃ₗ[ZMod p] Point p) {a : Point p}
    (ha : a ≠ 0) : pullbackNormal p g a ≠ 0 := by
  obtain ⟨y, hy⟩ := nonzero_normal_pairing p ha
  intro hzero
  have h := pairing_pullbackNormal p g a (g.symm y)
  rw [hzero] at h
  have hya : pairing p a y = 0 := by simpa [pairing] using h.symm
  exact hy hya

theorem image_card (g : Point p ≃ₗ[ZMod p] Point p) (S : Finset (Point p)) :
    (S.image g).card = S.card := Finset.card_image_of_injective _ g.injective

theorem image_symm_image (g : Point p ≃ₗ[ZMod p] Point p) (S : Finset (Point p)) :
    (S.image g).image g.symm = S := by
  simp [Finset.image_image, Function.comp_def]

theorem filter_image_plane (g : Point p ≃ₗ[ZMod p] Point p) (S : Finset (Point p))
    (a : Point p) (b : ZMod p) :
    (S.image g).filter (fun y => pairing p a y = b) =
      (S.filter (fun x => pairing p (pullbackNormal p g a) x = b)).image g := by
  ext y
  constructor
  · intro hy
    obtain ⟨himage, hplane⟩ := Finset.mem_filter.mp hy
    obtain ⟨x, hx, hxy⟩ := Finset.mem_image.mp himage
    apply Finset.mem_image.mpr
    refine ⟨x, Finset.mem_filter.mpr ⟨hx, ?_⟩, hxy⟩
    rw [pairing_pullbackNormal, hxy]
    exact hplane
  · intro hy
    obtain ⟨x, hx, hxy⟩ := Finset.mem_image.mp hy
    obtain ⟨hxS, hxplane⟩ := Finset.mem_filter.mp hx
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_image.mpr ⟨x, hxS, hxy⟩, ?_⟩
    rw [← hxy, ← pairing_pullbackNormal]
    exact hxplane

theorem pDivisible_image (g : Point p ≃ₗ[ZMod p] Point p) {S : Finset (Point p)}
    (hS : PDivisible p S) : PDivisible p (S.image g) := by
  intro a ha b
  rw [filter_image_plane, Finset.card_image_of_injective _ g.injective]
  exact hS (pullbackNormal p g a) (pullbackNormal_ne_zero p g ha) b

theorem pDivisible_image_iff (g : Point p ≃ₗ[ZMod p] Point p) (S : Finset (Point p)) :
    PDivisible p (S.image g) ↔ PDivisible p S := by
  constructor
  · intro h
    have hback := pDivisible_image p g.symm h
    simpa only [image_symm_image] using hback
  · exact pDivisible_image p g

theorem image_affineLine (g : Point p ≃ₗ[ZMod p] Point p) (base direction : Point p) :
    (affineLine p base direction).image g = affineLine p (g base) (g direction) := by
  simp [affineLine, Finset.image_image, Function.comp_def, map_add, map_smul]

theorem isCylinder_image (g : Point p ≃ₗ[ZMod p] Point p) {S : Finset (Point p)}
    (hS : IsCylinder p S) : IsCylinder p (S.image g) := by
  obtain ⟨direction, hd, base, hdisjoint, hUnion⟩ := hS
  have hgd : g direction ≠ 0 := by
    intro hzero
    apply hd
    exact g.injective (by simpa using hzero)
  refine ⟨g direction, hgd, (fun i => g (base i)), ?_, ?_⟩
  · intro i j hij
    rw [← image_affineLine p g (base i) direction,
      ← image_affineLine p g (base j) direction]
    exact (Finset.disjoint_image g.injective).mpr (hdisjoint hij)
  · rw [hUnion, Finset.biUnion_image]
    simp only [image_affineLine]

theorem isCylinder_image_iff (g : Point p ≃ₗ[ZMod p] Point p) (S : Finset (Point p)) :
    IsCylinder p (S.image g) ↔ IsCylinder p S := by
  constructor
  · intro h
    have hback := isCylinder_image p g.symm h
    simpa only [image_symm_image] using hback
  · exact isCylinder_image p g

theorem verticalDirection_eq_single :
    CoordinateProjection.verticalDirection p = Pi.single (2 : Fin 3) 1 := by
  funext i
  fin_cases i <;> simp [CoordinateProjection.verticalDirection]

/-- Extend the isomorphism between the spans of two nonzero vectors. -/
theorem exists_linearEquiv_vertical_to {v : Point p} (hv : v ≠ 0) :
    ∃ g : Point p ≃ₗ[ZMod p] Point p, g (CoordinateProjection.verticalDirection p) = v := by
  classical
  let u : Fin 1 → Point p := fun _ => CoordinateProjection.verticalDirection p
  let w : Fin 1 → Point p := fun _ => v
  have hu : LinearIndependent (ZMod p) u :=
    linearIndependent_unique_iff.mpr (CoordinateProjection.verticalDirection_ne_zero p)
  have hw : LinearIndependent (ZMod p) w := linearIndependent_unique_iff.mpr hv
  let f : Submodule.span (ZMod p) (Set.range u) ≃ₗ[ZMod p]
      Submodule.span (ZMod p) (Set.range w) :=
    hu.linearCombinationEquiv.symm.trans hw.linearCombinationEquiv
  let : FiniteDimensional (ZMod p) (Submodule.span (ZMod p) (Set.range u)) :=
    FiniteDimensional.span_of_finite (ZMod p) (Set.finite_range u)
  obtain ⟨g, hg⟩ := Submodule.exists_linearEquiv_restrict_eq f
  refine ⟨g, ?_⟩
  simpa [f, u, w] using (hg (hu.linearCombinationEquiv (Finsupp.single (0 : Fin 1) 1))).symm

theorem exists_linearEquiv_single_to {v : Point p} (hv : v ≠ 0) :
    ∃ g : Point p ≃ₗ[ZMod p] Point p, g (Pi.single (2 : Fin 3) 1) = v := by
  simpa only [verticalDirection_eq_single] using exists_linearEquiv_vertical_to p hv

theorem exists_linearEquiv_to_vertical {v : Point p} (hv : v ≠ 0) :
    ∃ g : Point p ≃ₗ[ZMod p] Point p, g v = CoordinateProjection.verticalDirection p := by
  obtain ⟨g, hg⟩ := exists_linearEquiv_vertical_to p hv
  refine ⟨g.symm, ?_⟩
  rw [← hg, g.symm_apply_apply]

/-- The fibre criterion remains sufficient after any invertible linear change of coordinates. -/
theorem isCylinder_of_image_fibreSize_dvd (g : Point p ≃ₗ[ZMod p] Point p)
    {S : Finset (Point p)} (hcard : S.card = p ^ 2)
    (hdiv : ∀ q : CoordinateProjection.QuotientPoint p,
      p ∣ CoordinateProjection.fibreSize p (S.image g) q) : IsCylinder p S := by
  apply (isCylinder_image_iff p g S).mp
  apply CoordinateProjection.isCylinder_of_fibreSize_dvd p
  · simpa only [image_card] using hcard
  · exact hdiv

#print axioms pDivisible_image_iff
#print axioms isCylinder_image_iff
#print axioms exists_linearEquiv_single_to
#print axioms isCylinder_of_image_fibreSize_dvd

end Cylinder.LinearTransport
