module

public import Cylinder.ProjectionPolynomial
public import Cylinder.AffineTransport

/-!
# Projection polynomials in arbitrary affine coordinates

The noncylinder conclusions are preserved by any genuine affine
equivalence of the actual three-space, including translations.
-/

@[expose] public section

namespace Cylinder.AffineProjection

open Cylinder.Geometry Cylinder.CoordinateProjection Cylinder.ProjectionPolynomial

variable (p : ℕ) [Fact p.Prime]

theorem noncylinder_projection (e : Point p ≃ᵃ[ZMod p] Point p)
    {S : Finset (Point p)} (hcard : S.card = p ^ 2)
    (hS : PDivisible p S) (hnon : ¬ IsCylinder p S) :
    (∀ q : QuotientPoint p, fibreSize p (S.image e) q < p) ∧
    countPolynomial p (S.image e) ≠ 0 ∧
    (countPolynomial p (S.image e)).totalDegree ≤ p - 2 := by
  have hcard' : (S.image e).card = p ^ 2 := by
    simpa only [AffineTransport.image_card] using hcard
  have hS' := AffineTransport.pDivisible_image p e hS
  have hnon' : ¬ IsCylinder p (S.image e) := by
    intro h
    exact hnon ((AffineTransport.isCylinder_image_iff p e S).mp h)
  exact ⟨fibreSize_lt_of_not_isCylinder p hcard' hS' hnon',
    countPolynomial_ne_zero_of_not_isCylinder p hcard' hnon',
    countPolynomial_totalDegree_le p hS'⟩

end Cylinder.AffineProjection
