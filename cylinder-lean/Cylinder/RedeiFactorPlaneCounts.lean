import Cylinder.RedeiPlaneMoment
import Cylinder.RedeiGluing
import Cylinder.RedeiProjection
import Cylinder.RedeiPowers
import Cylinder.RedeiMomentProduct
import Cylinder.RedeiSyzygy

/-! Plane divisibility of the larger factor of a normalized tiling of
prime-field three-space, assuming the smaller factor spans. -/
noncomputable section
namespace Cylinder.Redei
open Geometry PowerEvaluationRelation MvPolynomial
open scoped BigOperators Classical

/-- If the smaller p-point factor contains zero and spans the space, each
affine plane intersects the larger factor in a multiple of p points. -/
theorem pDivisible_of_spanning_factor (p : ℕ) [Fact p.Prime]
    {A B : Finset (Point p)} (hA : A.card = p) (hB : B.card = p^2) (h0 : 0 ∈ A)
    (tile : AddSubgroup.IsComplement (A : Set (Point p)) B)
    (hspan : Submodule.span (ZMod p) (A : Set (Point p)) = ⊤) : PDivisible p B := by
  classical
  obtain ⟨l,hl⟩ := RedeiProjection.exists_bijective_projection A B tile hA
  obtain ⟨j,_,hj,hjA⟩ := RedeiPlaneMoment.exists_nonzero_moment_three A h0 hspan l hl
  have hex : ∃ k, moment p A k ≠ 0 := ⟨j,hjA⟩
  let r := Nat.find hex
  have hrA : moment p A r ≠ 0 := Nat.find_spec hex
  have hrle : r ≤ j := Nat.find_min' hex hjA
  have hp := (Fact.out : p.Prime).two_le
  have hr : r < p := by omega
  have ha : ∀ k < r, moment p A k = 0 := by
    intro k hk
    by_contra h
    exact Nat.find_min hex hk h

  by_contra hn
  obtain ⟨d,hd0,hd,hdB,hb⟩ := first_nonzero_moment p hB hn
  have hdiv := factor_differences_divide tile hA hB d hd0 hd
  have hmem := first_moments_mem_coordinate_powers p A B tile r d hr hd ha hb
  obtain ⟨hle,U,hU,hprod⟩ := RedeiPowers.homogeneous_decomposition p (r+d)
    (moment p A r * moment p B d) ((moment_homogeneous p A r).mul (moment_homogeneous p B d))
    (mul_ne_zero hrA hdB) hmem
  have hs : r+d-p < r := by omega
  have hsum := frobenius_linear_sum_zero r d (r+d-p) hA (by omega) (by omega) hdiv U hU hprod
  exact no_frobenius_decomposition p A h0 hspan r hr ha hrA (r+d-p) hs
    (moment p A r) (moment p B d) hrA hdB U hU hprod hsum hdiv

end Cylinder.Redei
end
