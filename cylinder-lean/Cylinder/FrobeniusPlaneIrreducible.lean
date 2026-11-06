module

public import Cylinder.HomogeneousCurveChart
public import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Self-polar exclusion in the manuscript's actual three-variable ring

The permutation from `Fin 3` to `Option (Fin 2)` commutes with the
genuine Frobenius polar and preserves the homogeneous equation.
Thus the affine-chart proof applies to the usual three-coordinate
model, with no chart or smooth-point assumptions.
-/

@[expose] public section
noncomputable section

namespace Cylinder.FrobeniusPlaneIrreducible

open MvPolynomial Cylinder.FrobeniusPolar
open scoped BigOperators Classical

variable {K : Type*} [Field K]

section Reindex

variable {σ τ : Type*} [Fintype σ] [Fintype τ]

theorem rename_polar (p : ℕ) (e : σ ≃ τ) (Q : MvPolynomial σ K) :
    rename e (polar p Q) = polar p (rename e Q) := by
  unfold polar
  rw [map_sum]
  calc
    _ = ∑ i : σ, X (e i) ^ p * pderiv (e i) (rename e Q) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [map_mul, map_pow, rename_X, ← pderiv_rename e.injective i Q]
    _ = _ := e.sum_comp (fun j : τ => X j ^ p * pderiv j (rename e Q))

end Reindex

theorem not_self_polar [IsAlgClosed K] (p n : ℕ) [CharP K p]
    (Q : MvPolynomial (Fin 3) K) (hQ : Q.IsHomogeneous n)
    (hirr : Irreducible Q) (hn : 2 ≤ n) (hnp : n < p) : ¬ Q ∣ polar p Q := by
  intro hdiv
  let e : Fin 3 ≃ Option (Fin 2) := finSuccEquiv 2
  let g := MvPolynomial.renameEquiv K e
  have hhom : (g Q).IsHomogeneous n := by
    simpa only [g, MvPolynomial.renameEquiv_apply] using hQ.rename_isHomogeneous (f := e)
  have hirra : Irreducible (g Q) :=
    (MulEquiv.irreducible_iff (f := g.toMulEquiv)).mpr hirr
  have htheta : g (polar p Q) = polar p (g Q) := by
    simpa only [g, MvPolynomial.renameEquiv_apply] using rename_polar p e Q
  have hdiva := map_dvd g.toRingHom hdiv
  change g Q ∣ g (polar p Q) at hdiva
  rw [htheta] at hdiva
  exact HomogeneousCurveChart.not_self_polar p n (g Q) hhom hirra hn hnp hdiva

theorem polar_ne_zero [IsAlgClosed K] (p n : ℕ) [CharP K p]
    (Q : MvPolynomial (Fin 3) K) (hQ : Q.IsHomogeneous n)
    (hirr : Irreducible Q) (hn : 2 ≤ n) (hnp : n < p) : polar p Q ≠ 0 := by
  intro hz
  apply not_self_polar p n Q hQ hirr hn hnp
  rw [hz]
  exact dvd_zero Q

theorem polar_relPrime [IsAlgClosed K] (p n : ℕ) [CharP K p]
    (Q : MvPolynomial (Fin 3) K) (hQ : Q.IsHomogeneous n)
    (hirr : Irreducible Q) (hn : 2 ≤ n) (hnp : n < p) : IsRelPrime Q (polar p Q) := by
  intro D hDQ hDH
  rcases hirr.dvd_iff.mp hDQ with hunit | hassoc
  · exact hunit
  · exact False.elim (not_self_polar p n Q hQ hirr hn hnp (hassoc.dvd.trans hDH))

theorem polar_totalDegree [IsAlgClosed K] (p n : ℕ) [CharP K p]
    (Q : MvPolynomial (Fin 3) K) (hQ : Q.IsHomogeneous n)
    (hirr : Irreducible Q) (hn : 2 ≤ n) (hnp : n < p) :
    (polar p Q).totalDegree = n + p - 1 :=
  FrobeniusPolar.polar_totalDegree p n (by omega) Q hQ (polar_ne_zero p n Q hQ hirr hn hnp)

end Cylinder.FrobeniusPlaneIrreducible

end
