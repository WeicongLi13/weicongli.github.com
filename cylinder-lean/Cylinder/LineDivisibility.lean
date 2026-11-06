module

public import Cylinder.AffineLinePolynomial
public import Mathlib.Algebra.Polynomial.Div
public import Mathlib.Tactic.FinCases

/-!
# A line on which a low-degree polynomial vanishes is a factor

The first result treats the normalized graph line `x₀ = α + β*x₁`.
Its proof uses the actual polynomial-ring isomorphism and the univariate
factor theorem. Finite-field vanishing is upgraded to a polynomial
identity using the degree bound on the line restriction.
-/

@[expose] public section

namespace Cylinder.LineDivisibility

open Cylinder.AffineLinePolynomial

variable {K : Type*} [Field K]

noncomputable def innerGraph (α β : K) : MvPolynomial (Fin 1) K :=
  MvPolynomial.C α + MvPolynomial.C β * MvPolynomial.X 0

noncomputable def graphEquation (α β : K) : MvPolynomial (Fin 2) K :=
  MvPolynomial.X 0 - (MvPolynomial.C α + MvPolynomial.C β * MvPolynomial.X 1)

/-- The nested-polynomial evaluation is exactly restriction to the graph
line, after identifying the remaining variable with the univariate one. -/
theorem graphRestriction_eq (P : MvPolynomial (Fin 2) K) (α β : K) :
    (MvPolynomial.uniqueAlgEquiv K (Fin 1))
      ((MvPolynomial.finSuccEquiv K 1 P).eval (innerGraph α β)) =
        linePolynomial P ![α, 0] ![β, 1] := by
  let e := MvPolynomial.finSuccEquiv K 1
  let f := MvPolynomial.uniqueAlgEquiv K (Fin 1)
  have hhom : f.toRingHom.comp ((Polynomial.evalRingHom (innerGraph α β)).comp e.toRingHom) =
      MvPolynomial.eval₂Hom Polynomial.C
        (fun i : Fin 2 => affineLinear (![α, 0] i) (![β, 1] i)) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [RingHom.comp_apply, e, f, MvPolynomial.finSuccEquiv_apply,
        MvPolynomial.uniqueAlgEquiv_apply]
    · intro i
      have hX0 : e (MvPolynomial.X 0) = Polynomial.X :=
        MvPolynomial.finSuccEquiv_X_zero
      have hX1 : e (MvPolynomial.X 1) = Polynomial.C (MvPolynomial.X 0) :=
        MvPolynomial.finSuccEquiv_X_succ (R := K) (n := 1) (j := 0)
      fin_cases i <;>
        simp [RingHom.comp_apply, hX0, hX1, f, innerGraph, affineLinear,
          MvPolynomial.uniqueAlgEquiv_apply]
  change (f.toRingHom.comp ((Polynomial.evalRingHom (innerGraph α β)).comp e.toRingHom)) P = _
  rw [hhom]
  rfl

theorem graphEquation_image (α β : K) :
    MvPolynomial.finSuccEquiv K 1 (graphEquation α β) =
      Polynomial.X - Polynomial.C (innerGraph α β) := by
  have hC (c : K) : MvPolynomial.finSuccEquiv K 1 (MvPolynomial.C c) =
      Polynomial.C (MvPolynomial.C c) := by
    simp [MvPolynomial.finSuccEquiv_apply]
  have hX1 : MvPolynomial.finSuccEquiv K 1 (MvPolynomial.X 1) =
      Polynomial.C (MvPolynomial.X 0) :=
    MvPolynomial.finSuccEquiv_X_succ (R := K) (n := 1) (j := 0)
  rw [graphEquation, map_sub, map_add, map_mul, MvPolynomial.finSuccEquiv_X_zero,
    hX1, hC α, hC β]
  simp only [innerGraph, map_add, map_mul]

/-- A zero restriction as a polynomial forces divisibility by the actual
affine line equation. -/
theorem graphEquation_dvd_of_restriction_zero
    (P : MvPolynomial (Fin 2) K) (α β : K)
    (hzero : linePolynomial P ![α, 0] ![β, 1] = 0) :
    graphEquation α β ∣ P := by
  have heval : (MvPolynomial.finSuccEquiv K 1 P).eval (innerGraph α β) = 0 := by
    apply (MvPolynomial.uniqueAlgEquiv K (Fin 1)).injective
    rw [graphRestriction_eq, hzero, map_zero]
  have hdiv : Polynomial.X - Polynomial.C (innerGraph α β) ∣
      MvPolynomial.finSuccEquiv K 1 P := Polynomial.dvd_iff_isRoot.mpr heval
  rw [← graphEquation_image] at hdiv
  exact (map_dvd_iff (MvPolynomial.finSuccEquiv K 1)).mp hdiv

/-- Finite-field vanishing on the graph line gives a line factor when the
polynomial degree is strictly below the field size. -/
theorem graphEquation_dvd_of_vanishing [Fintype K]
    (P : MvPolynomial (Fin 2) K) (α β : K)
    (hdegree : P.totalDegree < Fintype.card K)
    (hvanish : ∀ t : K, MvPolynomial.eval ![α + t * β, t] P = 0) :
    graphEquation α β ∣ P := by
  apply graphEquation_dvd_of_restriction_zero P α β
  apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero _ Function.injective_id
  · intro t
    rw [linePolynomial_eval]
    have he : (fun i : Fin 2 => ![α, 0] i + t * ![β, 1] i) = ![α + t * β, t] := by
      funext i
      fin_cases i <;> simp
    dsimp only [id]
    rw [he]
    exact hvanish t
  · exact lt_of_le_of_lt (linePolynomial_degree_le P ![α, 0] ![β, 1]) hdegree

end Cylinder.LineDivisibility
