module

public import Cylinder.PolynomialDivisibilityDescent
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic

/-! Actual finite Frobenius periods of polynomials over algebraic prime-field extensions. -/

@[expose] public section
noncomputable section

namespace Cylinder.FrobeniusPolynomialPeriod

open MvPolynomial Cylinder.EquationScalarDescent
open scoped Classical BigOperators

variable (p : ℕ) [Fact p.Prime]
variable {L σ : Type*} [Field L] [Algebra (ZMod p) L] [CharP L p]

omit [CharP L p] in
theorem fixed_scalar_in_base (x : L) (hx : x ^ p = x) :
    ∃ a : ZMod p, algebraMap (ZMod p) L a = x := by
  let P : Polynomial L := Polynomial.X ^ p - Polynomial.X
  have hP0 : P ≠ 0 := FiniteField.X_pow_card_sub_X_ne_zero L (Fact.out : p.Prime).one_lt
  let S : Finset L := Finset.univ.image (algebraMap (ZMod p) L)
  have hScard : S.card = p := by
    rw [Finset.card_image_of_injective _ (algebraMap (ZMod p) L).injective, Finset.card_univ, ZMod.card]
  have hS : S ⊆ P.roots.toFinset := by
    intro y hy
    obtain ⟨a, _ha, rfl⟩ := Finset.mem_image.mp hy
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hP0]
    simp [Polynomial.IsRoot, P, ← map_pow, ZMod.pow_card]
  have hrootcard : P.roots.toFinset.card ≤ p := by
    exact (Multiset.toFinset_card_le _).trans ((Polynomial.card_roots' P).trans_eq
      (FiniteField.X_pow_card_sub_X_natDegree_eq L (Fact.out : p.Prime).one_lt))
  have heq : S = P.roots.toFinset := Finset.eq_of_subset_of_card_le hS (hrootcard.trans_eq hScard.symm)
  have hxroot : x ∈ P.roots.toFinset := by
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hP0]
    simp [Polynomial.IsRoot, P, hx]
  rw [← heq] at hxroot
  obtain ⟨a, _ha, hax⟩ := Finset.mem_image.mp hxroot
  exact ⟨a, hax⟩

def twist (n : ℕ) (H : MvPolynomial σ L) : MvPolynomial σ L :=
  MvPolynomial.map (iterateFrobenius L p n) H

omit [Algebra (ZMod p) L] in
@[simp] theorem twist_zero (H : MvPolynomial σ L) : twist p 0 H = H := by
  rw [twist, iterateFrobenius_zero, MvPolynomial.map_id]

omit [Algebra (ZMod p) L] in
theorem twist_add (m n : ℕ) (H : MvPolynomial σ L) :
    twist p m (twist p n H) = twist p (m + n) H := by
  rw [twist, twist, MvPolynomial.map_map, ← iterateFrobenius_add]
  rfl

omit [Algebra (ZMod p) L] in
theorem twist_ne_zero (n : ℕ) (H : MvPolynomial σ L) (hH : H ≠ 0) : twist p n H ≠ 0 := by
  intro hz
  change MvPolynomial.map (iterateFrobenius L p n) H = 0 at hz
  apply hH
  exact MvPolynomial.map_injective (iterateFrobenius L p n) (iterateFrobenius L p n).injective
    (by simpa only [map_zero] using hz)

theorem twist_mapped_base (n : ℕ) (F : MvPolynomial σ (ZMod p)) :
    twist p n (MvPolynomial.map (algebraMap (ZMod p) L) F) =
      MvPolynomial.map (algebraMap (ZMod p) L) F := by
  ext m
  simp only [twist, coeff_map, iterateFrobenius_def, ← map_pow, ZMod.pow_card_pow]

theorem exists_twist_period [Algebra.IsAlgebraic (ZMod p) L] (H : MvPolynomial σ L) :
    ∃ n : ℕ, 0 < n ∧ twist p n H = H := by
  let S : Finset L := H.support.image (fun m => H.coeff m)
  let E := IntermediateField.adjoin (ZMod p) (S : Set L)
  let : FiniteDimensional (ZMod p) E := IntermediateField.finiteDimensional_adjoin
    (fun x _ => Algebra.IsIntegral.isIntegral x)
  let n := Module.finrank (ZMod p) E
  let : Fintype E := Fintype.ofEquiv (Fin n → ZMod p) (Module.finBasis (ZMod p) E).equivFun.symm.toEquiv
  have hn : 0 < n := Module.finrank_pos
  have hcard : Fintype.card E = p ^ n := by
    simpa only [ZMod.card] using (Module.card_eq_pow_finrank (K := ZMod p) (V := E))
  refine ⟨n, hn, ?_⟩
  ext m
  rw [twist, coeff_map, iterateFrobenius_def]
  by_cases hm : m ∈ H.support
  · have hmem : H.coeff m ∈ E := IntermediateField.subset_adjoin (ZMod p) (S : Set L)
      (Finset.mem_image.mpr ⟨m, hm, rfl⟩)
    let a : E := ⟨H.coeff m, hmem⟩
    have ha := FiniteField.pow_card a
    rw [hcard] at ha
    simpa only [a, IntermediateField.coe_pow] using congrArg Subtype.val ha
  · rw [notMem_support_iff.mp hm]
    exact zero_pow (Nat.pow_pos (Fact.out : p.Prime).pos).ne'

def orbitProduct (n : ℕ) (H : MvPolynomial σ L) : MvPolynomial σ L :=
  ∏ i ∈ Finset.range n, twist p i H

omit [Algebra (ZMod p) L] in
theorem orbitProduct_ne_zero (n : ℕ) (H : MvPolynomial σ L) (hH : H ≠ 0) :
    orbitProduct p n H ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => twist_ne_zero p i H hH)

omit [Algebra (ZMod p) L] in
theorem orbitProduct_fixed (n : ℕ) (H : MvPolynomial σ L) (hH : H ≠ 0) (hperiod : twist p n H = H) :
    twist p 1 (orbitProduct p n H) = orbitProduct p n H := by
  have hshift : twist p 1 (orbitProduct p n H) = ∏ i ∈ Finset.range n, twist p (i + 1) H := by
    simp only [orbitProduct, twist, map_prod, MvPolynomial.map_map, ← iterateFrobenius_add,
      Nat.add_comm 1]
  have hsucc := Finset.prod_range_succ (fun i => twist p i H) n
  have hsucc' := Finset.prod_range_succ' (fun i => twist p i H) n
  rw [hperiod] at hsucc
  rw [twist_zero] at hsucc'
  apply mul_right_cancel₀ hH
  rw [hshift]
  exact hsucc'.symm.trans hsucc

end Cylinder.FrobeniusPolynomialPeriod

end
