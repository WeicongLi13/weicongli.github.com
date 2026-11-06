module

public import Mathlib.RingTheory.Multiplicity
public import Mathlib.Algebra.BigOperators.Associated
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Tactic.NormNum

/-! Exact prime multiplicities of actual weighted direction products. -/

@[expose] public section
noncomputable section
open scoped Classical BigOperators
namespace Cylinder.ExactRayMomentsMultiplicity
variable {K R I J : Type*} [Field K] [CommRing R] [IsDomain R] [Algebra K R]
variable [Fintype I] [Fintype J]

def directionExponent (dir : J → I) (weight : J → ℕ) (i : I) : ℕ :=
  ∑ j ∈ Finset.univ.filter (fun j => dir j = i), weight j

def directionProduct (dir : J → I) (a : I → R) (scale : J → K) (weight : J → ℕ) : R :=
  ∏ j, (algebraMap K R (scale j) * a (dir j)) ^ weight j

omit [Fintype I] in
theorem directionProduct_nonzero (dir : J → I) (a : I → R) (ha : ∀ i, a i ≠ 0)
    (scale : J → K) (hscale : ∀ j, scale j ≠ 0) (weight : J → ℕ) :
    directionProduct dir a scale weight ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro j _
  apply pow_ne_zero
  apply mul_ne_zero
  · exact ((isUnit_iff_ne_zero.mpr (hscale j)).map (algebraMap K R)).ne_zero
  · exact ha _

omit [Fintype I] in
theorem directionProduct_emultiplicity (dir : J → I) (a : I → R)
    (ha : ∀ i, Prime (a i)) (hsep : ∀ i k, i ≠ k → ¬a i ∣ a k)
    (scale : J → K) (hscale : ∀ j, scale j ≠ 0) (weight : J → ℕ) (i : I) :
    emultiplicity (a i) (directionProduct dir a scale weight) =
      (directionExponent dir weight i : ℕ∞) := by
  have hself : emultiplicity (a i) (a i) = 1 := by
    simpa only [pow_one, Nat.cast_one] using emultiplicity_pow_self_of_prime (ha i) 1
  rw [directionProduct, Finset.emultiplicity_prod (ha i), directionExponent, Finset.sum_filter]
  push_cast
  apply Finset.sum_congr rfl
  intro j _
  have hunit : IsUnit (algebraMap K R (scale j)) :=
    (isUnit_iff_ne_zero.mpr (hscale j)).map (algebraMap K R)
  rw [emultiplicity_pow (ha i), emultiplicity_mul (ha i),
    emultiplicity_of_isUnit_right (ha i).not_isUnit hunit, zero_add]
  by_cases hdir : dir j = i
  · simp only [hdir, hself, mul_one, ite_true]
  · have hzero : emultiplicity (a i) (a (dir j)) = 0 :=
      emultiplicity_eq_zero.mpr (hsep i (dir j) (Ne.symm hdir))
    simp only [hdir, hzero, mul_zero, ite_false]

omit [Fintype I] in
theorem balanced_direction_products_have_poles
    {E : Type*} [Fintype E] (dir : E → I) (blackDir : J → I) (a : I → R)
    (ha : ∀ i, Prime (a i)) (hsep : ∀ i k, i ≠ k → ¬a i ∣ a k)
    (scale : J → K) (hscale : ∀ j, scale j ≠ 0) (weight : J → ℕ) (w : ℕ)
    (hbalance : ∀ i, directionExponent dir (fun _ => 1) i =
      w + 1 + directionExponent blackDir weight i) :
    ∀ i, a i ^ directionExponent dir (fun _ => 1) i ∣
        directionProduct dir a (fun _ => (1 : K)) (fun _ => 1) ∧
      ¬a i ^ directionExponent dir (fun _ => 1) i ∣
        directionProduct blackDir a scale weight := by
  intro i
  have hwhite := directionProduct_emultiplicity dir a ha hsep (fun _ => (1 : K))
    (fun _ => one_ne_zero) (fun _ => 1) i
  have hblack := directionProduct_emultiplicity blackDir a ha hsep scale hscale weight i
  constructor
  · apply pow_dvd_of_le_emultiplicity
    rw [hwhite]
  · apply not_pow_dvd_of_emultiplicity_lt
    rw [hblack]
    have hlt : directionExponent blackDir weight i < directionExponent dir (fun _ => 1) i := by
      rw [hbalance i]
      omega
    exact_mod_cast hlt

end Cylinder.ExactRayMomentsMultiplicity
end
