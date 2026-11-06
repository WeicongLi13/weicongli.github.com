module

public import Mathlib.RingTheory.Valuation.PrimeMultiplicity
public import Mathlib.RingTheory.Valuation.ExtendToLocalization
public import Mathlib.RingTheory.Localization.NumDen
public import Mathlib.RingTheory.UniqueFactorizationDomain.Multiplicity
public import Mathlib.Data.ENat.Monoid

/-!
# Prime valuations and removal of denominators

For a unique factorization domain `R` and its fraction field `K`, this
file constructs the additive valuation at every prime element of `R`.
The construction starts with actual prime multiplicities on `R` and
uses Mathlib's extension to localization.  It proves that an element of
`K` belongs to `R` exactly when all these valuations are nonnegative.

This is the algebraic bridge needed after a recurrence argument has
excluded poles.  No valuation laws or denominator-removal conclusion
are assumed as hypotheses.
-/

@[expose] public section

namespace Cylinder.PrimeValuation

/-- The natural embedding of extended natural numbers into extended
integers, preserving the point at infinity. -/
def enatToInt : ℕ∞ →+o WithTop ℤ where
  toAddMonoidHom := (Nat.castAddMonoidHom ℤ).ENatMap
  monotone' := ENat.monotone_map_iff.mpr Nat.mono_cast

@[simp] theorem enatToInt_top : enatToInt ⊤ = ⊤ := rfl

@[simp] theorem enatToInt_nat (n : ℕ) : enatToInt n = ((n : ℤ) : WithTop ℤ) := rfl

@[simp] theorem enatToInt_zero : enatToInt 0 = 0 := by
  exact enatToInt.map_zero

theorem enatToInt_strictMono : StrictMono enatToInt :=
  ENat.strictMono_map_iff.mpr Nat.strictMono_cast

variable {R : Type*} [CommRing R] [IsDomain R]

/-- Prime multiplicity on the original ring, with extended integer
values. -/
noncomputable def onRing {p : R} (hp : Prime p) : AddValuation R (WithTop ℤ) :=
  (multiplicity_addValuation hp).map enatToInt enatToInt_top

@[simp] theorem onRing_apply {p : R} (hp : Prime p) (r : R) :
    onRing hp r = enatToInt (emultiplicity p r) := rfl

variable [UniqueFactorizationMonoid R]

theorem nonZeroDivisors_le_primeCompl {p : R} (hp : Prime p) :
    nonZeroDivisors R ≤ (AddValuation.toValuation (onRing hp)).supp.primeCompl := by
  intro r hr
  change onRing hp r ≠ ⊤
  rw [onRing_apply]
  change ENat.map (Nat.cast : ℕ → ℤ) (emultiplicity p r) ≠ ⊤
  apply ENat.map_eq_top_iff.not.mpr
  exact finiteMultiplicity_iff_emultiplicity_ne_top.mp
    (FiniteMultiplicity.of_prime_left hp (mem_nonZeroDivisors_iff_ne_zero.mp hr))

variable (R) (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]

/-- The actual additive prime valuation on the fraction field. -/
noncomputable def atPrime (p : R) (hp : Prime p) : AddValuation K (WithTop ℤ) :=
  AddValuation.ofValuation
    ((AddValuation.toValuation (onRing hp)).extendToLocalization
      (nonZeroDivisors_le_primeCompl hp) K)

@[simp] theorem atPrime_algebraMap (p : R) (hp : Prime p) (r : R) :
    atPrime R K p hp (algebraMap R K r) = enatToInt (emultiplicity p r) := by
  simp [atPrime, onRing]

/-- Elements of the original ring have nonnegative prime valuations. -/
theorem atPrime_algebraMap_nonnegative (p : R) (hp : Prime p) (r : R) :
    0 ≤ atPrime R K p hp (algebraMap R K r) := by
  rw [atPrime_algebraMap]
  have h := enatToInt.monotone' (show (0 : ℕ∞) ≤ emultiplicity p r from bot_le)
  simpa using h

theorem atPrime_algebraMap_positive_of_dvd (p : R) (hp : Prime p)
    (r : R) (hpr : p ∣ r) : 0 < atPrime R K p hp (algebraMap R K r) := by
  rw [atPrime_algebraMap]
  have h := enatToInt_strictMono (emultiplicity_pos_of_dvd hpr)
  simpa using h

/-- If every prime valuation of a fraction is nonnegative, its reduced
denominator is a unit, so the fraction belongs to the original ring. -/
theorem isInteger_of_nonnegative (x : K)
    (hx : ∀ (p : R) (hp : Prime p), 0 ≤ atPrime R K p hp x) :
    IsLocalization.IsInteger R x := by
  apply (IsFractionRing.isUnit_den_iff (A := R) x).mp
  by_contra hden
  obtain ⟨p, hpIrred, hpDen⟩ := WfDvdMonoid.exists_irreducible_factor hden
    (mem_nonZeroDivisors_iff_ne_zero.mp (IsFractionRing.den R x).property)
  have hp : Prime p := UniqueFactorizationMonoid.irreducible_iff_prime.mp hpIrred
  have hpNum : ¬p ∣ IsFractionRing.num R x := by
    intro h
    exact hp.not_isUnit ((IsFractionRing.num_den_reduced R x) h hpDen)
  have hnum : atPrime R K p hp (algebraMap R K (IsFractionRing.num R x)) = 0 := by
    rw [atPrime_algebraMap, emultiplicity_eq_zero.mpr hpNum, enatToInt_zero]
  have hdenPos : 0 <
      atPrime R K p hp (algebraMap R K (IsFractionRing.den R x)) :=
    atPrime_algebraMap_positive_of_dvd R K p hp _ hpDen
  have hprod : x * algebraMap R K (IsFractionRing.den R x) =
      algebraMap R K (IsFractionRing.num R x) :=
    (IsFractionRing.num_mul_den_eq_num_iff_eq (A := R) (x := x) (y := x)).mpr rfl
  have hvalue := congrArg (atPrime R K p hp) hprod
  rw [AddValuation.map_mul, hnum] at hvalue
  have hle : atPrime R K p hp (algebraMap R K (IsFractionRing.den R x)) ≤
      atPrime R K p hp x +
        atPrime R K p hp (algebraMap R K (IsFractionRing.den R x)) := by
    simpa only [zero_add, add_zero, add_comm] using add_le_add_right (hx p hp)
      (atPrime R K p hp (algebraMap R K (IsFractionRing.den R x)))
  rw [hvalue] at hle
  exact (not_le_of_gt hdenPos) hle

/-- The prime-valuation criterion for membership in a unique
factorization domain inside its fraction field. -/
theorem isInteger_iff_nonnegative (x : K) :
    IsLocalization.IsInteger R x ↔
      ∀ (p : R) (hp : Prime p), 0 ≤ atPrime R K p hp x := by
  constructor
  · rintro ⟨r, rfl⟩ p hp
    exact atPrime_algebraMap_nonnegative R K p hp r
  · exact isInteger_of_nonnegative R K x

end Cylinder.PrimeValuation
