module

public import Mathlib.RingTheory.Artinian.Ring
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.Algebra.Algebra.Pi

/-! A commutative Artinian ring is the product of its actual maximal
localizations. Nilpotents are retained throughout this decomposition. -/

@[expose] public section
noncomputable section
open scoped Classical

namespace Cylinder.ArtinianLocalDecomposition

variable (R : Type*) [CommRing R] [IsArtinianRing R]

def powerDecomposition (n : ℕ) (hn : nilradical R ^ n = ⊥) :
    R ≃ₐ[R] ∀ m : MaximalSpectrum R, R ⧸ m.asIdeal ^ n :=
  ((AlgEquiv.quotientBot R R).symm.trans (Ideal.quotientEquivAlgOfEq R hn.symm)).trans
    (IsArtinianRing.quotNilradicalPowEquivPi R n)

theorem powerDecomposition_apply (n : ℕ) (hn : nilradical R ^ n = ⊥)
    (r : R) (m : MaximalSpectrum R) :
    powerDecomposition R n hn r m = Ideal.Quotient.mk (m.asIdeal ^ n) r :=
  congrFun ((powerDecomposition R n hn).commutes r) m

theorem quotientPower_isLocalization (n : ℕ) (hn : nilradical R ^ n = ⊥)
    (m : MaximalSpectrum R) :
    IsLocalization m.asIdeal.primeCompl (R ⧸ m.asIdeal ^ n) := by
  let e := powerDecomposition R n hn
  constructor
  constructor
  · intro y
    exact Ideal.Quotient.isUnit_mk_pow_of_notMem m.asIdeal y.property
  · intro z
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective z
    exact ⟨⟨r, 1⟩, by simp⟩
  · intro x y hxy
    let c : R := e.symm (Pi.single m 1)
    have hcvalue : Ideal.Quotient.mk (m.asIdeal ^ n) c = 1 := by
      rw [← powerDecomposition_apply R n hn]
      change e (e.symm (Pi.single m 1)) m = 1
      simp
    have hn0 : n ≠ 0 := by
      intro hz
      have hb : (⊤ : Ideal R) = ⊥ := by simpa [hz] using hn
      apply m.isMaximal.ne_top
      apply top_unique
      rw [hb]
      exact bot_le
    have hc : c ∉ m.asIdeal :=
      (Ideal.Quotient.isUnit_mk_pow_iff_notMem m.asIdeal hn0).mp
        (hcvalue.symm ▸ isUnit_one)
    refine ⟨⟨c, hc⟩, ?_⟩
    apply e.injective
    ext j
    change e c j * e x j = e c j * e y j
    have hcj : e c j = (Pi.single m (1 : R ⧸ m.asIdeal ^ n) :
        ∀ j : MaximalSpectrum R, R ⧸ j.asIdeal ^ n) j := by
      exact congrFun (e.apply_symm_apply (Pi.single m 1)) j
    rw [hcj]
    by_cases hj : j = m
    · subst j
      simp only [Pi.single_eq_same, one_mul]
      exact (powerDecomposition_apply R n hn x m).trans
        (hxy.trans (powerDecomposition_apply R n hn y m).symm)
    · simp [Pi.single_eq_of_ne hj]

def quotientPowerEquivLocalization (n : ℕ) (hn : nilradical R ^ n = ⊥)
    (m : MaximalSpectrum R) :
    (R ⧸ m.asIdeal ^ n) ≃ₐ[R] Localization.AtPrime m.asIdeal := by
  letI := quotientPower_isLocalization R n hn m
  exact IsLocalization.algEquiv m.asIdeal.primeCompl _ _

def decompositionEquiv :
    R ≃ₐ[R] ∀ m : MaximalSpectrum R, Localization.AtPrime m.asIdeal := by
  let n := Classical.choose (IsArtinianRing.isNilpotent_nilradical (R := R))
  have hn' : nilradical R ^ n = ⊥ := by
    simpa only [Ideal.zero_eq_bot] using
      Classical.choose_spec (IsArtinianRing.isNilpotent_nilradical (R := R))
  exact (powerDecomposition R n hn').trans
    (AlgEquiv.piCongrRight (quotientPowerEquivLocalization R n hn'))

theorem decompositionEquiv_apply (r : R) (m : MaximalSpectrum R) :
    decompositionEquiv R r m = algebraMap R (Localization.AtPrime m.asIdeal) r :=
  congrFun ((decompositionEquiv R).commutes r) m

end Cylinder.ArtinianLocalDecomposition
end
