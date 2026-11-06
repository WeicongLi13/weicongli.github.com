module

public import Cylinder.ArtinianLocalDecomposition
public import Mathlib.RingTheory.LocalRing.Length
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank

/-! Actual local lengths of a finite dimensional commutative algebra.
The local terms are lengths of maximal localizations, not redefined
global dimensions. Over an algebraically closed field their sum is
the dimension of the original algebra. -/

@[expose] public section
noncomputable section
open scoped Classical BigOperators

namespace Cylinder.ArtinianLocalLength

open Module Cylinder.ArtinianLocalDecomposition

variable (K A : Type*) [Field K] [CommRing A] [Algebra K A] [FiniteDimensional K A]

variable [IsArtinianRing A] [Fintype (MaximalSpectrum A)]

abbrev LocalFactor (m : MaximalSpectrum A) := Localization.AtPrime m.asIdeal

omit [Fintype (MaximalSpectrum A)] in
theorem localFactor_finiteDimensional (m : MaximalSpectrum A) :
    FiniteDimensional K (LocalFactor A m) :=
  FiniteDimensional.of_surjective (IsScalarTower.toAlgHom K A (LocalFactor A m)).toLinearMap
    (IsArtinianRing.localization_surjective m.asIdeal.primeCompl (LocalFactor A m))

theorem sum_local_finrank :
    ∑ m : MaximalSpectrum A, finrank K (LocalFactor A m) = finrank K A := by
  let (m : MaximalSpectrum A) := localFactor_finiteDimensional K A m
  have h := ((decompositionEquiv A).restrictScalars K).toLinearEquiv.finrank_eq
  rw [Module.finrank_pi_fintype] at h
  exact h.symm

omit [Fintype (MaximalSpectrum A)] in
theorem local_length_eq_finrank [IsAlgClosed K] (m : MaximalSpectrum A) :
    Module.length (LocalFactor A m) (LocalFactor A m) = finrank K (LocalFactor A m) := by
  let L := LocalFactor A m
  let := localFactor_finiteDimensional K A m
  let : IsLocalRing L := IsLocalization.AtPrime.isLocalRing L m.asIdeal
  let : FiniteDimensional K (IsLocalRing.ResidueField L) := Module.Finite.trans L _
  have hres : Module.length K (IsLocalRing.ResidueField L) = 1 := by
    let e : K ≃ₐ[K] IsLocalRing.ResidueField L :=
      AlgEquiv.ofBijective (Algebra.ofId K _) IsAlgClosed.algebraMap_bijective_of_isIntegral
    rw [Module.length_eq_finrank, ← e.toLinearEquiv.finrank_eq, Module.finrank_self, Nat.cast_one]
  have hrestr := IsLocalRing.length_restrictScalars K L L
  have hres' : Module.length (IsLocalRing.ResidueField K) (IsLocalRing.ResidueField L) = 1 := by
    rw [← Module.length_eq_of_surjective (M := IsLocalRing.ResidueField L)
      (IsLocalRing.residue_surjective (R := K))]
    exact hres
  rw [hres', mul_one, Module.length_eq_finrank] at hrestr
  exact hrestr.symm

theorem sum_local_lengths [IsAlgClosed K] :
    ∑ m : MaximalSpectrum A, Module.length (LocalFactor A m) (LocalFactor A m) =
      (finrank K A : ℕ∞) := by
  simp_rw [local_length_eq_finrank K A]
  rw [← Nat.cast_sum, sum_local_finrank K A]

end Cylinder.ArtinianLocalLength
end
