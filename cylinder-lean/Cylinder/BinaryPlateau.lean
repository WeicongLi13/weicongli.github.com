module

public import Cylinder.BinaryFormLemma
public import Cylinder.LineFactors
public import Mathlib.RingTheory.Polynomial.UniqueFactorization
public import Mathlib.RingTheory.Coprime.Lemmas
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Plateau factorization in the actual binary polynomial ring

The homogeneous pieces are intersections with an actual ideal, and the Hilbert
values are ranks of maps into the actual quotient ring. Equal adjacent values
force equality in binary growth and a common factor. This file proves the
binary restriction step of `lem:plateau`; it does not claim the generic-line
lifting of that factor to a plane curve.
-/

@[expose] public section
noncomputable section
namespace Cylinder.BinaryPlateau
open MvPolynomial Module
open Cylinder.BinaryFormLemma
variable {K : Type*} [Field K]

abbrev BinaryForms (K : Type*) [Field K] (d : ℕ) := homogeneousSubmodule (Fin 2) K d

instance binaryForms_finiteDimensional (d : ℕ) : FiniteDimensional K (BinaryForms K d) :=
  homogeneous_finiteDimensional d

theorem binaryForms_finrank (d : ℕ) : finrank K (BinaryForms K d) = d + 1 := by
  calc
    _ = finrank K (Polynomial.degreeLE K d) := (Cylinder.BinaryHomogenization.homogeneousDegreeEquiv d).finrank_eq
    _ = d + 1 := by
      rw [← Polynomial.degreeLT_succ_eq_degreeLE]
      exact (Polynomial.degreeLTEquiv K (d + 1)).finrank_eq.trans (by simp)

/-- The actual homogeneous degree-d piece of an actual binary ideal. -/
def piece (J : Ideal (BinaryRing K)) (d : ℕ) : Submodule K (BinaryRing K) :=
  J.restrictScalars K ⊓ BinaryForms K d

instance piece_finiteDimensional (J : Ideal (BinaryRing K)) (d : ℕ) : FiniteDimensional K (piece J d) :=
  Submodule.finiteDimensional_of_le (show piece J d ≤ BinaryForms K d from inf_le_right)

def quotientMap (J : Ideal (BinaryRing K)) (d : ℕ) : BinaryForms K d →ₗ[K] ((BinaryRing K) ⧸ J) :=
  (Ideal.Quotient.mkₐ K J).toLinearMap.comp (BinaryForms K d).subtype

def quotientHilbert (J : Ideal (BinaryRing K)) (d : ℕ) : ℕ :=
  finrank K ↥(LinearMap.range (quotientMap J d))

theorem quotientMap_kernel (J : Ideal (BinaryRing K)) (d : ℕ) :
    LinearMap.ker (quotientMap J d) = (piece J d).comap (BinaryForms K d).subtype := by
  ext P
  change Ideal.Quotient.mk J P.val = 0 ↔ P.val ∈ J ∧ P.val ∈ BinaryForms K d
  rw [Ideal.Quotient.eq_zero_iff_mem]
  exact ⟨fun h => ⟨h, P.property⟩, fun h => h.1⟩

/-- Quotient Hilbert value plus true ideal-piece dimension equals d+1. -/
theorem quotient_dimension (J : Ideal (BinaryRing K)) (d : ℕ) :
    quotientHilbert J d + finrank K (piece J d) = d + 1 := by
  have hr := (quotientMap J d).finrank_range_add_finrank_ker
  rw [quotientMap_kernel,
    (Submodule.comapSubtypeEquivOfLe (show piece J d ≤ BinaryForms K d from inf_le_right)).finrank_eq,
    binaryForms_finrank] at hr
  exact hr

theorem piece_expansion_le (J : Ideal (BinaryRing K)) (d : ℕ) : expansion (piece J d) ≤ piece J (d + 1) := by
  have hmul (j : Fin 2) : (piece J d).map (mulVar j) ≤ piece J (d + 1) := by
    intro P hP
    obtain ⟨Q, hQ, rfl⟩ := Submodule.mem_map.mp hP
    refine ⟨J.mul_mem_left (X j) hQ.1, ?_⟩
    change (X j * Q).IsHomogeneous (d + 1)
    convert (isHomogeneous_X K j).mul hQ.2 using 1; omega
  exact sup_le (hmul 0) (hmul 1)

def InitialDegree (J : Ideal (BinaryRing K)) (z : ℕ) : Prop :=
  piece J z ≠ ⊥ ∧ ∀ d < z, piece J d = ⊥

theorem piece_nonzero_of_initial_le (J : Ideal (BinaryRing K)) (z q : ℕ)
    (hz : InitialDegree J z) (hzq : z ≤ q) : piece J q ≠ ⊥ := by
  obtain ⟨P, hP, hP0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hz.1
  have hpow : ((X (0 : Fin 2) : BinaryRing K) ^ (q - z)).IsHomogeneous (q - z) :=
    isHomogeneous_X_pow (R := K) 0 (q - z)
  have hmem : X (0 : Fin 2) ^ (q - z) * P ∈ piece J q := by
    refine ⟨J.mul_mem_left _ hP.1, ?_⟩
    change (X (0 : Fin 2) ^ (q - z) * P).IsHomogeneous q
    have hh := hpow.mul hP.2
    rw [Nat.sub_add_cancel hzq] at hh
    exact hh
  have hne : X (0 : Fin 2) ^ (q - z) * P ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (X_ne_zero 0)) hP0
  intro hz
  rw [hz, Submodule.mem_bot] at hmem
  exact hne hmem

theorem factorSpace_finrank (G : BinaryRing K) (hG0 : G ≠ 0) (n : ℕ) :
    finrank K (factorSpace G n) = n + 1 := by
  have hinj : Function.Injective (LinearMap.mul K (BinaryRing K) G) :=
    fun P Q h => mul_left_cancel₀ hG0 h
  have he := (Submodule.equivMapOfInjective (LinearMap.mul K (BinaryRing K) G) hinj (BinaryForms K n)).finrank_eq
  change finrank K (BinaryForms K n) = finrank K (factorSpace G n) at he
  rw [binaryForms_finrank] at he
  exact he.symm

theorem factorSpace_expansion (G : BinaryRing K) (c n : ℕ)
    (hG0 : G ≠ 0) (hG : G.IsHomogeneous c) : expansion (factorSpace G n) = factorSpace G (n + 1) := by
  have hU : factorSpace G n ≤ BinaryForms K (c + n) := by
    rintro P ⟨Q, hQ, rfl⟩
    exact hG.mul hQ
  have hU0 : factorSpace G n ≠ ⊥ := by
    intro hz
    have hr := factorSpace_finrank G hG0 n
    rw [hz, finrank_bot] at hr
    omega
  have hle : expansion (factorSpace G n) ≤ factorSpace G (n + 1) := by
    have hmul (j : Fin 2) : (factorSpace G n).map (mulVar j) ≤ factorSpace G (n + 1) := by
      rintro P ⟨Q, hQ, rfl⟩
      obtain ⟨A, hA, rfl⟩ := hQ
      refine ⟨X j * A, ?_, ?_⟩
      · change (X j * A).IsHomogeneous (n + 1)
        convert (isHomogeneous_X K j).mul hA using 1; omega
      · change G * (X j * A) = X j * (G * A)
        ac_rfl
    exact sup_le (hmul 0) (hmul 1)
  have hr := binary_growth (factorSpace G n) (c + n) hU hU0
  let : FiniteDimensional K (factorSpace G (n + 1)) := by unfold factorSpace; infer_instance
  apply Submodule.eq_of_le_of_finrank_le hle
  rw [factorSpace_finrank G hG0 n] at hr
  rw [factorSpace_finrank G hG0 (n + 1)]
  omega

theorem dvd_of_mem_factorSpace (G : BinaryRing K) (n : ℕ) {P : BinaryRing K}
    (hP : P ∈ factorSpace G n) : G ∣ P := by
  obtain ⟨Q, _, hQ⟩ := hP
  exact ⟨Q, hQ.symm⟩

/-- The genuine binary plateau: equal consecutive quotient Hilbert values force
one actual common factor in both adjacent homogeneous ideal pieces. -/
theorem binary_plateau (J : Ideal (BinaryRing K)) (q c : ℕ)
    (hU0 : piece J q ≠ ⊥)
    (hq : quotientHilbert J q = c) (hq1 : quotientHilbert J (q + 1) = c) :
    ∃ G : BinaryRing K, G ≠ 0 ∧ G.IsHomogeneous c ∧ G.totalDegree = c ∧
      piece J q = factorSpace G (q - c) ∧ piece J (q + 1) = factorSpace G (q + 1 - c) := by
  have hu := quotient_dimension J q
  have hv := quotient_dimension J (q + 1)
  rw [hq] at hu
  rw [hq1] at hv
  have hgrowth := binary_growth (piece J q) q inf_le_right hU0
  have hmono := Submodule.finrank_mono (piece_expansion_le J q)
  have hdim : finrank K (expansion (piece J q)) = finrank K (piece J q) + 1 := by omega
  have hspace : expansion (piece J q) = piece J (q + 1) :=
    Submodule.eq_of_le_of_finrank_eq (piece_expansion_le J q) (by omega)
  obtain ⟨G, hG0, hG, hfac⟩ := binary_equality (piece J q) q inf_le_right hU0 hdim
  have hc : q + 1 - finrank K (piece J q) = c := by omega
  rw [hc] at hG
  have hrpos : 0 < finrank K (piece J q) := by
    by_contra hn
    exact hU0 (Submodule.finrank_eq_zero.mp (Nat.eq_zero_of_not_pos hn))
  have huc : finrank K (piece J q) - 1 = q - c := by omega
  rw [huc] at hfac
  refine ⟨G, hG0, hG, hG.totalDegree hG0, hfac, ?_⟩
  rw [← hspace, hfac, factorSpace_expansion G c (q - c) hG0 hG]
  have he : q - c + 1 = q + 1 - c := by omega
  rw [he]


/-- The two independent binary variables are relatively prime in the actual ring. -/
theorem variables_isRelPrime : IsRelPrime (X (0 : Fin 2) : BinaryRing K) (X 1) := by
  have hh := Cylinder.LineFactors.equation_isRelPrime
    (Sum.inr ((0 : K), 0)) (Sum.inl (0 : K)) (by simp)
  simpa [Cylinder.LineFactors.equation, Cylinder.LineDivisibility.graphEquation] using hh

/-- If a nonzero form divides two relatively prime monomial multiples, it divides
the original form. This is proved using the ring's established factorization instance. -/
theorem dvd_of_coprime_multiples (G A u v : BinaryRing K) (hG0 : G ≠ 0)
    (huv : IsRelPrime u v) (hu : G ∣ u * A) (hv : G ∣ v * A) : G ∣ A := by
  obtain ⟨P, Q, hPu, hQA, rfl⟩ := exists_dvd_and_dvd_of_dvd_mul hu
  obtain ⟨B, rfl⟩ := hQA
  have hQ0 : Q ≠ 0 := right_ne_zero_of_mul hG0
  have hPdvd : P ∣ v * B := by
    apply (mul_dvd_mul_iff_left hQ0).mp
    simpa only [mul_assoc, mul_comm, mul_left_comm] using hv
  have hPv : IsRelPrime P v := huv.of_dvd_left hPu
  have hPB := hPv.dvd_of_dvd_mul_left hPdvd
  simpa only [mul_comm P Q] using mul_dvd_mul_left Q hPB

/-- A common divisor of the degree-(q+1) ideal piece divides every lower-degree
homogeneous ideal element, without assuming the desired lower-degree conclusion. -/
theorem divisor_of_all_lower_pieces (J : Ideal (BinaryRing K)) (q : ℕ)
    (G : BinaryRing K) (hG0 : G ≠ 0)
    (hGtop : ∀ P, P ∈ piece J (q + 1) → G ∣ P)
    (P : BinaryRing K) (d : ℕ) (hPd : P.IsHomogeneous d) (hPI : P ∈ J) (hd : d ≤ q + 1) : G ∣ P := by
  have hprod (j : Fin 2) : X j ^ (q + 1 - d) * P ∈ piece J (q + 1) := by
    refine ⟨J.mul_mem_left _ hPI, ?_⟩
    change (X j ^ (q + 1 - d) * P).IsHomogeneous (q + 1)
    have hh := (isHomogeneous_X_pow (R := K) j (q + 1 - d)).mul hPd
    rw [Nat.sub_add_cancel hd] at hh
    exact hh
  exact dvd_of_coprime_multiples G P (X 0 ^ (q + 1 - d)) (X 1 ^ (q + 1 - d)) hG0
    variables_isRelPrime.pow (hGtop _ (hprod 0)) (hGtop _ (hprod 1))

/-- The complete binary plateau factorization, including every lower-degree equation. -/
theorem binary_plateau_all_degrees (J : Ideal (BinaryRing K)) (z q c : ℕ)
    (hz : InitialDegree J z) (hzq : z ≤ q)
    (hq : quotientHilbert J q = c) (hq1 : quotientHilbert J (q + 1) = c) :
    ∃ G : BinaryRing K, G ≠ 0 ∧ G.IsHomogeneous c ∧ G.totalDegree = c ∧
      piece J q = factorSpace G (q - c) ∧ piece J (q + 1) = factorSpace G (q + 1 - c) ∧
      ∀ (d : ℕ) (P : BinaryRing K), P.IsHomogeneous d → P ∈ J → d ≤ q + 1 → G ∣ P := by
  obtain ⟨G, hG0, hGc, hGdeg, hU, hV⟩ :=
    binary_plateau J q c (piece_nonzero_of_initial_le J z q hz hzq) hq hq1
  refine ⟨G, hG0, hGc, hGdeg, hU, hV, ?_⟩
  intro d P hPd hPI hd
  apply divisor_of_all_lower_pieces J q G hG0 ?_ P d hPd hPI hd
  intro F hF
  rw [hV] at hF
  exact dvd_of_mem_factorSpace G (q + 1 - c) hF

end Cylinder.BinaryPlateau




