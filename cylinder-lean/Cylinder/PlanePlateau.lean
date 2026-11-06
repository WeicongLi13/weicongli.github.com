module

public import Cylinder.BinaryPlateau
public import Cylinder.PlaneBinaryReduction

/-!
# The initial-degree case of the actual plane plateau lemma

The quotient Hilbert function and homogeneous ideal pieces below use an actual
ideal of the three-variable polynomial ring. The case q=z-1 is proved for
these ideals, including nonreduced schemes. The general q>=z lifting from a
binary restriction to a plane common divisor remains outside this file.
-/

@[expose] public section
noncomputable section
namespace Cylinder.PlanePlateau
open MvPolynomial Module
open Cylinder.HilbertEvaluation
variable {K : Type*} [Field K]

/-- The homogeneous piece of an actual plane ideal. -/
def piece (J : Ideal (PlaneRing K)) (d : ℕ) : Submodule K (PlaneRing K) :=
  J.restrictScalars K ⊓ Forms K d

instance piece_finiteDimensional (J : Ideal (PlaneRing K)) (d : ℕ) : FiniteDimensional K (piece J d) :=
  Submodule.finiteDimensional_of_le (show piece J d ≤ Forms K d from inf_le_right)

/-- The actual degree-d quotient map R_d -> R/J. -/
def quotientMap (J : Ideal (PlaneRing K)) (d : ℕ) : Forms K d →ₗ[K] ((PlaneRing K) ⧸ J) :=
  (Ideal.Quotient.mkₐ K J).toLinearMap.comp (Forms K d).subtype

def quotientHilbert (J : Ideal (PlaneRing K)) (d : ℕ) : ℕ :=
  finrank K ↥(LinearMap.range (quotientMap J d))

theorem quotientMap_kernel (J : Ideal (PlaneRing K)) (d : ℕ) :
    LinearMap.ker (quotientMap J d) = (piece J d).comap (Forms K d).subtype := by
  ext P
  change Ideal.Quotient.mk J P.val = 0 ↔ P.val ∈ J ∧ P.val ∈ Forms K d
  rw [Ideal.Quotient.eq_zero_iff_mem]
  exact ⟨fun h => ⟨h, P.property⟩, fun h => h.1⟩

theorem quotient_dimension (J : Ideal (PlaneRing K)) (d : ℕ) :
    quotientHilbert J d + finrank K (piece J d) = finrank K (Forms K d) := by
  have hr := (quotientMap J d).finrank_range_add_finrank_ker
  rw [quotientMap_kernel,
    (Submodule.comapSubtypeEquivOfLe (show piece J d ≤ Forms K d from inf_le_right)).finrank_eq] at hr
  exact hr

def InitialDegree (J : Ideal (PlaneRing K)) (z : ℕ) : Prop :=
  piece J z ≠ ⊥ ∧ ∀ d < z, piece J d = ⊥

theorem quotientHilbert_eq_forms (J : Ideal (PlaneRing K)) (d : ℕ) (hI : piece J d = ⊥) :
    quotientHilbert J d = finrank K (Forms K d) := by
  have hh := quotient_dimension J d
  rw [hI, finrank_bot, Nat.add_zero] at hh
  exact hh

/-- Before the actual initial degree, the first difference equals d+1. -/
theorem initial_firstDifference (J : Ideal (PlaneRing K)) (z d : ℕ)
    (hz : InitialDegree J z) (hd : d < z) :
    Cylinder.NumericCharacterSequence.firstDifference (quotientHilbert J) d = d + 1 := by
  cases d with
  | zero =>
    exact (quotientHilbert_eq_forms J 0 (hz.2 0 hd)).trans Cylinder.PlaneBinaryReduction.forms_finrank_zero
  | succ d =>
    have h0 := quotientHilbert_eq_forms J d (hz.2 d (by omega))
    have h1 := quotientHilbert_eq_forms J (d + 1) (hz.2 (d + 1) hd)
    have hdim := Cylinder.PlaneBinaryReduction.forms_rank_succ (K := K) d
    change quotientHilbert J (d + 1) - quotientHilbert J d = d + 2
    omega

/-- The complete q=z-1 case of `lem:plateau`, on actual plane ideal pieces.
No generic-line or common-divisor assumption occurs in the hypotheses. -/
theorem plane_plateau_initial (J : Ideal (PlaneRing K)) (q c : ℕ)
    (hz : InitialDegree J (q + 1))
    (hq : Cylinder.NumericCharacterSequence.firstDifference (quotientHilbert J) q = c)
    (hq1 : Cylinder.NumericCharacterSequence.firstDifference (quotientHilbert J) (q + 1) = c) :
    ∃ G : PlaneRing K, G ≠ 0 ∧ G.IsHomogeneous c ∧ G.totalDegree = c ∧
      piece J (q + 1) = Submodule.span K {G} ∧
      ∀ (d : ℕ) (P : PlaneRing K), P.IsHomogeneous d → P ∈ J → d ≤ q + 1 → G ∣ P := by
  have hinit := initial_firstDifference J (q + 1) q hz (by omega)
  have hc : c = q + 1 := by omega
  have hprev := quotientHilbert_eq_forms J q (hz.2 q (by omega))
  have hdim := Cylinder.PlaneBinaryReduction.forms_rank_succ (K := K) q
  have hsum := quotient_dimension J (q + 1)
  have hdiff : quotientHilbert J (q + 1) - quotientHilbert J q = c := hq1
  have hpiece : finrank K (piece J (q + 1)) = 1 := by omega
  obtain ⟨G, hG, hG0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hz.1
  have hGc : G.IsHomogeneous c := hc.symm ▸ hG.2
  have hspan : piece J (q + 1) = Submodule.span K {G} :=
    eq_span_singleton_of_mem_of_finrank_eq_one hpiece hG hG0
  refine ⟨G, hG0, hGc, hGc.totalDegree hG0, hspan, ?_⟩
  intro d P hPd hPI hd
  by_cases he : d = q + 1
  · have hP : P ∈ Submodule.span K {G} := by
      rw [← hspan]
      exact ⟨hPI, he ▸ hPd⟩
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hP
    refine ⟨C a, ?_⟩
    rw [← ha, smul_eq_C_mul, mul_comm]
  · have hP : P ∈ piece J d := ⟨hPI, hPd⟩
    rw [hz.2 d (by omega), Submodule.mem_bot] at hP
    rw [hP]
    exact dvd_zero G


/-- Coprimality of two independent coordinate variables in the actual plane ring. -/
theorem variables_isRelPrime : IsRelPrime (X (0 : Fin 3) : PlaneRing K) (X 1) := by
  have hp : Prime (X (0 : Fin 3) : PlaneRing K) := by
    apply (MulEquiv.prime_iff (MvPolynomial.finSuccEquiv K 2)).mp
    rw [MvPolynomial.finSuccEquiv_X_zero]
    exact Polynomial.prime_X
  apply hp.irreducible.isRelPrime_iff_not_dvd.mpr
  intro hdiv
  have hd := (map_dvd_iff (MvPolynomial.finSuccEquiv K 2)).mpr hdiv
  have hx1 : MvPolynomial.finSuccEquiv K 2 (X (1 : Fin 3)) = Polynomial.C (X (0 : Fin 2)) :=
    MvPolynomial.finSuccEquiv_X_succ (R := K) (n := 2) (j := 0)
  rw [MvPolynomial.finSuccEquiv_X_zero, hx1, Polynomial.X_dvd_iff, Polynomial.coeff_C] at hd
  exact X_ne_zero 0 hd

/-- Cancellation of two coprime coordinate multiples in the genuine plane ring. -/
theorem dvd_of_coprime_multiples (G A u v : PlaneRing K) (hG0 : G ≠ 0)
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

/-- The last step of the plane proof: once a divisor of the top-degree system is
known, its divisibility of every lower homogeneous equation is derived using
coprime coordinate powers. This lemma does not supply the missing plane divisor. -/
theorem divisor_of_all_lower_pieces (J : Ideal (PlaneRing K)) (q : ℕ)
    (G : PlaneRing K) (hG0 : G ≠ 0)
    (hGtop : ∀ P, P ∈ piece J (q + 1) → G ∣ P)
    (P : PlaneRing K) (d : ℕ) (hPd : P.IsHomogeneous d) (hPI : P ∈ J) (hd : d ≤ q + 1) : G ∣ P := by
  have hprod (j : Fin 3) : X j ^ (q + 1 - d) * P ∈ piece J (q + 1) := by
    refine ⟨J.mul_mem_left _ hPI, ?_⟩
    change (X j ^ (q + 1 - d) * P).IsHomogeneous (q + 1)
    have hh := (isHomogeneous_X_pow (R := K) j (q + 1 - d)).mul hPd
    rw [Nat.sub_add_cancel hd] at hh
    exact hh
  exact dvd_of_coprime_multiples G P (X 0 ^ (q + 1 - d)) (X 1 ^ (q + 1 - d)) hG0
    variables_isRelPrime.pow (hGtop _ (hprod 0)) (hGtop _ (hprod 1))

end Cylinder.PlanePlateau


