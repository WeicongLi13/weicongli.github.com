import NSDensity.CodePolynomial
import NSDensity.CodeTrace
import NSDensity.CodeMinimalIdeal
import NSDensity.CodeWordQuotient
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.RingTheory.PrincipalIdealDomain

/-!
The principal ideal in the paper's quotient ring is exactly the annihilator
of its irreducible check polynomial.  This file declares no external input.
-/

open scoped BigOperators Polynomial

set_option maxHeartbeats 800000

namespace NSDensity.Concrete

/-- Applying a linear functional to every coefficient of a polynomial. -/
noncomputable def functionalPolynomial {F E : Type*} [Field F] [Field E]
    [Algebra F E] (φ : E →ₗ[F] F) (p : E[X]) : F[X] :=
  ⟨⟨p.toFinsupp.coeff.mapRange φ (map_zero φ)⟩⟩

@[simp] theorem functionalPolynomial_coeff {F E : Type*} [Field F] [Field E]
    [Algebra F E] (φ : E →ₗ[F] F) (p : E[X]) (i : ℕ) :
    (functionalPolynomial φ p).coeff i = φ (p.coeff i) := rfl

theorem functionalPolynomial_map_mul {F E : Type*} [Field F] [Field E]
    [Algebra F E] (φ : E →ₗ[F] F) (p : F[X]) (q : E[X]) :
    functionalPolynomial φ (p.map (algebraMap F E) * q) = p * functionalPolynomial φ q := by
  ext i
  simp only [functionalPolynomial_coeff, Polynomial.coeff_mul, Polynomial.coeff_map,
    map_sum]
  apply Finset.sum_congr rfl
  intro j _
  simpa [Algebra.smul_def] using map_smul φ (p.coeff j.1) (q.coeff j.2)

theorem functionalPolynomial_sub {F E : Type*} [Field F] [Field E]
    [Algebra F E] (φ : E →ₗ[F] F) (p q : E[X]) :
    functionalPolynomial φ (p - q) = functionalPolynomial φ p - functionalPolynomial φ q := by
  ext k
  simp

theorem functionalPolynomial_C {F E : Type*} [Field F] [Field E]
    [Algebra F E] (φ : E →ₗ[F] F) (a : E) :
    functionalPolynomial φ (Polynomial.C a) = Polynomial.C (φ a) := by
  ext k
  cases k with
  | zero => simp
  | succ k => simp only [functionalPolynomial_coeff, Polynomial.coeff_C_succ, map_zero]

noncomputable def functionalPolynomialAt {F E : Type*} [Field F] [Field E]
    [Algebra F E] (p : E[X]) : (E →ₗ[F] F) →ₗ[F] F[X] where
  toFun φ := functionalPolynomial φ p
  map_add' φ ψ := by ext k; rfl
  map_smul' r φ := by ext k; rfl

/-- The geometric polynomial whose coefficients are the inverse root powers. -/
noncomputable def rootGeometric {E : Type*} [Field E] (n : ℕ) (a : E) : E[X] :=
  Polynomial.C a * ∑ i ∈ Finset.range n,
    Polynomial.X ^ i * Polynomial.C (a ^ (n - 1 - i))

theorem rootGeometric_factor {E : Type*} [Field E] {n : ℕ} (a : E)
    (ha : a ^ n = 1) :
    (Polynomial.X - Polynomial.C a) * rootGeometric n a =
      Polynomial.C a * (Polynomial.X ^ n - 1 : E[X]) := by
  unfold rootGeometric
  rw [mul_left_comm]
  simp only [map_pow]
  rw [(Commute.all (Polynomial.X : E[X]) (Polynomial.C a)).mul_geom_sum₂]
  simp [← Polynomial.C_pow, ha]

theorem rootGeometric_coeff {E : Type*} [Field E] {n : ℕ} (a : E)
    (ha0 : a ≠ 0) (ha : a ^ n = 1) (k : ℕ) :
    (rootGeometric n a).coeff k = if k < n then (a⁻¹) ^ k else 0 := by
  classical
  simp only [rootGeometric, Polynomial.coeff_C_mul, Polynomial.finsetSum_coeff,
    Polynomial.coeff_mul_C, Polynomial.coeff_X_pow]
  by_cases hk : k < n
  · rw [ite_eq_left hk, Finset.sum_eq_single k]
    · simp only [ite_true, one_mul]
      rw [mul_comm a, ← pow_succ]
      have he : n - 1 - k + 1 = n - k := by omega
      rw [he, inv_pow]
      apply (mul_eq_one_iff_eq_inv₀ (pow_ne_zero k ha0)).1
      rw [← pow_add, Nat.sub_add_cancel hk.le, ha]
    · intro i hi hik
      simp [Ne.symm hik]
    · intro hk'
      exact False.elim (hk' (Finset.mem_range.2 hk))
  · rw [ite_eq_right hk]
    have hz : (∑ i ∈ Finset.range n,
        (if k = i then (1 : E) else 0) * a ^ (n - 1 - i)) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      have hik : i ≠ k := by intro hik; subst i; exact hk (Finset.mem_range.1 hi)
      simp [Ne.symm hik]
    rw [hz, mul_zero]

theorem functional_rootGeometric_eq_wordPolynomial {F E : Type*}
    [Field F] [Field E] [Algebra F E] {n : ℕ} (a : E)
    (ha0 : a ≠ 0) (ha : a ^ n = 1) (φ : E →ₗ[F] F) :
    functionalPolynomial φ (rootGeometric n a) =
      wordPolynomial (fun i : Fin n => φ ((a⁻¹) ^ i.val)) := by
  ext k
  rw [functionalPolynomial_coeff, rootGeometric_coeff a ha0 ha]
  by_cases hk : k < n
  · rw [ite_eq_left hk]
    exact (wordPolynomial_coeff (fun i : Fin n => φ ((a⁻¹) ^ i.val)) ⟨k, hk⟩).symm
  · rw [ite_eq_right hk, map_zero]
    exact (Polynomial.coeff_eq_zero_of_degree_lt
      ((wordPolynomial_degree_lt (fun i : Fin n => φ ((a⁻¹) ^ i.val))).trans_le
        (by exact_mod_cast Nat.le_of_not_gt hk))).symm

noncomputable def inverseFunctionalQuotient {F E : Type*} [Field F] [Field E]
    [Algebra F E] (n : ℕ) (a : E) :
    (E →ₗ[F] F) →ₗ[F] AdjoinRoot (Polynomial.X ^ n - 1 : F[X]) :=
  (AdjoinRoot.mkₐ (Polynomial.X ^ n - 1 : F[X])).toLinearMap.comp
    (functionalPolynomialAt (rootGeometric n a))

theorem inverseFunctionalQuotient_root_mul {F E : Type*} [Field F] [Field E]
    [Algebra F E] {n : ℕ} (a : E) (ha : a ^ n = 1) (φ : E →ₗ[F] F) :
    AdjoinRoot.root (Polynomial.X ^ n - 1 : F[X]) * inverseFunctionalQuotient n a φ =
      inverseFunctionalQuotient n a (φ.comp (LinearMap.mulLeft F a)) := by
  let ψ : E →ₗ[F] F := φ.comp (LinearMap.mulLeft F a)
  have hcomp : functionalPolynomial φ (Polynomial.C a * rootGeometric n a) =
      functionalPolynomial ψ (rootGeometric n a) := by ext k; simp [ψ]
  have hgeo := congrArg (functionalPolynomial φ) (rootGeometric_factor a ha)
  rw [sub_mul, functionalPolynomial_sub] at hgeo
  have hx : functionalPolynomial φ (Polynomial.X * rootGeometric n a) =
      Polynomial.X * functionalPolynomial φ (rootGeometric n a) := by
    simpa using functionalPolynomial_map_mul φ Polynomial.X (rootGeometric n a)
  have hh : functionalPolynomial φ (Polynomial.C a * (Polynomial.X ^ n - 1)) =
      (Polynomial.X ^ n - 1 : F[X]) * Polynomial.C (φ a) := by
    rw [mul_comm]
    have ht := functionalPolynomial_map_mul (F := F) (E := E) φ
      (Polynomial.X ^ n - 1) (Polynomial.C a)
    simpa only [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X,
      Polynomial.map_one, functionalPolynomial_C] using ht
  rw [hx, hcomp, hh] at hgeo
  change AdjoinRoot.mk (Polynomial.X ^ n - 1 : F[X]) Polynomial.X *
      AdjoinRoot.mk (Polynomial.X ^ n - 1 : F[X]) (functionalPolynomial φ (rootGeometric n a)) =
    AdjoinRoot.mk (Polynomial.X ^ n - 1 : F[X]) (functionalPolynomial ψ (rootGeometric n a))
  apply sub_eq_zero.mp
  calc
    _ = AdjoinRoot.mk (Polynomial.X ^ n - 1 : F[X])
        (Polynomial.X * functionalPolynomial φ (rootGeometric n a) -
          functionalPolynomial ψ (rootGeometric n a)) := by rw [map_sub, map_mul]
    _ = AdjoinRoot.mk (Polynomial.X ^ n - 1 : F[X])
        ((Polynomial.X ^ n - 1) * Polynomial.C (φ a)) := congrArg _ hgeo
    _ = 0 := by rw [map_mul, AdjoinRoot.mk_self, zero_mul]

theorem inverseFunctionalQuotient_range_mul {F E : Type*} [Field F] [Field E]
    [Algebra F E] {n : ℕ} (a : E) (ha : a ^ n = 1)
    (c : AdjoinRoot (Polynomial.X ^ n - 1 : F[X]))
    {x : AdjoinRoot (Polynomial.X ^ n - 1 : F[X])}
    (hx : x ∈ LinearMap.range (inverseFunctionalQuotient (F := F) n a)) :
    c * x ∈ LinearMap.range (inverseFunctionalQuotient (F := F) n a) := by
  let R := LinearMap.range (inverseFunctionalQuotient (F := F) n a)
  change x ∈ R at hx
  change c * x ∈ R
  have hroot {y} (hy : y ∈ R) : AdjoinRoot.root (Polynomial.X ^ n - 1 : F[X]) * y ∈ R := by
    obtain ⟨φ, rfl⟩ := hy
    rw [inverseFunctionalQuotient_root_mul a ha]
    exact ⟨_, rfl⟩
  have hpow (k : ℕ) : AdjoinRoot.root (Polynomial.X ^ n - 1 : F[X]) ^ k * x ∈ R := by
    induction k with
    | zero => simpa using hx
    | succ k ih => simpa [pow_succ, mul_assoc, mul_comm, mul_left_comm] using hroot ih
  obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective c
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simpa [map_add, add_mul] using R.add_mem hp hq
  | monomial k r =>
    rw [← Polynomial.C_mul_X_pow_eq_monomial, map_mul, map_pow, AdjoinRoot.mk_X]
    simpa [Algebra.smul_def, mul_assoc] using R.smul_mem r (hpow k)

noncomputable def inverseFunctionalIdeal {F E : Type*} [Field F] [Field E]
    [Algebra F E] {n : ℕ} (a : E) (ha : a ^ n = 1) :
    Ideal (AdjoinRoot (Polynomial.X ^ n - 1 : F[X])) where
  carrier := LinearMap.range (inverseFunctionalQuotient (F := F) n a)
  zero_mem' := Submodule.zero_mem _
  add_mem' := Submodule.add_mem _
  smul_mem' := fun c _ hx => inverseFunctionalQuotient_range_mul a ha c hx

theorem inverseFunctionalQuotient_eq_mk_word {F E : Type*} [Field F] [Field E]
    [Algebra F E] {n : ℕ} (a : E) (ha0 : a ≠ 0) (ha : a ^ n = 1)
    (φ : E →ₗ[F] F) :
    inverseFunctionalQuotient n a φ =
      AdjoinRoot.mk (Polynomial.X ^ n - 1 : F[X])
        (wordPolynomial (fun i : Fin n => φ ((a⁻¹) ^ i.val))) := by
  exact congrArg (AdjoinRoot.mk (Polynomial.X ^ n - 1 : F[X]))
    (functional_rootGeometric_eq_wordPolynomial a ha0 ha φ)

theorem inverseFunctionalIdeal_ne_bot {E : Type*} [Field E] (F : Subfield E)
    {n : ℕ} (hn : 0 < n) (a : E) (ha0 : a ≠ 0) (ha : a ^ n = 1) :
    inverseFunctionalIdeal (F := F) a ha ≠ ⊥ := by
  obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_eq_one F (one_ne_zero : (1 : E) ≠ 0)
  let w : Fin n → F := fun i => φ ((a⁻¹) ^ i.val)
  have hw0 : (wordPolynomial w).coeff 0 = 1 := by
    simpa [w, hφ] using wordPolynomial_coeff w ⟨0, hn⟩
  have hwne : wordPolynomial w ≠ 0 := by
    intro hw
    have hh := congrArg (fun p : F[X] => p.coeff 0) hw
    rw [hw0, Polynomial.coeff_zero] at hh
    exact one_ne_zero hh
  have hdegree : (wordPolynomial w).degree < (Polynomial.X ^ n - 1 : F[X]).degree := by
    simpa only [← Polynomial.C_1, Polynomial.degree_X_pow_sub_C hn] using wordPolynomial_degree_lt w
  have hnonzero : inverseFunctionalQuotient n a φ ≠ 0 := by
    rw [inverseFunctionalQuotient_eq_mk_word a ha0 ha φ]
    exact AdjoinRoot.mk_ne_zero_of_degree_lt (Polynomial.monic_X_pow_sub_one hn.ne') hwne hdegree
  intro hbot
  have hmem : inverseFunctionalQuotient n a φ ∈ inverseFunctionalIdeal (F := F) a ha := ⟨φ, rfl⟩
  exact hnonzero (by simpa only [hbot, Submodule.mem_bot] using hmem)

/-- In a polynomial quotient, the ideal generated by the complementary factor
is exactly the annihilator of the check factor. -/
theorem mem_complementary_ideal_iff_annihilated {F : Type*} [Field F]
    (h f g : F[X]) (hf : f ≠ 0) (hfg : f * g = h) (c : AdjoinRoot h) :
    c ∈ Ideal.span ({AdjoinRoot.mk h g} : Set (AdjoinRoot h)) ↔
      AdjoinRoot.mk h f * c = 0 := by
  constructor
  · intro hc
    obtain ⟨d, hd⟩ := Ideal.mem_span_singleton.mp hc
    rw [hd, ← mul_assoc, ← map_mul, hfg, AdjoinRoot.mk_self, zero_mul]
  · intro hc
    obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective c
    have hdiv : h ∣ f * p := AdjoinRoot.mk_eq_zero.mp (by simpa using hc)
    rw [← hfg, mul_dvd_mul_iff_left hf] at hdiv
    obtain ⟨d, hd⟩ := hdiv
    apply Ideal.mem_span_singleton.mpr
    exact ⟨AdjoinRoot.mk h d, by rw [← map_mul, ← hd]⟩

/-- The paper's actual ideal `⟨(X^n-1)/minpoly(a)⟩` in `F[X]/(X^n-1)`. -/
noncomputable def irreducibleCyclicIdeal {E : Type*} [Field E]
    (F : Subfield E) (n : ℕ) (a : E) : Ideal (AdjoinRoot (Polynomial.X ^ n - 1 : F[X])) :=
  Ideal.span (Set.singleton (AdjoinRoot.mk (Polynomial.X ^ n - 1 : F[X])
    ((Polynomial.X ^ n - 1) / minpoly F a)))

theorem mem_irreducibleCyclicIdeal_iff_annihilated {E : Type*} [Field E] [Finite E]
    (F : Subfield E) {n : ℕ} (a : E) (ha : orderOf a = n)
    (c : AdjoinRoot (Polynomial.X ^ n - 1 : F[X])) :
    c ∈ irreducibleCyclicIdeal F n a ↔
      AdjoinRoot.mk (Polynomial.X ^ n - 1 : F[X]) (minpoly F a) * c = 0 := by
  exact mem_complementary_ideal_iff_annihilated (Polynomial.X ^ n - 1)
    (minpoly F a) ((Polynomial.X ^ n - 1) / minpoly F a)
    (rootCheck_irreducible F a).ne_zero
    (EuclideanDomain.mul_div_cancel' (rootCheck_irreducible F a).ne_zero
      (rootCheck_dvd_cyclicModulus F ha)) c

/-- Every negative-root functional word belongs to exactly the principal
ideal printed in the paper. -/
theorem inverse_functional_word_mem_ideal {E : Type*} [Field E] [Finite E]
    (F : Subfield E) {n : ℕ} (hn : 0 < n) (a : E) (ha : orderOf a = n)
    (φ : E →ₗ[F] F) :
    AdjoinRoot.mk (Polynomial.X ^ n - 1 : F[X])
      (wordPolynomial (fun i : Fin n => φ ((a⁻¹) ^ i.val))) ∈
      irreducibleCyclicIdeal F n a := by
  let h : F[X] := Polynomial.X ^ n - 1
  let f := minpoly F a
  let g := h / f
  have hf : f ≠ 0 := (rootCheck_irreducible F a).ne_zero
  have hfg : f * g = h := EuclideanDomain.mul_div_cancel' hf (rootCheck_dvd_cyclicModulus F ha)
  have hapow : a ^ n = 1 := orderOf_dvd_iff_pow_eq_one.mp (ha ▸ dvd_refl n)
  have ha0 : a ≠ 0 := (orderOf_pos_iff.mp (ha.symm ▸ hn)).isUnit.ne_zero
  have hroot : (Polynomial.X - Polynomial.C a : E[X]) ∣ f.map F.subtype := by
    rw [Polynomial.dvd_iff_isRoot, Polynomial.IsRoot, Polynomial.eval_map]
    exact minpoly.aeval F a
  obtain ⟨d, hd⟩ := hroot
  have hQ : rootGeometric n a = g.map F.subtype * (Polynomial.C a * d) := by
    apply mul_left_cancel₀ (Polynomial.X_sub_C_ne_zero a)
    calc
      (Polynomial.X - Polynomial.C a) * rootGeometric n a =
          Polynomial.C a * (Polynomial.X ^ n - 1) := rootGeometric_factor a hapow
      _ = Polynomial.C a * (f.map F.subtype * g.map F.subtype) := by
        rw [← Polynomial.map_mul, hfg]
        simp [h]
      _ = (Polynomial.X - Polynomial.C a) * (g.map F.subtype * (Polynomial.C a * d)) := by
        rw [hd]
        ring
  have hword : wordPolynomial (fun i : Fin n => φ ((a⁻¹) ^ i.val)) =
      g * functionalPolynomial φ (Polynomial.C a * d) := by
    rw [← functional_rootGeometric_eq_wordPolynomial a ha0 hapow φ, hQ]
    exact functionalPolynomial_map_mul φ g _
  change AdjoinRoot.mk h _ ∈ Ideal.span {AdjoinRoot.mk h g}
  rw [Ideal.mem_span_singleton, hword, map_mul]
  exact dvd_mul_right _ _

theorem inverseFunctionalIdeal_eq_irreducibleCyclicIdeal {E : Type*} [Field E] [Finite E]
    (F : Subfield E) {n : ℕ} (hn : 0 < n) (a : E) (ha : orderOf a = n)
    (hapow : a ^ n = 1) :
    inverseFunctionalIdeal (F := F) a hapow = irreducibleCyclicIdeal F n a := by
  let h : F[X] := Polynomial.X ^ n - 1
  let f := minpoly F a
  let g := h / f
  have hf : Irreducible f := rootCheck_irreducible F a
  have hfg : f * g = h := EuclideanDomain.mul_div_cancel' hf.ne_zero (rootCheck_dvd_cyclicModulus F ha)
  have ha0 : a ≠ 0 := (orderOf_pos_iff.mp (ha.symm ▸ hn)).isUnit.ne_zero
  apply minimalIdeal_eq_of_ne_bot_of_factor h f g hfg hf
    (inverseFunctionalIdeal (F := F) a hapow)
  · intro c hc
    obtain ⟨φ, rfl⟩ := hc
    rw [inverseFunctionalQuotient_eq_mk_word a ha0 hapow φ]
    exact inverse_functional_word_mem_ideal F hn a ha φ
  · exact inverseFunctionalIdeal_ne_bot F hn a ha0 hapow

/-- Exact equality with the paper's ideal, with all its elements represented
by the negative-root functional words. -/
theorem mem_irreducibleCyclicIdeal_iff_inverse_functional_word {E : Type*}
    [Field E] [Finite E] (F : Subfield E) {n : ℕ} (hn : 0 < n)
    (a : E) (ha : orderOf a = n) (c : AdjoinRoot (Polynomial.X ^ n - 1 : F[X])) :
    c ∈ irreducibleCyclicIdeal F n a ↔
      ∃ φ : E →ₗ[F] F, AdjoinRoot.mk (Polynomial.X ^ n - 1 : F[X])
        (wordPolynomial (fun i : Fin n => φ ((a⁻¹) ^ i.val))) = c := by
  have hapow : a ^ n = 1 := orderOf_dvd_iff_pow_eq_one.mp (ha ▸ dvd_refl n)
  have ha0 : a ≠ 0 := (orderOf_pos_iff.mp (ha.symm ▸ hn)).isUnit.ne_zero
  rw [← inverseFunctionalIdeal_eq_irreducibleCyclicIdeal F hn a ha hapow]
  change (∃ φ, inverseFunctionalQuotient n a φ = c) ↔ _
  simp_rw [inverseFunctionalQuotient_eq_mk_word a ha0 hapow]

/-- The exact trace formula in the paper, in its exact quotient ideal.
Both directions are proved, with no trace or ideal representation assumption. -/
theorem mem_irreducibleCyclicIdeal_iff_trace_word {E : Type*}
    [Field E] [Finite E] (F : Subfield E) {n : ℕ} (hn : 0 < n)
    (a : E) (ha : orderOf a = n) (c : AdjoinRoot (Polynomial.X ^ n - 1 : F[X])) :
    c ∈ irreducibleCyclicIdeal F n a ↔
      ∃ b : E, AdjoinRoot.mk (Polynomial.X ^ n - 1 : F[X])
        (wordPolynomial (fun i : Fin n => Algebra.trace F E (b * a ^ (-(i.val : ℤ))))) = c := by
  rw [mem_irreducibleCyclicIdeal_iff_inverse_functional_word F hn a ha]
  constructor
  · rintro ⟨φ, hφ⟩
    obtain ⟨b, hb⟩ := exists_trace_functional F φ
    refine ⟨b, ?_⟩
    simpa only [hb, zpow_neg, zpow_natCast, inv_pow] using hφ
  · rintro ⟨b, hb⟩
    refine ⟨Algebra.traceForm F E b, ?_⟩
    simpa only [Algebra.traceForm_apply, zpow_neg, zpow_natCast, inv_pow] using hb

/-- The coefficient-vector form of the precise principal ideal in the paper. -/
noncomputable def polynomialCyclicCode {E : Type*} [Field E]
    (F : Subfield E) (n : ℕ) (a : E) : Submodule F (Fin n → F) :=
  ((irreducibleCyclicIdeal F n a).restrictScalars F).comap (wordQuotient F n)

@[simp] theorem mem_polynomialCyclicCode {E : Type*} [Field E]
    (F : Subfield E) {n : ℕ} (a : E) (w : Fin n → F) :
    w ∈ polynomialCyclicCode F n a ↔ wordQuotient F n w ∈ irreducibleCyclicIdeal F n a :=
  Iff.rfl

/-- The exact ideal code is the actual generator-matrix code for the inverse
root. This proves the convention change, rather than adding it as an input. -/
theorem polynomialCyclicCode_eq_rootFunctionalCode {E : Type*}
    [Field E] [Finite E] (F : Subfield E) {n : ℕ} (hn : 0 < n)
    (a : E) (ha : orderOf a = n) :
    polynomialCyclicCode F n a = rootFunctionalCode F n a⁻¹ := by
  ext w
  rw [mem_polynomialCyclicCode,
    mem_irreducibleCyclicIdeal_iff_inverse_functional_word F hn a ha]
  constructor
  · rintro ⟨φ, hφ⟩
    refine (mem_functionalCode F (fun i : Fin n => (a⁻¹) ^ i.val) w).2 ⟨φ, ?_⟩
    have hw : (fun i : Fin n => φ ((a⁻¹) ^ i.val)) = w :=
      wordQuotient_injective hn hφ
    intro i
    exact congrFun hw i
  · intro hw
    obtain ⟨φ, hφ⟩ := (mem_functionalCode F (fun i : Fin n => (a⁻¹) ^ i.val) w).1 hw
    exact ⟨φ, congrArg (wordQuotient F n) (funext hφ)⟩

/-- The polynomial ideal and the negative-power trace formula in the paper
are equal as actual submodules of the length-n coefficient-vector space. -/
theorem polynomialCyclicCode_eq_inverseRootTraceCode {E : Type*}
    [Field E] [Finite E] (F : Subfield E) {n : ℕ} (hn : 0 < n)
    (a : E) (ha : orderOf a = n) :
    polynomialCyclicCode F n a = inverseRootTraceCode F n a :=
  (polynomialCyclicCode_eq_rootFunctionalCode F hn a ha).trans
    (inverseRootTraceCode_eq_rootFunctionalCode F n a).symm

#print axioms mem_irreducibleCyclicIdeal_iff_inverse_functional_word
#print axioms mem_irreducibleCyclicIdeal_iff_trace_word
#print axioms polynomialCyclicCode_eq_rootFunctionalCode
#print axioms polynomialCyclicCode_eq_inverseRootTraceCode

end NSDensity.Concrete




