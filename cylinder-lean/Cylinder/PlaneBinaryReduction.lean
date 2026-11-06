module

public import Cylinder.PlaneNumericalCharacter
public import Cylinder.HomogeneousDivision
public import Cylinder.NumericCharacterSequence
public import Mathlib.Tactic.Ring
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination

@[expose] public section
noncomputable section
open scoped Classical BigOperators
namespace Cylinder.PlaneBinaryReduction
open MvPolynomial Module
open Cylinder.HilbertEvaluation Cylinder.PlaneNumericalCharacter
variable {K I : Type*} [Field K] [Fintype I]
local instance planeGradedAlgebra : GradedAlgebra (Forms K) := MvPolynomial.gradedAlgebra

abbrev BinaryRing (K : Type*) [Field K] := MvPolynomial (Fin 2) K
abbrev BinaryForms (K : Type*) [Field K] (d : ℕ) := homogeneousSubmodule (Fin 2) K d

def innerGraph (a b : K) : BinaryRing K := C a * X 0 + C b * X 1

def graphEquation (a b : K) : PlaneRing K := X 0 - (C a * X 1 + C b * X 2)

def graphRestriction (a b : K) : PlaneRing K →ₐ[K] BinaryRing K :=
  aeval (fun i : Fin 3 => Fin.cases (innerGraph a b) (fun j => X j) i)

theorem graphEquation_homogeneous (a b : K) : (graphEquation a b).IsHomogeneous 1 :=
  (isHomogeneous_X K 0).sub ((isHomogeneous_C_mul_X a 1).add (isHomogeneous_C_mul_X b 2))

theorem innerGraph_homogeneous (a b : K) : (innerGraph a b).IsHomogeneous 1 :=
  (isHomogeneous_C_mul_X a 0).add (isHomogeneous_C_mul_X b 1)

omit [Fintype I] in
theorem linear_form_expansion (L : PlaneRing K) (hL : L.IsHomogeneous 1) :
    ∃ c : Fin 3 → K, L = C (c 0) * X 0 + C (c 1) * X 1 + C (c 2) * X 2 := by
  have hspan : L ∈ Submodule.span K (Set.range (X : Fin 3 → PlaneRing K)) := by
    rw [← homogeneousSubmodule_one_eq_span_X]
    exact hL
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hspan
  refine ⟨c, ?_⟩
  rw [← hc]
  simp [Fin.sum_univ_succ, smul_eq_C_mul, add_assoc]

/-- The avoiding form can be chosen monic in X0, by avoiding the extra point e0 as well. -/
theorem exists_graph_avoiding [Infinite K]
    (v : I → Fin 3 → K) (hv : ∀ i, v i ≠ 0) :
    ∃ a b : K, ∀ i, eval (v i) (graphEquation a b) ≠ 0 := by
  let w : Option I → Fin 3 → K := fun i => i.elim (Pi.single 0 1) v
  have hw : ∀ i, w i ≠ 0 := by
    intro i
    cases i with
    | none =>
      intro hz
      have h := congrFun hz (0 : Fin 3)
      simp [w] at h
    | some i => exact hv i
  obtain ⟨L, hL, hLv⟩ := EvaluationProjection.exists_linear_form_avoiding w hw
  obtain ⟨c, hc⟩ := linear_form_expansion L hL
  have hc0 : c 0 ≠ 0 := by
    have h := hLv none
    simpa [w, hc, Pi.single_apply] using h
  let a := -((c 0)⁻¹ * c 1)
  let b := -((c 0)⁻¹ * c 2)
  have heq : graphEquation a b = C ((c 0)⁻¹) * L := by
    have hinv : C ((c 0)⁻¹) * C (c 0) = (1 : PlaneRing K) := by
      rw [← map_mul, inv_mul_cancel₀ hc0, map_one]
    rw [hc]
    simp only [graphEquation, a, b, map_neg, map_mul, mul_add]
    simp only [← mul_assoc, hinv, one_mul]
    ring
  refine ⟨a, b, fun i => ?_⟩
  rw [heq, map_mul, eval_C]
  exact mul_ne_zero (inv_ne_zero hc0) (hLv (some i))

omit [Fintype I] in
theorem graphRestriction_homogeneous (a b : K) (P : PlaneRing K) (d : ℕ)
    (hP : P.IsHomogeneous d) : (graphRestriction a b P).IsHomogeneous d := by
  have h := hP.aeval (fun i : Fin 3 => Fin.cases (innerGraph a b) (fun j => X j) i)
    (fun i => Fin.cases (innerGraph_homogeneous a b) (fun j => isHomogeneous_X K j) i)
  simpa only [graphRestriction, one_mul] using h

@[simp] theorem graphRestriction_equation (a b : K) : graphRestriction a b (graphEquation a b) = 0 := by
  have hx1 : graphRestriction a b (X (1 : Fin 3)) = X (0 : Fin 2) := by
    change graphRestriction a b (X (0 : Fin 2).succ) = X 0
    simp only [graphRestriction, aeval_X, Fin.cases_succ]
  have hx2 : graphRestriction a b (X (2 : Fin 3)) = X (1 : Fin 2) := by
    change graphRestriction a b (X (1 : Fin 2).succ) = X 1
    simp only [graphRestriction, aeval_X, Fin.cases_succ]
  rw [graphEquation, map_sub, map_add, map_mul, map_mul, hx1, hx2]
  simp only [graphRestriction, aeval_C, aeval_X, Fin.cases_zero, MvPolynomial.algebraMap_eq, innerGraph, sub_self]

@[simp] theorem graphRestriction_X_succ (a b : K) (j : Fin 2) :
    graphRestriction a b (X j.succ) = X j := by simp [graphRestriction]

omit [Fintype I] in
theorem graphRestriction_rename (a b : K) (P : BinaryRing K) :
    graphRestriction a b (rename Fin.succ P) = P := by
  have he : (graphRestriction a b).comp (rename (R := K) Fin.succ) = AlgHom.id K (BinaryRing K) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp
  exact AlgHom.congr_fun he P

omit [Fintype I] in
theorem graphRestriction_eq_nested (a b : K) (P : PlaneRing K) :
    graphRestriction a b P = (MvPolynomial.finSuccEquiv K 2 P).eval (innerGraph a b) := by
  have he : (graphRestriction a b).toRingHom =
      (Polynomial.evalRingHom (innerGraph a b)).comp (MvPolynomial.finSuccEquiv K 2).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [graphRestriction, MvPolynomial.finSuccEquiv_apply]
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i <;>
        simp [graphRestriction, MvPolynomial.finSuccEquiv_X_zero, MvPolynomial.finSuccEquiv_X_succ]
  exact RingHom.congr_fun he P

@[simp] theorem graphEquation_nested (a b : K) :
    MvPolynomial.finSuccEquiv K 2 (graphEquation a b) = Polynomial.X - Polynomial.C (innerGraph a b) := by
  have hx1 : MvPolynomial.finSuccEquiv K 2 (X (1 : Fin 3)) = Polynomial.C (X (0 : Fin 2)) :=
    MvPolynomial.finSuccEquiv_X_succ (R := K) (n := 2) (j := 0)
  have hx2 : MvPolynomial.finSuccEquiv K 2 (X (2 : Fin 3)) = Polynomial.C (X (1 : Fin 2)) :=
    MvPolynomial.finSuccEquiv_X_succ (R := K) (n := 2) (j := 1)
  have hC (c : K) : MvPolynomial.finSuccEquiv K 2 (C c) = Polynomial.C (C c) := by
    simp [MvPolynomial.finSuccEquiv_apply]
  simp [graphEquation, innerGraph, hC, hx1, hx2, MvPolynomial.finSuccEquiv_X_zero]

theorem graphEquation_ne_zero (a b : K) : graphEquation a b ≠ 0 := by
  intro hz
  have hh := congrArg (MvPolynomial.finSuccEquiv K 2) hz
  rw [graphEquation_nested, map_zero] at hh
  exact Polynomial.X_sub_C_ne_zero _ hh

omit [Fintype I] in
theorem graphRestriction_zero_iff_dvd (a b : K) (P : PlaneRing K) :
    graphRestriction a b P = 0 ↔ graphEquation a b ∣ P := by
  rw [graphRestriction_eq_nested, ← Polynomial.IsRoot, ← Polynomial.dvd_iff_isRoot]
  rw [← graphEquation_nested]
  exact map_dvd_iff (MvPolynomial.finSuccEquiv K 2)


instance binaryForms_finiteDimensional (d : ℕ) : FiniteDimensional K (BinaryForms K d) :=
  Cylinder.BinaryFormLemma.homogeneous_finiteDimensional d

theorem binaryForms_finrank (d : ℕ) : finrank K (BinaryForms K d) = d + 1 := by
  calc
    _ = finrank K (Polynomial.degreeLE K d) :=
      (Cylinder.BinaryHomogenization.homogeneousDegreeEquiv d).finrank_eq
    _ = d + 1 := by
      rw [← Polynomial.degreeLT_succ_eq_degreeLE]
      exact (Polynomial.degreeLTEquiv K (d + 1)).finrank_eq.trans (by simp)

def formsRestriction (a b : K) (d : ℕ) : Forms K d →ₗ[K] BinaryForms K d :=
  LinearMap.codRestrict (BinaryForms K d)
    ((graphRestriction a b).toLinearMap.comp (Forms K d).subtype)
    (fun P => graphRestriction_homogeneous a b P.val d P.property)

omit [Fintype I] in
theorem formsRestriction_surjective (a b : K) (d : ℕ) : Function.Surjective (formsRestriction a b d) := by
  intro P
  refine ⟨⟨rename Fin.succ P.val, P.property.rename_isHomogeneous⟩, ?_⟩
  apply Subtype.ext
  exact graphRestriction_rename a b P.val

omit [Fintype I] in
theorem formsRestriction_kernel (a b : K) (d : ℕ) :
    LinearMap.ker (formsRestriction a b (d + 1)) =
      LinearMap.range (multiplicationForm (graphEquation a b) (graphEquation_homogeneous a b) d) := by
  ext P
  constructor
  · intro hP
    have hz : graphRestriction a b P.val = 0 := congrArg Subtype.val (LinearMap.mem_ker.mp hP)
    obtain ⟨Q, hQ⟩ := (graphRestriction_zero_iff_dvd a b P.val).mp hz
    have hQhom : Q.IsHomogeneous d :=
      Cylinder.HomogeneousDivision.quotient_isHomogeneous (graphEquation a b) P.val Q 1 d
        (graphEquation_ne_zero a b) (graphEquation_homogeneous a b)
        (by simpa only [Nat.add_comm] using (show P.val.IsHomogeneous (d + 1) from P.property)) hQ.symm
    exact ⟨⟨Q, hQhom⟩, Subtype.ext hQ.symm⟩
  · rintro ⟨Q, rfl⟩
    apply LinearMap.mem_ker.mpr
    apply Subtype.ext
    change graphRestriction a b (graphEquation a b * Q.val) = 0
    rw [map_mul, graphRestriction_equation, zero_mul]

omit [Fintype I] in
theorem multiplicationForm_injective (a b : K) (d : ℕ) :
    Function.Injective (multiplicationForm (graphEquation a b) (graphEquation_homogeneous a b) d) := by
  intro P Q h
  apply Subtype.ext
  exact mul_left_cancel₀ (graphEquation_ne_zero a b) (congrArg Subtype.val h)

theorem forms_rank_succ (d : ℕ) : finrank K (Forms K (d + 1)) = finrank K (Forms K d) + d + 2 := by
  have hr := (formsRestriction (0 : K) 0 (d + 1)).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr (formsRestriction_surjective 0 0 (d + 1)), finrank_top,
    formsRestriction_kernel, LinearMap.finrank_range_of_inj (multiplicationForm_injective 0 0 d),
    binaryForms_finrank] at hr
  omega

/-- Restricting the actual homogeneous ideal to the binary graph gives an actual binary subspace. -/
def binaryIdealPiece (v : I → Fin 3 → K) (a b : K) (d : ℕ) : Submodule K (BinaryRing K) :=
  (idealPiece v d).map ((graphRestriction a b).toLinearMap.comp (Forms K d).subtype)

omit [Fintype I] in
theorem mem_binaryIdealPiece (v : I → Fin 3 → K) (a b : K) (d : ℕ) (F : BinaryRing K) :
    F ∈ binaryIdealPiece v a b d ↔
      ∃ P : PlaneRing K, P.IsHomogeneous d ∧ P ∈ (vanishingIdeal v).toIdeal ∧ graphRestriction a b P = F := by
  constructor
  · rintro ⟨P, hP, rfl⟩
    exact ⟨P.val, P.property, hP, rfl⟩
  · rintro ⟨P, hP, hPI, hF⟩
    exact ⟨⟨P, hP⟩, hPI, hF⟩

omit [Fintype I] in
theorem binaryIdealPiece_homogeneous (v : I → Fin 3 → K) (a b : K) (d : ℕ) :
    binaryIdealPiece v a b d ≤ BinaryForms K d := by
  intro F hF
  obtain ⟨P, hP, _, rfl⟩ := (mem_binaryIdealPiece v a b d F).mp hF
  exact graphRestriction_homogeneous a b P d hP

instance binaryIdealPiece_finiteDimensional (v : I → Fin 3 → K) (a b : K) (d : ℕ) :
    FiniteDimensional K (binaryIdealPiece v a b d) :=
  Submodule.finiteDimensional_of_le (binaryIdealPiece_homogeneous v a b d)

omit [Fintype I] in
theorem binaryIdealPiece_eq_map (v : I → Fin 3 → K) (a b : K) (d : ℕ) :
    binaryIdealPiece v a b d =
      ((idealPiece v d).map (formsRestriction a b d)).map (BinaryForms K d).subtype := by
  rw [← Submodule.map_comp]
  rfl

omit [Fintype I] in
theorem binaryIdealPiece_finrank (v : I → Fin 3 → K) (a b : K) (d : ℕ) :
    finrank K (binaryIdealPiece v a b d) = finrank K ↥((idealPiece v d).map (formsRestriction a b d)) := by
  have he := (Submodule.equivMapOfInjective (BinaryForms K d).subtype Subtype.val_injective
    ((idealPiece v d).map (formsRestriction a b d))).finrank_eq
  rw [← binaryIdealPiece_eq_map] at he
  exact he.symm

omit [Fintype I] in
theorem binaryIdealPiece_expansion_le (v : I → Fin 3 → K) (a b : K) (d : ℕ) :
    Cylinder.BinaryFormLemma.expansion (binaryIdealPiece v a b d) ≤ binaryIdealPiece v a b (d + 1) := by
  have hmul (j : Fin 2) : (binaryIdealPiece v a b d).map (Cylinder.BinaryFormLemma.mulVar j) ≤
      binaryIdealPiece v a b (d + 1) := by
    intro F hF
    obtain ⟨G, hG, rfl⟩ := Submodule.mem_map.mp hF
    obtain ⟨P, hP, hPI, hPG⟩ := (mem_binaryIdealPiece v a b d G).mp hG
    apply (mem_binaryIdealPiece v a b (d + 1) _).mpr
    refine ⟨X j.succ * P, ?_, ?_, ?_⟩
    · convert (isHomogeneous_X K j.succ).mul hP using 1; omega
    · exact (vanishingIdeal v).toIdeal.mul_mem_left _ hPI
    · change graphRestriction a b (X j.succ * P) = X j * G
      rw [map_mul, graphRestriction_X_succ, hPG]
  exact sup_le (hmul 0) (hmul 1)

omit [Fintype I] in
/-- Once the binary ideal is nonzero, its successive dimensions grow by at least one. -/
theorem binaryIdealPiece_growth (v : I → Fin 3 → K) (a b : K) (d : ℕ)
    (hI : binaryIdealPiece v a b d ≠ ⊥) :
    finrank K (binaryIdealPiece v a b d) + 1 ≤ finrank K (binaryIdealPiece v a b (d + 1)) := by
  have hg := Cylinder.BinaryFormLemma.binary_growth (binaryIdealPiece v a b d) d
    (binaryIdealPiece_homogeneous v a b d) hI
  exact hg.trans (Submodule.finrank_mono (binaryIdealPiece_expansion_le v a b d))


omit [Fintype I] in
theorem artinRelations_restriction (v : I → Fin 3 → K) (a b : K) (d : ℕ) :
    (artinRelations v (graphEquation a b) (graphEquation_homogeneous a b) d).map
      (formsRestriction a b (d + 1)) = (idealPiece v (d + 1)).map (formsRestriction a b (d + 1)) := by
  have hz : (LinearMap.range (multiplicationForm (graphEquation a b) (graphEquation_homogeneous a b) d)).map
      (formsRestriction a b (d + 1)) = ⊥ := by
    apply LinearMap.le_ker_iff_map.mp
    rw [formsRestriction_kernel]
  rw [artinRelations, Submodule.map_sup, hz, sup_bot_eq]

omit [Fintype I] in
/-- The actual Artin dimension is the full binary-form dimension minus the
actual restricted ideal dimension. -/
theorem artinComponent_add_binaryIdealPiece (v : I → Fin 3 → K) (a b : K) (d : ℕ) :
    finrank K (artinComponent v (graphEquation a b) (d + 1)) +
      finrank K (binaryIdealPiece v a b (d + 1)) = d + 2 := by
  have hN : (formsRestriction a b (d + 1)).ker ≤
      artinRelations v (graphEquation a b) (graphEquation_homogeneous a b) d := by
    rw [formsRestriction_kernel]
    exact le_sup_right
  have hn := finrank_map_add_finrank_ker_of_ker_le (formsRestriction a b (d + 1))
    (artinRelations v (graphEquation a b) (graphEquation_homogeneous a b) d) hN
  rw [artinRelations_restriction] at hn
  have hq := (artinRelations v (graphEquation a b) (graphEquation_homogeneous a b) d).finrank_quotient_add_finrank
  have hf := (formsRestriction a b (d + 1)).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr (formsRestriction_surjective a b (d + 1)), finrank_top,
    binaryForms_finrank] at hf
  have hb := binaryIdealPiece_finrank v a b (d + 1)
  have he := (artinRingMap v (graphEquation a b) (d + 1)).quotKerEquivRange.finrank_eq
  rw [artinRingMap_kernel v (graphEquation a b) (graphEquation_homogeneous a b) d] at he
  change finrank K ((Forms K (d + 1)) ⧸ artinRelations v (graphEquation a b) (graphEquation_homogeneous a b) d) =
    finrank K (artinComponent v (graphEquation a b) (d + 1)) at he
  omega
/-- A genuine initial degree, stated solely on the true vanishing spaces. -/
def InitialDegree (v : I → Fin 3 → K) (s : ℕ) : Prop :=
  idealPiece v s ≠ ⊥ ∧ ∀ d < s, idealPiece v d = ⊥

omit [Fintype I] in
theorem binaryIdealPiece_initial_nonzero (v : I → Fin 3 → K) (a b : K)
    (hLv : ∀ i, eval (v i) (graphEquation a b) ≠ 0) (s : ℕ)
    (hs : InitialDegree v s) (hs0 : 0 < s) : binaryIdealPiece v a b s ≠ ⊥ := by
  obtain ⟨P, hPI, hP0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hs.1
  have hpval0 : P.val ≠ 0 := by
    intro hz
    apply hP0
    exact Subtype.ext hz
  have hPideal : P.val ∈ (vanishingIdeal v).toIdeal := hPI
  intro hz
  have hRmem : graphRestriction a b P.val ∈ binaryIdealPiece v a b s :=
    (mem_binaryIdealPiece v a b s _).mpr ⟨P.val, P.property, hPideal, rfl⟩
  rw [hz, Submodule.mem_bot] at hRmem
  obtain ⟨Q, hQ⟩ := (graphRestriction_zero_iff_dvd a b P.val).mp hRmem
  have hQhom : Q.IsHomogeneous (s - 1) :=
    Cylinder.HomogeneousDivision.quotient_isHomogeneous (graphEquation a b) P.val Q 1 (s - 1)
      (graphEquation_ne_zero a b) (graphEquation_homogeneous a b)
      (by convert (show P.val.IsHomogeneous s from P.property) using 1; omega) hQ.symm
  have hQideal : Q ∈ (vanishingIdeal v).toIdeal := by
    rw [← vanishingIdeal_colon v (graphEquation a b) (graphEquation_homogeneous a b) hLv]
    apply Submodule.mem_colon_singleton.mpr
    change Q * graphEquation a b ∈ (vanishingIdeal v).toIdeal
    rw [mul_comm, ← hQ]
    exact hPideal
  have hQpiece : (⟨Q, hQhom⟩ : Forms K (s - 1)) ∈ idealPiece v (s - 1) := hQideal
  rw [hs.2 (s - 1) (by omega), Submodule.mem_bot] at hQpiece
  have hQzero : Q = 0 := congrArg Subtype.val hQpiece
  apply hpval0
  rw [hQ, hQzero, mul_zero]

omit [Fintype I] in
theorem binaryIdealPiece_nonzero_of_initial_le (v : I → Fin 3 → K) (a b : K)
    (hLv : ∀ i, eval (v i) (graphEquation a b) ≠ 0) (s : ℕ)
    (hs : InitialDegree v s) (hs0 : 0 < s) (d : ℕ) (hd : s ≤ d) :
    binaryIdealPiece v a b d ≠ ⊥ := by
  induction d, hd using Nat.le_induction with
  | base => exact binaryIdealPiece_initial_nonzero v a b hLv s hs hs0
  | succ d hd ih =>
    have hg := binaryIdealPiece_growth v a b d ih
    intro hz
    rw [hz, finrank_bot] at hg
    omega

omit [Fintype I] in
theorem firstDifference_decreasing (v : I → Fin 3 → K) (a b : K)
    (hLv : ∀ i, eval (v i) (graphEquation a b) ≠ 0) (s : ℕ)
    (hs : InitialDegree v s) (hs0 : 0 < s) (d : ℕ) (hd : s ≤ d + 1) :
    NumericCharacterSequence.firstDifference (hilbert v) (d + 2) ≤
      NumericCharacterSequence.firstDifference (hilbert v) (d + 1) := by
  have hnonzero := binaryIdealPiece_nonzero_of_initial_le v a b hLv s hs hs0 (d + 1) hd
  have hg := binaryIdealPiece_growth v a b (d + 1) hnonzero
  have hr1 := artinComponent_add_binaryIdealPiece v a b d
  have hr2 := artinComponent_add_binaryIdealPiece v a b (d + 1)
  rw [artinComponent_rank_difference v (graphEquation a b) (graphEquation_homogeneous a b) hLv d] at hr1
  rw [artinComponent_rank_difference v (graphEquation a b) (graphEquation_homogeneous a b) hLv (d + 1)] at hr2
  have heq : d + 1 + 1 = d + 2 := by omega
  rw [heq] at hr2 hg
  change hilbert v (d + 2) - hilbert v (d + 1) ≤ hilbert v (d + 1) - hilbert v d
  omega


omit [Fintype I] in
theorem hilbert_eq_forms_of_idealPiece_bot (v : I → Fin 3 → K) (d : ℕ)
    (hI : idealPiece v d = ⊥) : hilbert v d = finrank K (Forms K d) := by
  have hh := ideal_piece_dimension v d
  rw [← idealPiece_eq_kernel, hI, finrank_bot, Nat.add_zero] at hh
  exact hh

theorem forms_finrank_zero : finrank K (Forms K 0) = 1 := by
  change finrank K (homogeneousSubmodule (Fin 3) K 0) = 1
  rw [homogeneousSubmodule_zero, Submodule.one_eq_span]
  exact finrank_span_singleton (one_ne_zero : (1 : PlaneRing K) ≠ 0)

omit [Fintype I] in
theorem idealPiece_zero [Nonempty I] (v : I → Fin 3 → K) : idealPiece v 0 = ⊥ := by
  apply eq_bot_iff.mpr
  intro P hP
  have hvals := (homogeneous_mem_vanishingIdeal v P.val 0 P.property).mp hP
  have hdegree : P.val.totalDegree = 0 := Nat.eq_zero_of_le_zero
    (show P.val.IsHomogeneous 0 from P.property).totalDegree_le
  have hc := totalDegree_eq_zero_iff_eq_C.mp hdegree
  have hcoeff : P.val.coeff 0 = 0 := by
    have hi := hvals (Classical.choice (inferInstance : Nonempty I))
    rw [hc, eval_C] at hi
    exact hi
  apply Subtype.ext
  change P.val = 0
  rw [hc, hcoeff, map_zero]

omit [Fintype I] in
theorem hilbert_zero [Nonempty I] (v : I → Fin 3 → K) : hilbert v 0 = 1 := by
  rw [hilbert_eq_forms_of_idealPiece_bot v 0 (idealPiece_zero v), forms_finrank_zero]

omit [Fintype I] in
theorem initialDegree_pos [Nonempty I] (v : I → Fin 3 → K) (s : ℕ) (hs : InitialDegree v s) : 0 < s := by
  by_contra hn
  have hz : s = 0 := Nat.eq_zero_of_not_pos hn
  exact hs.1 (hz ▸ idealPiece_zero v)

omit [Fintype I] in
theorem firstDifference_initial [Nonempty I] (v : I → Fin 3 → K) (s : ℕ)
    (hs : InitialDegree v s) (d : ℕ) (hd : d < s) :
    NumericCharacterSequence.firstDifference (hilbert v) d = d + 1 := by
  cases d with
  | zero => exact hilbert_zero v
  | succ d =>
    have hr0 := hilbert_eq_forms_of_idealPiece_bot v d (hs.2 d (by omega))
    have hr1 := hilbert_eq_forms_of_idealPiece_bot v (d + 1) (hs.2 (d + 1) hd)
    have hr := forms_rank_succ (K := K) d
    change hilbert v (d + 1) - hilbert v d = d + 2
    omega

omit [Fintype I] in
theorem firstDifference_first_drop [Nonempty I] (v : I → Fin 3 → K) (a b : K)
    (hLv : ∀ i, eval (v i) (graphEquation a b) ≠ 0) (s : ℕ) (hs : InitialDegree v s) :
    NumericCharacterSequence.firstDifference (hilbert v) s ≤ s := by
  have hs0 := initialDegree_pos v s hs
  obtain ⟨d, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_zero_of_lt hs0)
  have hnonzero := binaryIdealPiece_initial_nonzero v a b hLv (d + 1) hs hs0
  have hpos : 0 < finrank K (binaryIdealPiece v a b (d + 1)) := by
    by_contra hn
    exact hnonzero (Submodule.finrank_eq_zero.mp (Nat.eq_zero_of_not_pos hn))
  have hr := artinComponent_add_binaryIdealPiece v a b d
  rw [artinComponent_rank_difference v (graphEquation a b) (graphEquation_homogeneous a b) hLv d] at hr
  change hilbert v (d + 1) - hilbert v d ≤ d + 1
  omega

/-- Every hypothesis of the numerical reconstruction is proved here from an
actual nonempty finite reduced set of plane points and its genuine initial degree.
In particular the binary Artin monotonicity is no longer an assumed Hilbert property. -/
theorem derivationShape [Infinite K] [Nonempty I]
    (v : I → Fin 3 → K) (hv : ∀ i, v i ≠ 0) (hsep : ProjectivelyDistinct v)
    (s : ℕ) (hs : InitialDegree v s) :
    NumericCharacterSequence.Shape (NumericCharacterSequence.firstDifference (hilbert v)) s (Fintype.card I) := by
  have hs0 := initialDegree_pos v s hs
  obtain ⟨a, b, hLv⟩ := exists_graph_avoiding v hv
  refine ⟨hs0, ?_, firstDifference_first_drop v a b hLv s hs, ?_, ?_⟩
  · exact firstDifference_initial v s hs
  · intro d hd
    cases d with
    | zero => omega
    | succ d => exact firstDifference_decreasing v a b hLv s hs hs0 d hd
  · intro d hd
    cases d with
    | zero =>
      have hcard : 0 < Fintype.card I := Fintype.card_pos_iff.mpr inferInstance
      omega
    | succ d =>
      exact hilbert_difference_eventually_zero v hv hsep d (by omega)

end Cylinder.PlaneBinaryReduction








