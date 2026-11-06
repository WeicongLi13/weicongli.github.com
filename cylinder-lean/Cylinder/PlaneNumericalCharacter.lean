module

public import Cylinder.HilbertEvaluation
public import Cylinder.BinaryFormLemma
public import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Homogeneous vanishing ideals and actual Artin reduction pieces

The ideal is the homogeneous core of the intersection of the point-evaluation
kernels. Consequently, its degree-d part is exactly the kernel of the true
homogeneous evaluation map. Avoiding linear forms are nonzero divisors on this
coordinate ring; the degree pieces of the Artin reduction are constructed as
actual submodule quotients below.
-/

@[expose] public section
noncomputable section
open scoped Classical
namespace Cylinder.PlaneNumericalCharacter
open MvPolynomial Module
open Cylinder.HilbertEvaluation
variable {K I : Type*} [Field K] [Fintype I]

local instance planeGradedAlgebra : GradedAlgebra (Forms K) := MvPolynomial.gradedAlgebra

/-- The intersection of actual evaluation kernels at the chosen representatives. -/
def representativeIdeal (v : I → Fin 3 → K) : Ideal (PlaneRing K) :=
  ⨅ i, RingHom.ker (eval (v i))

/-- The projective homogeneous vanishing ideal attached to the representatives. -/
def vanishingIdeal (v : I → Fin 3 → K) : HomogeneousIdeal (Forms K) :=
  (representativeIdeal v).homogeneousCore (Forms K)

omit [Fintype I] in
theorem mem_representativeIdeal (v : I → Fin 3 → K) (P : PlaneRing K) :
    P ∈ representativeIdeal v ↔ ∀ i, eval (v i) P = 0 := by
  simp [representativeIdeal, Submodule.mem_iInf, RingHom.mem_ker]

omit [Fintype I] in
/-- On each homogeneous component this genuine homogeneous ideal is precisely
vanishing at all the represented points. -/
theorem homogeneous_mem_vanishingIdeal (v : I → Fin 3 → K)
    (P : PlaneRing K) (d : ℕ) (hP : P.IsHomogeneous d) :
    P ∈ (vanishingIdeal v).toIdeal ↔ ∀ i, eval (v i) P = 0 := by
  constructor
  · intro h
    exact (mem_representativeIdeal v P).mp
      (Ideal.toIdeal_homogeneousCore_le (Forms K) (representativeIdeal v) h)
  · intro h
    exact Ideal.mem_homogeneousCore_of_homogeneous_of_mem ⟨d, hP⟩
      ((mem_representativeIdeal v P).mpr h)

omit [Fintype I] in
/-- Multiplication by an avoiding linear form is cancellable in the actual
homogeneous point ideal: the colon equality in the proof of `lem:character`. -/
theorem vanishingIdeal_colon (v : I → Fin 3 → K)
    (L : PlaneRing K) (hL : L.IsHomogeneous 1) (hLv : ∀ i, eval (v i) L ≠ 0) :
    (vanishingIdeal v).toIdeal.colon {L} = (vanishingIdeal v).toIdeal := by
  apply le_antisymm
  · intro P hP
    have hLP := Submodule.mem_colon_singleton.mp hP
    change P * L ∈ (vanishingIdeal v).toIdeal at hLP
    rw [mul_comm P L] at hLP
    apply (vanishingIdeal v).isHomogeneous.mem_iff.mpr
    intro d
    have hcomponent := (vanishingIdeal v).isHomogeneous (1 + d) hLP
    rw [DirectSum.coe_decompose_mul_add_of_left_mem (Forms K) hL] at hcomponent
    have hvals := (mem_representativeIdeal v _).mp
      (Ideal.toIdeal_homogeneousCore_le (Forms K) (representativeIdeal v) hcomponent)
    apply (homogeneous_mem_vanishingIdeal v _ d (DirectSum.decompose (Forms K) P d).property).mpr
    intro i
    have hi := hvals i
    rw [map_mul] at hi
    exact (mul_eq_zero.mp hi).resolve_left (hLv i)
  · exact Ideal.le_colon

/-- The avoiding form needed by the colon equality is constructed over an infinite field. -/
theorem exists_avoiding_colon [Infinite K] (v : I → Fin 3 → K) (hv : ∀ i, v i ≠ 0) :
    ∃ L : PlaneRing K, L.IsHomogeneous 1 ∧ (∀ i, eval (v i) L ≠ 0) ∧
      (vanishingIdeal v).toIdeal.colon {L} = (vanishingIdeal v).toIdeal := by
  obtain ⟨L, hL, hLv⟩ := EvaluationProjection.exists_linear_form_avoiding v hv
  exact ⟨L, hL, hLv, vanishingIdeal_colon v L hL hLv⟩


/-- The actual degree-d part of the homogeneous point ideal, inside the space of forms. -/
def idealPiece (v : I → Fin 3 → K) (d : ℕ) : Submodule K (Forms K d) :=
  ((vanishingIdeal v).toIdeal.restrictScalars K).comap (Forms K d).subtype

omit [Fintype I] in
theorem idealPiece_eq_kernel (v : I → Fin 3 → K) (d : ℕ) :
    idealPiece v d = LinearMap.ker (evaluationMap v d) := by
  ext P
  change P.val ∈ (vanishingIdeal v).toIdeal ↔ evaluationMap v d P = 0
  rw [homogeneous_mem_vanishingIdeal v P.val d P.property]
  exact ⟨fun h => funext h, fun h i => congrFun h i⟩

/-- Multiplication by the actual linear form between two successive spaces of forms. -/
def multiplicationForm (L : PlaneRing K) (hL : L.IsHomogeneous 1) (d : ℕ) :
    Forms K d →ₗ[K] Forms K (d + 1) :=
  LinearMap.codRestrict (Forms K (d + 1))
    ((LinearMap.mul K (PlaneRing K) L).comp (Forms K d).subtype)
    (fun P => by change (L * P.val).IsHomogeneous (d + 1); convert hL.mul P.property using 1; omega)

@[simp] theorem multiplicationForm_val (L : PlaneRing K) (hL : L.IsHomogeneous 1)
    (d : ℕ) (P : Forms K d) : (multiplicationForm L hL d P).val = L * P.val := rfl

/-- The homogeneous relations defining the degree-(d+1) Artin quotient piece. -/
def artinRelations (v : I → Fin 3 → K) (L : PlaneRing K) (hL : L.IsHomogeneous 1) (d : ℕ) :
    Submodule K (Forms K (d + 1)) :=
  idealPiece v (d + 1) ⊔ LinearMap.range (multiplicationForm L hL d)

abbrev artinPiece (v : I → Fin 3 → K) (L : PlaneRing K) (hL : L.IsHomogeneous 1) (d : ℕ) :=
  (Forms K (d + 1)) ⧸ artinRelations v L hL d

omit [Fintype I] in
/-- Rank-nullity for a submodule containing the kernel, derived from its restricted map. -/
theorem finrank_map_add_finrank_ker_of_ker_le
    {A B : Type*} [AddCommGroup A] [AddCommGroup B] [Module K A] [Module K B]
    [FiniteDimensional K A] (f : A →ₗ[K] B) (N : Submodule K A) (hN : f.ker ≤ N) :
    finrank K ↥(N.map f) + finrank K f.ker = finrank K N := by
  have hr := (f.domRestrict N).finrank_range_add_finrank_ker
  rw [LinearMap.range_domRestrict, LinearMap.ker_domRestrict,
    (Submodule.comapSubtypeEquivOfLe hN).finrank_eq] at hr
  exact hr

omit [Fintype I] in
theorem artinRelations_evaluation_image (v : I → Fin 3 → K)
    (L : PlaneRing K) (hL : L.IsHomogeneous 1) (hLv : ∀ i, eval (v i) L ≠ 0) (d : ℕ) :
    (artinRelations v L hL d).map (evaluationMap v (d + 1)) =
      (evaluationSpace v d).map (diagonalEquiv (fun i => eval (v i) L) hLv).toLinearMap := by
  have hker : (LinearMap.ker (evaluationMap v (d + 1))).map (evaluationMap v (d + 1)) = ⊥ :=
    LinearMap.le_ker_iff_map.mp le_rfl
  have hcomp : (evaluationMap v (d + 1)).comp (multiplicationForm L hL d) =
      (diagonalEquiv (fun i => eval (v i) L) hLv).toLinearMap.comp (evaluationMap v d) := by
    apply LinearMap.ext
    intro P
    funext i
    exact map_mul (eval (v i)) L P.val
  rw [artinRelations, idealPiece_eq_kernel, Submodule.map_sup, hker, bot_sup_eq,
    ← LinearMap.range_comp, hcomp, LinearMap.range_comp]
  rfl

omit [Fintype I] in
/-- The genuine quotient by I_(d+1)+L R_d has rank equal to the first difference
of the actual evaluation Hilbert function. -/
theorem artinPiece_rank_add (v : I → Fin 3 → K)
    (L : PlaneRing K) (hL : L.IsHomogeneous 1) (hLv : ∀ i, eval (v i) L ≠ 0) (d : ℕ) :
    finrank K (artinPiece v L hL d) + hilbert v d = hilbert v (d + 1) := by
  have hN : (evaluationMap v (d + 1)).ker ≤ artinRelations v L hL d := by
    rw [artinRelations, idealPiece_eq_kernel]
    exact le_sup_left
  have hn := finrank_map_add_finrank_ker_of_ker_le (evaluationMap v (d + 1))
    (artinRelations v L hL d) hN
  have he := (Submodule.equivMapOfInjective
    (diagonalEquiv (fun i => eval (v i) L) hLv).toLinearMap
    (diagonalEquiv (fun i => eval (v i) L) hLv).injective (evaluationSpace v d)).finrank_eq
  rw [artinRelations_evaluation_image v L hL hLv d] at hn
  have hq := (artinRelations v L hL d).finrank_quotient_add_finrank
  have hf := ideal_piece_dimension v (d + 1)
  change finrank K (evaluationSpace v d) = _ at he
  change finrank K ((Forms K (d + 1)) ⧸ artinRelations v L hL d) + hilbert v d = _
  unfold hilbert at hf ⊢
  omega

omit [Fintype I] in
theorem artinPiece_rank_difference (v : I → Fin 3 → K)
    (L : PlaneRing K) (hL : L.IsHomogeneous 1) (hLv : ∀ i, eval (v i) L ≠ 0) (d : ℕ) :
    finrank K (artinPiece v L hL d) = hilbert v (d + 1) - hilbert v d := by
  have hh := artinPiece_rank_add v L hL hLv d
  omega


/-- The actual ideal (I_D,L) in the three-variable polynomial ring. -/
def artinIdeal (v : I → Fin 3 → K) (L : PlaneRing K) : Ideal (PlaneRing K) :=
  (vanishingIdeal v).toIdeal ⊔ Ideal.span {L}

/-- Mapping homogeneous forms into the actual quotient ring R/(I_D,L). -/
def artinRingMap (v : I → Fin 3 → K) (L : PlaneRing K) (d : ℕ) :
    Forms K d →ₗ[K] ((PlaneRing K) ⧸ artinIdeal v L) :=
  (Ideal.Quotient.mkₐ K (artinIdeal v L)).toLinearMap.comp (Forms K d).subtype

/-- The degree-d component in the actual Artin quotient ring. -/
def artinComponent (v : I → Fin 3 → K) (L : PlaneRing K) (d : ℕ) :
    Submodule K ((PlaneRing K) ⧸ artinIdeal v L) := LinearMap.range (artinRingMap v L d)

omit [Fintype I] in
/-- The relations constructed above are exactly the kernel of the map into
R/(I_D,L), proved by taking actual homogeneous components of its ideal expression. -/
theorem artinRingMap_kernel (v : I → Fin 3 → K)
    (L : PlaneRing K) (hL : L.IsHomogeneous 1) (d : ℕ) :
    LinearMap.ker (artinRingMap v L (d + 1)) = artinRelations v L hL d := by
  ext P
  change Ideal.Quotient.mk (artinIdeal v L) P.val = 0 ↔ P ∈ artinRelations v L hL d
  rw [Ideal.Quotient.eq_zero_iff_mem]
  constructor
  · intro hP
    obtain ⟨A, hA, B, hB, hsum⟩ := Submodule.mem_sup.mp hP
    obtain ⟨Q, rfl⟩ := Ideal.mem_span_singleton'.mp hB
    have hc : (DirectSum.decompose (Forms K) A (d + 1) : PlaneRing K) +
        (DirectSum.decompose (Forms K) (Q * L) (d + 1) : PlaneRing K) = P.val := by
      calc
        _ = (DirectSum.decompose (Forms K) (A + Q * L) (d + 1) : PlaneRing K) := by
          rw [DirectSum.decompose_add]
          rfl
        _ = (DirectSum.decompose (Forms K) P.val (d + 1) : PlaneRing K) := by rw [hsum]
        _ = P.val := DirectSum.decompose_of_mem_same (Forms K) P.property
    rw [DirectSum.coe_decompose_mul_add_of_right_mem (Forms K) hL] at hc
    refine Submodule.mem_sup.mpr ⟨DirectSum.decompose (Forms K) A (d + 1), ?_,
      multiplicationForm L hL d (DirectSum.decompose (Forms K) Q d), ?_, ?_⟩
    · change (DirectSum.decompose (Forms K) A (d + 1) : PlaneRing K) ∈ (vanishingIdeal v).toIdeal
      exact (vanishingIdeal v).isHomogeneous (d + 1) hA
    · exact ⟨DirectSum.decompose (Forms K) Q d, rfl⟩
    · apply Subtype.ext
      change (DirectSum.decompose (Forms K) A (d + 1) : PlaneRing K) +
        L * (DirectSum.decompose (Forms K) Q d : PlaneRing K) = P.val
      simpa only [mul_comm L] using hc
  · intro hP
    obtain ⟨A, hA, B, hB, hsum⟩ := Submodule.mem_sup.mp hP
    obtain ⟨Q, rfl⟩ := hB
    have hAI : A.val ∈ (vanishingIdeal v).toIdeal := hA
    have hsum' : A.val + L * Q.val = P.val := congrArg Subtype.val hsum
    have hwhole : A.val + L * Q.val ∈ artinIdeal v L := by
      apply Ideal.add_mem
      · exact (le_sup_left : (vanishingIdeal v).toIdeal ≤ artinIdeal v L) hAI
      · apply (le_sup_right : Ideal.span {L} ≤ artinIdeal v L)
        exact Ideal.mem_span_singleton'.mpr ⟨Q.val, mul_comm _ _⟩
    exact hsum' ▸ hwhole

omit [Fintype I] in
/-- The actual degree component of R/(I_D,L) has dimension ΔH_D. -/
theorem artinComponent_rank_add (v : I → Fin 3 → K)
    (L : PlaneRing K) (hL : L.IsHomogeneous 1) (hLv : ∀ i, eval (v i) L ≠ 0) (d : ℕ) :
    finrank K (artinComponent v L (d + 1)) + hilbert v d = hilbert v (d + 1) := by
  have he := (artinRingMap v L (d + 1)).quotKerEquivRange.finrank_eq
  rw [artinRingMap_kernel v L hL d] at he
  change finrank K ↥(LinearMap.range (artinRingMap v L (d + 1))) + hilbert v d = _
  rw [← he]
  exact artinPiece_rank_add v L hL hLv d

omit [Fintype I] in
theorem artinComponent_rank_difference (v : I → Fin 3 → K)
    (L : PlaneRing K) (hL : L.IsHomogeneous 1) (hLv : ∀ i, eval (v i) L ≠ 0) (d : ℕ) :
    finrank K (artinComponent v L (d + 1)) = hilbert v (d + 1) - hilbert v d := by
  have hh := artinComponent_rank_add v L hL hLv d
  omega

/-- The actual Artin quotient pieces eventually vanish for the actual finite reduced point set. -/
theorem artinComponent_eventually_zero [Infinite K]
    (v : I → Fin 3 → K) (hv : ∀ i, v i ≠ 0) (hsep : ProjectivelyDistinct v)
    (L : PlaneRing K) (hL : L.IsHomogeneous 1) (hLv : ∀ i, eval (v i) L ≠ 0)
    (d : ℕ) (hd : Fintype.card I - 1 ≤ d) : artinComponent v L (d + 1) = ⊥ := by
  let : FiniteDimensional K (artinComponent v L (d + 1)) := by
    unfold artinComponent
    infer_instance
  apply Submodule.finrank_eq_zero.mp
  rw [artinComponent_rank_difference v L hL hLv d]
  exact hilbert_difference_eventually_zero v hv hsep d hd

end Cylinder.PlaneNumericalCharacter





