module

public import Cylinder.LocalPointReindexing

/-! The local theorem for any actual nonzero projectively distinct finite
family of representatives, including scalar-extended rational directions. -/

@[expose] public section
noncomputable section
open scoped Classical BigOperators

namespace Cylinder.LocalCurveFamily
open Module MvPolynomial Cylinder.HilbertEvaluation Cylinder.PlaneBinaryReduction
open Cylinder.HilbertCharacterFormulas Cylinder.ComponentCharacterNumeric
open Cylinder.LocalPointReindexing Cylinder.LocalRepresentativeTransport
open Cylinder.LocalCurveTheorem

variable {K I : Type*} [Field K] [Infinite K] [Fintype I]

theorem finite_point_model (v : I → Fin 3 → K) (hv : ∀ i, v i ≠ 0)
    (hsep : ProjectivelyDistinct v) :
    ∃ D : Finset (PlanePointModel.Plane K), ∃ E : I ≃ D, ∃ a : I → K,
      (∀ i, a i ≠ 0) ∧
      PlanePointModel.representatives D = (fun P : D => a (E.symm P) • v (E.symm P)) := by
  let point (i : I) : PlanePointModel.Plane K := Projectivization.mk K (v i) (hv i)
  let D : Finset (PlanePointModel.Plane K) := Finset.univ.image point
  have hinj : Function.Injective point := by
    intro i j hij
    by_contra hne
    have heq : Projectivization.mk K (v j) (hv j) = Projectivization.mk K (v i) (hv i) := hij.symm
    obtain ⟨c, hc⟩ := (Projectivization.mk_eq_mk_iff' K (v j) (v i) (hv j) (hv i)).mp heq
    exact hsep i j hne c hc.symm
  let f : I → D := fun i => ⟨point i, Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩
  have hbij : Function.Bijective f := by
    constructor
    · intro i j hij
      exact hinj (congrArg Subtype.val hij)
    · intro P
      obtain ⟨i, hi, hpoint⟩ := Finset.mem_image.mp P.property
      exact ⟨i, Subtype.ext hpoint⟩
  let E := Equiv.ofBijective f hbij
  choose a ha using fun i => Projectivization.exists_smul_eq_mk_rep K (v i) (hv i)
  refine ⟨D, E, fun i => (a i : K), fun i => Units.ne_zero (a i), ?_⟩
  funext P
  have hpoint : point (E.symm P) = P.val := congrArg Subtype.val (E.apply_symm_apply P)
  change P.val.rep = (a (E.symm P) : K) • v (E.symm P)
  rw [← hpoint]
  exact (ha (E.symm P)).symm

theorem local_curve_interpolation (v : I → Fin 3 → K) (hv : ∀ i, v i ≠ 0)
    (hsep : ProjectivelyDistinct v) (F : PlaneRing K) (e d m : ℕ)
    (hF : F.IsHomogeneous e) (hirr : Irreducible F) (hs : InitialDegree v e)
    (hFzero : ∀ i, eval (v i) F = 0) (hm : 0 < m)
    (hsmall : 4 * m + 2 < e) (hd : 2 * e ≤ d)
    (u : I → K) (hu : ∀ i, u i ≠ 0) (μ : ℕ → I → K) (hμ0 : μ 0 = u)
    (hrel : ∀ q ≤ 2 * m + 2, PowerEvaluationRelation.Relation v (μ q) (d - q))
    (hconn : ∀ i, 0 < i → i < e → numericalCharacter v (i - 1) ≤ numericalCharacter v i + 1)
    (hplateau : ∀ r < 4, increment (numericalCharacter v) d (3 * m + r) = m)
    (T : Finset I) (hcard : e * (5 * m + 2) < T.card)
    (hrec : ∀ i ∈ T, ∀ q, q + 2 ≤ 2 * m + 2 →
      μ (q + 2) i / u i = (μ 1 i / u i) * (μ (q + 1) i / u i) -
        ((μ 1 i / u i) ^ 2 - μ 2 i / u i) * (μ q i / u i)) :
    ∃ f g : PlaneRing K, f.IsHomogeneous 1 ∧ g.IsHomogeneous 2 ∧
      (∀ i, μ 1 i = eval (v i) f * u i) ∧ (∀ i, μ 2 i = eval (v i) g * u i) := by
  obtain ⟨D, E, a, ha, hreps⟩ := finite_point_model v hv hsep
  let v' := fun i => a i • v i
  have hs' : InitialDegree (PlanePointModel.representatives D) e := by
    rw [hreps]
    exact (initialDegree_reindex E v' e).mpr ((initialDegree_rescaling v a ha e).mpr hs)
  have hchar : numericalCharacter (PlanePointModel.representatives D) = numericalCharacter v := by
    rw [hreps, numericalCharacter_reindex E v', numericalCharacter_rescaling v a ha]
  let u' : I → K := fun i => u i / a i ^ d
  let μ' : ℕ → I → K := fun q i => μ q i / a i ^ (d - q)
  have hFzero' : ∀ P : D, eval P.val.rep F = 0 := by
    intro P
    change eval (PlanePointModel.representatives D P) F = 0
    rw [hreps, LinearEvaluationTransport.homogeneous_eval_smul F e hF, hFzero, mul_zero]
  have hu' : ∀ P : D, u' (E.symm P) ≠ 0 := fun P =>
    div_ne_zero (hu _) (pow_ne_zero d (ha _))
  have hμ0' : (fun P : D => μ' 0 (E.symm P)) = fun P : D => u' (E.symm P) := by
    funext P
    simp only [μ', u', Nat.sub_zero, hμ0]
  have hrel' : ∀ q ≤ 2 * m + 2,
      PowerEvaluationRelation.Relation (PlanePointModel.representatives D)
        (fun P : D => μ' q (E.symm P)) (d - q) := by
    intro q hq
    rw [hreps]
    exact relation_reindex E v' (μ' q) (d - q)
      (LinearEvaluationTransport.relation_after_rescaling v (μ q) a ha (d - q) (hrel q hq))
  have hconn' : ∀ i, 0 < i → i < e →
      numericalCharacter (PlanePointModel.representatives D) (i - 1) ≤
        numericalCharacter (PlanePointModel.representatives D) i + 1 := by
    simpa only [hchar] using hconn
  have hplateau' : ∀ r < 4,
      increment (numericalCharacter (PlanePointModel.representatives D)) d (3 * m + r) = m := by
    simpa only [hchar] using hplateau
  let T' : Finset D := T.map E.toEmbedding
  have hcard' : e * (5 * m + 2) < T'.card := by simpa only [T', Finset.card_map] using hcard
  have hrec' : ∀ P ∈ T', ∀ q, q + 2 ≤ 2 * m + 2 →
      μ' (q + 2) (E.symm P) / u' (E.symm P) =
        (μ' 1 (E.symm P) / u' (E.symm P)) * (μ' (q + 1) (E.symm P) / u' (E.symm P)) -
          ((μ' 1 (E.symm P) / u' (E.symm P)) ^ 2 - μ' 2 (E.symm P) / u' (E.symm P)) *
            (μ' q (E.symm P) / u' (E.symm P)) := by
    intro P hP q hq
    have hi : E.symm P ∈ T := by
      obtain ⟨i, hi, hEi⟩ := Finset.mem_map.mp hP
      change E i = P at hEi
      simpa only [← hEi, Equiv.symm_apply_apply] using hi
    have hratio (n : ℕ) (hn : n ≤ 2 * m + 2) :
        μ' n (E.symm P) / u' (E.symm P) =
          a (E.symm P) ^ n * (μ n (E.symm P) / u (E.symm P)) :=
      quotient_rescaling _ _ _ (ha _) (hu _) d n (by omega)
    rw [hratio (q + 2) hq, hratio 1 (by omega), hratio (q + 1) (by omega),
      hratio 2 (by omega), hratio q (by omega), pow_one]
    exact recurrence_rescaling (a (E.symm P)) (fun n => μ n (E.symm P) / u (E.symm P)) q
      (hrec (E.symm P) hi q hq)
  obtain ⟨f, g, hf, hg, hfirst, hsecond⟩ := LocalCurveTheorem.local_curve_interpolation
    D F e d m hF hirr hs' hFzero' hm hsmall hd (fun P : D => u' (E.symm P)) hu'
    (fun (q : ℕ) (P : D) => μ' q (E.symm P)) hμ0' hrel' hconn' hplateau' T' hcard' hrec'
  refine ⟨f, g, hf, hg, ?_, ?_⟩
  · intro i
    have hh := hfirst (E i)
    change μ' 1 (E.symm (E i)) = eval (PlanePointModel.representatives D (E i)) f * u' (E.symm (E i)) at hh
    rw [hreps, E.symm_apply_apply] at hh
    simp only [μ', u', E.symm_apply_apply] at hh
    exact interpolation_unscaling (a i) (μ 1 i) (u i) (ha i) d 1 (by omega) (v i) f hf hh
  · intro i
    have hh := hsecond (E i)
    change μ' 2 (E.symm (E i)) = eval (PlanePointModel.representatives D (E i)) g * u' (E.symm (E i)) at hh
    rw [hreps, E.symm_apply_apply] at hh
    simp only [μ', u', E.symm_apply_apply] at hh
    exact interpolation_unscaling (a i) (μ 2 i) (u i) (ha i) d 2 (by omega) (v i) g hg hh

#print axioms finite_point_model
#print axioms local_curve_interpolation

end Cylinder.LocalCurveFamily
end
