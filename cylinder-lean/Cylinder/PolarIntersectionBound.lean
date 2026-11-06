module

public import Cylinder.PolarJetConditions
public import Cylinder.CompleteIntersectionHilbert

/-! A real complete-intersection bound for the first jets of rational curve points. -/

@[expose] public section
noncomputable section
open scoped Classical

namespace Cylinder.PolarIntersectionBound

open MvPolynomial Module Cylinder.JetEvaluation Cylinder.JetIdeal Cylinder.HilbertEvaluation
open Cylinder.FrobeniusPolar Cylinder.PolarJetConditions

variable {K I : Type*} [Field K] [Infinite K] [Fintype I]

/-- The degree product is proved from the actual Koszul Hilbert calculation,
and each pair of conditions comes from actual first-jet interpolation. -/
theorem two_card_le_degree_product (F G : MvPolynomial (Fin 3) K) (e t : ℕ)
    (he : 0 < e) (ht : 0 < t) (hF : F.IsHomogeneous e) (hG : G.IsHomogeneous t)
    (hF0 : F ≠ 0) (hcop : IsRelPrime F G)
    (v w : I → Fin 3 → K) (hv : ∀ i, v i ≠ 0) (hsep : ProjectivelyDistinct v)
    (hw : ∀ i, Nonradial (v i) (w i))
    (hFjet : ∀ i, eval (v i) F = 0 ∧ eval (v i) (directional (w i) F) = 0)
    (hGjet : ∀ i, eval (v i) G = 0 ∧ eval (v i) (directional (w i) G) = 0) :
    2 * Fintype.card I ≤ e * t := by
  let d := max (2 * Fintype.card I - 1) (e + t - 2)
  have hlower := two_card_le_graded_quotient v w hv hsep hw (Ideal.span {F, G})
    (span_pair_le_firstJetIdeal v w F G hFjet hGjet) d (le_max_left _ _)
  have hdim : finrank K (Forms K d ⧸ JetIdeal.idealPiece (Ideal.span {F, G}) d) = e * t :=
    Cylinder.CompleteIntersectionHilbert.forms_quotient_finrank F G e t d he ht hF hG
      hF0 hcop (le_max_right _ _)
  rwa [hdim] at hlower

variable (p : ℕ) [Fact p.Prime] [CharP K p]

/-- The absolute-irreducible polar estimate once actual relative primality
is established. The degree product and the factor two are not hypotheses. -/
theorem rational_polar_point_bound_of_coprime (n : ℕ) (hn : 0 < n)
    (F : MvPolynomial (Fin 3) K) (hF : F.IsHomogeneous n) (hF0 : F ≠ 0)
    (hcop : IsRelPrime F (polar p F)) (v : I → Fin 3 → K)
    (hv : ∀ i, v i ≠ 0) (hsep : ProjectivelyDistinct v)
    (hfixed : ∀ i, FrobeniusFixed p (v i)) (hzero : ∀ i, eval (v i) F = 0) :
    2 * Fintype.card I ≤ n * (n + p - 1) := by
  choose w hw hD hP hDP using fun i => exists_polar_jet_direction p n F hF
    (v i) (hv i) (hfixed i) (hzero i)
  apply two_card_le_degree_product F (polar p F) n (n + p - 1) hn
    (by have hp := (Fact.out : p.Prime).two_le; omega) hF
    (polar_homogeneous_of_pos p n hn F hF) hF0 hcop v w hv hsep hw
    (fun i => ⟨hzero i, hD i⟩) (fun i => ⟨hP i, hDP i⟩)

end Cylinder.PolarIntersectionBound

end
