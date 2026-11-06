module
public import Cylinder.BinaryGrowth
@[expose] public section
noncomputable section
namespace Cylinder.BinarySubspace
open Polynomial Module
open Cylinder.BinaryGrowth
variable {K : Type*} [Field K]

/-- The span of the first n actual multiples of g by powers of X. -/
def powerSpan (g : K[X]) (n : ℕ) : Submodule K K[X] :=
  Submodule.span K (Set.range fun i : Fin n => X ^ (i : ℕ) * g)

theorem powerSpan_one (g : K[X]) : powerSpan g 1 = Submodule.span K {g} := by
  ext p
  simp [powerSpan, Fin.eq_zero]

theorem power_mem (g : K[X]) (n i : ℕ) (hi : i < n) :
    X ^ i * g ∈ powerSpan g n :=
  Submodule.subset_span ⟨⟨i, hi⟩, rfl⟩

theorem powerSpan_succ (g : K[X]) (n : ℕ) (hn : 0 < n) :
    powerSpan g n ⊔ (powerSpan g n).map mulX = powerSpan g (n + 1) := by
  apply le_antisymm
  · apply sup_le
    · apply Submodule.span_le.mpr
      rintro p ⟨i, rfl⟩
      exact power_mem g (n + 1) i (by omega)
    · rw [Submodule.map_le_iff_le_comap]
      apply Submodule.span_le.mpr
      rintro p ⟨i, rfl⟩
      change X * (X ^ (i : ℕ) * g) ∈ powerSpan g (n + 1)
      have hh := power_mem g (n + 1) (i.val + 1) (by omega)
      simpa [pow_succ, mul_assoc, mul_comm, mul_left_comm] using hh
  · apply Submodule.span_le.mpr
    rintro p ⟨i, rfl⟩
    by_cases hi : i.val = 0
    · apply (le_sup_left : powerSpan g n ≤ powerSpan g n ⊔ (powerSpan g n).map mulX)
      simpa [hi] using power_mem g n 0 hn
    · apply (le_sup_right : (powerSpan g n).map mulX ≤ powerSpan g n ⊔ (powerSpan g n).map mulX)
      have hii : i.val - 1 < n := by omega
      have hpow := power_mem g n (i.val - 1) hii
      have hmap := Submodule.mem_map_of_mem (f := mulX) hpow
      have hieq : i.val = (i.val - 1) + 1 := by omega
      have hxeq : mulX (X ^ (i.val - 1) * g) = X ^ i.val * g := by
        change X * (X ^ (i.val - 1) * g) = X ^ i.val * g
        rw [← mul_assoc, ← pow_succ', ← hieq]
      rwa [hxeq] at hmap

/-- Pulling back the intersection U ∩ XU by the injective multiplication map. -/
def predecessor (U : Submodule K K[X]) : Submodule K K[X] := U ⊓ U.comap mulX

theorem predecessor_map (U : Submodule K K[X]) :
    (predecessor U).map mulX = U ⊓ U.map mulX := by
  rw [predecessor, ← Submodule.map_inf_eq_map_inf_comap, inf_comm]

theorem predecessor_finrank (U : Submodule K K[X]) [FiniteDimensional K U]
    (heq : finrank K ↥(U ⊔ U.map mulX) = finrank K U + 1) :
    finrank K (predecessor U) + 1 = finrank K U := by
  have he := (Submodule.equivMapOfInjective mulX mulX_injective (predecessor U)).finrank_eq
  rw [predecessor_map] at he
  have hr := Submodule.finrank_sup_add_finrank_inf_eq U (U.map mulX)
  have hx := (Submodule.equivMapOfInjective mulX mulX_injective U).finrank_eq
  omega

/-- Equality forces the actual polynomial subspace to be spanned by a consecutive
string g, Xg, ..., X^(r-1)g. The proof uses dimension induction on the true intersection. -/
theorem equality_powerSpan (U : Submodule K K[X]) [FiniteDimensional K U]
    (hU : U ≠ ⊥)
    (heq : finrank K ↥(U ⊔ U.map mulX) = finrank K U + 1) :
    ∃ g : K[X], g ≠ 0 ∧ U = powerSpan g (finrank K U) := by
  generalize hr : finrank K U = r
  induction r using Nat.strong_induction_on generalizing U with
  | h r ih =>
    cases r with
    | zero =>
      have hz : U = ⊥ := Submodule.finrank_eq_zero.mp hr
      exact False.elim (hU hz)
    | succ n =>
      by_cases hn : n = 0
      · subst n
        obtain ⟨g, hg, hg0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hU
        refine ⟨g, hg0, ?_⟩
        rw [powerSpan_one]
        exact eq_span_singleton_of_mem_of_finrank_eq_one hr hg hg0
      · let W := predecessor U
        let : FiniteDimensional K W :=
          Submodule.finiteDimensional_of_le (show W ≤ U from inf_le_left)
        have hWr : finrank K W = n := by
          have hw := predecessor_finrank U heq
          change finrank K W + 1 = finrank K U at hw
          omega
        have hW : W ≠ ⊥ := by
          intro hz
          have hdim : finrank K W = 0 := by rw [hz]; exact finrank_bot K K[X]
          omega
        have hle : W ⊔ W.map mulX ≤ U := by
          apply sup_le
          · exact inf_le_left
          · rw [Submodule.map_le_iff_le_comap]
            exact inf_le_right
        have hgrowth := finrank_growth W hW
        have hmono := Submodule.finrank_mono hle
        have hWdim : finrank K ↥(W ⊔ W.map mulX) = n + 1 := by omega
        have hWeq : finrank K ↥(W ⊔ W.map mulX) = finrank K W + 1 := by omega
        have hWU : W ⊔ W.map mulX = U :=
          Submodule.eq_of_le_of_finrank_eq hle (by omega)
        obtain ⟨g, hg0, hg⟩ := ih n (by omega) W hW hWeq hWr
        refine ⟨g, hg0, ?_⟩
        rw [← hWU, hg]
        exact powerSpan_succ g n (by omega)


/-- Consecutive powers are exactly multiplication of all polynomials of degree less than n. -/
theorem powerSpan_eq_map_degreeLT (g : K[X]) (n : ℕ) :
    powerSpan g n = (degreeLT K n).map (LinearMap.mul K K[X] g) := by
  classical
  rw [degreeLT_eq_span_X_pow, Submodule.map_span]
  unfold powerSpan
  congr 1
  ext p
  constructor
  · rintro ⟨i, rfl⟩
    refine ⟨X ^ (i : ℕ), ?_, ?_⟩
    · exact Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr i.isLt, rfl⟩
    · change g * X ^ (i : ℕ) = X ^ (i : ℕ) * g
      exact mul_comm _ _
  · rintro ⟨q, hq, rfl⟩
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hq
    refine ⟨⟨i, Finset.mem_range.mp hi⟩, ?_⟩
    change X ^ i * g = g * X ^ i
    exact mul_comm _ _

/-- The complete univariate equality classification, with the standard bounded-degree space. -/
theorem equality_map_degreeLT (U : Submodule K K[X]) [FiniteDimensional K U]
    (hU : U ≠ ⊥)
    (heq : finrank K ↥(U ⊔ U.map mulX) = finrank K U + 1) :
    ∃ g : K[X], g ≠ 0 ∧
      U = (degreeLT K (finrank K U)).map (LinearMap.mul K K[X] g) := by
  obtain ⟨g, hg0, hg⟩ := equality_powerSpan U hU heq
  exact ⟨g, hg0, hg.trans (powerSpan_eq_map_degreeLT _ _)⟩


/-- The factor degree is derived from the original degree bound on U. -/
theorem equality_factor_degree (U : Submodule K K[X]) [FiniteDimensional K U]
    (hU : U ≠ ⊥)
    (heq : finrank K ↥(U ⊔ U.map mulX) = finrank K U + 1)
    (d : ℕ) (hd : U ≤ degreeLE K d) :
    ∃ g : K[X], g ≠ 0 ∧ g.natDegree ≤ d + 1 - finrank K U ∧
      finrank K U ≤ d + 1 ∧
      U = (degreeLT K (finrank K U)).map (LinearMap.mul K K[X] g) := by
  obtain ⟨g, hg0, hg⟩ := equality_powerSpan U hU heq
  have hr : 0 < finrank K U := by
    by_contra hn
    have hz : finrank K U = 0 := Nat.eq_zero_of_not_pos hn
    exact hU (Submodule.finrank_eq_zero.mp hz)
  have hp : X ^ (finrank K U - 1) * g ∈ U := by
    exact (le_of_eq hg.symm) (power_mem g (finrank K U) (finrank K U - 1) (by omega))
  have hb := natDegree_le_iff_degree_le.mpr (mem_degreeLE.mp (hd hp))
  rw [natDegree_mul (pow_ne_zero _ X_ne_zero) hg0, natDegree_X_pow] at hb
  refine ⟨g, hg0, ?_, ?_, hg.trans (powerSpan_eq_map_degreeLT _ _)⟩ <;> omega

end Cylinder.BinarySubspace






