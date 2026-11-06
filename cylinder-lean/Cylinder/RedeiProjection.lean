import Cylinder.RedeiPlane
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-! Averaging all dilates of the smaller factor gives a uniform projection
of the other factor whenever the smaller factor misses a level. -/

namespace Cylinder.RedeiProjection

open scoped BigOperators

variable {p : ℕ} [hp : Fact p.Prime]
variable {V : Type*} [AddCommGroup V] [Module (ZMod p) V] [Fintype V]

private theorem sum_linear_zero (L : V →ₗ[ZMod p] ZMod p) (hL : L ≠ 0)
    (h : ZMod p → ℚ) (hh : ∑ t, h t = 0) (u : ZMod p) :
    (∑ x : V, h (L x + u)) = 0 := by
  classical
  have hc (t : ZMod p) : (∑ x : V, h (L x + t)) = ∑ x : V, h (L x) := by
    obtain ⟨w,rfl⟩ := LinearMap.surjective hL t
    simpa [map_add] using Equiv.sum_comp (Equiv.addRight w) (fun x => h (L x))
  have hz : (∑ t : ZMod p, ∑ x : V, h (L x+t)) = 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro x _
    exact (Equiv.sum_comp (Equiv.addLeft (L x)) h).trans hh
  simp_rw [hc] at hz
  have hmul : (p : ℚ) * (∑ x : V, h (L x)) = 0 := by simpa [nsmul_eq_mul] using hz
  rw [hc]
  exact (mul_eq_zero.mp hmul).resolve_left (by exact_mod_cast hp.out.ne_zero)

/-- If the first tile misses a level of a nonzero linear map, the values
on the second tile sum to zero against every mean-zero rational function. -/
theorem sum_second_of_missing (A B : Finset V)
    (tile : AddSubgroup.IsComplement (A : Set V) (B : Set V)) (hA : A.card = p)
    (L : V →ₗ[ZMod p] ZMod p) (hL : L ≠ 0) (u : ZMod p)
    (miss : ∀ a : A, L a ≠ u) (h : ZMod p → ℚ) (hh : ∑ t, h t = 0) :
    (∑ b : B, h (L b)) = 0 := by
  classical
  let f (k : ZMod p) (ab : A × B) := h (k * (L ab.1 - u) + L ab.2)
  have hinner (ab : A × B) : (∑ k, f k ab) = 0 := by
    let e := (Equiv.mulRight₀ (L ab.1 - u) (sub_ne_zero.mpr (miss ab.1))).trans
      (Equiv.addRight (L ab.2))
    exact (Equiv.sum_comp e h).trans hh
  have houter (k : ZMod p) (hk : k ≠ 0) : (∑ ab, f k ab) = 0 := by
    let e := Equiv.ofBijective _ (RedeiPlane.scalar_dilation_bijective A B tile hA k hk)
    calc
      ∑ ab, f k ab = ∑ ab, h (L (e ab) + (-(k * u))) := by
        apply Finset.sum_congr rfl
        intro ab _
        apply congrArg h
        change k * (L ab.1 - u) + L ab.2 = L (k • (ab.1:V) + ab.2) + (-(k*u))
        simp [map_add,map_smul]
        ring
      _ = ∑ x : V, h (L x + (-(k*u))) := Equiv.sum_comp e (fun x : V => h (L x + (-(k*u))))
      _ = 0 := sum_linear_zero L hL h hh _
  have ht : (∑ k, ∑ ab, f k ab) = 0 := by
    rw [Finset.sum_comm]
    exact Finset.sum_eq_zero (fun ab _ => hinner ab)
  rw [Finset.sum_eq_single (0 : ZMod p) (fun k _ hk => houter k hk) (by simp)] at ht
  have hz : (p : ℚ) * (∑ b : B, h (L b)) = 0 := by
    simpa [f,Fintype.sum_prod_type,nsmul_eq_mul,hA] using ht
  exact (mul_eq_zero.mp hz).resolve_left (by exact_mod_cast hp.out.ne_zero)

/-- In an exact tiling by a p-element set, the first tile projects
bijectively or all fibers on the second have cardinality |B|/p. -/
theorem bijective_or_uniform (A B : Finset V)
    (tile : AddSubgroup.IsComplement (A : Set V) (B : Set V)) (hA : A.card = p)
    (L : V →ₗ[ZMod p] ZMod p) (hL : L ≠ 0) :
    Function.Bijective (fun a : A => L a) ∨
      ∀ v : ZMod p, p * (B.filter fun b => L b = v).card = B.card := by
  classical
  by_cases hs : Function.Surjective (fun a : A => L a)
  · exact Or.inl ((Fintype.bijective_iff_surjective_and_card _).2 ⟨hs, by simpa using hA⟩)
  right
  unfold Function.Surjective at hs
  push Not at hs
  obtain ⟨u,hu⟩ := hs
  intro v
  let h (t : ZMod p) : ℚ := (if t = v then (p : ℚ) else 0) - 1
  have hh : ∑ t : ZMod p, h t = 0 := by simp [h,Finset.sum_sub_distrib,nsmul_eq_mul]
  have hz := sum_second_of_missing A B tile hA L hL u hu h hh
  rw [Finset.sum_coe_sort B (fun b => h (L b))] at hz
  have eq : ((B.filter fun b => L b = v).card : ℚ) * p - B.card = 0 := by
    simpa [h,Finset.sum_sub_distrib,← Finset.sum_filter,nsmul_eq_mul] using hz
  have eq' := sub_eq_zero.mp eq
  exact_mod_cast (mul_comm _ _).trans eq'

private noncomputable def covector {ι : Type*} [Fintype ι] (u : ι → ZMod p) :
    (ι → ZMod p) →ₗ[ZMod p] ZMod p := ∑ i, u i • LinearMap.proj i

private theorem covector_apply {ι : Type*} [Fintype ι] (u x : ι → ZMod p) :
    covector u x = ∑ i, u i * x i := by simp [covector,LinearMap.sum_apply]

private theorem covector_ne {ι : Type*} [Fintype ι] (u : ι → ZMod p) (hu : u ≠ 0) :
    covector u ≠ 0 := by
  classical
  intro h
  apply hu
  ext i
  have he := LinearMap.congr_fun h (Pi.single i 1)
  simpa [covector_apply, Pi.single_apply, Finset.mul_sum, Finset.sum_ite_eq', mul_ite] using he

/-- Every p-point factor of a tiling of a prime-field coordinate space has a
bijective linear projection. The proof sums over all covectors and uses only
orthogonality of the elementary mean-zero function p·1_{0}−1. -/
theorem exists_bijective_projection {ι : Type*} [Fintype ι] (A B : Finset (ι → ZMod p))
    (tile : AddSubgroup.IsComplement (A : Set (ι → ZMod p)) (B : Set (ι → ZMod p)))
    (hA : A.card = p) :
    ∃ L : (ι → ZMod p) →ₗ[ZMod p] ZMod p, Function.Bijective (fun a : A => L a) := by
  classical
  obtain ⟨ab,_⟩ := tile.2 0
  let b₀ : B := ab.2
  let h (t : ZMod p) : ℚ := (if t = 0 then (p : ℚ) else 0) - 1
  have hh : ∑ t, h t = 0 := by simp [h,Finset.sum_sub_distrib,nsmul_eq_mul]
  by_contra! hn
  let f (u : ι → ZMod p) (b : B) := h (covector u ((b:ι → ZMod p) - b₀))
  have houter (u : ι → ZMod p) (hu : u ≠ 0) : (∑ b, f u b) = 0 := by
    have hs : ¬ Function.Surjective (fun a : A => covector u a) := fun sur =>
      hn _ ((Fintype.bijective_iff_surjective_and_card _).2 ⟨sur,by simpa using hA⟩)
    unfold Function.Surjective at hs
    push Not at hs
    obtain ⟨s,hs⟩ := hs
    let d := covector u (b₀ : ι → ZMod p)
    have hh' : (∑ t : ZMod p, h (t-d)) = 0 :=
      by simpa [sub_eq_add_neg] using (Equiv.sum_comp (Equiv.addRight (-d)) h).trans hh
    simpa [f,d,map_sub] using
      sum_second_of_missing A B tile hA (covector u) (covector_ne u hu) s hs (fun t => h (t-d)) hh'
  have hinner (b : B) (hb : b ≠ b₀) : (∑ u, f u b) = 0 := by
    let d := (b:ι → ZMod p) - (b₀:ι → ZMod p)
    have hd : d ≠ 0 := fun hd => hb (Subtype.ext (sub_eq_zero.mp hd))
    simpa [d,f,covector_apply,mul_comm] using sum_linear_zero (covector d) (covector_ne d hd) h hh 0
  have he : (∑ u, ∑ b, f u b) = ∑ b, ∑ u, f u b := Finset.sum_comm
  rw [Finset.sum_eq_single (0 : ι → ZMod p) (fun u _ hu => houter u hu) (by simp),
      Finset.sum_eq_single b₀ (fun b _ hb => hinner b hb) (by simp)] at he
  have eq : (Fintype.card B : ℚ) * (p-1) = (Fintype.card (ι → ZMod p) : ℚ) * (p-1) := by
    simp [f,h,covector_apply,nsmul_eq_mul] at he
    simp only [Fintype.card_coe, Fintype.card_fun, ZMod.card, Nat.cast_pow, mul_sub, mul_one]
    exact he
  have hp' : (1 : ℚ) < p := by exact_mod_cast hp.out.one_lt
  have eq' : Fintype.card B = Fintype.card (ι → ZMod p) := by
    exact_mod_cast (mul_right_cancel₀ (by linarith : (p:ℚ)-1 ≠ 0) eq)
  have cardeq := Fintype.card_of_bijective tile
  change Fintype.card (A × B) = Fintype.card (ι → ZMod p) at cardeq
  rw [Fintype.card_prod,Fintype.card_coe,hA,← eq'] at cardeq
  have hpos : 0 < Fintype.card B := Fintype.card_pos_iff.mpr ⟨b₀⟩
  have hlt : Fintype.card B < p * Fintype.card B := by
    simpa only [one_mul] using Nat.mul_lt_mul_of_pos_right hp.out.one_lt hpos
  exact (Nat.ne_of_lt hlt) cardeq.symm

end Cylinder.RedeiProjection

