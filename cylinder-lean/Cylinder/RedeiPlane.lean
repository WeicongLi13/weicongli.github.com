import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.GroupTheory.Complement
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Nat.Factorization.Induction
import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

/-! Dilation of an additive tiling. The Frobenius map in the auxiliary group
algebra proves the prime case without assuming that dilations preserve tiles. -/

namespace Cylinder.RedeiPlane

open scoped BigOperators

variable {V α β : Type*} [AddCommGroup V] [Fintype V] [Fintype α] [Fintype β]

private noncomputable def mask (R : Type*) [CommRing R] (f : α → V) : AddMonoidAlgebra R V :=
  ∑ i, AddMonoidAlgebra.single (f i) 1

omit [Fintype V] in
private theorem mask_mul (R : Type*) [CommRing R] (f : α → V) (g : β → V) :
    mask R f * mask R g = mask R (fun ab : α × β => f ab.1 + g ab.2) := by
  classical
  simp [mask, Fintype.sum_prod_type, Finset.sum_mul, Finset.mul_sum]
  exact Finset.sum_comm

private theorem mask_mul_all (R : Type*) [CommRing R] (f : α → V) :
    mask R f * mask R (id : V → V) = Fintype.card α • mask R (id : V → V) := by
  classical
  rw [mask_mul]
  unfold mask
  rw [Fintype.sum_prod_type]
  have ht (a : α) :
      (∑ b : V, AddMonoidAlgebra.single (f a + b) (1 : R)) =
        ∑ b : V, AddMonoidAlgebra.single b (1 : R) :=
    Equiv.sum_comp (Equiv.addLeft (f a)) (fun b => AddMonoidAlgebra.single b (1 : R))
  simp [ht]

private theorem mask_pow_mul_all (R : Type*) [CommRing R] (f : α → V) (n : ℕ) :
    mask R f ^ n * mask R (id : V → V) = (Fintype.card α)^n • mask R (id : V → V) := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ', mul_assoc, ih, mul_smul_comm, mask_mul_all, ← mul_nsmul, pow_succ, mul_comm (Fintype.card α)]

omit [AddCommGroup V] in
private theorem all_coeff (R : Type*) [CommRing R] (v : V) :
    (mask R (id : V → V)).coeff v = 1 := by
  classical
  simp [mask, Finsupp.single_apply, Finset.sum_ite_eq', Finsupp.finsetSum_apply]

omit [AddCommGroup V] [Fintype V] in
private theorem absent_coeff (R : Type*) [CommRing R] (f : α → V) (v : V)
    (h : ∀ i, f i ≠ v) : (mask R f).coeff v = 0 := by
  classical
  simp [mask, Finsupp.finsetSum_apply, h]

/-- Multiplying the first summand by a prime not dividing its cardinality
preserves unique representations in every finite abelian group. -/
theorem prime_dilation_bijective (f : α → V) (g : β → V)
    (tile : Function.Bijective (fun ab : α × β => f ab.1 + g ab.2))
    (r : ℕ) (hr : r.Prime) (hdiv : ¬ r ∣ Fintype.card α) :
    Function.Bijective (fun ab : α × β => r • f ab.1 + g ab.2) := by
  classical
  let : Fact r.Prime := ⟨hr⟩
  let : CharP (AddMonoidAlgebra (ZMod r) V) r :=
    { cast_eq_zero_iff := fun n => by
        change AddMonoidAlgebra.single 0 (n : ZMod r) = 0 ↔ r ∣ n
        simp [ZMod.natCast_eq_zero_iff] }
  have hu : mask (ZMod r) f * mask (ZMod r) g = mask (ZMod r) (id : V → V) := by
    rw [mask_mul]
    exact (Equiv.ofBijective _ tile).sum_comp (fun v => AddMonoidAlgebra.single v 1)
  have hf : (mask (ZMod r) f)^r = mask (ZMod r) (fun a => r • f a) := by
    unfold mask
    rw [sum_pow_char]
    simp
  have hr' : r - 1 + 1 = r := Nat.sub_add_cancel hr.one_le
  have he : mask (ZMod r) (fun ab : α × β => r • f ab.1 + g ab.2) =
      (Fintype.card α)^(r-1) • mask (ZMod r) (id : V → V) := by
    rw [← mask_mul (ZMod r) (fun a => r • f a) g, ← hf]
    calc
      _ = (mask (ZMod r) f ^ (r-1) * mask (ZMod r) f) * mask (ZMod r) g := by rw [← pow_succ, hr']
      _ = _ := by rw [mul_assoc, hu, mask_pow_mul_all]
  apply (Fintype.bijective_iff_surjective_and_card _).2
  refine ⟨?_, Fintype.card_of_bijective tile⟩
  intro v
  by_contra! hn
  have hz := congrArg (fun x : AddMonoidAlgebra (ZMod r) V => x.coeff v) he
  change (mask (ZMod r) _).coeff v = _ at hz
  rw [absent_coeff _ _ _ hn] at hz
  have h0 : (Fintype.card α : ZMod r) ≠ 0 := fun h => hdiv ((ZMod.natCast_eq_zero_iff ..).1 h)
  rw [AddMonoidAlgebra.coeff_smul_apply, all_coeff, nsmul_eq_mul, mul_one, Nat.cast_pow] at hz
  exact (pow_ne_zero _ h0) hz.symm

/-- Sands' dilation lemma for a positive integer coprime to the size of
the first factor. The factors are parameterized, so this includes arbitrary
finite abelian group factorizations and avoids intermediate cardinality casts. -/
theorem dilation_bijective (f : α → V) (g : β → V)
    (tile : Function.Bijective (fun ab : α × β => f ab.1 + g ab.2))
    (n : ℕ) (hn : n ≠ 0) (hc : n.Coprime (Fintype.card α)) :
    Function.Bijective (fun ab : α × β => n • f ab.1 + g ab.2) := by
  induction n using induction_on_primes with
  | zero => exact (hn rfl).elim
  | one => simpa using tile
  | prime_mul r n hr ih =>
    have H := Nat.coprime_mul_iff_left.mp hc
    have hn' : n ≠ 0 := by intro h; simp [h] at hn
    simpa [mul_smul] using
      prime_dilation_bijective (fun a => n • f a) g (ih hn' H.2) r hr (hr.coprime_iff_not_dvd.mp H.1)

/-- For prime-field factors, the translates of the scaled first factor
still give unique representations. The scalar may be any nonzero residue. -/
theorem scalar_dilation_bijective {p : ℕ} [hp : Fact p.Prime] [Module (ZMod p) V]
    (A B : Finset V) (tile : AddSubgroup.IsComplement (A : Set V) (B : Set V))
    (hA : A.card = p) (k : ZMod p) (hk : k ≠ 0) :
    Function.Bijective (fun ab : A × B => k • (ab.1 : V) + ab.2) := by
  have hn : k.val ≠ 0 := by
    intro h
    apply hk
    rw [← ZMod.natCast_zmod_val k, h, Nat.cast_zero]
  have hc : k.val.Coprime (Fintype.card A) := by
    rw [Fintype.card_coe, hA, Nat.coprime_comm, hp.out.coprime_iff_not_dvd]
    exact Nat.not_dvd_of_pos_of_lt (Nat.pos_of_ne_zero hn) (ZMod.val_lt k)
  have h := dilation_bijective (Subtype.val : A → V) (Subtype.val : B → V) tile k.val hn hc
  simpa only [← Nat.cast_smul_eq_nsmul (ZMod p), ZMod.natCast_zmod_val] using h

/-- Two distinct points of the smaller tile and two points of the larger
tile cannot determine the same direction. -/
theorem no_common_direction {p : ℕ} [Fact p.Prime] [Module (ZMod p) V]
    (A B : Finset V) (tile : AddSubgroup.IsComplement (A : Set V) (B : Set V))
    (hA : A.card = p) (a a' : A) (b b' : B) (ha : a ≠ a')
    (k : ZMod p) (hk : k ≠ 0) :
    k • ((a : V) - a') ≠ (b : V) - b' := by
  intro he
  rw [smul_sub, sub_eq_sub_iff_add_eq_add] at he
  have hinj := (scalar_dilation_bijective A B tile hA k hk).1
  have hpair : (a,b') = (a',b) := hinj (by simpa [add_comm] using he)
  exact ha (congrArg Prod.fst hpair)

abbrev Plane (p : ℕ) := Fin 2 → ZMod p

/-- For every nonzero linear projection of the plane onto the field, one
of the two tiles maps bijectively to the field. Otherwise, the nonzero
differences from colliding pairs would lie in the same one-dimensional kernel. -/
theorem projection_dichotomy {p : ℕ} [Fact p.Prime] (A B : Finset (Plane p))
    (tile : AddSubgroup.IsComplement (A : Set (Plane p)) (B : Set (Plane p)))
    (hA : A.card = p) (hB : B.card = p)
    (L : Plane p →ₗ[ZMod p] ZMod p) (hL : L ≠ 0) :
    Function.Bijective (fun a : A => L a) ∨ Function.Bijective (fun b : B => L b) := by
  classical
  have hdim : Module.finrank (ZMod p) (LinearMap.ker L) = 1 := by
    have h := Module.Dual.finrank_ker_add_one_of_ne_zero hL
    have h' : Module.finrank (ZMod p) (Plane p) = 2 := by simp [Plane]
    omega
  by_cases inj : Function.Injective (fun a : A => L a)
  · left
    exact (Fintype.bijective_iff_injective_and_card _).2 ⟨inj, by simpa using hA⟩
  right
  apply (Fintype.bijective_iff_injective_and_card _).2
  refine ⟨?_, by simpa using hB⟩
  intro b b' he
  change L (b : Plane p) = L (b' : Plane p) at he
  by_contra hneB
  simp only [Function.Injective, not_forall] at inj
  push Not at inj
  obtain ⟨a, a', heA, hneA⟩ := inj
  let x : LinearMap.ker L := ⟨(a : Plane p) - a', by
    change L ((a : Plane p) - a') = 0
    rw [map_sub, heA, sub_self]⟩
  let y : LinearMap.ker L := ⟨(b : Plane p) - b', by
    change L ((b : Plane p) - b') = 0
    rw [map_sub, he, sub_self]⟩
  have hx : x ≠ 0 := fun h => hneA <| Subtype.ext <| sub_eq_zero.mp
    (show (a : Plane p) - a' = 0 from congrArg Subtype.val h)
  obtain ⟨k, hk⟩ := exists_smul_eq_of_finrank_eq_one hdim hx y
  have hk' : k • ((a : Plane p) - a') = (b : Plane p) - b' := congrArg Subtype.val hk
  have hk0 : k ≠ 0 := by
    intro hk0
    rw [hk0, zero_smul] at hk'
    exact hneB (Subtype.ext (sub_eq_zero.mp hk'.symm))
  exact no_common_direction A B tile hA a a' b b' hneA k hk0 hk'

/-- The affine-coordinate projection used by the polynomial direction bound. -/
theorem slope_dichotomy {p : ℕ} [Fact p.Prime] (A B : Finset (Plane p))
    (tile : AddSubgroup.IsComplement (A : Set (Plane p)) (B : Set (Plane p)))
    (hA : A.card = p) (hB : B.card = p) (t : ZMod p) :
    Function.Bijective (fun a : A => a.1 0 + t * a.1 1) ∨
      Function.Bijective (fun b : B => b.1 0 + t * b.1 1) := by
  let L : Plane p →ₗ[ZMod p] ZMod p :=
    LinearMap.proj 0 + t • LinearMap.proj 1
  have hL : L ≠ 0 := by
    intro h
    have he := LinearMap.congr_fun h (![1,0] : Plane p)
    simp [L] at he
  exact projection_dichotomy A B tile hA hB L hL

/-- For a fixed nonzero covector, evaluation on one factor takes every
residue exactly once. -/
theorem dot_dichotomy {p : ℕ} [Fact p.Prime] (A B : Finset (Plane p))
    (tile : AddSubgroup.IsComplement (A : Set (Plane p)) (B : Set (Plane p)))
    (hA : A.card = p) (hB : B.card = p) (u : Plane p) (hu : u ≠ 0) :
    Function.Bijective (fun a : A => ∑ i, a.1 i * u i) ∨
      Function.Bijective (fun b : B => ∑ i, b.1 i * u i) := by
  classical
  let L : Plane p →ₗ[ZMod p] ZMod p :=
    u 0 • LinearMap.proj 0 + u 1 • LinearMap.proj 1
  have hL : L ≠ 0 := by
    intro h
    have hx := LinearMap.congr_fun h (![1,0] : Plane p)
    have hy := LinearMap.congr_fun h (![0,1] : Plane p)
    simp [L] at hx hy
    apply hu
    ext j
    fin_cases j <;> assumption
  simpa [L,Fin.sum_univ_two,mul_comm] using projection_dichotomy A B tile hA hB L hL

private theorem exists_noninjective_projection {p : ℕ} [hp : Fact p.Prime]
    (S : Finset (Plane p)) (hS : S.card = p) :
    ∃ L : Plane p →ₗ[ZMod p] ZMod p, L ≠ 0 ∧ ¬ Function.Injective (fun x : S => L x) := by
  classical
  have : Nontrivial S := Fintype.one_lt_card_iff_nontrivial.mp (by simpa [hS] using hp.out.one_lt)
  obtain ⟨a,b,hn⟩ := exists_pair_ne S
  let v : Plane p := (a : Plane p) - b
  let L : Plane p →ₗ[ZMod p] ZMod p := (v 1) • LinearMap.proj 0 - (v 0) • LinearMap.proj 1
  have hLv : L v = 0 := by simp [L, mul_comm]
  have hL : L ≠ 0 := by
    intro h
    have hx := LinearMap.congr_fun h (![1,0] : Plane p)
    have hy := LinearMap.congr_fun h (![0,1] : Plane p)
    simp [L] at hx hy
    apply hn
    apply Subtype.ext
    apply sub_eq_zero.mp
    change v = 0
    ext j
    fin_cases j <;> assumption
  refine ⟨L,hL,?_⟩
  intro inj
  apply hn
  apply inj
  exact sub_eq_zero.mp (by rw [← map_sub]; exact hLv)

/-- Each tile admits a linear functional which takes each residue exactly once. -/
theorem exists_bijective_projections {p : ℕ} [Fact p.Prime] (A B : Finset (Plane p))
    (tile : AddSubgroup.IsComplement (A : Set (Plane p)) (B : Set (Plane p)))
    (hA : A.card = p) (hB : B.card = p) :
    (∃ L : Plane p →ₗ[ZMod p] ZMod p, Function.Bijective (fun x : A => L x)) ∧
    (∃ L : Plane p →ₗ[ZMod p] ZMod p, Function.Bijective (fun x : B => L x)) := by
  obtain ⟨LA,hnA,hiA⟩ := exists_noninjective_projection A hA
  obtain ⟨LB,hnB,hiB⟩ := exists_noninjective_projection B hB
  exact ⟨⟨LB,(projection_dichotomy A B tile hA hB LB hnB).resolve_right (fun h => hiB h.1)⟩,
    ⟨LA,(projection_dichotomy A B tile hA hB LA hnA).resolve_left (fun h => hiA h.1)⟩⟩

end Cylinder.RedeiPlane

