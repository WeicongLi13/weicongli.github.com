import Mathlib.Algebra.Field.Subfield.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Pi

/-!
Concrete permutation codes and descent of non-affine automorphisms.

The code below consists of all linear relations among a vector of field
elements. For the vector `(1,a,...,a^(n-1))` it is the root-evaluation
kernel, the dual description of the irreducible cyclic code. Its permutation
automorphisms are defined by preservation of the actual code submodule.
Restriction of the coefficient field preserves these automorphisms. Since
being an affine permutation of the coordinates does not involve the
coefficient field, a non-affine automorphism stays non-affine under descent.

No classification or analytic theorem is used in this file.
-/

open scoped BigOperators

namespace NSDensity.Concrete

variable {E : Type*} [Field E] {I : Type*} [Fintype I]

/-- The kernel of evaluation at the vector `v`: all its coefficient relations. -/
def relationCode (F : Subfield E) (v : I → E) : Submodule F (I → F) where
  carrier := {c | ∑ i, (c i : E) * v i = 0}
  zero_mem' := by simp
  add_mem' := by
    intro c d hc hd
    change (∑ i, (c i : E) * v i) = 0 at hc
    change (∑ i, (d i : E) * v i) = 0 at hd
    change (∑ i, ((c + d) i : E) * v i) = 0
    simp only [Pi.add_apply, Subfield.coe_add, add_mul, Finset.sum_add_distrib,
      hc, hd, add_zero]
  smul_mem' := by
    intro s c hc
    change (∑ i, (c i : E) * v i) = 0 at hc
    change (∑ i, ((s * c i : F) : E) * v i) = 0
    simp only [Subfield.coe_mul, mul_assoc, ← Finset.mul_sum, hc, mul_zero]

@[simp]
theorem mem_relationCode (F : Subfield E) (v : I → E) (c : I → F) :
    c ∈ relationCode F v ↔ ∑ i, (c i : E) * v i = 0 := Iff.rfl

/-- A genuine coordinate permutation automorphism of the relation code. -/
def preservesRelations (F : Subfield E) (v : I → E) (σ : Equiv.Perm I) : Prop :=
  ∀ c : I → F, c ∈ relationCode F v ↔ (c ∘ σ) ∈ relationCode F v

/-- The permutation automorphism group of this concrete linear code. -/
def permutationAutGroup (F : Subfield E) (v : I → E) : Subgroup (Equiv.Perm I) where
  carrier := {σ | preservesRelations F v σ}
  one_mem' := fun _ => Iff.rfl
  mul_mem' := by
    intro σ τ hσ hτ c
    exact (hσ c).trans (hτ (c ∘ σ))
  inv_mem' := by
    intro σ hσ c
    change c ∈ relationCode F v ↔ (c ∘ σ.symm) ∈ relationCode F v
    simpa [Function.comp_def]
      using (hσ (c ∘ σ.symm)).symm

@[simp]
theorem mem_permutationAutGroup (F : Subfield E) (v : I → E) (σ : Equiv.Perm I) :
    σ ∈ permutationAutGroup F v ↔ preservesRelations F v σ := Iff.rfl

/-- Field descent for coordinate permutation automorphisms. -/
theorem preservesRelations_of_subfield {F K : Subfield E} (hFK : F ≤ K)
    {v : I → E} {σ : Equiv.Perm I} (hσ : preservesRelations K v σ) :
    preservesRelations F v σ := by
  intro c
  let d : I → K := fun i => ⟨(c i : E), hFK (c i).property⟩
  exact hσ d

/-- Descent is literally inclusion of groups of coordinate permutations, so
the restriction homomorphism is injective without a choice of linear basis. -/
theorem permutationAutGroup_le {F K : Subfield E} (hFK : F ≤ K) (v : I → E) :
    permutationAutGroup K v ≤ permutationAutGroup F v :=
  fun _ hσ => preservesRelations_of_subfield hFK hσ

/-- The affine permutation condition on a cyclically labelled set of n
coordinates. It is independent of the alphabet field. -/
def affinePermutation (n : ℕ) (σ : Equiv.Perm (Fin n)) : Prop :=
  ∃ (u : (ZMod n)ˣ) (b : ZMod n),
    ∀ i : Fin n, ((σ i).val : ZMod n) = (u : ZMod n) * (i.val : ZMod n) + b

/-- A concrete exceptional code has an actual non-affine coordinate
permutation preserving its root-evaluation kernel. -/
def nonstandardRootCode (F : Subfield E) (n : ℕ) (a : E) : Prop :=
  ∃ σ : Equiv.Perm (Fin n),
    preservesRelations F (fun i : Fin n => a ^ i.val) σ ∧ ¬affinePermutation n σ

/-- Unrestricted descent, with no condition on the extension degree. -/
theorem nonstandardRootCode_of_subfield {F K : Subfield E} (hFK : F ≤ K)
    {n : ℕ} {a : E} (h : nonstandardRootCode K n a) :
    nonstandardRootCode F n a := by
  obtain ⟨σ, hσ, hnonaffine⟩ := h
  exact ⟨σ, preservesRelations_of_subfield hFK hσ, hnonaffine⟩

/-- A nonstandard pair in an ambient field, requiring a root of exact order n.
The existence of a non-affine code automorphism is a concrete condition,
not an otherwise uninterpreted predicate parameter. -/
def nonstandardPair (F : Subfield E) (n : ℕ) : Prop :=
  ∃ a : E, orderOf a = n ∧ nonstandardRootCode F n a

theorem nonstandardPair_of_subfield {F K : Subfield E} (hFK : F ≤ K)
    {n : ℕ} (h : nonstandardPair K n) : nonstandardPair F n := by
  obtain ⟨a, ha, hNS⟩ := h
  exact ⟨a, ha, nonstandardRootCode_of_subfield hFK hNS⟩

/-- For every collection of coefficient fields containing the prime field,
exceptionality over one of them implies exceptionality over the prime field. -/
theorem nonstandardPair_exists_iff {F : Subfield E} {K : ℕ → Subfield E}
    (hFK : ∀ r, 0 < r → F ≤ K r) (hKone : K 1 = F) {n : ℕ} :
    (∃ r : ℕ, 0 < r ∧ nonstandardPair (K r) n) ↔ nonstandardPair F n := by
  constructor
  · rintro ⟨r, hr, h⟩
    exact nonstandardPair_of_subfield (hFK r hr) h
  · intro h
    exact ⟨1, by decide, hKone.symm ▸ h⟩

end NSDensity.Concrete
