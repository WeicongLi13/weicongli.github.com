import NSDensity.Classification

/-!
The cited FHLX results, before the harmless enlargements used for counting.

`FHLXInitialFamily` records Examples 3.1--3.5, including the primitive
exception (q,m) = (2,2) and the equally-spaced lower bound n >= 6.
`FHLXStep` records Constructions 3.7--3.10, with special rather than
unrestricted descent. The hypotheses for code lengths and alphabets are
written using the characteristic p and positive field exponents.

`FHLXOriginalClassificationInput` is precisely the forward classification
used as an external input. `FHLXOriginalInput` additionally bundles the
nonstandardness assertions of those same cited examples and constructions.
It does not assume unrestricted descent, a normal form, or any density result.
The full elementary-closure equivalence below takes unrestricted descent as
a separate theorem argument, so concrete code models must discharge it.
-/

namespace NSDensity

/-- The five initial families with the exclusions in the cited FHLX paper. -/
inductive FHLXInitialFamily (p a e : ℕ) : Prop
  | dual (he : e = 1) (ha : a.Prime) (ha5 : 5 ≤ a)
      (hord : orderOf (p : ZMod a) = a - 1) : FHLXInitialFamily p a e
  | primitive (m : ℕ) (hm : 2 ≤ m) (hexception : (p ^ e, m) ≠ (2, 2))
      (ha : a = p ^ (e * m) - 1) : FHLXInitialFamily p a e
  | ovoid (ha : a = (p ^ e - 1) * (p ^ (2 * e) + 1)) :
      FHLXInitialFamily p a e
  | golay_binary (hp : p = 2) (ha : a = 23) (he : e = 1) :
      FHLXInitialFamily p a e
  | golay_ternary (hp : p = 3) (ha : a = 11) (he : e = 1) :
      FHLXInitialFamily p a e
  | equally_spaced (ha6 : 6 ≤ a) (h : EquallySpaced (p ^ e) a) :
      FHLXInitialFamily p a e

def FHLXInitial (p a e : ℕ) : Prop :=
  0 < a ∧ 0 < e ∧ Nat.Coprime p a ∧ FHLXInitialFamily p a e

/-- The original four constructions. In the descent constructor r divides
the degree over the target alphabet, and r > 1 and n >= 4 are retained. -/
inductive FHLXStep (p : ℕ) : Pair → Pair → Prop
  | lift {n e t : ℕ} (hn : 0 < n) (he : 0 < e)
      (hcop : Nat.Coprime p n) (ht : 0 < t)
      (horder : Nat.Coprime t (orderOf (p ^ e : ZMod n))) :
      FHLXStep p (n, e) (n, e * t)
  | extension {n e u : ℕ} (hn : 0 < n) (he : 0 < e)
      (hcop : Nat.Coprime p n) (hu : 0 < u)
      (hdiv : u ∣ (p ^ e - 1) / Nat.gcd n (p ^ e - 1)) :
      FHLXStep p (n, e) (n * u, e)
  | special_descent {n e r : ℕ} (hn : 4 ≤ n) (he : 0 < e)
      (hcop : Nat.Coprime p n) (hr : 1 < r)
      (hdiv : r ∣ orderOf (p ^ e : ZMod n)) :
      FHLXStep p (n, e * r) (n, e)
  | tensor {n e s : ℕ} (hn : 0 < n) (he : 0 < e)
      (hcop : Nat.Coprime p n) (hs : 1 < s) (hscop : Nat.Coprime p s)
      (ht : 1 < orderOf (p ^ e : ZMod s))
      (horder : Nat.Coprime (orderOf (p ^ e : ZMod s))
        (orderOf (p ^ e : ZMod n))) :
      FHLXStep p (n, e) (Nat.lcm n s, e)

abbrev FHLXDerived (p : ℕ) : Pair → Pair → Prop :=
  Relation.ReflTransGen (FHLXStep p)

/-- FHLX Theorem 1.1 in terms of lengths and alphabet cardinalities. -/
def FHLXOriginalClassificationInput (NS : ℕ → ℕ → Prop) : Prop :=
  ∀ p : ℕ, p.Prime → ∀ n f : ℕ, 0 < n → Nat.Coprime p n → 0 < f →
    NS n (p ^ f) → ∃ a e : ℕ, FHLXInitial p a e ∧
      FHLXDerived p (a, e) (n, f)

/-- Only assertions contained in FHLX Theorem 1.1, Examples 3.1--3.5,
and Constructions 3.7--3.10. No unrestricted descent assertion is included. -/
structure FHLXOriginalInput (NS : ℕ → ℕ → Prop) : Prop where
  classification : FHLXOriginalClassificationInput NS
  initial_nonstandard : ∀ p : ℕ, p.Prime → ∀ a e : ℕ,
    FHLXInitial p a e → NS a (p ^ e)
  construction_nonstandard : ∀ p : ℕ, p.Prime → ∀ x y : Pair,
    FHLXStep p x y → NS x.1 (p ^ x.2) → NS y.1 (p ^ y.2)

theorem FHLXInitialFamily.toInitialFamily {p a e : ℕ}
    (h : FHLXInitialFamily p a e) : InitialFamily p a e := by
  cases h with
  | dual he ha ha5 hord => exact InitialFamily.dual he ha ha5 hord
  | primitive m hm _ ha => exact InitialFamily.primitive m hm ha
  | ovoid ha => exact InitialFamily.ovoid ha
  | golay_binary hp ha he => exact InitialFamily.golay_binary hp ha he
  | golay_ternary hp ha he => exact InitialFamily.golay_ternary hp ha he
  | equally_spaced _ h => exact InitialFamily.equally_spaced h

theorem FHLXInitial.toInitial {p a e : ℕ} (h : FHLXInitial p a e) :
    Initial p a e :=
  ⟨h.1, h.2.1, h.2.2.1.pow_left e, h.2.2.2.toInitialFamily⟩

theorem FHLXStep.toClassificationStep {p : ℕ} {x y : Pair}
    (h : FHLXStep p x y) : ClassificationStep p x y := by
  cases h with
  | lift hn he _ ht horder => exact Or.inl (Step.lift hn he ht horder)
  | extension hn he _ hu hdiv => exact Or.inl (Step.extension hn he hu hdiv)
  | special_descent hn he _ hr _ =>
      exact Or.inl (Step.descent (by omega) he (by omega))
  | tensor hn he _ hs _ ht horder =>
      exact Or.inr (TensorStep.tensor hn he (by omega) ht horder)

theorem FHLXDerived.toClassificationPath {p : ℕ} {x y : Pair}
    (h : FHLXDerived p x y) :
    Relation.ReflTransGen (ClassificationStep p) x y := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih => exact ih.tail hstep.toClassificationStep

/-- The exact original forward classification implies the relaxed counting
interface. All enlargements are checked by this adapter, not assumed. -/
theorem FHLXOriginalClassificationInput.toFHLXInput {NS : ℕ → ℕ → Prop}
    (h : FHLXOriginalClassificationInput NS) : FHLXInput NS := by
  intro p hp n f hn hcop hf hNS
  obtain ⟨a, e, hinit, hpath⟩ := h p hp n f hn hcop hf hNS
  exact ⟨a, e, hinit.toInitial, hpath.toClassificationPath⟩

theorem FHLXOriginalInput.toFHLXInput {NS : ℕ → ℕ → Prop}
    (h : FHLXOriginalInput NS) : FHLXInput NS :=
  h.classification.toFHLXInput

/-- Finite iteration of the four cited constructions preserves nonstandardness. -/
theorem FHLXOriginalInput.path_preserves {NS : ℕ → ℕ → Prop}
    (h : FHLXOriginalInput NS) {p : ℕ} (hp : p.Prime) {x y : Pair}
    (hpath : FHLXDerived p x y) (hNS : NS x.1 (p ^ x.2)) :
    NS y.1 (p ^ y.2) := by
  induction hpath with
  | refl => exact hNS
  | @tail y z _ hstep ih => exact h.construction_nonstandard p hp y z hstep ih

/-- The two directions of the classification, with precisely the original
initial families and construction path. -/
theorem FHLXOriginalInput.nonstandard_iff_originalDerived
    {NS : ℕ → ℕ → Prop} (h : FHLXOriginalInput NS)
    {p n f : ℕ} (hp : p.Prime) (hn : 0 < n) (hcop : Nat.Coprime p n)
    (hf : 0 < f) :
    NS n (p ^ f) ↔ ∃ a e : ℕ, FHLXInitial p a e ∧
      FHLXDerived p (a, e) (n, f) := by
  constructor
  · exact h.classification p hp n f hn hcop hf
  · rintro ⟨a, e, hinit, hpath⟩
    exact h.path_preserves hp hpath (h.initial_nonstandard p hp a e hinit)

/-- FHLX Construction 3.8, exposed separately for concrete applications. -/
theorem FHLXOriginalInput.lifting {NS : ℕ → ℕ → Prop}
    (h : FHLXOriginalInput NS) {p n e t : ℕ} (hp : p.Prime)
    (hn : 0 < n) (he : 0 < e) (hcop : Nat.Coprime p n) (ht : 0 < t)
    (horder : Nat.Coprime t (orderOf (p ^ e : ZMod n)))
    (hNS : NS n (p ^ e)) : NS n (p ^ (e * t)) :=
  h.construction_nonstandard p hp _ _
    (FHLXStep.lift hn he hcop ht horder) hNS

/-- FHLX Construction 3.7, exposed separately for concrete applications. -/
theorem FHLXOriginalInput.extension {NS : ℕ → ℕ → Prop}
    (h : FHLXOriginalInput NS) {p n e u : ℕ} (hp : p.Prime)
    (hn : 0 < n) (he : 0 < e) (hcop : Nat.Coprime p n) (hu : 0 < u)
    (hdiv : u ∣ (p ^ e - 1) / Nat.gcd n (p ^ e - 1))
    (hNS : NS n (p ^ e)) : NS (n * u) (p ^ e) :=
  h.construction_nonstandard p hp _ _
    (FHLXStep.extension hn he hcop hu hdiv) hNS

/-- A separate theorem interface for the internally proved unrestricted
descent. This is deliberately not a field of `FHLXOriginalInput`. -/
def UnrestrictedDescentRule (NS : ℕ → ℕ → Prop) : Prop :=
  ∀ p : ℕ, p.Prime → ∀ n e r : ℕ, 0 < n → Nat.Coprime p n →
    0 < e → 0 < r → NS n (p ^ (e * r)) → NS n (p ^ e)

/-- The normal-form path preserves nonstandardness, using the cited lifting
and extension results together with a separately proved descent theorem. -/
theorem FHLXOriginalInput.normalForm_preserves
    {NS : ℕ → ℕ → Prop} (h : FHLXOriginalInput NS)
    (hdescent : UnrestrictedDescentRule NS) {p a e n f : ℕ}
    (hp : p.Prime) (ha : 0 < a) (he : 0 < e)
    (hcopA : Nat.Coprime p a) (hcopN : Nat.Coprime p n)
    (hNF : NormalForm p (a, e) (n, f)) (hNS : NS a (p ^ e)) :
    NS n (p ^ f) := by
  obtain ⟨t, u, ht, hu, hna, horder, hdiv, hfe⟩ := hNF
  dsimp only at hna horder hdiv hfe
  have het : 0 < e * t := Nat.mul_pos he ht
  have hn : 0 < n := by rw [hna]; exact Nat.mul_pos ha hu
  have hf : 0 < f := Nat.pos_of_dvd_of_pos hfe het
  have hlift := h.lifting hp ha he hcopA ht horder hNS
  have hext := h.extension hp ha het hcopA hu hdiv hlift
  rw [← hna] at hext
  obtain ⟨r, hr⟩ := hfe
  have hrpos : 0 < r := by
    by_contra hnot
    have hrzero : r = 0 := by omega
    rw [hrzero, Nat.mul_zero] at hr
    exact Nat.ne_of_gt het hr
  rw [hr] at hext
  exact hdescent p hp n f r hn hcopN hf hrpos hext

/-- The full elementary closure in the density paper. The reverse direction
uses no assertion about the artificially enlarged initial families. -/
theorem FHLXOriginalInput.nonstandard_iff_derived
    {NS : ℕ → ℕ → Prop} (h : FHLXOriginalInput NS)
    (hdescent : UnrestrictedDescentRule NS) {p n f : ℕ}
    (hp : p.Prime) (hn : 0 < n) (hcop : Nat.Coprime p n) (hf : 0 < f) :
    NS n (p ^ f) ↔ ∃ a e : ℕ, FHLXInitial p a e ∧
      Derived p (a, e) (n, f) := by
  constructor
  · intro hNS
    obtain ⟨a, e, hinit, hpath⟩ := h.classification p hp n f hn hcop hf hNS
    exact ⟨a, e, hinit, classification_derived hp.one_lt.le
      hpath.toClassificationPath⟩
  · rintro ⟨a, e, hinit, hpath⟩
    exact h.normalForm_preserves hdescent hp hinit.1 hinit.2.1
      hinit.2.2.1 hcop (derived_normalForm hp.one_lt.le hinit.1 hpath)
      (h.initial_nonstandard p hp a e hinit)

#print axioms FHLXOriginalClassificationInput.toFHLXInput
#print axioms FHLXOriginalInput.nonstandard_iff_originalDerived
#print axioms FHLXOriginalInput.nonstandard_iff_derived

end NSDensity
