import NSDensity.CodeLifting
import NSDensity.CodeFieldTransport
import NSDensity.PaperPairs

open scoped BigOperators

namespace NSDensity

/-- An injective field map compatible with a coefficient-field isomorphism
preserves exactly the coordinate permutations of the relation code. -/
theorem columnRelationGroup_semilinear
    {F K E L I : Type*} [Field F] [Field K] [Field E] [Field L]
    [Algebra F E] [Algebra K L] [Fintype I]
    (e : F ≃+* K) (f : E →+* L)
    (hcomp : ∀ x : F, f (algebraMap F E x) = algebraMap K L (e x))
    (v : I → E) :
    columnRelationGroup (F := F) v =
      columnRelationGroup (F := K) (fun i => f (v i)) := by
  have heval (c : I → F) : f (columnEvalOver v c) =
      columnEvalOver (fun i => f (v i)) (fun i => e (c i)) := by
    change f (∑ i, c i • v i) = ∑ i, e (c i) • f (v i)
    simp only [Algebra.smul_def, map_sum, map_mul, hcomp]
  have hker (c : I → F) : columnEvalOver v c = 0 ↔
      columnEvalOver (fun i => f (v i)) (fun i => e (c i)) = 0 := by
    rw [← heval]
    constructor
    · intro h; rw [h, map_zero]
    · intro h
      apply f.injective
      simpa only [map_zero] using h
  ext σ
  constructor
  · intro h c
    let d : I → F := fun i => e.symm (c i)
    have hd := (hker d).symm.trans ((h d).trans (hker (d ∘ σ)))
    simpa [d, Function.comp_def] using hd
  · intro h c
    exact (hker c).trans ((h (fun i => e (c i))).trans (hker (c ∘ σ)).symm)

end NSDensity

namespace NSDensity.Concrete

/-- Nonstandardness is independent of both the ambient finite-field model
and the coefficient-field model. Only the common alphabet size and the
exact multiplicative order of the roots are prescribed. -/
theorem nonstandardRootCode_model_independent
    {E L : Type*} [Field E] [Field L] [Finite E] [Finite L]
    (F : Subfield E) (K : Subfield L) {n : ℕ} {a : E} {b : L}
    (hn : 0 < n) (hcard : Nat.card F = Nat.card K)
    (hcop : Nat.Coprime (Nat.card F) n)
    (ha : orderOf a = n) (hb : orderOf b = n) :
    nonstandardRootCode F n a ↔ nonstandardRootCode K n b := by
  classical
  let : NeZero n := ⟨hn.ne'⟩
  let : Fintype F := Fintype.ofFinite F
  let : Fintype K := Fintype.ofFinite K
  let : CharP F (ringChar F) := ringChar.charP F
  obtain ⟨e₀, hp, hF⟩ := FiniteField.card F (ringChar F)
  let e : ℕ := e₀
  have he : 0 < e := e₀.property
  change Fintype.card F = ringChar F ^ e at hF
  have hK : Fintype.card K = ringChar F ^ e := by
    rw [← Nat.card_eq_fintype_card, ← hcard, Nat.card_eq_fintype_card]
    exact hF
  have hcop' : Nat.Coprime (ringChar F) n := by
    apply (Nat.coprime_pow_left_iff he _ _).1
    simpa only [← hF, Nat.card_eq_fintype_card] using hcop
  let A := rootField F a
  let B := rootField K b
  have hA : Module.finrank F A = orderOf (ringChar F ^ e : ZMod n) :=
    rootField_finrank_eq_orderOf hp hF hn hcop' ha
  have hB : Module.finrank K B = orderOf (ringChar F ^ e : ZMod n) :=
    rootField_finrank_eq_orderOf hp hK hn hcop' hb
  have hAB : Nat.card A = Nat.card B := by
    rw [Module.natCard_eq_pow_finrank (K := F) (V := A),
      Module.natCard_eq_pow_finrank (K := K) (V := B), hA, hB, hcard]
  let coeff : F ≃+* K := FiniteField.ringEquivOfCardEq
    (by simpa only [Nat.card_eq_fintype_card] using hcard)
  let : Algebra F B := ((algebraMap K B).comp coeff.toRingHom).toAlgebra
  have hdegrees : Module.finrank F A = Module.finrank F B := by
    apply Nat.pow_right_injective (show 1 < Nat.card F by
      simpa only [Nat.card_eq_fintype_card] using Fintype.one_lt_card (α := F))
    change Nat.card F ^ Module.finrank F A = Nat.card F ^ Module.finrank F B
    rw [← Module.natCard_eq_pow_finrank (K := F) (V := A),
      ← Module.natCard_eq_pow_finrank (K := F) (V := B)]
    exact hAB
  obtain ⟨f⟩ := FiniteField.nonempty_algHom_of_finrank_dvd
    (F := F) (K := A) (L := B) (by rw [hdegrees])
  let g : A →+* L := (rootField K b).val.toRingHom.comp f.toRingHom
  have hcomp (x : F) : g (algebraMap F A x) = algebraMap K L (coeff x) := by
    change ((f (algebraMap F A x) : B) : L) = _
    rw [f.commutes]
    rfl
  let c : L := g (rootInField F a)
  have hc : orderOf c = n := by
    exact (orderOf_injective g.toMonoidHom g.injective (rootInField F a)).trans
      ((rootInField_orderOf F a).trans ha)
  have hgroups : permutationAutGroup F (fun i : Fin n => a ^ i.val) =
      permutationAutGroup K (fun i : Fin n => c ^ i.val) := by
    rw [← rootField_columnRelationGroup_eq F n a,
      ← columnRelationGroup_eq_permutationAutGroup K]
    simpa only [map_pow, c] using
      columnRelationGroup_semilinear coeff g hcomp
        (fun i : Fin n => (rootInField F a) ^ i.val)
  have hNS : nonstandardRootCode F n a ↔ nonstandardRootCode K n c := by
    change (∃ σ, σ ∈ permutationAutGroup F (fun i : Fin n => a ^ i.val) ∧
      ¬affinePermutation n σ) ↔
      (∃ σ, σ ∈ permutationAutGroup K (fun i : Fin n => c ^ i.val) ∧
        ¬affinePermutation n σ)
    rw [hgroups]
  exact hNS.trans (nonstandardRootCode_same_order_iff K hc hb)

#print axioms nonstandardRootCode_model_independent

end NSDensity.Concrete

namespace NSDensity

/-- The existential root-code predicate agrees with every specified finite
field model and every specified root of the prescribed order. -/
theorem codeNonstandard_iff_fixed_root
    {E : Type} [Field E] [Finite E] (F : Subfield E) {n : ℕ} {a : E}
    (hn : 0 < n) (hcop : Nat.Coprime (Nat.card F) n) (ha : orderOf a = n) :
    CodeNonstandard n (Nat.card F) ↔ Concrete.nonstandardRootCode F n a := by
  constructor
  · rintro ⟨L, fieldL, hL, K, hK, hcard, b, hb, hNS⟩
    let : Field L := fieldL
    let : Finite L := hL
    exact (Concrete.nonstandardRootCode_model_independent K F hn hcard
      (by simpa only [hcard] using hcop) hb ha).1 hNS
  · intro hNS
    exact ⟨E, inferInstance, inferInstance, F, inferInstance, rfl, a, ha, hNS⟩

/-- Thus the paper's pair predicate is also independent of choosing a
particular model of the alphabet or a particular primitive length root. -/
theorem paperNonstandard_iff_fixed_root
    {E : Type} [Field E] [Finite E] (F : Subfield E) {n : ℕ} {a : E}
    (hn : 0 < n) (hcop : Nat.Coprime (Nat.card F) n) (ha : orderOf a = n) :
    PaperNonstandard n (Nat.card F) ↔ Concrete.nonstandardRootCode F n a :=
  (codeNonstandard_iff_paper hn hcop).symm.trans
    (codeNonstandard_iff_fixed_root F hn hcop ha)

#print axioms codeNonstandard_iff_fixed_root
#print axioms paperNonstandard_iff_fixed_root

end NSDensity
