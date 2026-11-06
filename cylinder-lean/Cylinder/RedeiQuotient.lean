module

public import Cylinder.Geometry
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.GroupTheory.Complement

/-! Descent of a normalized tiling along the direction of a cylindrical factor. -/

@[expose] public section
namespace Cylinder.RedeiQuotient

open Cylinder.Geometry

section Descent
variable {V W : Type*} [AddCommGroup V] [AddCommGroup W]
variable {A B : Set V} (q : V →+ W)

/-- With a saturated second factor, equality of projected sums determines
the first summand itself and the image of the second summand. -/
private theorem recover_summands
    (hinj : Function.Injective (fun z : A × B => (z.1 : V) + z.2))
    (hsat : ∀ b ∈ B, ∀ x, q x = q b → x ∈ B)
    {a a' b b' : V} (ha : a ∈ A) (ha' : a' ∈ A) (hb : b ∈ B) (hb' : b' ∈ B)
    (h : q a + q b = q a' + q b') : a = a' ∧ q b = q b' := by
  have hk : q ((a + b) - a') = q b' := by
    rw [map_sub, map_add, h]
    simp
  have hm := hsat b' hb' ((a + b) - a') hk
  have he : ((⟨a, ha⟩, ⟨b, hb⟩) : A × B) = (⟨a', ha'⟩, ⟨(a + b) - a', hm⟩) :=
    hinj (by change a + b = a' + ((a + b) - a'); rw [add_comm a', sub_add_cancel])
  have haa : a = a' := congrArg (fun z : A × B => (z.1 : V)) he
  exact ⟨haa, add_left_cancel (haa ▸ h)⟩

/-- The quotient map is injective on the other factor. -/
theorem injOn_of_saturated (hB : B.Nonempty)
    (hinj : Function.Injective (fun z : A × B => (z.1 : V) + z.2))
    (hsat : ∀ b ∈ B, ∀ x, q x = q b → x ∈ B) : Set.InjOn q A := by
  obtain ⟨b, hb⟩ := hB
  intro a ha a' ha' he
  exact (recover_summands q hinj hsat ha ha' hb hb (congrArg (· + q b) he)).1

/-- A tiling by a union of complete fibres projects to a tiling. -/
theorem projected_tiling (hsurj : Function.Surjective q)
    (htile : Function.Bijective (fun z : A × B => (z.1 : V) + z.2))
    (hsat : ∀ b ∈ B, ∀ x, q x = q b → x ∈ B) :
    Function.Bijective (fun z : (q '' A) × (q '' B) => (z.1 : W) + z.2) := by
  constructor
  · rintro ⟨⟨_, a, ha, rfl⟩, ⟨_, b, hb, rfl⟩⟩
      ⟨⟨_, a', ha', rfl⟩, ⟨_, b', hb', rfl⟩⟩ he
    have h := recover_summands q htile.1 hsat ha ha' hb hb' he
    exact Prod.ext (Subtype.ext (congrArg q h.1)) (Subtype.ext h.2)
  · intro y
    obtain ⟨x, rfl⟩ := hsurj y
    obtain ⟨⟨⟨a, ha⟩, ⟨b, hb⟩⟩, he⟩ := htile.2 x
    refine ⟨(⟨q a, a, ha, rfl⟩, ⟨q b, b, hb, rfl⟩), ?_⟩
    change q a + q b = q x
    simpa only [map_add] using congrArg q he

end Descent

section Cylinder
variable {p : ℕ} [Fact p.Prime]

/-- The span of the common direction is precisely the set of allowed
translations along each of the parallel lines. -/
theorem quotient_saturated_of_cylinder {B : Finset (Point p)} (hcyl : IsCylinder p B) :
    ∃ L : Submodule (ZMod p) (Point p), Module.finrank (ZMod p) L = 1 ∧
      ∀ b ∈ B, ∀ x, L.mkQ x = L.mkQ b → x ∈ B := by
  classical
  obtain ⟨d, hd, base, _, rfl⟩ := hcyl
  let L : Submodule (ZMod p) (Point p) := Submodule.span (ZMod p) {d}
  refine ⟨L, finrank_span_singleton hd, ?_⟩
  intro b hb x hx
  obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hb
  obtain ⟨t, ht⟩ := (mem_affineLine p _ _ _).mp hi
  have hk : x - b ∈ L := (Submodule.Quotient.mk_eq_zero L).mp (by
    change L.mkQ (x - b) = 0
    rw [map_sub, hx, sub_self])
  obtain ⟨u, hu⟩ := Submodule.mem_span_singleton.mp hk
  apply Finset.mem_biUnion.mpr
  refine ⟨i, Finset.mem_univ _, (mem_affineLine p _ _ _).mpr ⟨t + u, ?_⟩⟩
  rw [add_smul, ← add_assoc, ht, hu, add_comm b, sub_add_cancel]

/-- If a projected factor is contained in a proper linear subspace, so
is the original factor. -/
theorem span_ne_top_of_image {V W : Type*} [AddCommGroup V] [AddCommGroup W]
    [Module (ZMod p) V] [Module (ZMod p) W] (q : V →ₗ[ZMod p] W)
    (hs : Function.Surjective q) (S : Set V)
    (h : Submodule.span (ZMod p) (q '' S) ≠ ⊤) :
    Submodule.span (ZMod p) S ≠ ⊤ := by
  intro htop
  apply h
  rw [← Submodule.map_span, htop, Submodule.map_top]
  exact LinearMap.range_eq_top.mpr hs


/-- The planar factorization theorem needed after quotienting by the line
direction. Both factors have cardinality p and contain zero. -/
def PlanarFactorization (p : ℕ) [Fact p.Prime] : Prop :=
  ∀ (S T : Finset (Fin 2 → ZMod p)), S.card = p → T.card = p → 0 ∈ S → 0 ∈ T →
    AddSubgroup.IsComplement (S : Set (Fin 2 → ZMod p)) (T : Set (Fin 2 → ZMod p)) →
    Submodule.span (ZMod p) (S : Set (Fin 2 → ZMod p)) ≠ ⊤ ∨ Submodule.span (ZMod p) (T : Set (Fin 2 → ZMod p)) ≠ ⊤

/-- The last geometric step of Rédei's argument. A cylindrical factor
descends to a normalized tiling by two p-point sets in the affine plane.
Pulling back a proper subspace of the quotient gives the desired conclusion. -/
theorem proper_span_of_cylinder
    (hplane : PlanarFactorization p)
    {A B : Finset (Point p)} (hcard : A.card = p) (hA : 0 ∈ A) (hB : 0 ∈ B)
    (htile : AddSubgroup.IsComplement (A : Set (Point p)) (B : Set (Point p)))
    (hcyl : IsCylinder p B) :
    Submodule.span (ZMod p) (A : Set (Point p)) ≠ ⊤ ∨ Submodule.span (ZMod p) (B : Set (Point p)) ≠ ⊤ := by
  classical
  obtain ⟨L, hL, hclosed⟩ := quotient_saturated_of_cylinder hcyl
  have hdim := L.finrank_quotient_add_finrank
  rw [hL, Module.finrank_fin_fun] at hdim
  let e : ((Point p) ⧸ L) ≃ₗ[ZMod p] (Fin 2 → ZMod p) :=
    LinearEquiv.ofFinrankEq _ _ (by rw [Module.finrank_fin_fun]; omega)
  let q : Point p →ₗ[ZMod p] (Fin 2 → ZMod p) := e.toLinearMap.comp L.mkQ
  have hsurj : Function.Surjective q := e.surjective.comp L.mkQ_surjective
  have hs : ∀ b ∈ (B : Set (Point p)), ∀ x, q x = q b → x ∈ (B : Set (Point p)) := by
    intro b hb x he
    exact hclosed b hb x (e.injective he)
  have hnext : AddSubgroup.IsComplement (↑(A.image q) : Set (Fin 2 → ZMod p)) (↑(B.image q) : Set (Fin 2 → ZMod p)) := by
    rw [Finset.coe_image, Finset.coe_image]
    exact projected_tiling q.toAddMonoidHom hsurj htile hs
  have hcardA : (A.image q).card = p :=
    (Finset.card_image_of_injOn (injOn_of_saturated q.toAddMonoidHom ⟨0, hB⟩ htile.1 hs)).trans hcard
  have hprod : (A.image q).card * (B.image q).card = p ^ 2 := by
    simpa [Nat.card_eq_fintype_card, Fintype.card_coe, Fintype.card_pi, ZMod.card] using
      hnext.card_mul_card
  have hcardB : (B.image q).card = p := by
    rw [hcardA, pow_two] at hprod
    exact Nat.mul_left_cancel (Fact.out : Nat.Prime p).pos hprod
  have hzero (S : Finset (Point p)) (hz : 0 ∈ S) : 0 ∈ S.image q :=
    Finset.mem_image.mpr ⟨0, hz, q.map_zero⟩
  obtain h | h := hplane _ _ hcardA hcardB (hzero A hA) (hzero B hB) hnext
  · apply Or.inl
    exact span_ne_top_of_image q hsurj _ (by simpa only [Finset.coe_image] using h)
  · apply Or.inr
    exact span_ne_top_of_image q hsurj _ (by simpa only [Finset.coe_image] using h)

end Cylinder
end Cylinder.RedeiQuotient
