module

public import Cylinder.PowerRelationScalarExtension
public import Cylinder.LinearEvaluationTransport
public import Mathlib.LinearAlgebra.Projectivization.Basic
public import Mathlib.Data.Fintype.BigOperators

/-! Actual projective points and homogeneous relations after a field embedding. -/

@[expose] public section
noncomputable section
open scoped Classical BigOperators

namespace Cylinder.ProjectiveFieldEmbedding

variable {K L σ : Type*} [Field K] [Field L]

abbrev Point (K σ : Type*) [Field K] := Projectivization K (σ → K)

def vectorMap (f : K →+* L) : (σ → K) →ₛₗ[f] (σ → L) where
  toFun x j := f (x j)
  map_add' x y := by ext j; exact f.map_add _ _
  map_smul' a x := by ext j; exact f.map_mul _ _

theorem vectorMap_injective (f : K →+* L) : Function.Injective (vectorMap (σ := σ) f) := by
  intro x y h
  funext j
  exact f.injective (congrFun h j)

def pointMap (f : K →+* L) : Point K σ → Point L σ :=
  Projectivization.map (vectorMap f) (vectorMap_injective f)

theorem pointMap_mk (f : K →+* L) (x : σ → K) (hx : x ≠ 0) :
    pointMap f (Projectivization.mk K x hx) =
      Projectivization.mk L (vectorMap f x) (by
        intro h; exact hx ((vectorMap_injective f) (by simpa using h))) :=
  Projectivization.map_mk _ _ _ _

/-- Injectivity holds for a field extension, without an inverse field homomorphism. -/
theorem pointMap_injective (f : K →+* L) : Function.Injective (pointMap (σ := σ) f) := by
  intro P Q h
  have hmk : Projectivization.mk L (vectorMap f P.rep)
      (by intro hz; exact P.rep_nonzero ((vectorMap_injective f) (by simpa using hz))) =
      Projectivization.mk L (vectorMap f Q.rep)
      (by intro hz; exact Q.rep_nonzero ((vectorMap_injective f) (by simpa using hz))) := by
    calc
      _ = pointMap f P := (pointMap_mk f P.rep P.rep_nonzero).symm.trans
        (congrArg (pointMap f) (Projectivization.mk_rep P))
      _ = pointMap f Q := h
      _ = _ := (congrArg (pointMap f) (Projectivization.mk_rep Q)).symm.trans
        (pointMap_mk f Q.rep Q.rep_nonzero)
  obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff' L _ _ _ _).mp hmk
  obtain ⟨j, hj⟩ : ∃ j, Q.rep j ≠ 0 := by
    by_contra hn
    apply Q.rep_nonzero
    funext j
    simpa using not_exists.mp hn j
  have hjL : f (Q.rep j) ≠ 0 := by
    intro hz
    exact hj (f.injective (by simpa only [map_zero] using hz))
  have hcoord (k : σ) : a * f (Q.rep k) = f (P.rep k) := congrFun ha k
  have ha' : f (P.rep j / Q.rep j) = a := by
    rw [map_div₀, ← hcoord j, mul_div_cancel_right₀ _ hjL]
  have hrep : (P.rep j / Q.rep j) • Q.rep = P.rep := by
    funext k
    apply f.injective
    change f ((P.rep j / Q.rep j) * Q.rep k) = f (P.rep k)
    rw [map_mul, ha']
    exact hcoord k
  have h := (Projectivization.mk_eq_mk_iff' K _ _ P.rep_nonzero Q.rep_nonzero).mpr
    ⟨P.rep j / Q.rep j, hrep⟩
  simpa only [Projectivization.mk_rep] using h

def imageSet (f : K →+* L) (E : Finset (Point K σ)) : Finset (Point L σ) :=
  E.image (pointMap f)

theorem imageSet_card (f : K →+* L) (E : Finset (Point K σ)) :
    (imageSet f E).card = E.card :=
  Finset.card_image_of_injective E (pointMap_injective f)

def imageEquiv (f : K →+* L) (E : Finset (Point K σ)) : E ≃ imageSet f E :=
  Equiv.ofBijective (fun x => ⟨pointMap f x.val,
    Finset.mem_image.mpr ⟨x.val, x.property, rfl⟩⟩) (by
      constructor
      · intro x y h
        exact Subtype.ext (pointMap_injective f (congrArg Subtype.val h))
      · intro y
        obtain ⟨x, hx, hxy⟩ := Finset.mem_image.mp y.property
        exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩)

def representativeUnit (f : K →+* L) (P : Point K σ) : Lˣ :=
  Classical.choose (Projectivization.exists_smul_eq_mk_rep L (vectorMap f P.rep)
    (by intro hz; exact P.rep_nonzero ((vectorMap_injective f) (by simpa using hz))))

theorem representativeUnit_spec (f : K →+* L) (P : Point K σ) :
    (representativeUnit f P : L) • vectorMap f P.rep = (pointMap f P).rep := by
  have h := Classical.choose_spec (Projectivization.exists_smul_eq_mk_rep L
    (vectorMap f P.rep)
    (by intro hz; exact P.rep_nonzero ((vectorMap_injective f) (by simpa using hz))))
  change (representativeUnit f P : L) • vectorMap f P.rep =
    (Projectivization.mk L (vectorMap f P.rep) _).rep at h
  rw [← pointMap_mk f P.rep P.rep_nonzero, Projectivization.mk_rep] at h
  exact h

variable [Fintype σ]

def HasFullSupportRelation (E : Finset (Point K σ)) (d : ℕ) : Prop :=
  ∃ c : E → K, (∀ x, c x ≠ 0) ∧
    PowerEvaluationRelation.Relation (fun x : E => x.val.rep) c d

/-- A relation written with any actual nonzero representatives gives a
relation on the finite point set with its canonical representatives. -/
theorem full_support_of_indexed_representatives {I : Type*} [Fintype I]
    (E : Finset (Point K σ)) (v : I → σ → K) (hv : ∀ i, v i ≠ 0)
    (e : I ≃ E) (he : ∀ i, (e i).val = Projectivization.mk K (v i) (hv i))
    (c : I → K) (hc : ∀ i, c i ≠ 0) (d : ℕ)
    (hrel : PowerEvaluationRelation.Relation v c d) : HasFullSupportRelation E d := by
  let u : I → Kˣ := fun i => Classical.choose
    (Projectivization.exists_smul_eq_mk_rep K (v i) (hv i))
  have hu : ∀ i, (u i : K) ≠ 0 := fun i => Units.ne_zero _
  have hrep (i : I) : (u i : K) • v i = (e i).val.rep := by
    rw [he]
    exact Classical.choose_spec (Projectivization.exists_smul_eq_mk_rep K (v i) (hv i))
  let b : I → K := fun i => c i / (u i : K) ^ d
  have hb : ∀ i, b i ≠ 0 := fun i => div_ne_zero (hc i) (pow_ne_zero d (hu i))
  have hs := LinearEvaluationTransport.relation_after_rescaling v c
    (fun i => (u i : K)) hu d hrel
  refine ⟨fun y => b (e.symm y), fun y => hb _, ?_⟩
  intro F hF
  calc
    (∑ y : E, b (e.symm y) * MvPolynomial.eval y.val.rep F) =
        ∑ i : I, b i * MvPolynomial.eval ((e i).val.rep) F := by
      simpa only [Equiv.symm_apply_apply] using
        (e.sum_comp (fun y => b (e.symm y) * MvPolynomial.eval y.val.rep F)).symm
    _ = ∑ i : I, b i * MvPolynomial.eval ((u i : K) • v i) F := by
      apply Finset.sum_congr rfl
      intro i _hi
      rw [hrep]
    _ = 0 := hs F hF

/-- The new relation is on the actual image point set and its chosen representatives. -/
theorem image_full_support_relation (p : ℕ) [Fact p.Prime] [CharP L p]
    (f : K →+* L) (E : Finset (Point K σ)) (d : ℕ) (hd : d < p)
    (hrel : HasFullSupportRelation E d) : HasFullSupportRelation (imageSet f E) d := by
  obtain ⟨c, hc, hrel⟩ := hrel
  let u : E → L := fun x => representativeUnit f x.val
  have hu : ∀ x, u x ≠ 0 := fun x => Units.ne_zero _
  let b : E → L := fun x => f (c x) / u x ^ d
  have hb : ∀ x, b x ≠ 0 := fun x => div_ne_zero
    (PowerRelationScalarExtension.coefficients_nonzero f c hc x) (pow_ne_zero d (hu x))
  have hmapped := PowerRelationScalarExtension.relation_scalar_extension p f
    (fun x : E => x.val.rep) c d hd hrel
  have hscaled := LinearEvaluationTransport.relation_after_rescaling
    (fun x : E => vectorMap f x.val.rep) (fun x => f (c x)) u hu d hmapped
  let e := imageEquiv f E
  refine ⟨fun y => b (e.symm y), fun y => hb _, ?_⟩
  intro F hF
  have hvalues (x : E) :
      MvPolynomial.eval ((e x).val.rep) F =
        MvPolynomial.eval (u x • vectorMap f x.val.rep) F := by
    rw [representativeUnit_spec]
    rfl
  calc
    (∑ y : imageSet f E, b (e.symm y) * MvPolynomial.eval y.val.rep F) =
        ∑ x : E, b x * MvPolynomial.eval ((e x).val.rep) F := by
      simpa only [Equiv.symm_apply_apply] using
        (e.sum_comp (fun y => b (e.symm y) * MvPolynomial.eval y.val.rep F)).symm
    _ = ∑ x : E, b x * MvPolynomial.eval (u x • vectorMap f x.val.rep) F := by
      apply Finset.sum_congr rfl
      intro x _hx
      rw [hvalues]
    _ = 0 := hscaled F hF

end Cylinder.ProjectiveFieldEmbedding

end
