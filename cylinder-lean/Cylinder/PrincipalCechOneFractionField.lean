module

public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Ideal.Operations

/-! Actual degree-one Čech exactness for a finite principal cover of a domain.
All cochains below live in concrete `Localization.Away` rings.  The common field
is used only to compare their images while uniformly clearing denominators.
This is an algebraic Čech statement; it does not identify Čech and Ext cohomology. -/

@[expose] public section
noncomputable section

namespace Cylinder.PrincipalCechOneFractionField

open scoped BigOperators

variable {R K : Type*} [CommRing R] [Field K]

def awayToField (ι : R →+* K) (f : R) (hf : ι f ≠ 0) :
    Localization.Away f →+* K :=
  IsLocalization.Away.lift f (g := ι) (isUnit_iff_ne_zero.mpr hf)

@[simp] theorem awayToField_algebraMap (ι : R →+* K) (f : R) (hf : ι f ≠ 0) (a : R) :
    awayToField ι f hf (algebraMap R (Localization.Away f) a) = ι a :=
  IsLocalization.Away.lift_eq _ _ _

theorem awayToField_injective (ι : R →+* K) (hι : Function.Injective ι)
    (f : R) (hf : ι f ≠ 0) : Function.Injective (awayToField ι f hf) := by
  apply (IsLocalization.injective_iff_map_algebraMap_eq (.powers f) _).mpr
  intro a b
  constructor
  · exact congrArg (awayToField ι f hf)
  · intro h
    exact congrArg (algebraMap R (Localization.Away f)) (hι (by simpa using h))

theorem denominator (ι : R →+* K) (f : R) (hf : ι f ≠ 0)
    (x : Localization.Away f) :
    ∃ n : ℕ, ∃ a : R, awayToField ι f hf x * (ι f) ^ n = ι a := by
  obtain ⟨n, a, ha⟩ := IsLocalization.Away.surj f x
  refine ⟨n, a, ?_⟩
  simpa using congrArg (awayToField ι f hf) ha

theorem exists_preimage_of_denominator (ι : R →+* K) (f : R) (hf : ι f ≠ 0)
    (x : K) (n : ℕ) (a : R) (ha : x * (ι f) ^ n = ι a) :
    ∃ y : Localization.Away f, awayToField ι f hf y = x := by
  let s : Submonoid.powers f := ⟨f ^ n, n, rfl⟩
  let y : Localization.Away f := IsLocalization.mk' _ a s
  refine ⟨y, mul_right_cancel₀ (pow_ne_zero n hf) ?_⟩
  have h := congrArg (awayToField ι f hf) (IsLocalization.mk'_spec (Localization.Away f) a s)
  have hy : awayToField ι f hf y * (ι f) ^ n = ι a := by
    simpa [y, s] using h
  exact hy.trans ha.symm

def restriction (f g : R) (h : f ∣ g) : Localization.Away f →+* Localization.Away g :=
  IsLocalization.Away.lift f (IsLocalization.Away.isUnit_of_dvd g h)

@[simp] theorem restriction_algebraMap (f g : R) (h : f ∣ g) (a : R) :
    restriction f g h (algebraMap R (Localization.Away f) a) =
      algebraMap R (Localization.Away g) a :=
  IsLocalization.Away.lift_eq _ _ _

theorem awayToField_restriction (ι : R →+* K) (f g : R) (h : f ∣ g)
    (hf : ι f ≠ 0) (hg : ι g ≠ 0) (x : Localization.Away f) :
    awayToField ι g hg (restriction f g h x) = awayToField ι f hf x := by
  have he : (awayToField ι g hg).comp (restriction f g h) = awayToField ι f hf := by
    apply IsLocalization.ringHom_ext (.powers f)
    ext a
    simp
  exact RingHom.congr_fun he x

theorem pairNonzero {I : Type*} (ι : R →+* K) (f : I → R) (hf : ∀ i, ι (f i) ≠ 0)
    (i j : I) : ι (f i * f j) ≠ 0 := by
  simpa only [map_mul] using mul_ne_zero (hf i) (hf j)

theorem uniform_denominators {I : Type*} [Fintype I]
    (ι : R →+* K) (f : I → R) (hf : ∀ i, ι (f i) ≠ 0)
    (z : ∀ i j, Localization.Away (f i * f j)) :
    ∃ N : ℕ, ∀ i j, ∃ a : R,
      awayToField ι (f i * f j) (pairNonzero ι f hf i j) (z i j) *
        (ι (f i) * ι (f j)) ^ N = ι a := by
  classical
  choose n a ha using fun ij : I × I =>
    denominator ι (f ij.1 * f ij.2) (pairNonzero ι f hf ij.1 ij.2) (z ij.1 ij.2)
  let N := Finset.univ.sup n
  refine ⟨N, fun i j => ⟨(f i * f j) ^ (N - n (i, j)) * a (i, j), ?_⟩⟩
  have hn : n (i, j) ≤ N := Finset.le_sup (Finset.mem_univ (i, j))
  have hN : N = (N - n (i, j)) + n (i, j) := (Nat.sub_add_cancel hn).symm
  have hz := ha (i, j)
  simp only [map_mul] at hz
  calc
    awayToField ι (f i * f j) (pairNonzero ι f hf i j) (z i j) *
        (ι (f i) * ι (f j)) ^ N =
      (ι (f i) * ι (f j)) ^ (N - n (i, j)) *
        (awayToField ι (f i * f j) (pairNonzero ι f hf i j) (z i j) *
          (ι (f i) * ι (f j)) ^ n (i, j)) := by
            conv_lhs => rw [hN, pow_add]
            ring
    _ = _ := by rw [hz]; simp

theorem exists_primitives_in_field {I : Type*} [Fintype I]
    (ι : R →+* K) (f : I → R) (hf : ∀ i, ι (f i) ≠ 0)
    (hspan : Ideal.span (Set.range f) = ⊤)
    (z : ∀ i j, Localization.Away (f i * f j))
    (hcocycle : ∀ i j k,
      awayToField ι (f i * f k) (pairNonzero ι f hf i k) (z i k) -
        awayToField ι (f j * f k) (pairNonzero ι f hf j k) (z j k) =
      awayToField ι (f i * f j) (pairNonzero ι f hf i j) (z i j)) :
    ∃ b : ∀ i, Localization.Away (f i), ∀ i j,
      awayToField ι (f i) (hf i) (b i) - awayToField ι (f j) (hf j) (b j) =
        awayToField ι (f i * f j) (pairNonzero ι f hf i j) (z i j) := by
  classical
  obtain ⟨N, hN⟩ := uniform_denominators ι f hf z
  have hu (i j : I) : ∃ u : Localization.Away (f i),
      awayToField ι (f i) (hf i) u = (ι (f j)) ^ N *
        awayToField ι (f i * f j) (pairNonzero ι f hf i j) (z i j) := by
    obtain ⟨a, ha⟩ := hN i j
    apply exists_preimage_of_denominator ι (f i) (hf i) _ N a
    simpa only [mul_pow] using (by convert ha using 1; ring)
  choose u hu using hu
  have hp : Ideal.span (Set.range (fun i => f i ^ N)) = ⊤ := by
    have he : Set.range (fun i => f i ^ N) = (fun x : R => x ^ N) '' Set.range f := by
      ext x
      constructor
      · rintro ⟨i, rfl⟩
        exact ⟨f i, ⟨i, rfl⟩, rfl⟩
      · rintro ⟨y, ⟨i, rfl⟩, rfl⟩
        exact ⟨i, rfl⟩
    rw [he]
    exact Ideal.span_pow_eq_top (Set.range f) hspan N
  obtain ⟨c, hc⟩ := Ideal.mem_span_range_iff_exists_fun.mp
    ((Ideal.eq_top_iff_one _).mp hp)
  have hcK : ∑ i, ι (c i) * (ι (f i)) ^ N = (1 : K) := by
    simpa using congrArg ι hc
  refine ⟨fun i => ∑ j, algebraMap R (Localization.Away (f i)) (c j) * u i j, ?_⟩
  intro i j
  simp only [map_sum, map_mul, awayToField_algebraMap, hu]
  rw [← Finset.sum_sub_distrib]
  calc
    ∑ k, (ι (c k) * ((ι (f k)) ^ N *
        awayToField ι (f i * f k) (pairNonzero ι f hf i k) (z i k)) -
      ι (c k) * ((ι (f k)) ^ N *
        awayToField ι (f j * f k) (pairNonzero ι f hf j k) (z j k))) =
      ∑ k, (ι (c k) * (ι (f k)) ^ N) *
        awayToField ι (f i * f j) (pairNonzero ι f hf i j) (z i j) := by
      apply Finset.sum_congr rfl
      intro k _
      rw [← hcocycle i j k]
      ring
    _ = _ := by rw [← Finset.sum_mul, hcK, one_mul]

def tripleRestriction {I : Type*} (f : I → R) (i j k : I) :
    Localization.Away (f i * f j) →+* Localization.Away (f i * f j * f k) :=
  restriction _ _ ⟨f k, by ring⟩

/-- Every actual Čech one-cocycle on a finite principal cover is a coboundary.
The injective embedding into a field is used to compare the concrete localizations.
No coboundary, denominator-lift, or vanishing conclusion is an input. -/
theorem finite_principal_cech_one_exact {I : Type*} [Fintype I]
    (ι : R →+* K) (hι : Function.Injective ι) (f : I → R)
    (hf : ∀ i, ι (f i) ≠ 0) (hspan : Ideal.span (Set.range f) = ⊤)
    (z : ∀ i j, Localization.Away (f i * f j))
    (hcocycle : ∀ i j k,
      restriction (f i * f k) (f i * f j * f k) (⟨f j, by ring⟩) (z i k) -
        restriction (f j * f k) (f i * f j * f k) (⟨f i, by ring⟩) (z j k) =
      tripleRestriction f i j k (z i j)) :
    ∃ b : ∀ i, Localization.Away (f i), ∀ i j,
      restriction (f i) (f i * f j) (dvd_mul_right _ _) (b i) -
        restriction (f j) (f i * f j) (dvd_mul_left _ _) (b j) = z i j := by
  have hc (i j k : I) :
      awayToField ι (f i * f k) (pairNonzero ι f hf i k) (z i k) -
        awayToField ι (f j * f k) (pairNonzero ι f hf j k) (z j k) =
      awayToField ι (f i * f j) (pairNonzero ι f hf i j) (z i j) := by
    have hijk : ι (f i * f j * f k) ≠ 0 := by
      simpa only [map_mul] using mul_ne_zero (mul_ne_zero (hf i) (hf j)) (hf k)
    have h := congrArg (awayToField ι (f i * f j * f k) hijk) (hcocycle i j k)
    simpa only [map_sub, tripleRestriction,
      awayToField_restriction ι _ _ _ (pairNonzero ι f hf i k) hijk,
      awayToField_restriction ι _ _ _ (pairNonzero ι f hf j k) hijk,
      awayToField_restriction ι _ _ _ (pairNonzero ι f hf i j) hijk] using h
  obtain ⟨b, hb⟩ := exists_primitives_in_field ι f hf hspan z hc
  refine ⟨b, fun i j => ?_⟩
  apply awayToField_injective ι hι (f i * f j) (pairNonzero ι f hf i j)
  simpa only [map_sub,
    awayToField_restriction ι _ _ _ (hf i) (pairNonzero ι f hf i j),
    awayToField_restriction ι _ _ _ (hf j) (pairNonzero ι f hf i j)] using hb i j

end Cylinder.PrincipalCechOneFractionField

end
