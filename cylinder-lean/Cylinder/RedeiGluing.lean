import Cylinder.RedeiPlane
import Cylinder.RedeiDivisibility

/-! Direction factors and descent of the Frobenius decomposition to the
unshifted variables. -/
noncomputable section
namespace Cylinder.Redei

open Geometry PowerEvaluationRelation WeakDirectionsGeometry MvPolynomial
open scoped BigOperators Classical
variable {p : ℕ} [Fact p.Prime]

/-- A direction determined by the small factor forces its linear form
to divide every positive moment below p of the other factor. -/
theorem factor_differences_divide {A B : Finset (Point p)}
    (tile : AddSubgroup.IsComplement (A : Set (Point p)) B)
    (hA : A.card = p) (hB : B.card = p^2) (d : ℕ) (hd : 0 < d) (hdp : d < p)
    (a : Point p) (ha : a ∈ A) (a' : Point p) (ha' : a' ∈ A) (hne : a ≠ a') :
    linearForm (a-a') ∣ moment p B d := by
  have hv : a-a' ≠ 0 := sub_ne_zero.mpr hne
  let D := Projectivization.mk (ZMod p) (a-a') hv
  obtain ⟨k,hk⟩ := Projectivization.exists_smul_eq_mk_rep (ZMod p) (a-a') hv
  have hk' : (k : ZMod p) • (a-a') = D.rep := hk
  have hm : ¬ Determines p B D := by
    rintro ⟨x,hx,y,hy,hxy,t,ht⟩
    have htn : t ≠ 0 := by
      intro h
      rw [h, zero_smul, add_zero] at ht
      exact hxy ht
    have hdiff : (t * (k : ZMod p)) • (a-a') = y-x := by
      rw [mul_smul, hk']
      exact (eq_sub_iff_add_eq).mpr ((add_comm _ _).trans ht)
    exact RedeiPlane.no_common_direction A B tile hA ⟨a,ha⟩ ⟨a',ha'⟩ ⟨y,hy⟩ ⟨x,hx⟩
      (fun he => hne (congrArg Subtype.val he)) _ (mul_ne_zero htn k.ne_zero) hdiff
  apply dvd_trans _ (direction_dvd_moment p hB hm d hd hdp)
  refine ⟨C (k : ZMod p), ?_⟩
  rw [← hk']
  simp only [linearForm, Pi.smul_apply, smul_eq_mul, map_mul, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- At every normal the low moment of the small factor or the moment
of the large factor vanishes. -/
theorem eval_product_moments_zero {A B : Finset (Point p)}
    (hA : A.card = p) (r d : ℕ) (hr : r < p-1)
    (hdiv : ∀ a ∈ A, ∀ b ∈ A, a ≠ b → linearForm (a-b) ∣ moment p B d) (u : Point p) :
    eval u (moment p A r * moment p B d) = 0 := by
  rw [map_mul]
  let l : A → ZMod p := fun x => pairing p u x
  by_cases hi : Function.Injective l
  · apply mul_eq_zero_of_left
    have hc : Fintype.card A = Fintype.card (ZMod p) := by simpa [ZMod.card] using hA
    have hb : Function.Bijective l := (Fintype.bijective_iff_injective_and_card l).mpr ⟨hi,hc⟩
    rw [eval_moment]
    have he := (hb.sum_comp (fun t => t^r)).trans (PowerSums.prime_sum_pow_low p r hr)
    exact (Finset.sum_coe_sort A (fun x => pairing p u x ^ r)).symm.trans he
  · apply mul_eq_zero_of_right
    simp only [Function.Injective] at hi
    push Not at hi
    obtain ⟨a,b,he,hab⟩ := hi
    have hne : (a : Point p) ≠ b := fun h => hab (Subtype.ext h)
    obtain ⟨Q, hQ⟩ := hdiv a a.prop b b.prop hne
    have hz : eval u (linearForm ((a : Point p) - b)) = 0 := by
      have he' : (∑ i, (a : Point p) i * u i) = ∑ i, (b : Point p) i * u i := by
        simpa only [l, pairing, mul_comm] using he
      rw [FiniteFieldHyperplaneDivisibility.eval_linearForm]
      simp only [Pi.sub_apply, sub_mul, Finset.sum_sub_distrib, he', sub_self]
    simp [hQ,hz]

/-- The discarded p-th powers may be read as first powers after evaluation.
The low degree upgrades the resulting pointwise equality to a polynomial one. -/
theorem frobenius_linear_sum_zero {A B : Finset (Point p)} (r d s : ℕ)
    (hA : A.card = p) (hr : r < p-1) (hs : s+1 < p)
    (hdiv : ∀ a ∈ A, ∀ b ∈ A, a ≠ b → linearForm (a-b) ∣ moment p B d)
    (U : Fin 3 → MvPolynomial (Fin 3) (ZMod p)) (hU : ∀ i, (U i).IsHomogeneous s)
    (hprod : moment p A r * moment p B d = ∑ i, X i ^ p * U i) :
    ∑ i, X i * U i = 0 := by
  apply FiniteGrid.eq_zero_of_degreeOf_lt_card
  · have hhom : (∑ i, X i * U i).IsHomogeneous (1+s) := by
      apply IsHomogeneous.sum
      intro i _
      exact (isHomogeneous_X _ _).mul (hU i)
    intro i
    apply lt_of_le_of_lt (degreeOf_le_totalDegree _ i)
    rw [ZMod.card]
    exact hhom.totalDegree_le.trans_lt (by omega)
  · intro u
    have hz := eval_product_moments_zero hA r d hr hdiv u
    rw [hprod] at hz
    simpa only [map_sum, map_mul, map_pow, eval_X, ZMod.pow_card] using hz

end Cylinder.Redei
end
