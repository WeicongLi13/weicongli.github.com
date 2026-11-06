module

public import Cylinder.RedeiInterpolation
public import Mathlib.RingTheory.MvPolynomial.EulerIdentity

/-! Final polynomial contradiction for a nondivisible large factor.
Euler's identity produces the three coefficients of the determinant without
dividing by any coordinate. -/

@[expose] public section
noncomputable section
namespace Cylinder.Redei
open scoped Classical BigOperators
open MvPolynomial Geometry PowerEvaluationRelation

private abbrev Form (p : ℕ) := MvPolynomial (Fin 3) (ZMod p)

private def cross {R : Type*} [CommRing R] (a b : Fin 3 → R) : Fin 3 → R :=
  ![a 1*b 2-a 2*b 1, a 2*b 0-a 0*b 2, a 0*b 1-a 1*b 0]

private theorem dot_cross_identity {R : Type*} [CommRing R] (l a b w : Fin 3 → R) (i : Fin 3) :
    l i*(∑ j,a j*cross b w j) =
      (∑ j,l j*a j)*cross b w i - (∑ j,l j*b j)*cross a w i + (∑ j,l j*w j)*cross a b i := by
  fin_cases i <;> simp [cross, Fin.sum_univ_three] <;> ring

private theorem linear_pow_prime (p : ℕ) [Fact p.Prime] (v : Point p) :
    linearForm v ^ p = ∑ i, C (v i) * X i ^ p := by
  rw [linearForm, sum_pow_char]
  apply Finset.sum_congr rfl
  intro i _
  rw [mul_pow, ← C_pow, ZMod.pow_card]

private theorem minor_not_divisible (p : ℕ) [Fact p.Prime] (v : Point p)
    (i j k : Fin 3) (hv : v i ≠ 0) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    ¬ linearForm v ∣ ((X j)^p*X k - (X k)^p*X j : Form p) := by
  let M : Form p := (X j)^p*X k - (X k)^p*X j
  have hn : M ≠ 0 := by
    intro hz
    have hd := congrArg (pderiv k) hz
    simp [M,pderiv_X,hjk] at hd
  have hmd : M.degreeOf i = 0 := by
    apply Nat.le_zero.mp
    apply (MvPolynomial.degreeOf_sub_le ..).trans
    apply max_le <;> apply (MvPolynomial.degreeOf_mul_le ..).trans
    · simp only [MvPolynomial.degreeOf_X_pow_of_ne _ hij,MvPolynomial.degreeOf_X_of_ne hik,Nat.zero_add,le_refl]
    · simp only [MvPolynomial.degreeOf_X_pow_of_ne _ hik,MvPolynomial.degreeOf_X_of_ne hij,Nat.zero_add,le_refl]
  have hd : (linearForm v).degreeOf i ≠ 0 := by
    intro hz
    have hnot : i ∉ (linearForm v).vars := fun hi => (mem_vars_iff_degreeOf_ne_zero.mp hi) hz
    have he := pderiv_eq_zero_of_notMem_vars hnot
    apply hv
    apply MvPolynomial.C_injective (σ := Fin 3) (R := ZMod p)
    simpa [linearForm,map_sum,pderiv_X,Pi.single_apply,mul_ite] using he
  rintro ⟨T,hT⟩
  change M = linearForm v * T at hT
  have hprodne : linearForm v * T ≠ 0 := hT ▸ hn
  obtain ⟨hl,ht⟩ := mul_ne_zero_iff.mp hprodne
  have hdeg := congrArg (degreeOf i) hT
  rw [hmd,MvPolynomial.degreeOf_mul_eq hl ht] at hdeg
  omega

/-- A rational linear factor of the Frobenius determinant forces divisibility
of the same linear combination of the three entries of W. -/
private theorem linear_dvd_vector_of_frobenius_det (p : ℕ) [Fact p.Prime] (v : Point p) (hv : v ≠ 0)
    (W : Fin 3 → Form p) (hdet : linearForm v ∣ ∑ i,(X i)^p*cross X W i) :
    linearForm v ∣ ∑ i,C (v i)*W i := by
  obtain ⟨i,hi⟩ := nonzero_coordinate p hv
  have hp := LinearFormFactors.linearForm_prime v hv
  have hpow : linearForm v ∣ linearForm v ^ p :=
    dvd_pow_self _ (Nat.ne_of_gt (Fact.out : p.Prime).pos)
  have h := dot_cross_identity (fun j => C (v j)) (fun j => (X j)^p) X W i
  change C (v i) * _ = (∑ j,C (v j)*X j^p)*_ - (linearForm v)*_ + _ at h
  rw [← linear_pow_prime] at h
  have hdiv : linearForm v ∣ (∑ j,C (v j)*W j) * cross (fun j => X j ^p) X i := by
    rw [show (∑ j,C (v j)*W j) * cross (fun j => X j ^p) X i =
      C (v i)*(∑ j,X j^p*cross X W j) -
       (linearForm v ^ p * cross X W i - linearForm v * cross (fun j => X j^p) W i) by
       linear_combination -h]
    exact dvd_sub (dvd_mul_of_dvd_right hdet _) (dvd_sub (dvd_mul_of_dvd_left hpow _) (dvd_mul_right ..))
  apply (hp.dvd_mul.mp hdiv).resolve_right
  fin_cases i
  · exact minor_not_divisible p v 0 1 2 hi (by decide) (by decide) (by decide)
  · exact minor_not_divisible p v 1 2 0 hi (by decide) (by decide) (by decide)
  · exact minor_not_divisible p v 2 0 1 hi (by decide) (by decide) (by decide)

theorem no_frobenius_decomposition (p : ℕ) [Fact p.Prime] (A : Finset (Point p))
    (h0 : 0 ∈ A) (hspan : Submodule.span (ZMod p) (↑A : Set (Point p)) = ⊤)
    (r : ℕ) (hr : r < p) (hlow : ∀ j < r, moment p A j=0) (hnon : moment p A r ≠ 0)
    (s : ℕ) (hsr : s < r) (F G : MvPolynomial (Fin 3) (ZMod p)) (hF : F ≠ 0) (hG : G ≠ 0)
    (U : Fin 3 → MvPolynomial (Fin 3) (ZMod p)) (hU : ∀ i, (U i).IsHomogeneous s)
    (hFG : F*G = ∑ i, X i^p * U i) (hsum : ∑ i, X i * U i=0)
    (hdiv : ∀ a ∈ A, ∀ b ∈ A, a ≠ b → linearForm (a-b) ∣ G) : False := by
  let W : Fin 3 → Form p := ![pderiv 2 (U 1) - pderiv 1 (U 2),
    pderiv 0 (U 2)-pderiv 2 (U 0), pderiv 1 (U 0)-pderiv 0 (U 1)]
  have hW (i : Fin 3) : (W i).totalDegree ≤ s-1 := by
    fin_cases i
    · exact ((hU 1).pderiv.sub (hU 2).pderiv).totalDegree_le
    · exact ((hU 2).pderiv.sub (hU 0).pderiv).totalDegree_le
    · exact ((hU 0).pderiv.sub (hU 1).pderiv).totalDegree_le
  have hder (i : Fin 3) : ∑ j,X j * pderiv i (U j) = - U i := by
    have h := congrArg (pderiv i) hsum
    simp [map_sum,pderiv_X,Pi.single_apply,Finset.sum_add_distrib] at h
    exact eq_neg_of_add_eq_zero_left h
  have hcurl (i : Fin 3) : (∑ j,X j*(pderiv j (U i)-pderiv i (U j))) =
       ((s+1 : ℕ) : Form p) * U i := by
    simp only [mul_sub, Finset.sum_sub_distrib,(hU i).sum_X_mul_pderiv,hder,nsmul_eq_mul,Nat.cast_add,Nat.cast_one]
    ring
  have hcross (i : Fin 3) : cross X W i = ((s+1 : ℕ) : Form p) * U i := by
    rw [← hcurl]
    fin_cases i <;> simp [cross,W,Fin.sum_univ_three] <;> ring
  have hscale : (∑ i,X i ^ p * cross X W i) = ((s+1 : ℕ) : Form p)*(F*G) := by
    simp_rw [hcross]
    rw [hFG,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  obtain ⟨q,hq⟩ := interpolation_radial p A h0 hspan r hr hlow hnon (s-1) (by omega) W hW (by
    intro a ha b hb hab
    apply linear_dvd_vector_of_frobenius_det p (a-b) (sub_ne_zero.mpr hab) W
    rw [hscale]
    exact dvd_mul_of_dvd_right (dvd_mul_of_dvd_right (hdiv a ha b hb hab) _) _)
  have hzero : cross X W = 0 := by
    funext i
    fin_cases i <;> simp [cross,hq] <;> ring
  have hscalar : ((s+1 : ℕ) : Form p) ≠ 0 := by
    intro hz
    have hd := (CharP.cast_eq_zero_iff (Form p) p (s+1)).mp hz
    have := Nat.le_of_dvd (by omega : 0 < s+1) hd
    omega
  apply mul_ne_zero hscalar (mul_ne_zero hF hG)
  rw [← hscale,hzero]
  simp

end Cylinder.Redei
end