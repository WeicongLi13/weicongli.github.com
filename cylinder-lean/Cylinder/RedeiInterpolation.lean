module

public import Cylinder.RedeiDivisibility
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Algebra.Polynomial.BigOperators
public import Mathlib.Algebra.Polynomial.RingDivision

/-! Polynomial interpolation of the values of a vector of forms on
the linear forms associated with the points of the small factor. -/

@[expose] public section
noncomputable section
namespace Cylinder.Redei
open scoped Classical BigOperators
open Geometry PowerEvaluationRelation
open Polynomial

private theorem node_product_dvd {R ι : Type*} [CommRing R] [IsDomain R]
    (nodes : ι → R) (hinj : Function.Injective nodes) (s : Finset ι) (P : Polynomial R)
    (h : ∀ i ∈ s, P.eval (nodes i) = 0) :
    (∏ i ∈ s, (X - C (nodes i))) ∣ P := by
  classical
  induction s using Finset.induction_on generalizing P with
  | empty => simp
  | @insert i s hi ih =>
    obtain ⟨Q, hQ⟩ := Polynomial.dvd_iff_isRoot.mpr (h i (Finset.mem_insert_self ..))
    have hz : ∀ j ∈ s, Q.eval (nodes j) = 0 := by
      intro j hj
      have hg := h j (Finset.mem_insert_of_mem hj)
      rw [hQ, eval_mul, eval_sub, eval_X, eval_C] at hg
      exact (mul_eq_zero.mp hg).resolve_left (sub_ne_zero.mpr (fun he => hi (hinj he ▸ hj)))
    obtain ⟨T,hT⟩ := ih Q hz
    refine ⟨T, ?_⟩
    rw [hQ,hT,Finset.prod_insert hi,mul_assoc]

/-- Divisibility of the correction at a new node. Requirements are checked
on each parallel class, so repeated proportional differences cause no loss. -/
private theorem newton_difference_dvd {R ι : Type*}
    [CommRing R] [IsDomain R] [DecompositionMonoid R]
    (nodes values : ι → R) (hinj : Function.Injective nodes)
    (s : Finset ι) (a : ι) (P : Polynomial R) (hP : ∀ b ∈ s, P.eval (nodes b) = values b)
    (hprime : ∀ b ∈ s, Prime (nodes a - nodes b))
    (hslopes : ∀ b ∈ s, ∃ q : R, ∀ c ∈ s,
      Associated (nodes a - nodes c) (nodes a - nodes b) →
      values a - values c = q*(nodes a - nodes c)) :
    (∏ b ∈ s, (nodes a - nodes b)) ∣ values a - P.eval (nodes a) := by
  classical
  let direction := fun b => Associates.mk (nodes a - nodes b)
  let group := fun k => s.filter (fun b => direction b = k)
  let term := fun k => ∏ b ∈ group k, (nodes a - nodes b)
  have hp : ∏ k ∈ s.image direction, term k = ∏ b ∈ s, (nodes a - nodes b) :=
    Finset.prod_fiberwise_of_maps_to (fun b hb => Finset.mem_image_of_mem direction hb) _
  rw [← hp]
  apply Finset.prod_dvd_of_isRelPrime
  · intro k hk l hl hkl
    apply IsRelPrime.prod_left
    intro b hb
    apply IsRelPrime.prod_right
    intro c hc
    obtain ⟨hbs,hbk⟩ := Finset.mem_filter.mp hb
    obtain ⟨hcs,hcl⟩ := Finset.mem_filter.mp hc
    apply (hprime b hbs).irreducible.isRelPrime_iff_not_dvd.mpr
    intro hdvd
    have hassoc := (hprime b hbs).associated_of_dvd (hprime c hcs) hdvd
    apply hkl
    exact hbk.symm.trans ((Associates.mk_eq_mk_iff_associated.mpr hassoc).trans hcl)
  · intro k hk
    obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hk
    obtain ⟨q,hq⟩ := hslopes b hb
    let T : Polynomial R := C (values a) + C q * (X - C (nodes a)) - P
    have hz : ∀ c ∈ group (direction b), T.eval (nodes c) = 0 := by
      intro c hc
      obtain ⟨hcs, hdir⟩ := Finset.mem_filter.mp hc
      have hlin := hq c hcs (Associates.mk_eq_mk_iff_associated.mp hdir)
      simp only [T,eval_sub,eval_add,eval_mul,eval_C,eval_X,hP c hcs]
      linear_combination hlin
    obtain ⟨U,hu⟩ := node_product_dvd nodes hinj _ T hz
    refine ⟨U.eval (nodes a), ?_⟩
    have he := congrArg (fun z : Polynomial R => z.eval (nodes a)) hu
    simpa only [T,eval_sub,eval_add,eval_mul,eval_C,eval_X,sub_self,mul_zero,add_zero,
      eval_prod,term] using he


/-- Bounded Newton interpolation with a polynomial correction on each step.
The common slope requirement only compares points whose differences define
associated primes; parallel classes may have any size. -/
theorem bounded_newton_interpolation {K σ ι : Type*} [Field K]
    (nodes values : ι → MvPolynomial σ K) (hinj : Function.Injective nodes)
    (e : ℕ) (hv : ∀ a, (values a).totalDegree ≤ e)
    (hprime : ∀ a b, a ≠ b → Prime (nodes a - nodes b))
    (hdeg : ∀ a b, a ≠ b → (nodes a - nodes b).totalDegree = 1)
    (hsl : ∀ a b, a ≠ b → ∃ q, ∀ c,
      Associated (nodes a - nodes c) (nodes a - nodes b) →
      values a - values c = q*(nodes a - nodes c))
    (s : Finset ι) :
    ∃ P : Polynomial (MvPolynomial σ K), P.natDegree ≤ e ∧
      (∀ a, (P.eval (nodes a)).totalDegree ≤ e) ∧ ∀ a ∈ s, P.eval (nodes a) = values a := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, by simp, by simp, by simp⟩
  | @insert a s ha ih =>
    obtain ⟨P,hdegree,hglobal,hdata⟩ := ih
    have hne : ∀ b ∈ s, a ≠ b := fun b hb he => ha (he ▸ hb)
    have hdiv := newton_difference_dvd nodes values hinj s a P hdata
      (fun b hb => hprime a b (hne b hb)) (fun b hb => by
        obtain ⟨q,h⟩ := hsl a b (hne b hb)
        exact ⟨q,fun c _ hc => h c hc⟩)
    obtain ⟨q,hq⟩ := hdiv
    by_cases hq0 : q = 0
    · refine ⟨P,hdegree,hglobal,?_⟩
      rw [hq0,mul_zero,sub_eq_zero] at hq
      rw [Finset.forall_mem_insert]
      exact ⟨hq.symm,hdata⟩
    have hprodne : (∏ b ∈ s, (nodes a - nodes b)) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr (fun b hb => sub_ne_zero.mpr (hinj.ne (hne b hb)))
    have hproddeg : (∏ b ∈ s, (nodes a - nodes b)).totalDegree = s.card := by
      rw [FactorDegreeBound.totalDegree_prod s _ (Finset.prod_ne_zero_iff.mp hprodne)]
      simp [Finset.sum_const_nat (fun b hb => hdeg a b (hne b hb))]
    have hexcess : s.card + q.totalDegree ≤ e := by
      calc
        _ = ((∏ b ∈ s, (nodes a - nodes b))*q).totalDegree := by
          rw [MvPolynomial.totalDegree_mul_of_isDomain hprodne hq0,hproddeg]
        _ = (values a - P.eval (nodes a)).totalDegree := by rw [← hq]
        _ ≤ e := by
          rw [sub_eq_add_neg]
          exact (MvPolynomial.totalDegree_add _ _).trans
            (max_le (hv a) (by simpa using hglobal a))
    let T : Polynomial (MvPolynomial σ K) := ∏ b ∈ s, (X - C (nodes b))
    have hT (x : ι) : T.eval (nodes x) = ∏ b ∈ s, (nodes x - nodes b) := by
      simp [T, Polynomial.eval_prod]
    refine ⟨P + C q * T, ?_, ?_, ?_⟩
    · apply (natDegree_add_le ..).trans
      apply max_le hdegree
      apply (natDegree_mul_le ..).trans
      simpa [T] using (by omega : s.card ≤ e)
    · intro x
      rw [eval_add, eval_mul, eval_C, hT]
      apply (MvPolynomial.totalDegree_add ..).trans
      apply max_le (hglobal x)
      apply (MvPolynomial.totalDegree_mul _ _).trans
      have hu : (∏ b ∈ s, (nodes x - nodes b)).totalDegree ≤ s.card := by
        apply (MvPolynomial.totalDegree_finsetProd ..).trans
        calc
          _ ≤ ∑ _b ∈ s, 1 := Finset.sum_le_sum (fun b _ => by
            by_cases he : x = b
            · simp [he]
            · exact (hdeg x b he).le)
          _ = _ := by simp
      omega
    · rw [Finset.forall_mem_insert]
      refine ⟨?_,?_⟩
      · rw [eval_add,eval_mul,eval_C,hT, mul_comm q, ← hq]
        ring
      · intro b hb
        have hz : (∏ x ∈ s, (nodes b-nodes x)) = 0 :=
          Finset.prod_eq_zero hb (sub_self _)
        rw [eval_add,eval_mul,eval_C,hT,hz,mul_zero,add_zero,hdata b hb]

private def vectorValue {p : ℕ} [Fact p.Prime] (W : Fin 3 → MvPolynomial (Fin 3) (ZMod p))
    (a : Point p) : MvPolynomial (Fin 3) (ZMod p) :=
  ∑ i, MvPolynomial.C (a i)*W i

private lemma vectorValue_sub {p : ℕ} [Fact p.Prime] (W : Fin 3 → MvPolynomial (Fin 3) (ZMod p))
    (a b : Point p) : vectorValue W (a-b) = vectorValue W a - vectorValue W b := by
  simp [vectorValue,sub_mul,Finset.sum_sub_distrib]

private lemma vectorValue_smul {p : ℕ} [Fact p.Prime] (W : Fin 3 → MvPolynomial (Fin 3) (ZMod p))
    (t : ZMod p) (a : Point p) :
    vectorValue W (t • a) = MvPolynomial.C t * vectorValue W a := by
  simp [vectorValue,Pi.smul_apply,smul_eq_mul,Finset.mul_sum,mul_assoc]

private lemma node_sub {p : ℕ} [Fact p.Prime] (a b : Point p) :
    linearForm (a-b) = linearForm a - linearForm b := vectorValue_sub MvPolynomial.X a b

private lemma node_smul {p : ℕ} [Fact p.Prime] (t : ZMod p) (a : Point p) :
    linearForm (t • a) = MvPolynomial.C t * linearForm a := vectorValue_smul MvPolynomial.X t a

/-- Under the pairwise divisibilities of the interpolation lemma, the
interpolating polynomial can be chosen over the polynomial ring itself,
with degree no greater than the original vector of forms. -/
theorem exists_direction_interpolant (p : ℕ) [Fact p.Prime] (A : Finset (Point p)) (e : ℕ)
    (W : Fin 3 → MvPolynomial (Fin 3) (ZMod p)) (hw : ∀ i, (W i).totalDegree ≤ e)
    (hdiv : ∀ a ∈ A, ∀ b ∈ A, a ≠ b →
      linearForm (a-b) ∣ ∑ i, MvPolynomial.C ((a-b) i) * W i) :
    ∃ P : Polynomial (MvPolynomial (Fin 3) (ZMod p)), P.natDegree ≤ e ∧
      ∀ a ∈ A, P.eval (linearForm a) = ∑ i, MvPolynomial.C (a i)*W i := by
  classical
  let L : A → MvPolynomial (Fin 3) (ZMod p) := fun a => linearForm a.val
  let V : A → MvPolynomial (Fin 3) (ZMod p) := fun a => vectorValue W a.val
  have hdiff (a b : A) : L a - L b = linearForm (a.val-b.val) := (node_sub ..).symm
  have hdiffV (a b : A) : V a - V b = vectorValue W (a.val-b.val) := (vectorValue_sub ..).symm
  have hn (a b : A) (h : a ≠ b) : a.val-b.val ≠ 0 := sub_ne_zero.mpr fun he => h (Subtype.ext he)
  obtain ⟨P, hd, _, he⟩ := bounded_newton_interpolation L V (by
    intro a b hab
    apply Subtype.ext
    funext i
    by_contra hcoord
    have hne := hn a b (fun he => hcoord (congrArg (fun z : A => z.val i) he))
    have hd := LinearFormFactors.linearForm_ne_zero _ hne
    exact hd (by rw [← hdiff,hab,sub_self]))
    e (fun a => by
      apply MvPolynomial.totalDegree_finsetSum_le
      intro i _
      exact (MvPolynomial.totalDegree_mul _ _).trans (by simpa using hw i))
    (fun a b h => by rw [hdiff]; exact LinearFormFactors.linearForm_prime _ (hn a b h))
    (fun a b h => by rw [hdiff]; exact LinearFormFactors.linearForm_totalDegree _ (hn a b h))
    (fun a b h => by
      obtain ⟨q,hq⟩ := hdiv a.val a.property b.val b.property (fun he => h (Subtype.ext he))
      refine ⟨q,?_⟩
      intro c hass
      rw [hdiff,hdiff] at hass
      obtain ⟨t,_,ht⟩ := LinearFormFactors.coefficients_proportional_of_associated _ _ hass.symm
      change vectorValue W (a.val-b.val) = linearForm (a.val-b.val) * q at hq
      rw [hdiff,hdiffV,ht,node_smul,vectorValue_smul,hq]
      ring)
    Finset.univ
  exact ⟨P,hd,fun a ha => he ⟨a,ha⟩ (Finset.mem_univ _)⟩


private theorem pderiv_node {p : ℕ} [Fact p.Prime] (x : Point p) (i : Fin 3) :
    MvPolynomial.pderiv i (linearForm x) = MvPolynomial.C (x i) := by
  classical
  simp [linearForm, map_sum, MvPolynomial.pderiv_X, Pi.single_apply,
    mul_ite]

/-- Differentiate the first vanished moments in a polynomial direction. -/
theorem weighted_moment_of_zero (p : ℕ) [Fact p.Prime] (A : Finset (Point p))
    (W : Fin 3 → MvPolynomial (Fin 3) (ZMod p)) (k : ℕ) (hk : 0 < k) (hkp : k < p)
    (hz : moment p A k = 0) :
    (∑ a ∈ A, linearForm a ^ (k-1) * ∑ i, MvPolynomial.C (a i) * W i) = 0 := by
  have hkn : (k : MvPolynomial (Fin 3) (ZMod p)) ≠ 0 := by
    intro he
    exact (Nat.not_le_of_gt hkp) (Nat.le_of_dvd hk ((CharP.cast_eq_zero_iff _ p _).mp he))
  have hder (i : Fin 3) :
      (∑ a ∈ A, linearForm a^(k-1)*MvPolynomial.C (a i)) = 0 := by
    have he := congrArg (MvPolynomial.pderiv i) hz
    simp only [moment,map_sum,map_zero,MvPolynomial.pderiv_pow,pderiv_node,
      mul_assoc,← Finset.mul_sum] at he
    exact (mul_eq_zero.mp he).resolve_left hkn
  simp_rw [Finset.mul_sum, ← mul_assoc]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro i _
  rw [← Finset.sum_mul,hder,zero_mul]

private theorem interpolant_moment_sum (p : ℕ) [Fact p.Prime] (A : Finset (Point p))
    (P : Polynomial (MvPolynomial (Fin 3) (ZMod p))) (k : ℕ) :
    (∑ a ∈ A, linearForm a ^ k * P.eval (linearForm a)) =
    ∑ j ∈ Finset.range (P.natDegree+1), P.coeff j * moment p A (k+j) := by
  simp_rw [Polynomial.eval_eq_sum_range,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  simp only [moment,Finset.mul_sum,pow_add]
  apply Finset.sum_congr rfl
  intro a _
  ring

private theorem vectorValue_add {p : ℕ} [Fact p.Prime] (W : Fin 3 → MvPolynomial (Fin 3) (ZMod p))
    (a b : Point p) : vectorValue W (a+b) = vectorValue W a + vectorValue W b := by
  simp [vectorValue,add_mul,Finset.sum_add_distrib]

/-- The complete interpolation lemma in the Rédei proof: divisibility along
all differences of a spanning set with first nonzero moment r forces W=qX. -/
theorem interpolation_radial (p : ℕ) [Fact p.Prime] (A : Finset (Point p))
    (hzero : 0 ∈ A) (hspan : Submodule.span (ZMod p) (↑A : Set (Point p)) = ⊤)
    (r : ℕ) (hr : r < p) (hlow : ∀ j < r, moment p A j = 0) (hnon : moment p A r ≠ 0)
    (e : ℕ) (he : e ≤ r) (W : Fin 3 → MvPolynomial (Fin 3) (ZMod p))
    (hw : ∀ i, (W i).totalDegree ≤ e)
    (hdiv : ∀ a ∈ A, ∀ b ∈ A, a ≠ b →
      linearForm (a-b) ∣ ∑ i, MvPolynomial.C ((a-b) i)*W i) :
    ∃ q : MvPolynomial (Fin 3) (ZMod p), ∀ i, W i = q * MvPolynomial.X i := by
  classical
  obtain ⟨P,hdegree,hP⟩ := exists_direction_interpolant p A e W hw hdiv
  have h1 : P.natDegree ≤ 1 := by
    by_contra! hbig
    let k := r-P.natDegree+1
    have hkpos : 0 < k := by dsimp [k]; omega
    have hkr : k < r := by dsimp [k]; omega
    have htop : k-1+P.natDegree = r := by dsimp [k]; omega
    have hz := weighted_moment_of_zero p A W k hkpos (hkr.trans hr) (hlow _ hkr)
    have hz' : (∑ a ∈ A, linearForm a^(k-1)*P.eval (linearForm a)) = 0 := by
      convert hz using 1
      apply Finset.sum_congr rfl
      intro a ha
      rw [hP a ha]
    rw [interpolant_moment_sum,Finset.sum_range_succ,htop] at hz'
    have hsmall : ∑ j ∈ Finset.range P.natDegree, P.coeff j * moment p A (k-1+j) = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      have hj' := Finset.mem_range.mp hj
      rw [hlow _ (by omega),mul_zero]
    rw [hsmall,zero_add,Polynomial.coeff_natDegree] at hz'
    have hPne : P ≠ 0 := by rintro rfl; simp at hbig
    exact (Polynomial.leadingCoeff_ne_zero.mpr hPne) ((mul_eq_zero.mp hz').resolve_right hnon)
  have hz : P.coeff 0 = 0 := by
    rw [Polynomial.coeff_zero_eq_eval_zero]
    simpa [linearForm] using hP 0 hzero
  have hlin (a : Point p) (ha : a ∈ A) :
      vectorValue W a = P.coeff 1 * linearForm a := by
    rw [show vectorValue W a = P.eval (linearForm a) from (hP a ha).symm,
      Polynomial.eval_eq_sum_range' (n := 2) (by omega)]
    simp [Finset.sum_range_succ,hz]
  have hext (a : Point p) (ha : a ∈ Submodule.span (ZMod p) (↑A : Set (Point p))) :
      vectorValue W a = P.coeff 1 * linearForm a := by
    induction ha using Submodule.span_induction with
    | mem x hx => exact hlin x hx
    | zero => simp [vectorValue,linearForm]
    | add x y _ _ hx hy => rw [vectorValue_add, hx, hy, ← mul_add]; congr 1; exact (vectorValue_add MvPolynomial.X x y).symm
    | smul t x _ hx => rw [vectorValue_smul, hx, node_smul]; ring
  refine ⟨P.coeff 1,fun i => ?_⟩
  have h := hext (Pi.single i 1) (by rw [hspan]; trivial)
  simpa [vectorValue,linearForm,Pi.single_apply,ite_mul] using h

end Cylinder.Redei
end