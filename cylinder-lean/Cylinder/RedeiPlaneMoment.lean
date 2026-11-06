import Cylinder.RedeiPlane
import Cylinder.RedeiQuotient
import Cylinder.RedeiGraphMoment
import Cylinder.LinearFormFactors
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Algebra.Polynomial.Degree.SmallDegree
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! Low moments show that two normalized planar factors cannot both span the plane. -/

noncomputable section
namespace Cylinder.RedeiPlaneMoment

open scoped BigOperators Classical
open PowerEvaluationRelation

variable {p : ℕ} [Fact p.Prime]
abbrev Plane (p : ℕ) := Fin 2 → ZMod p

/-- Interpolating coordinates of a spanning graph over its bijective
parameter must give a genuinely nonlinear coordinate function. -/
theorem exists_nonlinear_coordinate {n : ℕ} (hn : 2 ≤ n) (S : Finset (Fin n → ZMod p)) (h0 : 0 ∈ S)
    (hspan : Submodule.span (ZMod p) (S : Set (Fin n → ZMod p)) = ⊤)
    (l : (Fin n → ZMod p) →ₗ[ZMod p] ZMod p) (hl : Function.Bijective (fun x : S => l x)) :
    ∃ i : Fin n, ∃ f : Polynomial (ZMod p), 2 ≤ f.natDegree ∧ f.natDegree < p ∧
      ∀ x : S, f.eval (l x) = (x : Fin n → ZMod p) i := by
  let e : S ≃ ZMod p := Equiv.ofBijective (fun x : S => l x) hl
  let f (i : Fin n) := Lagrange.interpolate Finset.univ id (fun t : ZMod p => ((e.symm t : S) : Fin n → ZMod p) i)
  have hnode (i : Fin n) (x : S) : (f i).eval (l x) = (x : Fin n → ZMod p) i := by
    change (f i).eval (id (e x)) = _
    rw [show (f i).eval (id (e x)) = ((e.symm (e x) : S) : Fin n → ZMod p) i from
      Lagrange.eval_interpolate_at_node (fun t : ZMod p => ((e.symm t : S) : Fin n → ZMod p) i)
        (Set.injOn_id _) (Finset.mem_univ _)]
    simp
  have hdeg (i : Fin n) : (f i).natDegree < p := by
    have hp := (Fact.out : p.Prime).pos
    by_cases h : f i = 0
    · simpa [h] using hp
    · apply (Polynomial.natDegree_lt_iff_degree_lt h).mpr
      simpa [f, ZMod.card] using Lagrange.degree_interpolate_lt
        (r := fun t : ZMod p => ((e.symm t : S) : Fin n → ZMod p) i)
        (s := Finset.univ) (v := id) (Set.injOn_id _)
  by_cases he : ∃ i, 2 ≤ (f i).natDegree
  · obtain ⟨i, hi⟩ := he
    exact ⟨i, f i, hi, hdeg i, hnode i⟩
  · push Not at he
    let w : Fin n → ZMod p := fun i => (f i).coeff 1
    have hle : Submodule.span (ZMod p) (S : Set (Fin n → ZMod p)) ≤
        Submodule.span (ZMod p) {w} := by
      apply Submodule.span_le.mpr
      intro x hx
      apply Submodule.mem_span_singleton.mpr
      refine ⟨l x, ?_⟩
      funext i
      have hform := Polynomial.eq_X_add_C_of_natDegree_le_one (p := f i) (by have := he i; omega)
      have hcoeff (t : ZMod p) : (f i).eval t = (f i).coeff 1 * t + (f i).coeff 0 := by
        conv_lhs => rw [hform]
        simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
      have hzero := hnode i (⟨0,h0⟩ : S)
      change (f i).eval (l 0) = 0 at hzero
      rw [map_zero, hcoeff, mul_zero, zero_add] at hzero
      change l x * (f i).coeff 1 = x i
      calc
        _ = (f i).coeff 1 * l x := mul_comm _ _
        _ = (f i).eval (l x) := by rw [hcoeff, hzero, add_zero]
        _ = x i := hnode i ⟨x,hx⟩
    rw [hspan] at hle
    have hdim := Submodule.finrank_mono hle
    rw [finrank_top, Module.finrank_fin_fun] at hdim
    have hone : Module.finrank (ZMod p) ↥(Submodule.span (ZMod p) {w}) ≤ 1 := by
      simpa using (finrank_span_le_card (R := ZMod p) ({w} : Set (Fin n → ZMod p)))
    omega

def moment {n : ℕ} (S : Finset (Fin n → ZMod p)) (r : ℕ) : MvPolynomial (Fin n) (ZMod p) :=
  powerSum (fun x : S => (x : Fin n → ZMod p)) (fun _ => 1) r

private theorem moment_homogeneous {n : ℕ} (S : Finset (Fin n → ZMod p)) (r : ℕ) : (moment S r).IsHomogeneous r := by
  unfold moment powerSum
  apply MvPolynomial.IsHomogeneous.sum
  intro i _
  simpa only [one_mul] using
    (((LinearFormFactors.linearForm_homogeneous (i : Fin n → ZMod p)).pow r).C_mul (1 : ZMod p))

private theorem reconstruct_linear {n : ℕ} (l : (Fin n → ZMod p) →ₗ[ZMod p] ZMod p) (x : Fin n → ZMod p) :
    ∑ i, l (Pi.single i 1) * x i = l x := by
  have h : ∑ i, x i • (Pi.single i (1 : ZMod p) : Fin n → ZMod p) = x := by
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  conv_rhs => rw [← h, map_sum]
  simp [mul_comm]

/-- In the original coordinates, some positive low moment of a
normalized spanning factor is nonzero whenever a linear parameter is bijective. -/
theorem exists_nonzero_moment {n : ℕ} (hn : 2 ≤ n) (S : Finset (Fin n → ZMod p)) (h0 : 0 ∈ S)
    (hspan : Submodule.span (ZMod p) (S : Set (Fin n → ZMod p)) = ⊤)
    (l : (Fin n → ZMod p) →ₗ[ZMod p] ZMod p) (hl : Function.Bijective (fun x : S => l x)) :
    ∃ r, 0 < r ∧ 2*r ≤ p-1 ∧ moment S r ≠ 0 := by
  obtain ⟨i,f,hf,hfp,hval⟩ := exists_nonlinear_coordinate hn S h0 hspan l hl
  obtain ⟨a,b,hab,hr,hsum⟩ := Redei.graph_mixed_moment p f hf hfp
  refine ⟨a+b,hab,hr,?_⟩
  intro hz
  have hp := (Fact.out : p.Prime).pos
  have hrel := relation_of_powerSum_eq_zero p (fun x : S => (x : Fin n → ZMod p))
    (fun _ => 1) (a+b) (by omega) hz
  let L := linearForm fun j : Fin n => l (Pi.single j 1)
  have hhom : (L^a * (MvPolynomial.X i)^b).IsHomogeneous (a+b) := by
    simpa only [one_mul] using ((LinearFormFactors.linearForm_homogeneous _).pow a).mul
      (MvPolynomial.isHomogeneous_X_pow i b)
  have hz' := hrel _ hhom
  have hev (x : S) : MvPolynomial.eval (x : Fin n → ZMod p) L = l x :=
    (FiniteFieldHyperplaneDivisibility.eval_linearForm _ _).trans (reconstruct_linear l _)
  simp only [map_mul, map_pow, MvPolynomial.eval_X, one_mul, hev] at hz'
  apply hsum
  calc
    (∑ x : ZMod p, x^a * (f.eval x)^b) = ∑ x : S, (l x)^a*(f.eval (l x))^b :=
      (hl.sum_comp (fun x => x^a*(f.eval x)^b)).symm
    _ = 0 := by simpa only [hval] using hz'

private theorem eval_moment (S : Finset (Plane p)) (r : ℕ) (u : Plane p) :
    MvPolynomial.eval u (moment S r) = ∑ x : S, (∑ i, (x : Plane p) i * u i)^r := by
  simp [moment, powerSum, linearForm]

/-- A linearly bijective projection on one of the two factors in every
direction is incompatible with both factors spanning the plane. -/
theorem proper_span_of_projection_dichotomy (A B : Finset (Plane p)) (h0A : 0 ∈ A) (h0B : 0 ∈ B)
    (lA lB : Plane p →ₗ[ZMod p] ZMod p)
    (hlA : Function.Bijective (fun x : A => lA x)) (hlB : Function.Bijective (fun x : B => lB x))
    (hd : ∀ u : Plane p, u ≠ 0 →
      Function.Bijective (fun x : A => ∑ i, (x : Plane p) i * u i) ∨
      Function.Bijective (fun x : B => ∑ i, (x : Plane p) i * u i)) :
    Submodule.span (ZMod p) (A : Set (Plane p)) ≠ ⊤ ∨
    Submodule.span (ZMod p) (B : Set (Plane p)) ≠ ⊤ := by
  by_contra! hspan
  obtain ⟨r,hr,hrp,ha⟩ := exists_nonzero_moment (by decide : 2 ≤ 2) A h0A hspan.1 lA hlA
  obtain ⟨s,hs,hsp,hb⟩ := exists_nonzero_moment (by decide : 2 ≤ 2) B h0B hspan.2 lB hlB
  have hp := (Fact.out : p.Prime).two_le
  apply mul_ne_zero ha hb
  apply FiniteGrid.eq_zero_of_degreeOf_lt_card
  · intro i
    apply lt_of_le_of_lt (MvPolynomial.degreeOf_le_totalDegree _ i)
    have hbound := ((moment_homogeneous A r).mul (moment_homogeneous B s)).totalDegree_le
    rw [ZMod.card]
    omega
  · intro u
    rw [map_mul, eval_moment, eval_moment]
    by_cases hu : u = 0
    · simp [hu, zero_pow (Nat.ne_of_gt hr)]
    · obtain h | h := hd u hu
      · apply mul_eq_zero_of_left
        exact (h.sum_comp (fun z => z^r)).trans (PowerSums.prime_sum_pow_low p r (by omega))
      · apply mul_eq_zero_of_right
        exact (h.sum_comp (fun z => z^s)).trans (PowerSums.prime_sum_pow_low p s (by omega))


/-- The normalized Rédei factorization theorem in the plane, for the two
prime-sized images arising from the quotient of a cylinder. -/
theorem planar_factorization (p : ℕ) [Fact p.Prime] : RedeiQuotient.PlanarFactorization p := by
  intro A B hA hB hzeroA hzeroB htile
  obtain ⟨⟨lA,hlA⟩,⟨lB,hlB⟩⟩ := RedeiPlane.exists_bijective_projections A B htile hA hB
  exact proper_span_of_projection_dichotomy A B hzeroA hzeroB lA lB hlA hlB
    (RedeiPlane.dot_dichotomy A B htile hA hB)

/-- The last section of the three-dimensional proof with the planar
factorization input discharged. -/
theorem proper_span_of_cylindrical_factor {A B : Finset (Geometry.Point p)}
    (hcard : A.card = p) (hA : 0 ∈ A) (hB : 0 ∈ B)
    (htile : AddSubgroup.IsComplement (A : Set (Geometry.Point p)) B)
    (hcyl : Geometry.IsCylinder p B) :
    Submodule.span (ZMod p) (A : Set (Geometry.Point p)) ≠ ⊤ ∨
    Submodule.span (ZMod p) (B : Set (Geometry.Point p)) ≠ ⊤ :=
  RedeiQuotient.proper_span_of_cylinder (planar_factorization p) hcard hA hB htile hcyl


/-- The same coordinate argument gives the small-factor moment in three
dimensions, without having to transport the moment of a graph through a
chosen change of coordinates. -/
theorem exists_nonzero_moment_three (S : Finset (Geometry.Point p)) (h0 : 0 ∈ S)
    (hspan : Submodule.span (ZMod p) (S : Set (Geometry.Point p)) = ⊤)
    (l : Geometry.Point p →ₗ[ZMod p] ZMod p) (hl : Function.Bijective (fun x : S => l x)) :
    ∃ r, 0 < r ∧ 2*r ≤ p-1 ∧ Redei.moment p S r ≠ 0 := by
  obtain ⟨r,hr,hrp,h⟩ := exists_nonzero_moment (by decide : 2 ≤ 3) S h0 hspan l hl
  refine ⟨r,hr,hrp,?_⟩
  have heq : moment S r = Redei.moment p S r := by
    simp only [moment, powerSum, map_one, one_mul, Redei.moment]
    exact Finset.sum_coe_sort S (fun x => linearForm x ^ r)
  rwa [← heq]

end Cylinder.RedeiPlaneMoment
end
