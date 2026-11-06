module

public import Cylinder.CompleteIntersectionKoszul
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.Spectrum.Maximal.Basic
public import Mathlib.RingTheory.Artinian.Ring

/-! The actual common affine zeros of two equations are in bijection
with the maximal ideals of their actual finite dimensional quotient.
The reverse map is constructed from the residue field, which equals
the algebraically closed ground field. -/

@[expose] public section
noncomputable section
open scoped Classical
set_option autoImplicit false

namespace Cylinder.AffineIntersectionPoints

open MvPolynomial Module Cylinder.CompleteIntersectionKoszul

variable {K σ : Type*} [Field K] (f g : MvPolynomial σ K)

abbrev CommonZero := {x : σ → K // eval x f = 0 ∧ eval x g = 0}

def polynomialEvaluation (x : σ → K) : MvPolynomial σ K →ₐ[K] K where
  __ := eval x
  commutes' c := eval_C c

def evaluationAt (x : CommonZero f g) : QuotientRing f g →ₐ[K] K :=
  Ideal.Quotient.liftₐ (equationsIdeal f g) (polynomialEvaluation x.val) (by
    intro P hP
    obtain ⟨a, b, hab⟩ := Ideal.mem_span_pair.mp hP
    change eval x.val P = 0
    simp only [← hab, map_add, map_mul, x.property.1, x.property.2, mul_zero, add_zero])

theorem evaluationAt_mk (x : CommonZero f g) (P : MvPolynomial σ K) :
    evaluationAt f g x (Ideal.Quotient.mk (equationsIdeal f g) P) = eval x.val P := rfl

theorem evaluationAt_surjective (x : CommonZero f g) : Function.Surjective (evaluationAt f g x) := by
  intro c
  exact ⟨Ideal.Quotient.mk (equationsIdeal f g) (C c), eval_C c⟩

def toMaximalSpectrum (x : CommonZero f g) : MaximalSpectrum (QuotientRing f g) :=
  ⟨RingHom.ker (evaluationAt f g x).toRingHom,
    RingHom.ker_isMaximal_of_surjective _ (evaluationAt_surjective f g x)⟩

theorem toMaximalSpectrum_injective : Function.Injective (toMaximalSpectrum f g) := by
  intro x y hxy
  apply Subtype.ext
  funext i
  have hi := congrArg MaximalSpectrum.asIdeal hxy
  have hx : Ideal.Quotient.mk (equationsIdeal f g) (X i - C (x.val i)) ∈
      (toMaximalSpectrum f g x).asIdeal := by
    change eval x.val (X i - C (x.val i)) = 0
    simp
  have hy : eval y.val (X i - C (x.val i)) = 0 := by
    change Ideal.Quotient.mk (equationsIdeal f g) (X i - C (x.val i)) ∈
      (toMaximalSpectrum f g y).asIdeal
    rw [← hi]
    exact hx
  exact (sub_eq_zero.mp (by simpa using hy)).symm

theorem toMaximalSpectrum_surjective [IsAlgClosed K] [FiniteDimensional K (QuotientRing f g)] :
    Function.Surjective (toMaximalSpectrum f g) := by
  intro m
  let B := QuotientRing f g ⧸ m.asIdeal
  let : Field B := Ideal.Quotient.field m.asIdeal
  let : FiniteDimensional K B := inferInstance
  let e : K ≃ₐ[K] B :=
    AlgEquiv.ofBijective (Algebra.ofId K B) IsAlgClosed.algebraMap_bijective_of_isIntegral
  let phi : QuotientRing f g →ₐ[K] K := e.symm.toAlgHom.comp (Ideal.Quotient.mkₐ K m.asIdeal)
  let psi : MvPolynomial σ K →ₐ[K] K := phi.comp (Ideal.Quotient.mkₐ K (equationsIdeal f g))
  let v : σ → K := fun i => psi (X i)
  have hpsi : psi = polynomialEvaluation v := by
    ext i
    change psi (X i) = eval v (X i)
    rw [eval_X]
  have hf0 : Ideal.Quotient.mk (equationsIdeal f g) f = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_insert f {g}))
  have hg0 : Ideal.Quotient.mk (equationsIdeal f g) g = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_insert_of_mem f (Set.mem_singleton g)))
  have hvf : eval v f = 0 := by
    change polynomialEvaluation v f = 0
    rw [← hpsi]
    change phi (Ideal.Quotient.mk (equationsIdeal f g) f) = 0
    rw [hf0, map_zero]
  have hvg : eval v g = 0 := by
    change polynomialEvaluation v g = 0
    rw [← hpsi]
    change phi (Ideal.Quotient.mk (equationsIdeal f g) g) = 0
    rw [hg0, map_zero]
  let x : CommonZero f g := ⟨v, hvf, hvg⟩
  refine ⟨x, ?_⟩
  apply MaximalSpectrum.ext
  ext a
  obtain ⟨P, rfl⟩ := Ideal.Quotient.mk_surjective a
  change eval v P = 0 ↔ Ideal.Quotient.mk (equationsIdeal f g) P ∈ m.asIdeal
  change polynomialEvaluation v P = 0 ↔ _
  rw [← hpsi]
  change e.symm (Ideal.Quotient.mk m.asIdeal (Ideal.Quotient.mk (equationsIdeal f g) P)) = 0 ↔ _
  constructor
  · intro h
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    apply e.symm.injective
    exact h.trans (map_zero e.symm).symm
  · intro h
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr h, map_zero]

def commonZeroEquivMaximalSpectrum [IsAlgClosed K] [FiniteDimensional K (QuotientRing f g)] :
    CommonZero f g ≃ MaximalSpectrum (QuotientRing f g) :=
  Equiv.ofBijective (toMaximalSpectrum f g)
    ⟨toMaximalSpectrum_injective f g, toMaximalSpectrum_surjective f g⟩

end Cylinder.AffineIntersectionPoints
end
