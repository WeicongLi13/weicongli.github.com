module

public import Cylinder.MomentCoordinatePullback
public import Cylinder.FinalGlobalMoments

/-! Exact finite moment identities under reindexing, representative scaling,
and the affine change of time induced by a centre-preserving linear chart. -/

@[expose] public section
noncomputable section
open scoped Classical BigOperators
namespace Cylinder.MomentCoordinateTransport
open MvPolynomial Cylinder.LinearEvaluationTransport

variable {K I J σ : Type*} [Field K]

def moment [Fintype J] (t c : J → K) (j : ℕ) : K := ∑ ν, c ν * t ν ^ j

theorem moment_reindex [Fintype I] [Fintype J] (e : I ≃ J) (t c : J → K) (j : ℕ) :
    moment (t ∘ e) (c ∘ e) j = moment t c j := by
  exact e.sum_comp (fun ν => c ν * t ν ^ j)

theorem moment_affine_zero [Fintype J] (t c : J → K) (q lam ℓ κ : K) :
    moment (fun ν => lam * (ℓ + κ * t ν)) (fun ν => q * c ν) 0 = q * moment t c 0 := by
  simp [moment, Finset.mul_sum, mul_assoc]

theorem moment_affine_one [Fintype J] (t c : J → K) (q lam ℓ κ : K) :
    moment (fun ν => lam * (ℓ + κ * t ν)) (fun ν => q * c ν) 1 =
      q * lam * (ℓ * moment t c 0 + κ * moment t c 1) := by
  simp only [moment, mul_add, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro ν _
  ring

theorem moment_affine_two [Fintype J] (t c : J → K) (q lam ℓ κ : K) :
    moment (fun ν => lam * (ℓ + κ * t ν)) (fun ν => q * c ν) 2 =
      q * lam ^ 2 * (ℓ ^ 2 * moment t c 0 + 2 * ℓ * κ * moment t c 1 +
        κ ^ 2 * moment t c 2) := by
  simp only [moment, mul_add, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro ν _
  ring

theorem moment_affine_three [Fintype J] (t c : J → K) (q lam ℓ κ : K) :
    moment (fun ν => lam * (ℓ + κ * t ν)) (fun ν => q * c ν) 3 =
      q * lam ^ 3 * (ℓ ^ 3 * moment t c 0 + 3 * ℓ ^ 2 * κ * moment t c 1 +
        3 * ℓ * κ ^ 2 * moment t c 2 + κ ^ 3 * moment t c 3) := by
  simp only [moment, mul_add, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro ν _
  ring

/-- The low moments after a change of chart use the original fixed weights. -/
theorem first_moments [Fintype J] (t c : J → K) (q lam ℓ κ : K)
    (h0 : moment t c 0 = 0) :
    moment (fun ν => lam * (ℓ + κ * t ν)) (fun ν => q * c ν) 0 = 0 ∧
    moment (fun ν => lam * (ℓ + κ * t ν)) (fun ν => q * c ν) 1 =
      q * lam * κ * moment t c 1 ∧
    moment (fun ν => lam * (ℓ + κ * t ν)) (fun ν => q * c ν) 2 =
      q * lam ^ 2 * (2 * ℓ * κ * moment t c 1 + κ ^ 2 * moment t c 2) ∧
    moment (fun ν => lam * (ℓ + κ * t ν)) (fun ν => q * c ν) 3 =
      q * lam ^ 3 * (3 * ℓ ^ 2 * κ * moment t c 1 +
        3 * ℓ * κ ^ 2 * moment t c 2 + κ ^ 3 * moment t c 3) := by
  simp only [moment_affine_zero, moment_affine_one, moment_affine_two, moment_affine_three,
    h0, mul_zero, zero_add, add_zero, mul_assoc]
  repeat' constructor

variable [Fintype σ]

def linearPolynomial (ℓ : (σ → K) →ₗ[K] K) : MvPolynomial σ K :=
  ∑ i, C (ℓ (Pi.single i 1)) * X i

theorem linearPolynomial_homogeneous (ℓ : (σ → K) →ₗ[K] K) :
    (linearPolynomial ℓ).IsHomogeneous 1 := by
  apply IsHomogeneous.sum
  intro i _
  exact isHomogeneous_C_mul_X _ _

@[simp] theorem linearPolynomial_eval (ℓ : (σ → K) →ₗ[K] K) (a : σ → K) :
    eval a (linearPolynomial ℓ) = ℓ a := by
  have h := congrArg ℓ (vector_eq_sum_single a)
  simpa [linearPolynomial, map_sum, map_smul, smul_eq_mul, mul_comm] using h.symm

/-- The linear moment form in the target plane coordinates. -/
def linearMomentForm (A : (σ → K) ≃ₗ[K] (σ → K))
    (ℓ : (σ → K) →ₗ[K] K) (κ : K) (f : MvPolynomial σ K) : MvPolynomial σ K :=
  linearPullback A.symm (C 2 * linearPolynomial ℓ + C κ * f)

/-- The quadratic moment form in the target plane coordinates. -/
def quadraticMomentForm (A : (σ → K) ≃ₗ[K] (σ → K))
    (ℓ : (σ → K) →ₗ[K] K) (κ : K) (f g : MvPolynomial σ K) : MvPolynomial σ K :=
  linearPullback A.symm (C 3 * linearPolynomial ℓ ^ 2 +
    C (3 * κ) * (linearPolynomial ℓ * f) + C (κ ^ 2) * g)

theorem linearMomentForm_homogeneous (A : (σ → K) ≃ₗ[K] (σ → K))
    (ℓ : (σ → K) →ₗ[K] K) (κ : K) (f : MvPolynomial σ K)
    (hf : f.IsHomogeneous 1) : (linearMomentForm A ℓ κ f).IsHomogeneous 1 := by
  apply linearPullback_homogeneous
  exact ((linearPolynomial_homogeneous ℓ).C_mul 2).add (hf.C_mul κ)

theorem quadraticMomentForm_homogeneous (A : (σ → K) ≃ₗ[K] (σ → K))
    (ℓ : (σ → K) →ₗ[K] K) (κ : K) (f g : MvPolynomial σ K)
    (hf : f.IsHomogeneous 1) (hg : g.IsHomogeneous 2) :
    (quadraticMomentForm A ℓ κ f g).IsHomogeneous 2 := by
  apply linearPullback_homogeneous
  have hℓ := linearPolynomial_homogeneous ℓ
  exact (((by simpa using hℓ.pow 2 : (linearPolynomial ℓ ^ 2).IsHomogeneous 2).C_mul 3).add
    ((hℓ.mul hf).C_mul (3 * κ))).add (hg.C_mul (κ ^ 2))

theorem linearMomentForm_eval (A : (σ → K) ≃ₗ[K] (σ → K))
    (ℓ : (σ → K) →ₗ[K] K) (κ : K) (f : MvPolynomial σ K)
    (hf : f.IsHomogeneous 1) (lam : K) (a : σ → K) :
    eval (lam • A a) (linearMomentForm A ℓ κ f) = lam * (2 * ℓ a + κ * eval a f) := by
  rw [homogeneous_eval_smul _ 1 (linearMomentForm_homogeneous A ℓ κ f hf)]
  simp [linearMomentForm, linearPullback_eval]

theorem quadraticMomentForm_eval (A : (σ → K) ≃ₗ[K] (σ → K))
    (ℓ : (σ → K) →ₗ[K] K) (κ : K) (f g : MvPolynomial σ K)
    (hf : f.IsHomogeneous 1) (hg : g.IsHomogeneous 2) (lam : K) (a : σ → K) :
    eval (lam • A a) (quadraticMomentForm A ℓ κ f g) =
      lam ^ 2 * (3 * (ℓ a) ^ 2 + 3 * κ * (ℓ a * eval a f) + κ ^ 2 * eval a g) := by
  rw [homogeneous_eval_smul _ 2 (quadraticMomentForm_homogeneous A ℓ κ f g hf hg)]
  simp [quadraticMomentForm, linearPullback_eval]

/-- Transport the two interpolation equations with their fixed residues. -/
theorem interpolation_transport [Fintype J]
    (A : (σ → K) ≃ₗ[K] (σ → K)) (ℓ : (σ → K) →ₗ[K] K)
    (κ q lam : K) (a : σ → K) (t c : J → K) (f g : MvPolynomial σ K)
    (hf : f.IsHomogeneous 1) (hg : g.IsHomogeneous 2)
    (h0 : moment t c 0 = 0)
    (h2 : moment t c 2 = eval a f * moment t c 1)
    (h3 : moment t c 3 = eval a g * moment t c 1) :
    moment (fun ν => lam * (ℓ a + κ * t ν)) (fun ν => q * c ν) 2 =
      eval (lam • A a) (linearMomentForm A ℓ κ f) *
        moment (fun ν => lam * (ℓ a + κ * t ν)) (fun ν => q * c ν) 1 ∧
    moment (fun ν => lam * (ℓ a + κ * t ν)) (fun ν => q * c ν) 3 =
      eval (lam • A a) (quadraticMomentForm A ℓ κ f g) *
        moment (fun ν => lam * (ℓ a + κ * t ν)) (fun ν => q * c ν) 1 := by
  rw [moment_affine_one, moment_affine_two, moment_affine_three,
    linearMomentForm_eval A ℓ κ f hf, quadraticMomentForm_eval A ℓ κ f g hf hg,
    h0, h2, h3]
  constructor <;> ring

end Cylinder.MomentCoordinateTransport
end
