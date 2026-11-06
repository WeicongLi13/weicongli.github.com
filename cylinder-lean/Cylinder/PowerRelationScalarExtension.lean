module

public import Cylinder.PowerEvaluationRelation

/-! Power identities and evaluation relations after extension of the field. -/

@[expose] public section
noncomputable section
open scoped Classical

namespace Cylinder.PowerRelationScalarExtension

open MvPolynomial Finset Cylinder.PowerEvaluationRelation

variable {K L σ I : Type*} [Field K] [Field L] [Fintype σ] [Fintype I]

theorem map_linearForm (f : K →+* L) (a : σ → K) :
    MvPolynomial.map f (linearForm a) = linearForm (fun j => f (a j)) := by
  simp [linearForm]

theorem map_powerSum (f : K →+* L) (v : I → σ → K) (c : I → K) (d : ℕ) :
    MvPolynomial.map f (powerSum v c d) =
      powerSum (fun i j => f (v i j)) (fun i => f (c i)) d := by
  simp [powerSum, map_linearForm]

omit [Fintype I] in
/-- Every nonzero relation coefficient stays nonzero under the actual field embedding. -/
theorem coefficients_nonzero (f : K →+* L) (c : I → K) (hc : ∀ i, c i ≠ 0) :
    ∀ i, f (c i) ≠ 0 := by
  intro i hz
  apply hc i
  exact f.injective (by simpa only [map_zero] using hz)

theorem relation_of_mapped_power_identity (p : ℕ) [Fact p.Prime] [CharP L p]
    (f : K →+* L) (v : I → σ → K) (c : I → K) (d : ℕ) (hd : d < p)
    (hzero : powerSum v c d = 0) :
    Relation (fun i j => f (v i j)) (fun i => f (c i)) d := by
  apply relation_of_powerSum_eq_zero p _ _ d hd
  have h := congrArg (MvPolynomial.map f) hzero
  simpa only [map_powerSum, map_zero] using h

/-- A relation over the base field gives the same relation on all homogeneous
forms over the extension field, including forms whose coefficients are new. -/
theorem relation_scalar_extension (p : ℕ) [Fact p.Prime] [CharP L p]
    (f : K →+* L) (v : I → σ → K) (c : I → K) (d : ℕ) (hd : d < p)
    (hrel : Relation v c d) :
    Relation (fun i j => f (v i j)) (fun i => f (c i)) d :=
  relation_of_mapped_power_identity p f v c d hd (powerSum_eq_zero_of_relation v c d hrel)

end Cylinder.PowerRelationScalarExtension

end
