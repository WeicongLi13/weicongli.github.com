import NSDensity.Classification
import NSDensity.ESArithmetic

namespace NSDensity

/-- Equally-spaced pairs remain equally spaced at the actual alphabet of
every normal-form endpoint, not only after descent to the prime alphabet. -/
theorem EquallySpaced.of_normalForm_endpoint {p a e n f : ℕ}
    (hp : 1 < p) (he : 0 < e) (hcopFinal : Nat.Coprime p n)
    (hES : EquallySpaced (p ^ e) a) (hNF : NormalForm p (a, e) (n, f)) :
    EquallySpaced (p ^ f) n := by
  obtain ⟨t, u, ht, hu, hnu, hcop, hdiv, hfe⟩ := hNF
  dsimp only at hnu hcop hdiv hfe
  have hEt : 0 < e * t := Nat.mul_pos he ht
  have hbase : 1 < p ^ (e * t) := by
    simpa only [pow_zero] using Nat.pow_lt_pow_right hp hEt
  have hLift : EquallySpaced (p ^ (e * t)) a := by
    simpa only [pow_mul] using
      hES.lift (by simpa only [Nat.cast_pow] using hcop)
  have hExt : EquallySpaced (p ^ (e * t)) n := by
    rw [hnu]
    exact hLift.extension hbase hdiv
  obtain ⟨r, hr⟩ := hfe
  have hrpos : 0 < r := by
    by_contra hnot
    have hrzero : r = 0 := by omega
    rw [hrzero, Nat.mul_zero] at hr
    exact Nat.ne_of_gt hEt hr
  rw [hr, pow_mul] at hExt
  exact EquallySpaced.descent hrpos (hcopFinal.pow_left f) hExt

/-- Closure under any finite sequence of lifting, extension, and
unrestricted descent, with the final alphabet retained. -/
theorem EquallySpaced.of_derived {p a e n f : ℕ}
    (hp : 1 < p) (he : 0 < e) (hcopFinal : Nat.Coprime p n)
    (hES : EquallySpaced (p ^ e) a) (hpath : Derived p (a, e) (n, f)) :
    EquallySpaced (p ^ f) n :=
  hES.of_normalForm_endpoint hp he hcopFinal
    (derived_normalForm hp.le hES.1 hpath)

/-- The same closure holds for the four-construction classification path,
because the tensor construction has an elementary-operation reduction. -/
theorem EquallySpaced.of_classificationPath {p a e n f : ℕ}
    (hp : 1 < p) (he : 0 < e) (hcopFinal : Nat.Coprime p n)
    (hES : EquallySpaced (p ^ e) a)
    (hpath : Relation.ReflTransGen (ClassificationStep p) (a, e) (n, f)) :
    EquallySpaced (p ^ f) n :=
  hES.of_derived hp he hcopFinal (classification_derived hp.le hpath)

/-- The nonstandard initial family's lower bound also survives every
elementary construction. -/
theorem EquallySpaced.of_derived_length_ge_six {p a e n f : ℕ}
    (hp : 1 < p) (he : 0 < e) (hcopFinal : Nat.Coprime p n)
    (ha6 : 6 ≤ a) (hES : EquallySpaced (p ^ e) a)
    (hpath : Derived p (a, e) (n, f)) :
    6 ≤ n ∧ EquallySpaced (p ^ f) n := by
  have hNF := derived_normalForm hp.le hES.1 hpath
  refine ⟨?_, hES.of_normalForm_endpoint hp he hcopFinal hNF⟩
  obtain ⟨t, u, ht, hu, hnu, _⟩ := hNF
  dsimp only at hnu
  rw [hnu]
  exact ha6.trans (Nat.le_mul_of_pos_right a hu)

#print axioms EquallySpaced.of_derived
#print axioms EquallySpaced.of_classificationPath
#print axioms EquallySpaced.of_derived_length_ge_six

end NSDensity
