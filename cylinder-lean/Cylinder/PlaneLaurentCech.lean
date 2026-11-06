module

public import Cylinder.PlaneLaurentPieces
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-! The ordered three-chart Laurent Čech model in each integer degree.
Its actual module-category middle homology is zero. Identifying this
model with sections of a projective twisting sheaf, and comparing Čech
cohomology to Ext-defined sheaf cohomology, are separate steps. -/

@[expose] public section
noncomputable section
open scoped Classical

universe u

namespace Cylinder.PlaneLaurentCech

open Cylinder.PlaneLaurentPieces CategoryTheory CategoryTheory.Limits

set_option autoImplicit false
set_option maxHeartbeats 800000

variable {K : Type u} [CommRing K]

abbrev ZeroCochains (v : ℤ) :=
  piece (K := K) v {0} × piece (K := K) v {1} × piece (K := K) v {2}

abbrev OneCochains (v : ℤ) :=
  piece (K := K) v {0, 1} × piece (K := K) v {0, 2} × piece (K := K) v {1, 2}

abbrev TwoCochains (v : ℤ) := piece (K := K) v Finset.univ

def differentialZero (v : ℤ) : ZeroCochains (K := K) v →ₗ[K] OneCochains (K := K) v where
  toFun s :=
    (⟨s.2.1.val - s.1.val, (piece (K := K) v {0, 1}).sub_mem
      (piece_mono (K := K) v (I := {1}) (J := {0, 1}) (by simp) s.2.1.property)
      (piece_mono (K := K) v (I := {0}) (J := {0, 1}) (by simp) s.1.property)⟩,
    ⟨s.2.2.val - s.1.val, (piece (K := K) v {0, 2}).sub_mem
      (piece_mono (K := K) v (I := {2}) (J := {0, 2}) (by simp) s.2.2.property)
      (piece_mono (K := K) v (I := {0}) (J := {0, 2}) (by simp) s.1.property)⟩,
    ⟨s.2.2.val - s.2.1.val, (piece (K := K) v {1, 2}).sub_mem
      (piece_mono (K := K) v (I := {2}) (J := {1, 2}) (by simp) s.2.2.property)
      (piece_mono (K := K) v (I := {1}) (J := {1, 2}) (by simp) s.2.1.property)⟩)
  map_add' s t := by
    apply Prod.ext
    · apply Subtype.ext
      change (s.2.1.val + t.2.1.val) - (s.1.val + t.1.val) =
        (s.2.1.val - s.1.val) + (t.2.1.val - t.1.val)
      abel
    · apply Prod.ext
      · apply Subtype.ext
        change (s.2.2.val + t.2.2.val) - (s.1.val + t.1.val) =
          (s.2.2.val - s.1.val) + (t.2.2.val - t.1.val)
        abel
      · apply Subtype.ext
        change (s.2.2.val + t.2.2.val) - (s.2.1.val + t.2.1.val) =
          (s.2.2.val - s.2.1.val) + (t.2.2.val - t.2.1.val)
        abel
  map_smul' a s := by
    apply Prod.ext
    · apply Subtype.ext
      exact (smul_sub a s.2.1.val s.1.val).symm
    · apply Prod.ext
      · apply Subtype.ext
        exact (smul_sub a s.2.2.val s.1.val).symm
      · apply Subtype.ext
        exact (smul_sub a s.2.2.val s.2.1.val).symm

def differentialOne (v : ℤ) : OneCochains (K := K) v →ₗ[K] TwoCochains (K := K) v where
  toFun f := ⟨f.2.2.val - f.2.1.val + f.1.val, (piece (K := K) v Finset.univ).add_mem
    ((piece (K := K) v Finset.univ).sub_mem
      (piece_mono (K := K) v (Finset.subset_univ _) f.2.2.property)
      (piece_mono (K := K) v (Finset.subset_univ _) f.2.1.property))
    (piece_mono (K := K) v (Finset.subset_univ _) f.1.property)⟩
  map_add' f g := by
    apply Subtype.ext
    change (f.2.2.val + g.2.2.val) - (f.2.1.val + g.2.1.val) + (f.1.val + g.1.val) =
      (f.2.2.val - f.2.1.val + f.1.val) + (g.2.2.val - g.2.1.val + g.1.val)
    abel
  map_smul' a f := by
    apply Subtype.ext
    change a • f.2.2.val - a • f.2.1.val + a • f.1.val =
      a • (f.2.2.val - f.2.1.val + f.1.val)
    rw [smul_add, smul_sub]

theorem differential_comp_zero (v : ℤ) :
    (differentialOne (K := K) v).comp (differentialZero v) = 0 := by
  apply LinearMap.ext
  intro s
  apply Subtype.ext
  change (s.2.2.val - s.2.1.val) - (s.2.2.val - s.1.val) + (s.2.1.val - s.1.val) = 0
  abel

theorem range_differentialZero_eq_ker (v : ℤ) :
    LinearMap.range (differentialZero (K := K) v) = LinearMap.ker (differentialOne v) := by
  apply le_antisymm
  · rintro t ⟨s, rfl⟩
    apply LinearMap.mem_ker.mpr
    exact congrArg (fun f : ZeroCochains (K := K) v →ₗ[K] TwoCochains (K := K) v => f s)
      (differential_comp_zero v)
  · intro t ht
    have hc : t.2.2.val - t.2.1.val + t.1.val = 0 :=
      congrArg (fun q : TwoCochains (K := K) v => q.val) (LinearMap.mem_ker.mp ht)
    obtain ⟨s₀, s₁, s₂, h₀₁, h₀₂, h₁₂⟩ := one_cocycle_has_primitive v
      t.1.val t.2.1.val t.2.2.val t.1.property t.2.1.property t.2.2.property hc
    refine ⟨(s₀, s₁, s₂), ?_⟩
    apply Prod.ext
    · apply Subtype.ext
      exact h₀₁.symm
    · apply Prod.ext
      · apply Subtype.ext
        exact h₀₂.symm
      · apply Subtype.ext
        exact h₁₂.symm

def standardComplex (v : ℤ) : ShortComplex (ModuleCat.{u} K) :=
  ShortComplex.mk
    (ModuleCat.ofHom (differentialZero (K := K) v) :
      ModuleCat.of K (ZeroCochains (K := K) v) ⟶ ModuleCat.of K (OneCochains (K := K) v))
    (ModuleCat.ofHom (differentialOne (K := K) v) :
      ModuleCat.of K (OneCochains (K := K) v) ⟶ ModuleCat.of K (TwoCochains (K := K) v))
    (by
      apply ModuleCat.hom_ext
      exact differential_comp_zero (K := K) v)

theorem standardComplex_exact (v : ℤ) : (standardComplex (K := K) v).Exact := by
  apply (ShortComplex.moduleCat_exact_iff_range_eq_ker (R := K) (standardComplex (K := K) v)).mpr
  exact range_differentialZero_eq_ker (K := K) v

theorem standardComplex_homology_isZero (v : ℤ) :
    IsZero (standardComplex (K := K) v).homology :=
  (ShortComplex.exact_iff_isZero_homology _).mp (standardComplex_exact (K := K) v)

end Cylinder.PlaneLaurentCech

end
