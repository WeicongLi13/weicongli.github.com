module

public import Mathlib.RingTheory.IntegralDomain

/-! A finite subgroup of a field's units is cyclic. Its power roots
inject into the roots of the actual polynomial X^n - 1. -/

@[expose] public section
noncomputable section
open scoped Classical

namespace Cylinder.FieldSubgroupCyclic

variable {K : Type*} [Field K]

def valueHom (H : Subgroup Kˣ) : H →* K where
  toFun g := (g.val : K)
  map_one' := rfl
  map_mul' _ _ := rfl

theorem valueHom_injective (H : Subgroup Kˣ) : Function.Injective (valueHom H) :=
  Units.val_injective.comp Subtype.val_injective

theorem power_root_card_le (H : Subgroup Kˣ) [Fintype H] (n : ℕ) (hn : 0 < n) :
    (Finset.univ.filter (fun g : H => g ^ n = 1)).card ≤ n := by
  calc
    _ ≤ (Polynomial.nthRoots n (valueHom H 1)).card :=
      card_nthRoots_subgroup_units (valueHom H) (valueHom_injective H) hn 1
    _ ≤ n := Polynomial.card_nthRoots n (valueHom H 1)

theorem isCyclic (H : Subgroup Kˣ) [Finite H] : IsCyclic H := by
  let : Fintype H := Fintype.ofFinite H
  exact isCyclic_of_card_pow_eq_one_le (fun n hn => power_root_card_le H n hn)

theorem exists_generator (H : Subgroup Kˣ) [Finite H] :
    ∃ g : H, orderOf g = Nat.card H ∧ ∀ x : H, x ∈ Subgroup.zpowers g := by
  let : IsCyclic H := isCyclic H
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := H)
  exact ⟨g, orderOf_eq_card_of_forall_mem_zpowers hg, hg⟩

def generator (H : Subgroup Kˣ) [Finite H] : H := Classical.choose (exists_generator H)

theorem generator_order (H : Subgroup Kˣ) [Finite H] : orderOf (generator H) = Nat.card H :=
  (Classical.choose_spec (exists_generator H)).1

theorem generator_generates (H : Subgroup Kˣ) [Finite H] (x : H) :
    x ∈ Subgroup.zpowers (generator H) := (Classical.choose_spec (exists_generator H)).2 x

theorem unit_generator_order (H : Subgroup Kˣ) [Finite H] :
    orderOf (generator H).val = Nat.card H := by
  exact (orderOf_injective H.subtype Subtype.val_injective (generator H)).trans (generator_order H)

theorem value_generator_order (H : Subgroup Kˣ) [Finite H] :
    orderOf ((generator H).val : K) = Nat.card H := by
  exact (orderOf_injective (valueHom H) (valueHom_injective H) (generator H)).trans (generator_order H)

end Cylinder.FieldSubgroupCyclic

end
