import Cylinder.Geometry
import Cylinder.PrimeTwo

/-!
# Connecting the exhaustive binary model with affine coordinates

This file relates `Fin 8` and Boolean subsets to `Fin 3 → ZMod 2` and
`Finset`.  Its final theorem concerns the same geometric predicate used for
all primes in `Geometry.lean`; it does not extend that result beyond `p = 2`.
-/

namespace Cylinder.PrimeTwoGeometry

open Cylinder.Geometry

local instance : Fact (Nat.Prime 2) := ⟨by decide⟩

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Decode the three bits as an actual vector over `ZMod 2`. -/
def decode (q : PrimeTwo.Point) : Geometry.Point 2 :=
  fun i => if i = 0 then PrimeTwo.x q else if i = 1 then PrimeTwo.y q else PrimeTwo.z q

/-- Encode the three coordinates as their binary index. -/
def encode (v : Geometry.Point 2) : PrimeTwo.Point :=
  PrimeTwo.encode (v 0) (v 1) (v 2)

/-- Interpret a binary constant term as a field element. -/
def toScalar (b : PrimeTwo.Bit) : ZMod 2 := (b.val : ZMod 2)

@[simp] theorem encode_decode : ∀ q : PrimeTwo.Point, encode (decode q) = q := by
  intro q
  exact PrimeTwo.coordinates_encode q

@[simp] theorem decode_encode : ∀ v : Geometry.Point 2, decode (encode v) = v := by
  intro v
  have h := PrimeTwo.encode_coordinates (v 0) (v 1) (v 2)
  funext i
  fin_cases i
  · exact h.1
  · exact h.2.1
  · exact h.2.2

theorem decode_injective : Function.Injective decode := by
  intro q r h
  have := congrArg encode h
  simpa using this

@[simp] theorem decode_ne_zero :
    ∀ q : PrimeTwo.Point, decode q ≠ 0 ↔ q ≠ 0 := by
  decide

theorem decode_add :
    ∀ q r : PrimeTwo.Point, decode (PrimeTwo.add q r) = decode q + decode r := by
  decide

/-- The enumerated affine-plane test is exactly the coordinate equation. -/
theorem onPlane_decode :
    ∀ (n : PrimeTwo.Point) (b : PrimeTwo.Bit) (q : PrimeTwo.Point),
      PrimeTwo.onPlane n b q =
        decide (pairing 2 (decode n) (decode q) = toScalar b) := by
  decide

/-- The enumerated two-point line is the affine line over `ZMod 2`. -/
theorem onLine_decode :
    ∀ a d q : PrimeTwo.Point,
      PrimeTwo.onLine a d q =
        decide (decode q ∈ affineLine 2 (decode a) (decode d)) := by
  decide

/-- Convert a finite coordinate set to its Boolean membership function. -/
def subsetOf (S : Finset (Geometry.Point 2)) : PrimeTwo.Point → Bool :=
  fun q => decide (decode q ∈ S)

theorem subsetCardinality_filter :
    ∀ s : PrimeTwo.Point → Bool,
      PrimeTwo.subsetCardinality s =
        (Finset.univ.filter (fun q => s q = true)).card := by
  decide

theorem decoded_subsetOf (S : Finset (Geometry.Point 2)) :
    (Finset.univ.filter (fun q => subsetOf S q = true)).image decode = S := by
  ext x
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
    subsetOf, decide_eq_true_eq]
  constructor
  · rintro ⟨q, hq, hqx⟩
    exact hqx ▸ hq
  · intro hx
    exact ⟨encode x, by simpa using hx, decode_encode x⟩

theorem subsetOf_cardinality (S : Finset (Geometry.Point 2)) :
    PrimeTwo.subsetCardinality (subsetOf S) = S.card := by
  calc
    PrimeTwo.subsetCardinality (subsetOf S) =
        (Finset.univ.filter (fun q => subsetOf S q = true)).card :=
      subsetCardinality_filter _
    _ = ((Finset.univ.filter (fun q => subsetOf S q = true)).image decode).card :=
      (Finset.card_image_of_injective _ decode_injective).symm
    _ = S.card := congrArg Finset.card (decoded_subsetOf S)

theorem subsetOf_intersection (S : Finset (Geometry.Point 2))
    (n : PrimeTwo.Point) (b : PrimeTwo.Bit) :
    PrimeTwo.subsetIntersectionSize (subsetOf S) n b =
      (S.filter (fun x => pairing 2 (decode n) x = toScalar b)).card := by
  have hsubset :
      (fun q => subsetOf S q && PrimeTwo.onPlane n b q) =
        subsetOf (S.filter (fun x => pairing 2 (decode n) x = toScalar b)) := by
    funext q
    rw [onPlane_decode]
    by_cases hmem : decode q ∈ S <;>
      by_cases hplane : pairing 2 (decode n) (decode q) = toScalar b <;>
        simp [subsetOf, Finset.mem_filter, hmem, hplane]
  change PrimeTwo.subsetCardinality
    (fun q => subsetOf S q && PrimeTwo.onPlane n b q) = _
  rw [hsubset, subsetOf_cardinality]

theorem parallel_binary_lines_disjoint :
    ∀ d a b : PrimeTwo.Point,
      d ≠ 0 → b ≠ a → b ≠ PrimeTwo.add a d →
        Disjoint (affineLine 2 (decode a) (decode d))
          (affineLine 2 (decode b) (decode d)) := by
  decide

theorem binary_line_family_disjoint :
    ∀ d a b : PrimeTwo.Point,
      d ≠ 0 → b ≠ a → b ≠ PrimeTwo.add a d →
        Pairwise (fun i j : Fin 2 =>
          Disjoint
            (affineLine 2 (if i = 0 then decode a else decode b) (decode d))
            (affineLine 2 (if j = 0 then decode a else decode b) (decode d))) := by
  intro d a b hd hba hbad i j hij
  fin_cases i <;> fin_cases j
  · exact False.elim (hij rfl)
  · exact parallel_binary_lines_disjoint d a b hd hba hbad
  · exact (parallel_binary_lines_disjoint d a b hd hba hbad).symm
  · exact False.elim (hij rfl)

/-- The prime-two theorem in the common finite affine-space model. -/
theorem strongCylinderConjecture_two : StrongCylinderConjecture 2 := by
  intro S hcard hplanes
  have hcard' : PrimeTwo.subsetCardinality (subsetOf S) = 4 := by
    rw [subsetOf_cardinality, hcard]
    decide
  have hplanes' : ∀ n : PrimeTwo.Point, n ≠ 0 → ∀ b : PrimeTwo.Bit,
      PrimeTwo.subsetIntersectionSize (subsetOf S) n b % 2 = 0 := by
    intro n hn b
    rw [subsetOf_intersection]
    exact Nat.mod_eq_zero_of_dvd
      (hplanes (decode n) ((decode_ne_zero n).mpr hn) (toScalar b))
  obtain ⟨d, a, b, hd, hba, hbad, hmem⟩ :=
    PrimeTwo.cylinder_conjecture_predicate_prime_two (subsetOf S) hcard' hplanes'
  refine ⟨decode d, (decode_ne_zero d).mpr hd,
    (fun i : Fin 2 => if i = 0 then decode a else decode b),
    binary_line_family_disjoint d a b hd hba hbad, ?_⟩
  have hUnion :
      Finset.univ.biUnion (fun i : Fin 2 =>
        affineLine 2 (if i = 0 then decode a else decode b) (decode d)) =
      affineLine 2 (decode a) (decode d) ∪ affineLine 2 (decode b) (decode d) := by
    ext x
    simp [Finset.mem_biUnion, Fin.exists_fin_two]
  rw [hUnion]
  ext x
  rw [Finset.mem_union]
  have hbool : decide (x ∈ S) =
      (decide (x ∈ affineLine 2 (decode a) (decode d)) ||
        decide (x ∈ affineLine 2 (decode b) (decode d))) := by
    simpa only [subsetOf, onLine_decode, decode_encode] using hmem (encode x)
  have hiff : (decide (x ∈ S) = true) ↔
      ((decide (x ∈ affineLine 2 (decode a) (decode d)) ||
        decide (x ∈ affineLine 2 (decode b) (decode d))) = true) := by
    rw [hbool]
  simpa only [Bool.or_eq_true, decide_eq_true_eq] using hiff

#print axioms strongCylinderConjecture_two

end Cylinder.PrimeTwoGeometry
