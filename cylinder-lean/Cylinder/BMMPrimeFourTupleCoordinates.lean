module

public import Cylinder.BMMFourTupleCoordinates
public import Cylinder.BMMBlackLineCapFour

/-! The prime-field four-tuple coordinates now use the proved black
line bound internally. No black-line cap is supplied as a hypothesis. -/

@[expose] public section
noncomputable section

namespace Cylinder.BMMPrimeFourTupleCoordinates

open Cylinder.BMMBlackLineBlocks Cylinder.BMMSpecialFourTuple
open Cylinder.BMMFourTupleBlackGeometry Cylinder.BMMFourTupleFrame
open Cylinder.BMMFourTupleCoordinates Cylinder.BMMBlackLineCapFour

variable (p : ℕ) [Fact p.Prime]

def primeBlackFrame (hp : 3 ≤ p) (A : NormalizedSystem (ZMod p)) {R : A.B}
    (T : FourTuple (configuration A) A.E R) : (Fin 3 → ZMod p) ≃ₗ[ZMod p] (Fin 3 → ZMod p) :=
  blackFrame A T (normalized_black_line_cap_four p hp A)

theorem prime_black_lines_distinct (hp : 3 ≤ p) (A : NormalizedSystem (ZMod p)) {R : A.B}
    (T : FourTuple (configuration A) A.E R) : firstLine A T ≠ secondLine A T :=
  black_lines_distinct_of_cap_four A T (normalized_black_line_cap_four p hp A)

theorem prime_basis_determinant_nonzero (hp : 3 ≤ p) (A : NormalizedSystem (ZMod p)) {R : A.B}
    (T : FourTuple (configuration A) A.E R) :
    Cylinder.BMMTriangleFrame.determinant (basisVectors A T) ≠ 0 :=
  basis_determinant_nonzero A T (normalized_black_line_cap_four p hp A)

theorem actual_prime_four_white_coordinates (hp : 3 ≤ p) (A : NormalizedSystem (ZMod p)) {R : A.B}
    (T : FourTuple (configuration A) A.E R) :
    ∃ a c : ZMod p, a ≠ 0 ∧ c ≠ 0 ∧ c - 2 * a ≠ 0 ∧ c - a ≠ 0 ∧
      primeBlackFrame p hp A T (A.E T.P) = ![a, a, c] ∧
      primeBlackFrame p hp A T (A.E T.Q) = ![-a, -a, c - 2 * a] ∧
      primeBlackFrame p hp A T (A.E T.U) = ![a, -a, -c] ∧
      primeBlackFrame p hp A T (A.E T.V) = ![-a, a, -c] :=
  actual_four_white_coordinates A T (normalized_black_line_cap_four p hp A)
    (Cylinder.BMMFinitePlaneArcBound.prime_two_nonzero p hp)

end Cylinder.BMMPrimeFourTupleCoordinates

end
