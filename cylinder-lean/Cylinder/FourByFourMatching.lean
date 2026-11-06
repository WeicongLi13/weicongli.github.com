module

public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.Card

/-! The missing entries in an actual four-by-four matching are forced
by injectivity. This lemma does not assume a cyclic group table. -/

@[expose] public section
noncomputable section
open scoped Classical

namespace Cylinder.FourByFourMatching

theorem unique_fourth {I : Type*} (F : Finset I) (hF : F.card = 4)
    (A B C X Y : I) (hA : A ∈ F) (hB : B ∈ F) (hC : C ∈ F)
    (hAB : A ≠ B) (hAC : A ≠ C) (hBC : B ≠ C)
    (hX : X ∈ F) (hXA : X ≠ A) (hXB : X ≠ B) (hXC : X ≠ C)
    (hY : Y ∈ F) (hYA : Y ≠ A) (hYB : Y ≠ B) (hYC : Y ≠ C) : X = Y := by
  have hB' : B ∈ F.erase A := Finset.mem_erase.mpr ⟨hAB.symm, hB⟩
  have hC' : C ∈ (F.erase A).erase B :=
    Finset.mem_erase.mpr ⟨hBC.symm, Finset.mem_erase.mpr ⟨hAC.symm, hC⟩⟩
  have hc : (((F.erase A).erase B).erase C).card ≤ 1 := by
    rw [Finset.card_erase_of_mem hC', Finset.card_erase_of_mem hB', Finset.card_erase_of_mem hA, hF]
  apply Finset.card_le_one.mp hc
  · exact Finset.mem_erase.mpr ⟨hXC, Finset.mem_erase.mpr ⟨hXB, Finset.mem_erase.mpr ⟨hXA, hX⟩⟩⟩
  · exact Finset.mem_erase.mpr ⟨hYC, Finset.mem_erase.mpr ⟨hYB, Finset.mem_erase.mpr ⟨hYA, hY⟩⟩⟩

theorem forced_entries {I : Type*} (F G : Finset I) (hF : F.card = 4) (hG : G.card = 4)
    (M : Fin 4 → I → I) (hinv : ∀ k, Function.Involutive (M k))
    (hsep : ∀ k l, k ≠ l → ∀ P, M k P ≠ M l P)
    (hFG : ∀ k P, P ∈ F → M k P ∈ G) (hGF : ∀ k P, P ∈ G → M k P ∈ F)
    (P J Q N : I) (hP : P ∈ F) (hJ : J ∈ F) (hQ : Q ∈ G) (hN : N ∈ G)
    (hPJ : P ≠ J) (hQN : Q ≠ N)
    (h0P : M 0 P = Q) (h0J : M 0 J = N) (h1P : M 1 P = N) (h2J : M 2 J = Q) :
    M 2 (M 1 Q) = M 1 J ∧ M 3 P = M 1 J ∧ M 3 N = M 1 Q := by
  let X := M 1 Q
  let Y := M 1 J
  have hX : X ∈ F := hGF 1 Q hQ
  have hY : Y ∈ G := hFG 1 J hJ
  have h0Q : M 0 Q = P := by rw [← h0P, hinv 0]
  have h0N : M 0 N = J := by rw [← h0J, hinv 0]
  have h1N : M 1 N = P := by rw [← h1P, hinv 1]
  have h2Q : M 2 Q = J := by rw [← h2J, hinv 2]
  have h1X : M 1 X = Q := hinv 1 Q
  have hXP : X ≠ P := by
    intro h
    exact hQN (h1X.symm.trans ((congrArg (M 1) h).trans h1P))
  have hXJ : X ≠ J := by
    intro h
    apply hsep 1 2 (by decide) J
    exact (congrArg (M 1) h.symm).trans (h1X.trans h2J.symm)
  have hYQ : Y ≠ Q := by
    change M 1 J ≠ Q
    rw [← h2J]
    exact hsep 1 2 (by decide) J
  have hYN : Y ≠ N := by
    intro h
    apply hPJ
    exact (hinv 1).injective (h1P.trans h.symm)
  have h2PY : M 2 P ≠ Y := by
    intro h
    have h3P := hFG 3 P hP
    have h3J := hFG 3 J hJ
    have he := unique_fourth G hG Q N Y (M 3 P) (M 3 J) hQ hN hY hQN hYQ.symm hYN.symm
      h3P (by simpa only [← h0P] using hsep 3 0 (by decide) P)
      (by simpa only [← h1P] using hsep 3 1 (by decide) P)
      (by simpa only [← h] using hsep 3 2 (by decide) P)
      h3J (by simpa only [← h2J] using hsep 3 2 (by decide) J)
      (by simpa only [← h0J] using hsep 3 0 (by decide) J)
      (hsep 3 1 (by decide) J)
    exact hPJ ((hinv 3).injective he)
  have h2XN : M 2 X ≠ N := by
    intro h
    have h2N : M 2 N = X := by rw [← h, hinv 2]
    have he := unique_fourth F hF P J X (M 3 Q) (M 3 N) hP hJ hX hPJ hXP.symm hXJ.symm
      (hGF 3 Q hQ)
      (by simpa only [← h0Q] using hsep 3 0 (by decide) Q)
      (by simpa only [← h2Q] using hsep 3 2 (by decide) Q)
      (hsep 3 1 (by decide) Q)
      (hGF 3 N hN)
      (by simpa only [← h1N] using hsep 3 1 (by decide) N)
      (by simpa only [← h0N] using hsep 3 0 (by decide) N)
      (by simpa only [← h2N] using hsep 3 2 (by decide) N)
    exact hQN ((hinv 3).injective he)
  have h2PQ : M 2 P ≠ Q := by
    rw [← h0P]
    exact hsep 2 0 (by decide) P
  have h2PN : M 2 P ≠ N := by
    rw [← h1P]
    exact hsep 2 1 (by decide) P
  have hCX : M 2 X = Y := unique_fourth G hG Q N (M 2 P) (M 2 X) Y
    hQ hN (hFG 2 P hP) hQN h2PQ.symm h2PN.symm (hFG 2 X hX)
    (by rw [← h1X]; exact hsep 2 1 (by decide) X) h2XN
    (fun h => hXP ((hinv 2).injective h)) hY hYQ hYN h2PY.symm
  have hDP : M 3 P = Y := unique_fourth G hG Q N (M 2 P) (M 3 P) Y
    hQ hN (hFG 2 P hP) hQN h2PQ.symm h2PN.symm (hFG 3 P hP)
    (by rw [← h0P]; exact hsep 3 0 (by decide) P)
    (by rw [← h1P]; exact hsep 3 1 (by decide) P)
    (hsep 3 2 (by decide) P) hY hYQ hYN h2PY.symm
  have h2NP : M 2 N ≠ P := by
    intro h
    apply h2PN
    exact ((hinv 2).injective (h.trans (hinv 2 P).symm)).symm
  have h2NJ : M 2 N ≠ J := by
    intro h
    apply hQN
    exact h2J.symm.trans ((congrArg (M 2) h).symm.trans (hinv 2 N))
  have h2NX : M 2 N ≠ X := by
    intro h
    exact h2XN (((hinv 2).injective (h.trans (hinv 2 X).symm)).symm)
  have hDN : M 3 N = X := unique_fourth F hF P J (M 2 N) (M 3 N) X
    hP hJ (hGF 2 N hN) hPJ h2NP.symm h2NJ.symm (hGF 3 N hN)
    (by rw [← h1N]; exact hsep 3 1 (by decide) N)
    (by rw [← h0N]; exact hsep 3 0 (by decide) N)
    (hsep 3 2 (by decide) N) hX hXP hXJ h2NX.symm
  exact ⟨hCX, hDP, hDN⟩

end Cylinder.FourByFourMatching

end
