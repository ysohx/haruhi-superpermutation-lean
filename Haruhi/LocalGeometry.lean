import PreimageChain.PortalCoordinates
import PreimageChain.MaximalRunCollision
import PreimageChain.ComponentPortalChains
import PreimageChain.GapCapacity

/-!
# Local geometry needed by the new order-fourteen argument

The principal theorem is about an actual exitless `Hunter.HPath 14`.
It excludes a full thirteen-block run followed by two twelve-block runs,
with weight-three seams. The six possible seam successors are exhausted
symbolically. No finite-search oracle or additional geometric hypothesis is used.
-/

namespace Haruhi

open Hunter PreimageChain
open scoped Classical BigOperators

set_option maxHeartbeats 1600000

private theorem rotClass_append_swap (P Q : List ℕ) :
    rotClass (P ++ Q) = rotClass (Q ++ P) := by
  calc
    rotClass (P ++ Q) = rotClass ((P ++ Q).rotate P.length) :=
      (Hunter.ProofsClosure3.rotClass_rotate (P ++ Q) P.length).symm
    _ = rotClass (Q ++ P) := by
      rw [Hunter.ProofsFill.rotate_append_left]

/-- Actual-path form of the full / deficit-one / deficit-one obstruction.
The final run may continue further; only its first twelve blocks are needed. -/
theorem full_unit_unit_impossible
    {p : HPath 14} (hp : p.Exitless) {s : ℕ}
    (hfull : FullIntervalPiece p s)
    (hseam₁ : Hunter.ProofsLedger.bw p (s + 13) = 3)
    (hunit₁ : ∀ i, 1 ≤ i → i ≤ 11 →
      Hunter.ProofsLedger.IsDoor p (s + 13 + i))
    (hseam₂ : Hunter.ProofsLedger.bw p (s + 25) = 3)
    (hunit₂ : ∀ i, 1 ≤ i → i ≤ 11 →
      Hunter.ProofsLedger.IsDoor p (s + 25 + i))
    (hrange : 14 * (s + 36) < p.numVerts) : False := by
  have range : ∀ i, i ≤ s + 36 → 14 * i < p.numVerts := by
    intro i hi
    omega
  have collide : ∀ i j, i ≤ s + 36 → j ≤ s + 36 → i ≠ j →
      rotClass (Hunter.ProofsChartEq.blockWord p i) =
        rotClass (Hunter.ProofsChartEq.blockWord p j) → False := by
    intro i j hi hj hij heq
    exact (Hunter.ProofsChartEq.blockWord_distinct (by decide : 1 ≤ 14)
      hp (range i hi) (range j hj) hij) heq
  have hsource : Hunter.ProofsLedger.IsComplete p (s + 13 - 1) := by
    have h := fullIntervalPiece_complete (by decide : 3 ≤ 14) hp hfull
    convert h using 1; omega
  have hunit : UnitDeficitDoorSegment p (s + 13) := by
    refine ⟨?_, ?_⟩
    · simpa [Nat.add_assoc] using range (s + 25) (by omega)
    · intro i hi hi'
      exact hunit₁ i hi (by simpa using hi')
  have halpha : Hunter.ProofsLedger.IsAlpha p (s + 13) :=
    weightThree_complete_to_unitDeficit_isAlpha (by decide : 4 ≤ 14) hp
      (by omega) hunit hseam₁ hsource
  have hlen : (Hunter.ProofsChartEq.blockWord p s).length = 14 :=
    (Hunter.ProofsChartEq.blockWord_isPermWord p s).length
  obtain ⟨V, d, b, c, hV, hroot⟩ :=
    exists_split_last_three (Hunter.ProofsChartEq.blockWord p s) (by omega)
  let A := V ++ [d]
  have hA : A.length = 12 := by
    simp only [A, List.length_append, List.length_singleton]
    omega
  obtain ⟨a, R, hAR⟩ : ∃ a R, A = a :: R := by
    cases h : A with
    | nil => simp [h] at hA
    | cons a R => exact ⟨a, R, rfl⟩
  have hR : R.length = 11 := by rw [hAR] at hA; simp at hA; omega
  have hstart : Hunter.ProofsChartEq.blockWord p s = (a :: R) ++ [b, c] := by
    rw [hroot]
    simpa [A, List.append_assoc] using congrArg (fun L => L ++ [b, c]) hAR
  have hnext := fullPiece_alpha_next_start (by decide : 3 ≤ 14) hp
    (A := a :: R) (by simp [hR]) (range (s + 13) (by omega))
    hfull.doors hstart halpha
  have hunitWord : Hunter.ProofsChartEq.blockWord p (s + 13) =
      R ++ [a, b, c] := by
    simpa [List.rotate_cons_succ, List.append_assoc] using hnext
  have hsecondRaw := fullPiece_block_word (by decide : 3 ≤ 14) hp
    (A := a :: R) (by simp [hR]) (l := 1) (by decide)
    hfull.inRange hfull.doors hstart
  have hsecond : Hunter.ProofsChartEq.blockWord p (s + 1) =
      R ++ [b, a, c] := by
    simpa [List.rotate_cons_succ, List.append_assoc] using hsecondRaw
  have hlastRaw := fullPiece_block_word (by decide : 3 ≤ 14) hp
    (A := a :: R) (by simp [hR]) (l := 12) (by decide)
    hfull.inRange hfull.doors hstart
  have hlast : Hunter.ProofsChartEq.blockWord p (s + 12) =
      (b :: a :: R) ++ [c] := by
    rw [show (12 : ℕ) = (a :: R).length by simp [hR],
      List.rotate_append_length_eq] at hlastRaw
    simpa [hR] using hlastRaw
  have hunitStart : Hunter.ProofsChartEq.blockWord p (s + 13) =
      (R ++ [a, b]) ++ [c] := by simpa [List.append_assoc] using hunitWord
  have hunitLastRaw := doorSegment_block_word (by decide : 2 ≤ 14) hp
    (start := s + 13) (r := 11) (l := 11) (by decide)
    (range (s + 13 + 11) (by omega)) hunit₁ hunitStart
  have hunitLast : Hunter.ProofsChartEq.blockWord p (s + 24) =
      (a :: b :: R) ++ [c] := by
    rw [show (11 : ℕ) = R.length by omega,
      List.rotate_append_length_eq] at hunitLastRaw
    simpa [Nat.add_assoc, hR] using hunitLastRaw
  have hheadRaw := blockBoundarySource_eq_bexit (by decide : 1 ≤ 14) hp
    (t := s + 25) (by omega) (range (s + 25) (by omega))
  have hhead : (p.vert (14 * (s + 25) - 1) : List ℕ) =
      c :: a :: b :: R := by
    rw [show s + 25 - 1 = s + 24 by omega, hunitLast] at hheadRaw
    unfold Hunter.ProofsRigidity2.bexit at hheadRaw
    rw [show (14 - 1 : ℕ) = (a :: b :: R).length by simp [hR],
      List.rotate_append_length_eq] at hheadRaw
    simpa using hheadRaw
  obtain ⟨o, htarget⟩ := weightThreeTarget_normalizes_from_head
    (by decide : 4 ≤ 14) (p := p) (V := R) (m := c) (a := a) (c := b)
    (by simpa using hR) hhead hseam₂
  cases o with
  | mab =>
      have ht : Hunter.ProofsChartEq.blockWord p (s + 25) = R ++ [c, a, b] := by
        simpa [orientedSuccessorStartWord] using htarget
      apply collide (s + 25) (s + 24) (by omega) (by omega) (by omega)
      rw [ht, hunitLast]
      simpa [List.append_assoc] using rotClass_append_swap (R ++ [c]) [a, b]
  | mba =>
      have ht : Hunter.ProofsChartEq.blockWord p (s + 25) = R ++ [c, b, a] := by
        simpa [orientedSuccessorStartWord] using htarget
      apply collide (s + 25) (s + 12) (by omega) (by omega) (by omega)
      rw [ht, hlast]
      simpa [List.append_assoc] using rotClass_append_swap (R ++ [c]) [b, a]
  | abm =>
      have ht : Hunter.ProofsChartEq.blockWord p (s + 25) = R ++ [a, b, c] := by
        simpa [orientedSuccessorStartWord] using htarget
      apply collide (s + 25) (s + 13) (by omega) (by omega) (by omega)
      rw [ht, hunitWord]
  | amb =>
      have ht : Hunter.ProofsChartEq.blockWord p (s + 25) =
          (R ++ [a, c]) ++ [b] := by
        simpa [orientedSuccessorStartWord, List.append_assoc] using htarget
      have hfinalRaw := doorSegment_block_word (by decide : 2 ≤ 14) hp
        (start := s + 25) (r := 11) (l := 11) (by decide)
        (range (s + 25 + 11) (by omega)) hunit₂ ht
      rw [show (11 : ℕ) = R.length by omega,
        List.rotate_append_length_eq] at hfinalRaw
      have hfinal : Hunter.ProofsChartEq.blockWord p (s + 36) =
          (a :: c :: R) ++ [b] := by
        simpa [Nat.add_assoc, hR] using hfinalRaw
      apply collide (s + 1) (s + 36) (by omega) (by omega) (by omega)
      rw [hsecond, hfinal]
      simpa [List.append_assoc] using rotClass_append_swap (R ++ [b]) [a, c]
  | bma =>
      have ht : Hunter.ProofsChartEq.blockWord p (s + 25) = R ++ [b, c, a] := by
        simpa [orientedSuccessorStartWord] using htarget
      apply collide (s + 25) s (by omega) (by omega) (by omega)
      rw [ht, hstart]
      simpa [List.append_assoc] using rotClass_append_swap (R ++ [b, c]) [a]
  | bam =>
      have ht : Hunter.ProofsChartEq.blockWord p (s + 25) = R ++ [b, a, c] := by
        simpa [orientedSuccessorStartWord] using htarget
      apply collide (s + 25) (s + 1) (by omega) (by omega) (by omega)
      rw [ht, hsecond]

/-- A full actual interval piece followed by a deficit-one actual piece forces
any next actual piece across two exact-three seams to have deficit at least two. -/
theorem actual_full_unit_next_deficit_ge_two
    {p : HPath 14} (hp : p.StronglyExitless)
    {s t u v : ℕ}
    (hleft : ActualIntervalPieceSpan p s t)
    (hmiddle : ActualIntervalPieceSpan p t u)
    (hright : ActualIntervalPieceSpan p u v)
    (hleftFull : actualPieceDeficit 14 s t = 0)
    (hmiddleUnit : actualPieceDeficit 14 t u = 1)
    (hseam₁ : Hunter.ProofsLedger.bw p t = 3)
    (hseam₂ : Hunter.ProofsLedger.bw p u = 3) :
    2 ≤ actualPieceDeficit 14 u v := by
  by_contra hdef
  have hl := actualIntervalPieceSpan_size_add_deficit
    (by decide : 4 ≤ 14) hp hleft
  have hm := actualIntervalPieceSpan_size_add_deficit
    (by decide : 4 ≤ 14) hp hmiddle
  have hr := actualIntervalPieceSpan_size_add_deficit
    (by decide : 4 ≤ 14) hp hright
  simp only [actualPieceSize] at hl hm hr
  rw [hleftFull] at hl
  rw [hmiddleUnit] at hm
  have ht : t = s + 13 := by omega
  have hu : u = s + 25 := by omega
  have hv : s + 37 ≤ v := by omega
  have hfull := fullIntervalPiece_of_actual_deficit_zero
    (by decide : 4 ≤ 14) hp hleft hleftFull
  have hrange := actualIntervalPieceSpan_last_inRange
    (by decide : 1 ≤ 14) hp hright
  apply full_unit_unit_impossible hp.1 hfull
  · simpa [ht] using hseam₁
  · intro i hi1 hi2
    have hd := hmiddle.doors i hi1 (by omega)
    simpa [ht] using hd
  · simpa [hu] using hseam₂
  · intro i hi1 hi2
    have hd := hright.doors i hi1 (by omega)
    simpa [hu] using hd
  · omega

/-! The following finite-sum lemma is deliberately stated with its local
combinatorial hypotheses explicit. Its path instantiation uses the actual
interval-piece theorem above; it is not itself a path-capacity assertion. -/

private theorem sum_range_start (f : ℕ → ℕ) (n : ℕ) :
    (∑ i ∈ Finset.range (n + 1), f i) =
      f 0 + ∑ i ∈ Finset.range n, f (i + 1) := by
  rw [Finset.sum_range_succ']
  omega

/-- The number of positive full-run gaps is at most the number of partial
pieces of deficit at least two, plus one. -/
theorem gap_run_count_le_large_add_one
    (m : ℕ) (gap deficit : ℕ → ℕ)
    (hpositive : ∀ j < m, 1 ≤ deficit j)
    (hunit : ∀ j < m, deficit j = 1 → 0 < gap j → gap (j + 1) = 0)
    (hnext : ∀ j, j + 1 < m → deficit j = 1 → 0 < gap j →
      2 ≤ deficit (j + 1)) :
    (∑ i ∈ Finset.range (m + 1), positiveIndicator (gap i)) ≤
      (∑ j ∈ Finset.range m, largeIndicator (deficit j)) + 1 := by
  induction m using Nat.strong_induction_on generalizing gap deficit with
  | h m ih =>
      cases m with
      | zero =>
          simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
          unfold positiveIndicator
          split <;> omega
      | succ m =>
          have ih₁ := ih m (by omega)
            (fun j => gap (j + 1)) (fun j => deficit (j + 1))
            (by intro j hj; exact hpositive (j + 1) (by omega))
            (by intro j hj hu hg; exact hunit (j + 1) (by omega) hu hg)
            (by intro j hj hu hg; exact hnext (j + 1) (by omega) hu hg)
          by_cases hg : gap 0 = 0
          · have hzero : positiveIndicator (gap 0) = 0 := by simp [positiveIndicator, hg]
            rw [sum_range_start (fun i => positiveIndicator (gap i)) (m + 1),
              sum_range_start (fun i => largeIndicator (deficit i)) m]
            simp only [hzero, zero_add]
            omega
          · have hgpos : 0 < gap 0 := by omega
            have hone : positiveIndicator (gap 0) = 1 := by simp [positiveIndicator, hgpos]
            by_cases hd : 2 ≤ deficit 0
            · have hlarge : largeIndicator (deficit 0) = 1 := by simp [largeIndicator, hd]
              rw [sum_range_start (fun i => positiveIndicator (gap i)) (m + 1),
                sum_range_start (fun i => largeIndicator (deficit i)) m]
              simp only [hone, hlarge]
              omega
            · have hdpos := hpositive 0 (by omega)
              have hdunit : deficit 0 = 1 := by omega
              have hg₁ : gap 1 = 0 := by simpa using hunit 0 (by omega) hdunit hgpos
              cases m with
              | zero =>
                  simp only [Finset.sum_range_succ, Finset.sum_range_zero,
                    Nat.zero_add]
                  simp [positiveIndicator, largeIndicator, hgpos, hg₁, hdunit]
              | succ r =>
                  have hd₁ : 2 ≤ deficit 1 := by
                    simpa using hnext 0 (by omega) hdunit hgpos
                  have ih₂ := ih r (by omega)
                    (fun j => gap (j + 2)) (fun j => deficit (j + 2))
                    (by intro j hj; exact hpositive (j + 2) (by omega))
                    (by
                      intro j hj hu hg
                      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
                        hunit (j + 2) (by omega) hu hg)
                    (by
                      intro j hj hu hg
                      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
                        hnext (j + 2) (by omega) hu hg)
                  have hzero : positiveIndicator (gap 1) = 0 := by
                    simp [positiveIndicator, hg₁]
                  have hlarge₀ : largeIndicator (deficit 0) = 0 := by
                    simp [largeIndicator, hdunit]
                  have hlarge₁ : largeIndicator (deficit 1) = 1 := by
                    simp [largeIndicator, hd₁]
                  rw [sum_range_start (fun i => positiveIndicator (gap i)) (r + 2),
                    sum_range_start (fun i => largeIndicator (deficit i)) (r + 1),
                    sum_range_start (fun i => positiveIndicator (gap (i + 1))) (r + 1),
                    sum_range_start (fun i => largeIndicator (deficit (i + 1))) r]
                  simp only [hone, hzero, hlarge₀, hlarge₁, Nat.add_assoc,
                    Nat.zero_add, show (1 + 1 : ℕ) = 2 by decide]
                  omega

end Haruhi
