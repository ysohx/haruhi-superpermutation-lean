import Haruhi.LocalGeometry
import PreimageChain.ActualChainCapacity
import Haruhi.Capacity

/-!
# The actual-path bridge to the additional full-chain count constraint

This file derives the additional gap-profile inequality from actual adjacent
interval pieces. The list argument ensures that the witness used in the count
is the next actual partial piece, rather than an assumed abstract witness.
-/

namespace Haruhi

open Hunter PreimageChain
open scoped Classical BigOperators

set_option maxHeartbeats 1600000

/-- Consecutive partial entries are adjacent in the source list whenever the
full gap between them is empty. -/
theorem betweenPartials_of_empty_gap
    {α : Type} {R : α → α → Prop}
    (gaps : List (List α)) (partials : List α)
    (hlen : gaps.length = partials.length + 1)
    (hadj : AdjacentList R (interleavePieceGaps gaps partials)) :
    ∀ i, (hi : i + 1 < partials.length) → gaps[i + 1] = [] →
      R partials[i] partials[i + 1] := by
  induction partials generalizing gaps with
  | nil => intro i hi; simp at hi
  | cons part partials ih =>
      cases gaps with
      | nil => simp at hlen
      | cons gap gaps =>
          have htailLength : gaps.length = partials.length + 1 := by
            simp at hlen
            omega
          intro i hi hgap
          cases i with
          | zero =>
              cases partials with
              | nil => simp at hi
              | cons next partials =>
                  cases gaps with
                  | nil => simp at htailLength
                  | cons between gaps =>
                      have hbetween : between = [] := by simpa using hgap
                      have hdrop := hadj.drop gap.length
                      simp only [interleavePieceGaps, List.drop_left] at hdrop
                      rw [hbetween] at hdrop
                      simpa [interleavePieceGaps, AdjacentList, Adjacent] using hdrop.1
          | succ i =>
              have htailAdj : AdjacentList R
                  (interleavePieceGaps gaps partials) := by
                have hdropped := hadj.drop (gap.length + 1)
                simpa [interleavePieceGaps] using hdropped
              have hi' : i + 1 < partials.length := by simpa using hi
              simpa only [List.getElem_cons_succ, Nat.succ_eq_add_one,
                Nat.add_assoc] using ih gaps htailLength htailAdj i hi' hgap

private theorem gapLength_at {p : HPath 14}
    (gaps : List (List (ComponentIntervalPiece p)))
    (i : ℕ) (hi : i < gaps.length) :
    natListAt 0 (gapLengths gaps) i = gaps[i].length := by
  simp [natListAt, gapLengths, List.getElem?_eq_getElem hi]

private theorem partialDeficit_at {p : HPath 14}
    (partials : List (ComponentIntervalPiece p))
    (i : ℕ) (hi : i < partials.length) :
    natListAt 1 (partialDeficits partials) i = partials[i].deficit := by
  simp [natListAt, partialDeficits, List.getElem?_eq_getElem hi]

/-- The new local inequality applied to the canonical partition of an actual
exact-three piece chain. -/
theorem partition_unit_following_positive_gap_next_large
    {p : HPath 14} (hp : p.StronglyExitless)
    {chain : ExactWeightThreePieceChain p}
    {gaps : List (List (ComponentIntervalPiece p))}
    {partials : List (ComponentIntervalPiece p)}
    (partition : ExactPieceGapPartition chain.pieces gaps partials)
    (geometry : ExactPieceGapGeometry gaps partials)
    (j : ℕ) (hj : j + 1 < partials.length)
    (hunit : natListAt 1 (partialDeficits partials) j = 1)
    (hgap : 0 < natListAt 0 (gapLengths gaps) j) :
    2 ≤ natListAt 1 (partialDeficits partials) (j + 1) := by
  have hj0 : j < partials.length := by omega
  have hjGap : j < gaps.length := by rw [partition.gaps_length]; omega
  have hjNextGap : j + 1 < gaps.length := by rw [partition.gaps_length]; omega
  have hne : gaps[j] ≠ [] := by
    rw [gapLength_at gaps j hjGap] at hgap
    exact List.length_pos_iff.mp hgap
  have hnextGap : gaps[j + 1] = [] := by
    have hside := geometry.unitOneSided j hj0 hunit
    have hpos : positiveIndicator (natListAt 0 (gapLengths gaps) j) = 1 := by
      simp [positiveIndicator, hgap]
    rw [hpos, gapLength_at gaps (j + 1) hjNextGap] at hside
    have hz : (gaps[j + 1]).length = 0 := by
      unfold positiveIndicator at hside
      split at hside <;> omega
    exact List.length_eq_zero_iff.mp hz
  have hadj : AdjacentList PieceExactJoin
      (interleavePieceGaps gaps partials) := by
    rw [partition.interleave_eq]
    exact exactWeightThreeChain_adjacent chain
  have hleft := rightBoundary_of_interleave gaps partials
    partition.gaps_length hadj j hj0 hne
  have hright := betweenPartials_of_empty_gap gaps partials
    partition.gaps_length hadj j hj hnextGap
  have hfull : (gaps[j].getLast hne).deficit = 0 :=
    partition.gaps_all_full gaps[j] (List.getElem_mem hjGap)
      (gaps[j].getLast hne) (List.getLast_mem hne)
  rw [partialDeficit_at partials j hj0] at hunit
  rw [partialDeficit_at partials (j + 1) hj]
  apply actual_full_unit_next_deficit_ge_two hp
    (s := (gaps[j].getLast hne).start)
    (t := partials[j].start) (u := partials[j + 1].start)
  · simpa only [← hleft.1] using (gaps[j].getLast hne).valid
  · simpa only [← hright.1] using partials[j].valid
  · exact partials[j + 1].valid
  · simpa only [ComponentIntervalPiece.deficit, ← hleft.1] using hfull
  · simpa only [ComponentIntervalPiece.deficit, ← hright.1] using hunit
  · exact hleft.2
  · exact hright.2

/-- Every actual canonical gap profile obeys the new full-chain count bound.
The supplied geometry is already constructed unconditionally by the upstream
actual-chain API; the new constraint follows from the path collision lemma. -/
theorem partition_full_run_count_le_excess_add_one
    {p : HPath 14} (hp : p.StronglyExitless)
    {chain : ExactWeightThreePieceChain p}
    {gaps : List (List (ComponentIntervalPiece p))}
    {partials : List (ComponentIntervalPiece p)}
    (partition : ExactPieceGapPartition chain.pieces gaps partials)
    (geometry : ExactPieceGapGeometry gaps partials) :
    (∑ i ∈ Finset.range (partials.length + 1),
      positiveIndicator (natListAt 0 (gapLengths gaps) i)) ≤
      (∑ j ∈ Finset.range partials.length,
        deficitExcess (natListAt 1 (partialDeficits partials)) j) + 1 := by
  let profile := partition.toLocalProfile geometry
  have hcount := gap_run_count_le_large_add_one partials.length
    (natListAt 0 (gapLengths gaps)) (natListAt 1 (partialDeficits partials))
    profile.deficitPositive
    (by
      intro j hj hu hg
      have hside := geometry.unitOneSided j hj hu
      have hpos : positiveIndicator (natListAt 0 (gapLengths gaps) j) = 1 := by
        simp [positiveIndicator, hg]
      rw [hpos] at hside
      unfold positiveIndicator at hside
      split at hside <;> omega)
    (partition_unit_following_positive_gap_next_large hp partition geometry)
  have hlarge :
      (∑ j ∈ Finset.range partials.length,
        largeIndicator (natListAt 1 (partialDeficits partials) j)) ≤
      (∑ j ∈ Finset.range partials.length,
        deficitExcess (natListAt 1 (partialDeficits partials)) j) := by
    apply Finset.sum_le_sum
    intro j hj
    unfold largeIndicator deficitExcess
    split <;> omega
  omega

/-- A strengthened capacity package whose extra inequality is proved for the
actual path, rather than supplied as a premise. -/
structure StrongActualChainCapacityPackage
    {p : HPath 14} (chain : ExactWeightThreePieceChain p) where
  certificate : ExactWeightThreeChainRunCertificate chain
  endpoint_eq : certificate.endpointFullCount =
    chainFirstFullBit chain + chainLastFullBit chain
  full_runs_le_excess : certificate.fullRunCount ≤
    exactChainTotalDeficit chain -
      (exactChainUnitCount chain + exactChainLargeCount chain) + 1

/-- Unconditional construction of the strengthened actual-chain package. -/
noncomputable def strongActualChainCapacityPackage
    {p : HPath 14} (hp : p.StronglyExitless)
    (chain : ExactWeightThreePieceChain p) :
    StrongActualChainCapacityPackage chain := by
  classical
  let hexists := ExactPieceGapPartition.exists_for chain.pieces
  let gaps := Classical.choose hexists
  let hpartials := Classical.choose_spec hexists
  let partials := Classical.choose hpartials
  let partition : ExactPieceGapPartition chain.pieces gaps partials :=
    Classical.choose_spec hpartials
  let witness : ExactPieceGapRunWitness partition :=
    partition.toRunWitness (by decide : 4 ≤ 14) hp
      (leading_gap_length_le (by decide : 5 ≤ 14) hp partition)
  let geometry : ExactPieceGapGeometry gaps partials :=
    witness.toGeometry (by decide : 5 ≤ 14) hp
  let profile : ExactWeightThreeChainLocalProfile chain :=
    partition.toLocalProfile geometry
  refine ⟨profile.toRunCertificate (by decide),
    partition_endpointFullCount_eq (by decide) hp partition, ?_⟩
  have hcount := partition_full_run_count_le_excess_add_one hp partition geometry
  have hpcount : profile.partialCount =
      exactChainUnitCount chain + exactChainLargeCount chain := by
    have hparts := exactChain_pieceCount_eq_full_add_partial chain
    have hpc := profile.pieceCount
    have hfc := profile.fullCount
    omega
  have hexcess := sum_deficitExcess profile.partialCount profile.deficit
    profile.deficitPositive
  rw [← profile.totalDeficit, hpcount] at hexcess
  change (∑ i ∈ Finset.range (partials.length + 1),
    positiveIndicator (natListAt 0 (gapLengths gaps) i)) ≤ _
  rw [hexcess, ← hpcount]
  exact hcount

/-- Capacity for any actual exact-three chain with its actual endpoint
allowance. All geometry and finite-count hypotheses are discharged. -/
theorem actual_light_chain_capacity
    {p : HPath 14} (hp : p.StronglyExitless)
    (chain : ExactWeightThreePieceChain p)
    (c : ℤ)
    (hendpoints : (chainFirstFullBit chain + chainLastFullBit chain : ℤ) ≤ c)
    (hc : c ≤ 2) :
    let ρ : ℤ := 6 * ((exactChainTotalDeficit chain : ℤ) + c) -
      exactChainPieceCount chain
    0 ≤ ρ ∧
      9 * (pieceListTotalSize chain.pieces : ℤ) ≤ 1577 * ρ + 1404 := by
  let package := strongActualChainCapacityPackage hp chain
  let cert := package.certificate
  have hpartial := exactChain_partialCount_le_totalDeficit chain
  have hunit := exactChain_unit_add_two_large_le_totalDeficit chain
  have hinc : 2 * cert.fullRunCount ≤
      exactChainTotalDeficit chain + cert.endpointFullCount := by
    have h := cert.oneSided
    omega
  have hfull := cert.fullBound
  have hlong := cert.longBound
  have hchain := package.full_runs_le_excess
  have hr := exactChain_pieceCount_eq_full_add_partial chain
  have hb := pieceListTotalSize_add_deficit (by decide : 4 ≤ 14) hp chain.pieces
  have he : (cert.endpointFullCount : ℤ) ≤ c := by
    change (package.certificate.endpointFullCount : ℤ) ≤ c
    rw [package.endpoint_eq]
    exact_mod_cast hendpoints
  have hEcast :
      ((exactChainTotalDeficit chain -
        (exactChainUnitCount chain + exactChainLargeCount chain) : ℕ) : ℤ) =
      (exactChainTotalDeficit chain : ℤ) -
        (exactChainUnitCount chain + exactChainLargeCount chain : ℕ) := by
    exact Nat.cast_sub hpartial
  apply local_capacity_int
    (K := cert.fullRunCount) (F := exactChainFullCount chain)
    (p := (exactChainUnitCount chain + exactChainLargeCount chain : ℕ))
    (Δ := exactChainTotalDeficit chain)
    (E := (exactChainTotalDeficit chain -
      (exactChainUnitCount chain + exactChainLargeCount chain) : ℕ))
    (N := cert.longInternalRunCount) (e := cert.endpointFullCount)
    (R := exactChainPieceCount chain)
  · exact hEcast
  · exact_mod_cast hr
  · exact_mod_cast hinc
  · exact_mod_cast hfull
  · exact_mod_cast hlong
  · exact_mod_cast hchain
  · exact_mod_cast Nat.zero_le (exactChainTotalDeficit chain -
      (exactChainUnitCount chain + exactChainLargeCount chain))
  · exact he
  · exact hc
  · rfl
  · have hb' : pieceListTotalSize chain.pieces + exactChainTotalDeficit chain =
        13 * exactChainPieceCount chain := by
      simpa [pieceListTotalDeficit, exactChainTotalDeficit, exactChainDeficits,
        exactChainPieceCount, Nat.mul_comm] using hb
    have hbInt := congrArg (fun n : ℕ => (n : ℤ)) hb'
    push_cast at hbInt
    linarith

/-- The exact numerical shape of an actual cheap chain with zero residual. -/
theorem actual_light_chain_zero_shape
    {p : HPath 14} (hp : p.StronglyExitless)
    (chain : ExactWeightThreePieceChain p)
    (hlast : chainLastFullBit chain = 0)
    (hzero : 6 * ((exactChainTotalDeficit chain : ℤ) + 1) -
      exactChainPieceCount chain = 0) :
    chainFirstFullBit chain = 1 ∧ exactChainTotalDeficit chain = 1 ∧
      exactChainPieceCount chain = 12 ∧ pieceListTotalSize chain.pieces = 155 := by
  let package := strongActualChainCapacityPackage hp chain
  let cert := package.certificate
  have hpartial := exactChain_partialCount_le_totalDeficit chain
  have hunit := exactChain_unit_add_two_large_le_totalDeficit chain
  have hinc : 2 * cert.fullRunCount ≤
      exactChainTotalDeficit chain + cert.endpointFullCount := by
    have h := cert.oneSided
    omega
  have hfull := cert.fullBound
  have hlong := cert.longBound
  have hchain := package.full_runs_le_excess
  have hr := exactChain_pieceCount_eq_full_add_partial chain
  have hb := pieceListTotalSize_add_deficit (by decide : 4 ≤ 14) hp chain.pieces
  have he : (cert.endpointFullCount : ℤ) ≤ 1 := by
    change (package.certificate.endpointFullCount : ℤ) ≤ 1
    rw [package.endpoint_eq, hlast, Nat.add_zero]
    exact_mod_cast chainFirstFullBit_le_one chain
  have hEcast :
      ((exactChainTotalDeficit chain -
        (exactChainUnitCount chain + exactChainLargeCount chain) : ℕ) : ℤ) =
      (exactChainTotalDeficit chain : ℤ) -
        (exactChainUnitCount chain + exactChainLargeCount chain : ℕ) :=
    Nat.cast_sub hpartial
  have hbNat : pieceListTotalSize chain.pieces + exactChainTotalDeficit chain =
      13 * exactChainPieceCount chain := by
    simpa [pieceListTotalDeficit, exactChainTotalDeficit, exactChainDeficits,
      exactChainPieceCount, Nat.mul_comm] using hb
  have hbInt := congrArg (fun n : ℕ => (n : ℤ)) hbNat
  push_cast at hbInt
  have hshape := local_zero_residual_int
    (K := (cert.fullRunCount : ℤ)) (F := (exactChainFullCount chain : ℤ))
    (p := ((exactChainUnitCount chain + exactChainLargeCount chain : ℕ) : ℤ))
    (Δ := (exactChainTotalDeficit chain : ℤ))
    (E := ((exactChainTotalDeficit chain -
      (exactChainUnitCount chain + exactChainLargeCount chain) : ℕ) : ℤ))
    (N := (cert.longInternalRunCount : ℤ)) (e := (cert.endpointFullCount : ℤ))
    (c := 1) (R := (exactChainPieceCount chain : ℤ))
    (b := (pieceListTotalSize chain.pieces : ℤ)) (ρ := 0)
    hEcast (by exact_mod_cast hr) (by exact_mod_cast hinc)
    (by exact_mod_cast hfull) (by exact_mod_cast hlong)
    (by exact_mod_cast hchain) (by positivity) (by positivity)
    he (by decide) (by decide) (by linarith) (by linarith) rfl
  norm_num at hshape
  have hend : cert.endpointFullCount = 1 := by exact_mod_cast hshape.1
  have hfirst : chainFirstFullBit chain = 1 := by
    change package.certificate.endpointFullCount = 1 at hend
    rw [package.endpoint_eq, hlast, Nat.add_zero] at hend
    exact hend
  refine ⟨hfirst, ?_, ?_, ?_⟩
  · exact_mod_cast hshape.2.2.2.1
  · exact_mod_cast hshape.2.2.2.2.2.2.1
  · exact_mod_cast hshape.2.2.2.2.2.2.2

end Haruhi
