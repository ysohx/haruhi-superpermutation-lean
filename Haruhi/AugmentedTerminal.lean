import Haruhi.ActualAugmentation

/-! Terminal-full exclusion survives the actual one-orbit augmentation.
The single-full-piece case is isolated by its exact block count. -/
namespace Haruhi
open Hunter PreimageChain Hunter.ProofsPu
open scoped Classical
variable {k : ℕ}

/-- Vertex access in the retained suffix after one complete orbit is prepended. -/
theorem prepend_orbit_suffix_vert {p q : HPath k} {u : Vtx k}
    (hv : q.verts = orbitList (sigma u) ++ p.verts)
    {i : ℕ} (hi : i < p.numVerts) : q.vert (k + i) = p.vert i := by
  have hn : q.numVerts = k + p.numVerts := by
    change q.verts.length = _
    rw [hv, List.length_append, orbitList_length]
    rfl
  rw [Hunter.ProofsExitless.vert_getElem q (by rw [hn]; omega)]
  simp only [hv]
  rw [List.getElem_append_right (by rw [orbitList_length]; omega)]
  rw [Hunter.ProofsExitless.vert_getElem p hi]
  congr 1
  rw [orbitList_length]
  omega

/-- An augmented path with a cheap original head can be terminal-full only
when it has exactly one full piece. -/
theorem prepended_cheap_head_full_classCount
    {P : HPath k} (hP : P.IsHamiltonian) (hk : 3 ≤ k)
    (hred : Sigma2Reduced P) (C : ActualComponent P)
    {q : HPath k} {u y : Vtx k}
    (hq : q.StronglyExitless)
    (hverts : q.verts = orbitList (sigma u) ++ (actualComponentPath hP C).verts)
    (hlast : q.last = actualComponentHead hP C)
    (hedge : (actualComponentHead hP C, y) ∈ P.edges)
    (hweight : ew k (actualComponentHead hP C) y = 2)
    (hfull : componentLastPieceFull q) :
    componentClassCount q = k - 1 := by
  let p := actualComponentPath hP C
  have hp : p.StronglyExitless := actualComponentPath_stronglyExitless hP (by omega) C
  have hn : q.numVerts = p.numVerts + k := by
    change q.verts.length = _
    rw [hverts, List.length_append, orbitList_length]
    change k + p.numVerts = p.numVerts + k
    omega
  have hcount := prepend_orbit_classCount (by omega : 1 ≤ k) hn
  obtain ⟨j, hjend, hj, htau, hidx⟩ :=
    component_last_piece_full_tau_entry hk hq hfull
  by_contra hneq
  have hjpos : 0 < j := by omega
  have hjprev : j - 1 < componentClassCount p := by omega
  have hmul : k * j = k + k * (j - 1) := by
    have heq : j = (j - 1) + 1 := by omega
    calc
      k * j = k * ((j - 1) + 1) := congrArg (fun n => k * n) heq
      _ = k + k * (j - 1) := by ring
  have hpidx : k * (j - 1) < p.numVerts - 1 := by
    rw [hmul, hn] at hidx
    omega
  have hsuffix : q.vert (k * j) = p.vert (k * (j - 1)) := by
    rw [hmul]
    exact prepend_orbit_suffix_vert hverts
      (show k * (j - 1) < p.numVerts by omega)
  rw [hsuffix, hlast] at htau
  have hy : y = tau (actualComponentHead hP C) := by
    rcases weight_two_successors (by omega) hweight with hd | ht
    · exfalso
      apply hred (actualComponentHead hP C)
      rw [← hd]
      exact hedge
    · exact ht
  have hcomp : IsPathComponent p (F P) := actualComponentPath_isPathComponent hP C
  have hentry := component_block_entry_mem_C0 hP (by omega) hcomp hp hjprev
  have hmem := Hunter.ProofsExitless.vert_mem p (by omega : k * (j - 1) < p.numVerts)
  have hpos : p.pos (p.vert (k * (j - 1))) < p.pos p.last := by
    rw [Hunter.ProofsExitless.pos_vert p (by omega), Hunter.ProofsStructure.pos_last]
    exact hpidx
  have horder := Hunter.Proved.clm_ordering hP hcomp
    (Finset.mem_union.mpr (Or.inl hentry)) hmem p.last_mem hpos
  rw [← htau, ← hy, show p.last = actualComponentHead hP C from
    actualComponentPath_last hP C] at horder
  have hedgepos := Hunter.ProofsStructure.edge_pos_succ hedge
  omega

/-- For every actual component, terminal-fullness of its canonical augmentation
and a cheap selected head force the one-full-piece exceptional case. -/
theorem actual_augmented_cheap_head_full_classCount
    {P : HPath k} (hP : P.IsHamiltonian) (hk : 3 ≤ k)
    (hred : Sigma2Reduced P) (C : ActualComponent P) {y : Vtx k}
    (hedge : (actualComponentHead hP C, y) ∈ P.edges)
    (hweight : ew k (actualComponentHead hP C) y = 2)
    (hfull : componentLastPieceFull (actualAugmentedPath hP (by omega) C)) :
    componentClassCount (actualAugmentedPath hP (by omega) C) = k - 1 := by
  by_cases hc : C = actualRootComponent hP (by omega)
  · have heq : actualAugmentedPath hP (by omega) C = actualComponentPath hP C := by
      simp only [actualAugmentedPath, dif_pos hc]
    rw [heq] at hfull
    exact False.elim ((actual_head_weight_two_not_last_piece_full hP hk hred C
      hedge hweight) hfull)
  · have hverts : (actualAugmentedPath hP (by omega) C).verts =
        orbitList (sigma (actualEntrySlot hP (by omega) C hc).1) ++
          (actualComponentPath hP C).verts := by
      simp only [actualAugmentedPath, dif_neg hc]
      exact (Classical.choose_spec (actualAugmentation_exists hP (by omega) C hc)).1
    exact prepended_cheap_head_full_classCount hP hk hred C
      (actualAugmentedPath_stronglyExitless hP (by omega) C) hverts
      (actualAugmentedPath_last hP (by omega) C) hedge hweight hfull

/-- A terminal deficit-one door segment beginning after the prepended block
produces a visit in the original component after its tail. -/
theorem actual_augmented_terminal_door_segment_certificate
    {P : HPath k} (hP : P.IsHamiltonian) (hk : 4 ≤ k)
    (C : ActualComponent P) {start : ℕ} (hstart : 1 < start)
    (hend : start + (k - 2) =
      componentClassCount (actualAugmentedPath hP (by omega) C))
    (hdoors : ∀ r, 1 ≤ r → r ≤ k - 3 →
      Hunter.ProofsLedger.IsDoor (actualAugmentedPath hP (by omega) C) (start + r)) :
    TerminalFullVisitCertificate hP C := by
  by_cases hc : C = actualRootComponent hP (by omega)
  · have heq : actualAugmentedPath hP (by omega) C = actualComponentPath hP C := by
      simp only [actualAugmentedPath, dif_pos hc]
    rw [heq] at hend hdoors
    exact actual_terminal_door_segment_certificate hP hk C (by omega) hend hdoors
  · let p := actualComponentPath hP C
    let q := actualAugmentedPath hP (by omega) C
    have hp : p.StronglyExitless := actualComponentPath_stronglyExitless hP (by omega) C
    have hq : q.StronglyExitless := actualAugmentedPath_stronglyExitless hP (by omega) C
    have hverts : q.verts =
        orbitList (sigma (actualEntrySlot hP (by omega) C hc).1) ++ p.verts := by
      dsimp [q, p]
      simp only [actualAugmentedPath, dif_neg hc]
      exact (Classical.choose_spec (actualAugmentation_exists hP (by omega) C hc)).1
    have hcount : componentClassCount q = componentClassCount p + 1 := by
      dsimp [q, p]
      rw [actualAugmentedPath_classCount, if_neg hc]
    have hpsi := terminal_door_segment_psi hk hq hend hdoors
    have hmul : k * start = k + k * (start - 1) := by
      have heq : start = (start - 1) + 1 := by omega
      calc
        k * start = k * ((start - 1) + 1) := congrArg (fun n => k * n) heq
        _ = k + k * (start - 1) := by ring
    have hidxpos : 1 ≤ k * (start - 1) := Nat.mul_pos (by omega) (by omega)
    have hidxlt : k * (start - 1) < p.numVerts := by
      rw [component_numVerts_eq (by omega) hp]
      apply Nat.mul_lt_mul_of_pos_left _ (by omega)
      change start + (k - 2) = componentClassCount q at hend
      omega
    have hsuffix : q.vert (k * start) = p.vert (k * (start - 1)) := by
      rw [hmul]
      exact prepend_orbit_suffix_vert hverts hidxlt
    rw [hsuffix, actualAugmentedPath_last hP (by omega) C] at hpsi
    unfold TerminalFullVisitCertificate
    rw [hpsi]
    simpa only [List.drop_one] using
      (Hunter.ProofsUnwind2.vert_mem_drop1 (p := p) hidxpos hidxlt)

/-- The augmented terminal bit vanishes outside the single-full-piece case. -/
theorem actual_augmented_cheap_head_lastFullBit_zero
    {P : HPath k} (hP : P.IsHamiltonian) (hk : 5 ≤ k)
    (hred : Sigma2Reduced P) (C : ActualComponent P) {y : Vtx k}
    (hedge : (actualComponentHead hP C, y) ∈ P.edges)
    (hweight : ew k (actualComponentHead hP C) y = 2)
    (hcount : componentClassCount (actualAugmentedPath hP (by omega) C) ≠ k - 1) :
    componentLastFullBit (actualAugmentedPath hP (by omega) C) (by omega)
      (actualAugmentedPath_stronglyExitless hP (by omega) C) = 0 := by
  have hp := actualAugmentedPath_stronglyExitless hP (by omega) C
  have hle := componentLastFullBit_le_one (actualAugmentedPath hP (by omega) C) (by omega) hp
  by_contra hne
  have hbit : componentLastFullBit (actualAugmentedPath hP (by omega) C) (by omega) hp = 1 := by
    omega
  exact hcount (actual_augmented_cheap_head_full_classCount hP (by omega) hred C
    hedge hweight (componentLastFullBit_one_implies_lastPieceFull hk hp hbit))

end Haruhi
