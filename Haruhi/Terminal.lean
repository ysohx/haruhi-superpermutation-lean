import PreimageChain.ComponentEndpointRigidity

/-!
# Deficit-one terminal rigidity for actual Hunter components

Proofs adapt block-coordinate arguments from PreimageChain.ComponentGeometry
and endpoint-piece extraction from PreimageChain.ComponentEndpointRigidity,
commit 8474c74a15fa59b8ce55bcf6bceaaa23b9a3dca8 (CC BY 4.0).
The new results are the deficit-one coordinate and its actual-component consequences.

This module proves the new coordinate fact used in the candidate bound directly
for actual strongly exitless paths and actual components of `F P`.  The
connector theorem assumes the concrete entry edge is not the double rotation;
it does not assume a global reduced normal form.
-/

namespace Haruhi

open Hunter PreimageChain
open scoped Classical

variable {k : ℕ}

/-- After a run of `k-2` complete rotation blocks, `psi` of its head is
exactly its first entry. -/
theorem psi_of_deficit_one_run_head
    (hk : 4 ≤ k) {base : List ℕ} (hbase : base.length = k - 1)
    {m : ℕ} {h : Vtx k}
    (hhead : h.1 = Hunter.ProofsRigidity2.bexit k
      (base.rotate (k - 3) ++ [m])) :
    (psi h).1 = base ++ [m] := by
  have htau₁ := Hunter.ProofsRigidity2.tau2_step
    (by omega : 2 ≤ k) hbase m (k - 3)
  have hfirstDoor :
      door (Hunter.ProofsRigidity2.bexit k (base.rotate (k - 3) ++ [m])) =
        base.rotate (k - 2) ++ [m] := by
    change Hunter.ProofsRigidity2.tau2 k
      (base.rotate (k - 3) ++ [m]) = base.rotate (k - 2) ++ [m]
    rw [htau₁, show k - 3 + 1 = k - 2 by omega]
  have htau₂ := Hunter.ProofsRigidity2.tau2_step
    (by omega : 2 ≤ k) hbase m (k - 2)
  have hperiod : base.rotate (k - 1) = base := by
    rw [← hbase, List.rotate_length]
  change (tau (sigmaInv (tau h))).1 = _
  rw [Hunter.tau_val_of_door
    (Hunter.door_isPermWord (by omega) (sigmaInv (tau h)).2)]
  change door ((tau h).1.rotate (k - 1)) = _
  rw [Hunter.tau_val_of_door (Hunter.door_isPermWord (by omega) h.2)]
  rw [hhead, hfirstDoor]
  change Hunter.ProofsRigidity2.tau2 k (base.rotate (k - 2) ++ [m]) = _
  rw [htau₂, show k - 2 + 1 = k - 1 by omega, hperiod]

/-- The terminal near-full run is identified using actual block positions and
actual weight-two doors in a strongly exitless path. -/
theorem terminal_door_segment_psi
    (hk : 4 ≤ k) {p : HPath k} (hp : p.StronglyExitless)
    {start : ℕ}
    (hend : start + (k - 2) = componentClassCount p)
    (hdoors : ∀ r, 1 ≤ r → r ≤ k - 3 →
      Hunter.ProofsLedger.IsDoor p (start + r)) :
    psi p.last = p.vert (k * start) := by
  let t := componentClassCount p
  have hN : p.numVerts = k * t := component_numVerts_eq (by omega) hp
  have ht : 0 < t := componentClassCount_pos (by omega) hp
  have hlastBlockIndex : start + (k - 3) = t - 1 := by
    dsimp [t]
    omega
  have hNrun : k * (start + (k - 3)) < p.numVerts := by
    rw [hlastBlockIndex, hN]
    exact Nat.mul_lt_mul_of_pos_left (by omega) (by omega)
  have hrun := Hunter.ProofsFillPath.blockrun_eq
    (by omega : 2 ≤ k) hp.1 start (k - 3) hNrun (by
      intro r hr1 hr2
      simpa [Hunter.ProofsLedger.IsDoor, Hunter.ProofsLedger.bw] using
        hdoors r hr1 hr2)
  let m := (p.vert (k * start) : List ℕ).getLastD 0
  let base := (p.vert (k * start) : List ℕ).erase m
  have hbase : base.length = k - 1 := by
    dsimp [base, m]
    rw [Hunter.ProofsConfinement.erase_getLastD (p.vert (k * start)).2.nodup,
      List.length_dropLast, (p.vert (k * start)).2.length]
  have hlastBlock := hrun (k - 3) (le_refl _)
  rw [hlastBlockIndex] at hlastBlock
  change (p.vert (k * (t - 1)) : List ℕ) =
    base.rotate (k - 3) ++ [m] at hlastBlock
  have hlastIndex : p.numVerts - 1 = k * (t - 1) + (k - 1) := by
    have htEq : t = (t - 1) + 1 := by omega
    have hmul : k * t = k * (t - 1) + k := by
      calc
        k * t = k * ((t - 1) + 1) := congrArg (fun n => k * n) htEq
        _ = k * (t - 1) + k := Nat.mul_succ _ _
    rw [hN, hmul]
    omega
  have hBlt : k * (t - 1) + (k - 1) < p.numVerts := by
    rw [← hlastIndex]
    omega
  have hcycle :
      p.vert (k * (t - 1) + (k - 1)) =
        sigma^[k - 1] (p.vert (k * (t - 1))) :=
    Hunter.ProofsExitless.block_is_full_cycle (by omega) hp.1
      ⟨t - 1, rfl⟩ (by omega) hBlt
  have hhead : (p.last : List ℕ) = Hunter.ProofsRigidity2.bexit k
      (base.rotate (k - 3) ++ [m]) := by
    rw [Hunter.Proved.last_eq_vert, hlastIndex, hcycle,
      Hunter.ProofsExitless.sigma_iter_val, hlastBlock]
    rfl
  have hpsiVal := psi_of_deficit_one_run_head hk hbase hhead
  have hrunZero := hrun 0 (by omega)
  change (p.vert (k * (start + 0)) : List ℕ) = base.rotate 0 ++ [m] at hrunZero
  have hfirstWord : (p.vert (k * start) : List ℕ) = base ++ [m] := by
    simpa using hrunZero
  apply Subtype.ext
  exact hpsiVal.trans hfirstWord.symm

/-- When the terminal near-full run does not start at the overall tail, its
forced target is a later vertex of the actual path. -/
theorem terminal_door_segment_visit
    (hk : 4 ≤ k) {p : HPath k} (hp : p.StronglyExitless)
    {start : ℕ} (hstart : 0 < start)
    (hend : start + (k - 2) = componentClassCount p)
    (hdoors : ∀ r, 1 ≤ r → r ≤ k - 3 →
      Hunter.ProofsLedger.IsDoor p (start + r)) :
    psi p.last ∈ p.verts.tail := by
  rw [terminal_door_segment_psi hk hp hend hdoors]
  have hidxpos : 1 ≤ k * start := Nat.mul_pos (by omega) hstart
  have hidxlt : k * start < p.numVerts := by
    rw [component_numVerts_eq (by omega) hp]
    exact Nat.mul_lt_mul_of_pos_left (by omega) (by omega)
  simpa only [List.drop_one] using
    (Hunter.ProofsUnwind2.vert_mem_drop1 hidxpos hidxlt)

/-- A concrete terminal interval piece of deficit one with positive start
supplies the required visit certificate. -/
theorem terminal_deficit_one_piece_visit
    (hk : 4 ≤ k) {p : HPath k} (hp : p.StronglyExitless)
    (piece : ComponentIntervalPiece p)
    (hstop : piece.stop = componentClassCount p)
    (hdeficit : piece.deficit = 1)
    (hstart : 0 < piece.start) :
    psi p.last ∈ p.verts.tail := by
  have hsize := ComponentIntervalPiece.size_add_deficit hk hp piece
  rw [hdeficit] at hsize
  have hpieceSize : piece.stop - piece.start = k - 2 := by
    simp only [ComponentIntervalPiece.size, actualPieceSize] at hsize
    omega
  have hend : piece.start + (k - 2) = componentClassCount p := by
    have hn := piece.valid.nonempty
    omega
  apply terminal_door_segment_visit hk hp hstart hend
  intro r hr1 hr2
  exact piece.valid.doors r hr1 (by omega)

/-- The visit statement is expressed using an actual component of `F P`, not
an abstract profile or an assumed cost inequality. -/
theorem actual_terminal_deficit_one_certificate
    {P : HPath k} (hP : P.IsHamiltonian) (hk : 4 ≤ k)
    (C : ActualComponent P)
    (piece : ComponentIntervalPiece (actualComponentPath hP C))
    (hstop : piece.stop = componentClassCount (actualComponentPath hP C))
    (hdeficit : piece.deficit = 1)
    (hstart : 0 < piece.start) :
    TerminalFullVisitCertificate hP C := by
  unfold TerminalFullVisitCertificate
  rw [← actualComponentPath_last hP C]
  exact terminal_deficit_one_piece_visit hk
    (actualComponentPath_stronglyExitless hP (by omega) C)
    piece hstop hdeficit hstart

/-- A weight-two edge into a component from an outside slot is a proper door.
The excluded double rotation stays in the target's rotation class. -/
theorem proper_door_into_actual_component
    {P : HPath k} (hP : P.IsHamiltonian) (hk : 2 ≤ k)
    (A : ActualComponent P) (slot : Vtx k)
    (hout : slot ∉ A.1)
    (hweight : ew k slot (actualComponentTail hP A) = 2) :
    actualComponentTail hP A = tau slot := by
  rcases weight_two_successors hk hweight with hdouble | hproper
  · exfalso
    let p := actualComponentPath hP A
    have hp : p.StronglyExitless := actualComponentPath_stronglyExitless hP hk A
    have hfirst : p.first = sigma2 slot := by
      change (actualComponentPath hP A).first = _
      rw [actualComponentPath_first hP A, hdouble]
    have hrot : rotClass (sigma2 slot).1 = rotClass slot.1 := by
      simpa [sigma2, Function.iterate_succ_apply'] using
        Hunter.ProofsExitless.rotClass_sigma_iter 2 slot
    have hslotCycle : slot ∈ cyc p.first := by
      apply Hunter.ProofsExitless.mem_cyc.mpr
      rw [hfirst]
      exact hrot.symm
    have hslotMem : slot ∈ p.vertsFinset :=
      Hunter.Proved.clm_1cyclesubset hp p.first p.first_mem hslotCycle
    apply hout
    simpa [p, actualComponentPath_vertsFinset hP A] using hslotMem
  · exact hproper

/-- The concrete direct connector formula, with the two local exclusions
needed for an unreduced well-behaved original Hamiltonian path. -/
theorem actual_direct_connector_psi
    {P : HPath k} (hP : P.IsHamiltonian) (hk : 2 ≤ k)
    (C A : ActualComponent P) (slot : Vtx k)
    (hentryWeight : ew k (actualComponentHead hP C) (sigma slot) = 2)
    (hentryProper : sigma slot ≠ sigma2 (actualComponentHead hP C))
    (hout : slot ∉ A.1)
    (hexitWeight : ew k slot (actualComponentTail hP A) = 2) :
    actualComponentTail hP A = psi (actualComponentHead hP C) := by
  have hentry : sigma slot = tau (actualComponentHead hP C) := by
    rcases weight_two_successors hk hentryWeight with hdouble | hproper
    · exact False.elim (hentryProper hdouble)
    · exact hproper
  have hslot : slot = sigmaInv (tau (actualComponentHead hP C)) := by
    have h := congrArg sigmaInv hentry
    rw [sigmaInv_sigma (by omega)] at h
    exact h
  rw [proper_door_into_actual_component hP hk A slot hout hexitWeight,
    hslot, psi]

/-- A source with a retained later `psi` visit cannot have a direct connector
to a target whose selected incoming edge has weight two. -/
theorem actual_rigid_source_no_direct_connector
    {P : HPath k} (hP : P.IsHamiltonian) (hk : 2 ≤ k)
    (C A : ActualComponent P) (slot : Vtx k)
    (hvisit : TerminalFullVisitCertificate hP C)
    (hentryWeight : ew k (actualComponentHead hP C) (sigma slot) = 2)
    (hentryProper : sigma slot ≠ sigma2 (actualComponentHead hP C))
    (hout : slot ∉ A.1)
    (hexitWeight : ew k slot (actualComponentTail hP A) = 2) : False := by
  have hpsi := actual_direct_connector_psi hP hk C A slot
    hentryWeight hentryProper hout hexitWeight
  have hmemC : psi (actualComponentHead hP C) ∈ C.1 :=
    terminalFullVisit_mem_component hP C hvisit
  have hmemA : psi (actualComponentHead hP C) ∈ A.1 := by
    rw [← hpsi]
    exact actualComponentTail_mem_component hP A
  have hCA : C = A := by
    apply Subtype.ext
    exact (Hunter.ProofsWP.comp_eq_block_of_mem C.2 hmemC).trans
      ((Hunter.ProofsWP.comp_eq_block_of_mem A.2 hmemA).symm)
  have hrigid := terminal_full_visit_rigidity hP C hvisit
  apply hrigid
  calc
    actualComponentTail hP C = actualComponentTail hP A := by rw [hCA]
    _ = psi (actualComponentHead hP C) := hpsi

/-- Direct block-coordinate certificate for an actual component. -/
theorem actual_terminal_door_segment_certificate
    {P : HPath k} (hP : P.IsHamiltonian) (hk : 4 ≤ k)
    (C : ActualComponent P) {start : ℕ} (hstart : 0 < start)
    (hend : start + (k - 2) = componentClassCount (actualComponentPath hP C))
    (hdoors : ∀ r, 1 ≤ r → r ≤ k - 3 →
      Hunter.ProofsLedger.IsDoor (actualComponentPath hP C) (start + r)) :
    TerminalFullVisitCertificate hP C := by
  unfold TerminalFullVisitCertificate
  rw [← actualComponentPath_last hP C]
  exact terminal_door_segment_visit hk
    (actualComponentPath_stronglyExitless hP (by omega) C)
    hstart hend hdoors

/-- The final source theorem starts from a genuine terminal piece of a genuine
Hunter component; its conclusion rules out the actual direct connector. -/
theorem actual_terminal_deficit_one_no_direct_connector
    {P : HPath k} (hP : P.IsHamiltonian) (hk : 4 ≤ k)
    (C A : ActualComponent P)
    (piece : ComponentIntervalPiece (actualComponentPath hP C))
    (hstop : piece.stop = componentClassCount (actualComponentPath hP C))
    (hdeficit : piece.deficit = 1)
    (hstart : 0 < piece.start)
    (slot : Vtx k)
    (hentryWeight : ew k (actualComponentHead hP C) (sigma slot) = 2)
    (hentryProper : sigma slot ≠ sigma2 (actualComponentHead hP C))
    (hout : slot ∉ A.1)
    (hexitWeight : ew k slot (actualComponentTail hP A) = 2) : False := by
  exact actual_rigid_source_no_direct_connector hP (by omega) C A slot
    (actual_terminal_deficit_one_certificate hP hk C piece hstop hdeficit hstart)
    hentryWeight hentryProper hout hexitWeight

/-- The original predecessor of an actual component tail lies outside the
component. This discharges the local slot-exclusion premise from real edges. -/
theorem actual_tail_predecessor_outside
    {P : HPath k} (hP : P.IsHamiltonian)
    (A : ActualComponent P) {slot : Vtx k}
    (hedge : (slot, actualComponentTail hP A) ∈ P.edges) :
    slot ∉ A.1 := by
  intro hmem
  have hpathMem : slot ∈ (actualComponentPath hP A).verts := by
    rw [← HPath.mem_vertsFinset, actualComponentPath_vertsFinset hP A]
    exact hmem
  have hle := Hunter.Proved.cor_pathfirst hP
    (actualComponentPath_isPathComponent hP A) hpathMem
  rw [actualComponentPath_first hP A] at hle
  have hpos := Hunter.ProofsStructure.edge_pos_succ hedge
  omega

/-- Convenience form for a reduced Hamilton path: both connector edges are
actual original-path edges, and no local exclusion is left as a hypothesis. -/
theorem actual_terminal_deficit_one_no_direct_connector_reduced
    {P : HPath k} (hP : P.IsHamiltonian) (hk : 4 ≤ k)
    (hred : Sigma2Reduced P)
    (C A : ActualComponent P)
    (piece : ComponentIntervalPiece (actualComponentPath hP C))
    (hstop : piece.stop = componentClassCount (actualComponentPath hP C))
    (hdeficit : piece.deficit = 1)
    (hstart : 0 < piece.start)
    (slot : Vtx k)
    (hentryEdge : (actualComponentHead hP C, sigma slot) ∈ P.edges)
    (hentryWeight : ew k (actualComponentHead hP C) (sigma slot) = 2)
    (hexitEdge : (slot, actualComponentTail hP A) ∈ P.edges)
    (hexitWeight : ew k slot (actualComponentTail hP A) = 2) : False := by
  apply actual_terminal_deficit_one_no_direct_connector hP hk C A piece
    hstop hdeficit hstart slot hentryWeight
  · intro hdouble
    apply hred (actualComponentHead hP C)
    rw [← hdouble]
    exact hentryEdge
  · exact actual_tail_predecessor_outside hP A hexitEdge
  · exact hexitWeight

/-- Reduced-path connector exclusion from an already derived concrete visit.
This accepts either the exact-piece or the direct block-coordinate theorem. -/
theorem actual_rigid_source_no_direct_connector_reduced
    {P : HPath k} (hP : P.IsHamiltonian) (hk : 2 ≤ k)
    (hred : Sigma2Reduced P)
    (C A : ActualComponent P) (slot : Vtx k)
    (hvisit : TerminalFullVisitCertificate hP C)
    (hentryEdge : (actualComponentHead hP C, sigma slot) ∈ P.edges)
    (hentryWeight : ew k (actualComponentHead hP C) (sigma slot) = 2)
    (hexitEdge : (slot, actualComponentTail hP A) ∈ P.edges)
    (hexitWeight : ew k slot (actualComponentTail hP A) = 2) : False := by
  apply actual_rigid_source_no_direct_connector hP hk C A slot hvisit hentryWeight
  · intro hdouble
    apply hred (actualComponentHead hP C)
    rw [← hdouble]
    exact hentryEdge
  · exact actual_tail_predecessor_outside hP A hexitEdge
  · exact hexitWeight

/-- The next proper door after a complete terminal run returns to the first
entry of that run. -/
theorem tau_of_complete_run_head
    (hk : 3 ≤ k) {base : List ℕ} (hbase : base.length = k - 1)
    {m : ℕ} {h : Vtx k}
    (hhead : h.1 = Hunter.ProofsRigidity2.bexit k
      (base.rotate (k - 2) ++ [m])) :
    (tau h).1 = base ++ [m] := by
  have htau := Hunter.ProofsRigidity2.tau2_step
    (by omega : 2 ≤ k) hbase m (k - 2)
  have hperiod : base.rotate (k - 1) = base := by
    rw [← hbase, List.rotate_length]
  rw [Hunter.tau_val_of_door (Hunter.door_isPermWord (by omega) h.2), hhead]
  change Hunter.ProofsRigidity2.tau2 k
    (base.rotate (k - 2) ++ [m]) = base ++ [m]
  rw [htau, show k - 2 + 1 = k - 1 by omega, hperiod]

/-- Each rotation-block entry of a genuine component of `F P` is in `C0 P`.
This permits applying Hunter's walking order to the actual entry. -/
theorem component_block_entry_mem_C0
    {P : HPath k} (hP : P.IsHamiltonian) (hk : 1 ≤ k)
    {p : HPath k} (hcomp : IsPathComponent p (F P))
    (hp : p.StronglyExitless) {j : ℕ} (hj : j < componentClassCount p) :
    p.vert (k * j) ∈ C0 P := by
  by_cases hjzero : j = 0
  · subst j
    simp only [Nat.mul_zero, HPath.vert_zero]
    have htail : intoV (F P) p.first = ∅ := by
      have h := Hunter.ProofsSpine.compTails_eq hcomp
      have hmem : p.first ∈ compTails (F P) p.vertsFinset := by
        rw [h]
        exact Finset.mem_singleton_self _
      rw [compTails, Finset.mem_filter] at hmem
      exact hmem.2
    by_contra hc
    have h25 := Hunter.Proved.clm_rule2_5 hP hc
    rw [h25] at htail
    exact absurd htail (Finset.singleton_ne_empty _)
  · have hjpos : 1 ≤ j := by omega
    have hidxpos : 1 ≤ k * j := Nat.mul_pos hk hjpos
    have hidx : k * j - 1 + 1 = k * j := by omega
    have hidxlt : k * j < p.numVerts := by
      rw [component_numVerts_eq hk hp]
      exact Nat.mul_lt_mul_of_pos_left hj hk
    have hedge : (p.vert (k * j - 1), p.vert (k * j)) ∈ F P := by
      apply hcomp.1
      have h := Hunter.ProofsStructure.vert_consec_mem_edges
        (p := p) (i := k * j - 1) (by omega)
      simpa only [hidx] using h
    have hbound : j ∈ componentBoundaries p := by
      simp only [componentBoundaries, Finset.mem_Icc]
      omega
    have hweight := componentBoundary_weight_ge_two hk hp hbound
    by_contra hc
    have h25 := Hunter.Proved.clm_rule2_5 hP hc
    have hinto : (p.vert (k * j - 1), p.vert (k * j)) ∈
        intoV (F P) (p.vert (k * j)) := by
      simp only [intoV, mem_into, Finset.mem_singleton]
      exact ⟨hedge, trivial⟩
    rw [h25, Finset.mem_singleton] at hinto
    have heq : p.vert (k * j - 1) = sigmaInv (p.vert (k * j)) :=
      congrArg Prod.fst hinto
    have hback : sigma (p.vert (k * j - 1)) = p.vert (k * j) := by
      rw [heq]
      exact Hunter.ProofsStructure.sigma_sigmaInv _
    have hone : ew k (p.vert (k * j - 1)) (p.vert (k * j)) = 1 := by
      rw [← hback]
      exact Hunter.ew_sigma hk _
    change 2 ≤ ew k (p.vert (k * j - 1)) (p.vert (k * j)) at hweight
    omega

/-- A terminal full run forces the proper door back to an actual, earlier
block entry in its component. -/
theorem component_last_piece_full_tau_entry
    (hk : 3 ≤ k) {p : HPath k} (hp : p.StronglyExitless)
    (hfull : componentLastPieceFull p) :
    ∃ j, j + (k - 1) = componentClassCount p ∧
      j < componentClassCount p ∧
      tau p.last = p.vert (k * j) ∧ k * j < p.numVerts - 1 := by
  let t := componentClassCount p
  have hN : p.numVerts = k * t := component_numVerts_eq (by omega) hp
  have ht : 0 < t := componentClassCount_pos (by omega) hp
  have hcomplete : Hunter.ProofsLedger.doorDepth p (t - 1) = k - 2 := hfull
  have hdepth := Hunter.ProofsLedger.doorDepth_le p (t - 1)
  have htlarge : k - 1 ≤ t := by rw [hcomplete] at hdepth; omega
  let g0 := (t - 1) - (k - 2)
  have hg0 : g0 + (k - 2) = t - 1 := by dsimp [g0]; omega
  have hdoor : ∀ r, 1 ≤ r → r ≤ k - 2 →
      ew k (p.vert (k * (g0 + r) - 1)) (p.vert (k * (g0 + r))) = 2 := by
    intro r hr1 hr2
    have hj : (k - 2) - r < Hunter.ProofsLedger.doorDepth p (t - 1) := by
      rw [hcomplete]
      omega
    have hd := Hunter.ProofsLedger.isDoor_of_lt_doorDepth p
      (t - 1) ((k - 2) - r) hj
    have hidx : (t - 1) - ((k - 2) - r) = g0 + r := by dsimp [g0]; omega
    rw [hidx, Hunter.ProofsLedger.IsDoor, Hunter.ProofsLedger.bw] at hd
    exact hd
  have hNrun : k * (g0 + (k - 2)) < p.numVerts := by
    rw [hg0, hN]
    exact Nat.mul_lt_mul_of_pos_left (by omega) (by omega)
  have hrun := Hunter.ProofsFillPath.blockrun_eq
    (by omega : 2 ≤ k) hp.1 g0 (k - 2) hNrun hdoor
  let m := (p.vert (k * g0) : List ℕ).getLastD 0
  let base := (p.vert (k * g0) : List ℕ).erase m
  have hbase : base.length = k - 1 := by
    dsimp [base, m]
    rw [Hunter.ProofsConfinement.erase_getLastD (p.vert (k * g0)).2.nodup,
      List.length_dropLast, (p.vert (k * g0)).2.length]
  have hlastBlock := hrun (k - 2) (le_refl _)
  rw [hg0] at hlastBlock
  change (p.vert (k * (t - 1)) : List ℕ) =
    base.rotate (k - 2) ++ [m] at hlastBlock
  have hlastIndex : p.numVerts - 1 = k * (t - 1) + (k - 1) := by
    have htEq : t = (t - 1) + 1 := by omega
    have hmul : k * t = k * (t - 1) + k := by
      calc
        k * t = k * ((t - 1) + 1) := congrArg (fun n => k * n) htEq
        _ = k * (t - 1) + k := Nat.mul_succ _ _
    rw [hN, hmul]
    omega
  have hBlt : k * (t - 1) + (k - 1) < p.numVerts := by
    rw [← hlastIndex]
    omega
  have hcycle :
      p.vert (k * (t - 1) + (k - 1)) =
        sigma^[k - 1] (p.vert (k * (t - 1))) :=
    Hunter.ProofsExitless.block_is_full_cycle (by omega) hp.1
      ⟨t - 1, rfl⟩ (by omega) hBlt
  have hhead : (p.last : List ℕ) = Hunter.ProofsRigidity2.bexit k
      (base.rotate (k - 2) ++ [m]) := by
    rw [Hunter.Proved.last_eq_vert, hlastIndex, hcycle,
      Hunter.ProofsExitless.sigma_iter_val, hlastBlock]
    rfl
  have htauVal := tau_of_complete_run_head hk hbase hhead
  have hrunZero := hrun 0 (by omega)
  change (p.vert (k * (g0 + 0)) : List ℕ) = base.rotate 0 ++ [m] at hrunZero
  have hfirstWord : (p.vert (k * g0) : List ℕ) = base ++ [m] := by
    simpa using hrunZero
  have htau : tau p.last = p.vert (k * g0) := by
    apply Subtype.ext
    exact htauVal.trans hfirstWord.symm
  have hglt : g0 < t := by dsimp [g0]; omega
  refine ⟨g0, by dsimp [t] at hg0 ⊢; omega, hglt, htau, ?_⟩
  rw [hlastIndex]
  have hle : k * g0 ≤ k * (t - 1) :=
    Nat.mul_le_mul_left k (by omega)
  omega

/-- An actual component with a selected outgoing edge of weight two cannot
end with a full piece in a reduced Hamiltonian path. -/
theorem actual_head_weight_two_not_last_piece_full
    {P : HPath k} (hP : P.IsHamiltonian) (hk : 3 ≤ k)
    (hred : Sigma2Reduced P) (C : ActualComponent P) {y : Vtx k}
    (hedge : (actualComponentHead hP C, y) ∈ P.edges)
    (hweight : ew k (actualComponentHead hP C) y = 2) :
    ¬ actualComponentLastPieceFull hP C := by
  intro hfull
  have hy : y = tau (actualComponentHead hP C) := by
    rcases weight_two_successors (by omega) hweight with hd | ht
    · exfalso
      apply hred (actualComponentHead hP C)
      rw [← hd]
      exact hedge
    · exact ht
  let p := actualComponentPath hP C
  have hp : p.StronglyExitless := actualComponentPath_stronglyExitless hP (by omega) C
  have hcomp : IsPathComponent p (F P) := actualComponentPath_isPathComponent hP C
  obtain ⟨j, _, hj, htau, hidx⟩ := component_last_piece_full_tau_entry hk hp hfull
  have hentry : p.vert (k * j) ∈ C0 P := component_block_entry_mem_C0 hP (by omega) hcomp hp hj
  have hmem := Hunter.ProofsExitless.vert_mem p (by omega : k * j < p.numVerts)
  have hpos : p.pos (p.vert (k * j)) < p.pos p.last := by
    rw [Hunter.ProofsExitless.pos_vert p (by omega), Hunter.ProofsStructure.pos_last]
    exact hidx
  have horder := Hunter.Proved.clm_ordering hP hcomp
    (Finset.mem_union.mpr (Or.inl hentry)) hmem p.last_mem hpos
  have hlast : p.last = actualComponentHead hP C := actualComponentPath_last hP C
  rw [← htau, hlast, ← hy] at horder
  have hedgepos := Hunter.ProofsStructure.edge_pos_succ hedge
  omega

/-- Numerical endpoint-bit form of the actual cheap-head exclusion. -/
theorem actual_head_weight_two_lastFullBit_zero
    {P : HPath k} (hP : P.IsHamiltonian) (hk : 5 ≤ k)
    (hred : Sigma2Reduced P) (C : ActualComponent P) {y : Vtx k}
    (hedge : (actualComponentHead hP C, y) ∈ P.edges)
    (hweight : ew k (actualComponentHead hP C) y = 2) :
    componentLastFullBit (actualComponentPath hP C) (by omega)
      (actualComponentPath_stronglyExitless hP (by omega) C) = 0 := by
  have hp := actualComponentPath_stronglyExitless hP (by omega) C
  have hle := componentLastFullBit_le_one (actualComponentPath hP C) (by omega) hp
  by_contra hne
  have hbit : componentLastFullBit (actualComponentPath hP C) (by omega) hp = 1 := by
    omega
  exact actual_head_weight_two_not_last_piece_full hP (by omega) hred C hedge hweight
    (componentLastFullBit_one_implies_lastPieceFull hk hp hbit)

/-- Total component deficit one and a partial final piece force that actual
final piece to have deficit exactly one. -/
theorem component_deficit_one_terminal_piece
    (hk : 4 ≤ k) {p : HPath k} (hp : p.StronglyExitless)
    (hdeficit : componentPieceDeficit p = 1)
    (hlast : componentLastFullBit p (by omega) hp = 0) :
    ∃ piece : ComponentIntervalPiece p,
      piece.stop = componentClassCount p ∧ piece.deficit = 1 := by
  have hreverseNe :
      (componentIntervalPieces p (by omega : 1 ≤ k) hp).reverse ≠ [] := by
    simp [componentIntervalPieces_ne_nil (by omega : 1 ≤ k) hp]
  obtain ⟨piece, rest, hreverse⟩ := List.exists_cons_of_ne_nil hreverseNe
  have hpartial : piece.deficit ≠ 0 := by
    unfold componentLastFullBit lastNatValue firstNatValue at hlast
    rw [hreverse] at hlast
    change (if piece.deficit = 0 then 1 else 0) = 0 at hlast
    intro hzero
    simp [hzero] at hlast
  have htotal := componentIntervalPieces_totalDeficit hk hp
  rw [hdeficit] at htotal
  unfold pieceListTotalDeficit at htotal
  have hreverseSum :
      ((componentIntervalPieces p (by omega : 1 ≤ k) hp).reverse.map
        ComponentIntervalPiece.deficit).sum = 1 := by
    rw [List.map_reverse, List.sum_reverse]
    exact htotal
  rw [hreverse, List.map_cons, List.sum_cons] at hreverseSum
  have hone : piece.deficit = 1 := by omega
  have hstops := componentIntervalPieces_stops p (by omega) hp
  have hrevStops := congrArg List.reverse hstops
  have hstop : piece.stop = componentClassCount p := by
    rw [← List.map_reverse, hreverse] at hrevStops
    have hhead := congrArg List.head? hrevStops
    simpa [componentPieceStops] using hhead
  exact ⟨piece, hstop, hone⟩

/-- The terminal deficit-one piece is exposed as actual block coordinates,
so an augmentation can later retain its `psi` visit. -/
theorem component_deficit_one_terminal_segment
    (hk : 4 ≤ k) {p : HPath k} (hp : p.StronglyExitless)
    (hdeficit : componentPieceDeficit p = 1)
    (hlast : componentLastFullBit p (by omega) hp = 0) :
    ∃ start, start + (k - 2) = componentClassCount p ∧
      ∀ r, 1 ≤ r → r ≤ k - 3 →
        Hunter.ProofsLedger.IsDoor p (start + r) := by
  obtain ⟨piece, hstop, hpiece⟩ :=
    component_deficit_one_terminal_piece hk hp hdeficit hlast
  have hsize := ComponentIntervalPiece.size_add_deficit hk hp piece
  rw [hpiece] at hsize
  have hpieceSize : piece.stop - piece.start = k - 2 := by
    simp only [ComponentIntervalPiece.size, actualPieceSize] at hsize
    omega
  have hend : piece.start + (k - 2) = componentClassCount p := by
    have hn := piece.valid.nonempty
    omega
  refine ⟨piece.start, hend, ?_⟩
  intro r hr1 hr2
  exact piece.valid.doors r hr1 (by omega)

end Haruhi
