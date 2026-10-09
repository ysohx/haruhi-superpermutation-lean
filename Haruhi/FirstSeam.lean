import Haruhi.AugmentedTerminal
import Haruhi.ComponentCapacity
import Haruhi.ZeroRigidity

/-! A standard augmented target uses an actual selected weight-two entry. -/
namespace Haruhi
open Hunter PreimageChain Hunter.ProofsPu
open scoped Classical
variable {k : ℕ}

/-- A full first actual interval piece contains the first block-boundary door. -/
theorem componentFirstFullBit_one_first_door
    (hk : 4 ≤ k) {p : HPath k} (hp : p.StronglyExitless)
    (hbit : componentFirstFullBit p (by omega) hp = 1) :
    Hunter.ProofsLedger.IsDoor p 1 := by
  obtain ⟨first, rest, hpieces⟩ :=
    List.exists_cons_of_ne_nil (componentIntervalPieces_ne_nil (by omega) hp)
  have hdeficit : first.deficit = 0 := by
    unfold componentFirstFullBit firstNatValue at hbit
    rw [hpieces] at hbit
    change (if first.deficit = 0 then 1 else 0) = 1 at hbit
    by_cases hzero : first.deficit = 0
    · exact hzero
    · simp [hzero] at hbit
  have hstart : first.start = 0 := by
    have hstarts := componentIntervalPieces_starts p (by omega) hp
    rw [hpieces] at hstarts
    have hhead := congrArg List.head? hstarts
    simpa [componentPieceStarts] using hhead
  have hsize := ComponentIntervalPiece.size_add_deficit hk hp first
  rw [hdeficit, Nat.add_zero] at hsize
  simp only [ComponentIntervalPiece.size, actualPieceSize] at hsize
  have hdoor := first.valid.doors 1 (by omega) (by omega)
  simpa only [hstart, Nat.zero_add] using hdoor

/-- Vertex access inside the prepended orbit, for a path given by its actual
vertex list. -/
theorem prepend_orbit_prefix_vert {p q : HPath k} {u : Vtx k}
    (hv : q.verts = orbitList (sigma u) ++ p.verts)
    {i : ℕ} (hi : i < k) : q.vert i = sigma^[i] (sigma u) := by
  have hn : q.numVerts = k + p.numVerts := by
    change q.verts.length = _
    rw [hv, List.length_append, orbitList_length]
    rfl
  have hil : i < (orbitList (sigma u)).length := by
    rw [orbitList_length]
    exact hi
  rw [Hunter.ProofsExitless.vert_getElem q (by rw [hn]; omega)]
  simp only [hv]
  rw [List.getElem_append_left hil, orbitList_getElem (sigma u) hil]

/-- The first augmented seam is the selected original incoming edge, with
exactly its original overlap weight. -/
theorem prepend_orbit_first_boundary_weight
    (hk : 1 ≤ k) {p q : HPath k} {u : Vtx k}
    (hv : q.verts = orbitList (sigma u) ++ p.verts) :
    Hunter.ProofsLedger.bw q 1 = ew k u p.first := by
  have hlastOrbit : sigma^[k - 1] (sigma u) = u := by
    have h1 : sigma u = sigma^[1] u := by rw [Function.iterate_one]
    rw [h1, ← Function.iterate_add_apply sigma (k - 1) 1 u,
      show k - 1 + 1 = k from by omega,
      Hunter.ProofsExitless.sigma_iter_period u]
  have hleft : q.vert (k - 1) = u := by
    rw [prepend_orbit_prefix_vert hv (by omega), hlastOrbit]
  have hright : q.vert k = p.first := by
    have h := prepend_orbit_suffix_vert hv p.numVerts_pos
    simpa only [Nat.add_zero, HPath.vert_zero] using h
  simp only [Hunter.ProofsLedger.bw, Nat.mul_one, hleft, hright]

/-- A full initial piece of a non-root actual augmentation forces its actual
selected incoming edge to have weight two. -/
theorem actualEntrySlot_weight_two_of_augmented_firstFullBit
    {P : HPath k} (hP : P.IsHamiltonian) (hk : 4 ≤ k)
    (C : ActualComponent P) (hne : C ≠ actualRootComponent hP (by omega))
    (hbit : componentFirstFullBit (actualAugmentedPath hP (by omega) C) (by omega)
      (actualAugmentedPath_stronglyExitless hP (by omega) C) = 1) :
    ew k (actualEntrySlot hP (by omega) C hne).1 (actualComponentTail hP C) = 2 := by
  have hdoor := componentFirstFullBit_one_first_door hk
    (actualAugmentedPath_stronglyExitless hP (by omega) C) hbit
  have hverts : (actualAugmentedPath hP (by omega) C).verts =
      orbitList (sigma (actualEntrySlot hP (by omega) C hne).1) ++
        (actualComponentPath hP C).verts := by
    simp only [actualAugmentedPath, dif_neg hne]
    exact (Classical.choose_spec (actualAugmentation_exists hP (by omega) C hne)).1
  unfold Hunter.ProofsLedger.IsDoor at hdoor
  rw [prepend_orbit_first_boundary_weight (by omega) hverts,
    actualComponentPath_first hP C] at hdoor
  exact hdoor

/-- The selected incoming edge of an actual zero-residual target has weight
two, derived from its actual interval-piece geometry. -/
theorem actualEntrySlot_weight_two_of_augmented_zero_residual
    {P : HPath 14} (hP : P.IsHamiltonian) (C : ActualComponent P)
    (hne : C ≠ actualRootComponent hP (by decide))
    (hη : componentSeamResidual (actualAugmentedPath hP (by decide) C) = 0)
    (hlast : componentLastFullBit (actualAugmentedPath hP (by decide) C) (by decide)
      (actualAugmentedPath_stronglyExitless hP (by decide) C) = 0)
    (hzero : 6 * ((componentPieceDeficit (actualAugmentedPath hP (by decide) C) : ℤ) + 1) -
      componentPieceCount (actualAugmentedPath hP (by decide) C) = 0) :
    ew 14 (actualEntrySlot hP (by decide) C hne).1 (actualComponentTail hP C) = 2 := by
  have hp := actualAugmentedPath_stronglyExitless hP (by decide) C
  have hshape := actual_component_zero_shape hp hη hlast hzero
  exact actualEntrySlot_weight_two_of_augmented_firstFullBit hP (by decide) C hne hshape.1

/-- Both ends of the forbidden connector are now actual zero-residual
components, and the selected target edge is recovered canonically from `P`. -/
theorem actual_zero_residual_source_target_incompatible
    {P : HPath 14} (hP : P.IsHamiltonian) (hred : Sigma2Reduced P)
    (C A : ActualComponent P) (hne : A ≠ actualRootComponent hP (by decide))
    (hηC : componentSeamResidual (actualAugmentedPath hP (by decide) C) = 0)
    (hlastC : componentLastFullBit (actualAugmentedPath hP (by decide) C) (by decide)
      (actualAugmentedPath_stronglyExitless hP (by decide) C) = 0)
    (hzeroC : 6 * ((componentPieceDeficit (actualAugmentedPath hP (by decide) C) : ℤ) + 1) -
      componentPieceCount (actualAugmentedPath hP (by decide) C) = 0)
    (hηA : componentSeamResidual (actualAugmentedPath hP (by decide) A) = 0)
    (hlastA : componentLastFullBit (actualAugmentedPath hP (by decide) A) (by decide)
      (actualAugmentedPath_stronglyExitless hP (by decide) A) = 0)
    (hzeroA : 6 * ((componentPieceDeficit (actualAugmentedPath hP (by decide) A) : ℤ) + 1) -
      componentPieceCount (actualAugmentedPath hP (by decide) A) = 0)
    (hentryEdge : (actualComponentHead hP C,
      sigma (actualEntrySlot hP (by decide) A hne).1) ∈ P.edges)
    (hentryWeight : ew 14 (actualComponentHead hP C)
      (sigma (actualEntrySlot hP (by decide) A hne).1) = 2) : False := by
  exact actual_augmented_zero_residual_no_direct_connector hP hred C A
    (actualEntrySlot hP (by decide) A hne).1 hηC hlastC hzeroC hentryEdge hentryWeight
    (E1removed_subset P (Sset P) (actualEntrySlot_edge hP (by decide) A hne))
    (actualEntrySlot_weight_two_of_augmented_zero_residual hP A hne hηA hlastA hzeroA)

end Haruhi
