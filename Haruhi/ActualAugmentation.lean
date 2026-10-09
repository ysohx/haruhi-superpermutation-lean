import Haruhi.Augmentation
import Haruhi.Terminal
import PreimageChain.PathwiseAssemblyCore

/-! # Actual augmentation of every non-root Hunter component

The predecessor is selected from the original Hamilton path through the proved
chain-end/tail bijection. No external existence hypothesis is supplied.
-/
namespace Haruhi
open Hunter PreimageChain Hunter.ProofsPu
open scoped Classical BigOperators
variable {k : ℕ} {P : HPath k}

noncomputable def actualNewTail (hP : P.IsHamiltonian) (hk : 2 ≤ k)
    (C : ActualComponent P) (hne : C ≠ actualRootComponent hP hk) :
    {a : Vtx k // a ∈ tails (F P) \ tails P.edges} := by
  refine ⟨actualComponentTail hP C, Finset.mem_sdiff.mpr ⟨
    actualComponentTail_mem_tails hP C, ?_⟩⟩
  rw [Hunter.ProofsWP.tails_edges_ham hP, Finset.mem_singleton]
  intro heq
  apply hne
  apply actualComponentTail_injective hP
  rw [actualComponentTail_root hP hk]
  exact heq

noncomputable def actualEntrySlot (hP : P.IsHamiltonian) (hk : 2 ≤ k)
    (C : ActualComponent P) (hne : C ≠ actualRootComponent hP hk) :
    {v : Vtx k // v ∈ chainEnds P ∧ v ≠ P.last} :=
  (chainTargetTailEquiv hP).symm (actualNewTail hP hk C hne)

/-- Actual non-root components are in bijection with the new tails. -/
noncomputable def actualNonRootTailEquiv (hP : P.IsHamiltonian) (hk : 2 ≤ k) :
    {C : ActualComponent P // C ≠ actualRootComponent hP hk} ≃
      {a : Vtx k // a ∈ tails (F P) \ tails P.edges} := by
  apply Equiv.ofBijective (fun C => actualNewTail hP hk C.1 C.2)
  constructor
  · intro C D heq
    apply Subtype.ext
    apply actualComponentTail_injective hP
    exact congrArg Subtype.val heq
  · intro a
    let C := (actualComponentTailEquiv hP hk).symm
      ⟨a.1, (Finset.mem_sdiff.mp a.2).1⟩
    have htail : actualComponentTail hP C = a.1 := by
      exact congrArg Subtype.val ((actualComponentTailEquiv hP hk).apply_symm_apply
        ⟨a.1, (Finset.mem_sdiff.mp a.2).1⟩)
    have hne : C ≠ actualRootComponent hP hk := by
      intro heq
      have ha := (Finset.mem_sdiff.mp a.2).2
      rw [heq, actualComponentTail_root hP hk] at htail
      apply ha
      rw [← htail, Hunter.ProofsWP.tails_edges_ham hP]
      exact Finset.mem_singleton_self _
    refine ⟨⟨C, hne⟩, ?_⟩
    apply Subtype.ext
    exact htail

/-- The selected predecessors enumerate every nonterminal chain end once. -/
noncomputable def actualEntrySlotEquiv (hP : P.IsHamiltonian) (hk : 2 ≤ k) :
    {C : ActualComponent P // C ≠ actualRootComponent hP hk} ≃
      {v : Vtx k // v ∈ chainEnds P ∧ v ≠ P.last} :=
  (actualNonRootTailEquiv hP hk).trans (chainTargetTailEquiv hP).symm

@[simp] theorem actualEntrySlotEquiv_apply (hP : P.IsHamiltonian) (hk : 2 ≤ k)
    (C : {C : ActualComponent P // C ≠ actualRootComponent hP hk}) :
    actualEntrySlotEquiv hP hk C = actualEntrySlot hP hk C.1 C.2 := rfl

theorem actualEntrySlot_target (hP : P.IsHamiltonian) (hk : 2 ≤ k)
    (C : ActualComponent P) (hne : C ≠ actualRootComponent hP hk) :
    (chainTargetTail hP (actualEntrySlot hP hk C hne)).1 =
      actualComponentTail hP C := by
  exact congrArg Subtype.val ((chainTargetTailEquiv hP).apply_symm_apply
    (actualNewTail hP hk C hne))

theorem actualEntrySlot_edge (hP : P.IsHamiltonian) (hk : 2 ≤ k)
    (C : ActualComponent P) (hne : C ≠ actualRootComponent hP hk) :
    ((actualEntrySlot hP hk C hne).1, actualComponentTail hP C) ∈
      E1removed P (Sset P) := by
  have h := chainTargetTail_spec hP (actualEntrySlot hP hk C hne)
  rwa [actualEntrySlot_target hP hk C hne] at h

theorem actualEntrySlot_outside (hP : P.IsHamiltonian) (hk : 2 ≤ k)
    (C : ActualComponent P) (hne : C ≠ actualRootComponent hP hk) :
    (actualEntrySlot hP hk C hne).1 ∉ (actualComponentPath hP C).verts := by
  have h := actual_tail_predecessor_outside hP C
    (E1removed_subset P (Sset P) (actualEntrySlot_edge hP hk C hne))
  rw [← HPath.mem_vertsFinset, actualComponentPath_vertsFinset hP C]
  exact h

theorem actualAugmentation_exists (hP : P.IsHamiltonian) (hk : 2 ≤ k)
    (C : ActualComponent P) (hne : C ≠ actualRootComponent hP hk) :
    ∃ q : HPath k,
      q.verts = orbitList (sigma (actualEntrySlot hP hk C hne).1) ++
        (actualComponentPath hP C).verts ∧
      q.StronglyExitless ∧
      q.numVerts = (actualComponentPath hP C).numVerts + k ∧
      q.wtP = (k - 1) +
        ew k (actualEntrySlot hP hk C hne).1 (actualComponentTail hP C) +
        (actualComponentPath hP C).wtP ∧
      q.last = actualComponentHead hP C := by
  obtain ⟨q, hv, hs, hn, hw, hl⟩ := prepend_orbit_strong_exists hk
    (actualComponentPath_stronglyExitless hP hk C)
    (actualEntrySlot_outside hP hk C hne)
  rw [actualComponentPath_first hP C] at hw
  rw [actualComponentPath_last hP C] at hl
  exact ⟨q, hv, hs, hn, hw, hl⟩

noncomputable def actualAugmentedPath (hP : P.IsHamiltonian) (hk : 2 ≤ k)
    (C : ActualComponent P) : HPath k :=
  if hroot : C = actualRootComponent hP hk then actualComponentPath hP C
  else Classical.choose (actualAugmentation_exists hP hk C hroot)

theorem actualAugmentedPath_root (hP : P.IsHamiltonian) (hk : 2 ≤ k) :
    actualAugmentedPath hP hk (actualRootComponent hP hk) =
      actualComponentPath hP (actualRootComponent hP hk) := by
  simp [actualAugmentedPath]

theorem actualAugmentedPath_stronglyExitless (hP : P.IsHamiltonian) (hk : 2 ≤ k)
    (C : ActualComponent P) : (actualAugmentedPath hP hk C).StronglyExitless := by
  unfold actualAugmentedPath
  split
  · exact actualComponentPath_stronglyExitless hP hk C
  · exact (Classical.choose_spec (actualAugmentation_exists hP hk C ‹_›)).2.1

theorem actualAugmentedPath_classCount (hP : P.IsHamiltonian) (hk : 2 ≤ k)
    (C : ActualComponent P) :
    componentClassCount (actualAugmentedPath hP hk C) =
      componentClassCount (actualComponentPath hP C) +
      if C = actualRootComponent hP hk then 0 else 1 := by
  by_cases hc : C = actualRootComponent hP hk
  · simp [actualAugmentedPath, hc]
  · simp only [actualAugmentedPath, dif_neg hc, if_neg hc]
    exact prepend_orbit_classCount (by omega)
      (Classical.choose_spec (actualAugmentation_exists hP hk C hc)).2.2.1

theorem actualAugmentedPath_last (hP : P.IsHamiltonian) (hk : 2 ≤ k)
    (C : ActualComponent P) :
    (actualAugmentedPath hP hk C).last = actualComponentHead hP C := by
  by_cases hc : C = actualRootComponent hP hk
  · simp only [actualAugmentedPath, dif_pos hc]
    exact actualComponentPath_last hP C
  · simp only [actualAugmentedPath, dif_neg hc]
    exact (Classical.choose_spec (actualAugmentation_exists hP hk C hc)).2.2.2.2

theorem actualAugmentedPath_weight (hP : P.IsHamiltonian) (hk : 2 ≤ k)
    (C : ActualComponent P) :
    (actualAugmentedPath hP hk C).wtP =
      (actualComponentPath hP C).wtP +
      if hc : C = actualRootComponent hP hk then 0 else
        (k - 1) + ew k (actualEntrySlot hP hk C hc).1 (actualComponentTail hP C) := by
  by_cases hc : C = actualRootComponent hP hk
  · simp [actualAugmentedPath, hc]
  · simp only [actualAugmentedPath, dif_neg hc]
    have hw := (Classical.choose_spec (actualAugmentation_exists hP hk C hc)).2.2.2.1
    omega

end Haruhi
