import Haruhi.ActualAugmentation
import Haruhi.GraphAccounting

/-! # Counting actual new heads through direct transformation slots -/
namespace Haruhi
open Hunter PreimageChain
open scoped Classical BigOperators
variable {k : ℕ} {P : HPath k}

noncomputable def actualEndTarget (hP : P.IsHamiltonian) (hk : 2 ≤ k)
    (e : {v : Vtx k // v ∈ chainEnds P ∧ v ≠ P.last}) : ActualComponent P :=
  ((actualEntrySlotEquiv hP hk).symm e).1

theorem actualEndTarget_injective (hP : P.IsHamiltonian) (hk : 2 ≤ k) :
    Function.Injective (actualEndTarget hP hk) := by
  intro e f hef
  apply (actualEntrySlotEquiv hP hk).symm.injective
  exact Subtype.ext hef

theorem actualEndTarget_tail (hP : P.IsHamiltonian) (hk : 2 ≤ k)
    (e : {v : Vtx k // v ∈ chainEnds P ∧ v ≠ P.last}) :
    actualComponentTail hP (actualEndTarget hP hk e) = (chainTargetTail hP e).1 := by
  let C := (actualEntrySlotEquiv hP hk).symm e
  have he : actualEntrySlot hP hk C.1 C.2 = e := by
    exact (actualEntrySlotEquiv hP hk).apply_symm_apply e
  have ht := actualEntrySlot_target hP hk C.1 C.2
  rw [he] at ht
  exact ht.symm

theorem continuing_start_has_edge
    (s : {v : Vtx k // v ∈ chainStarts P}) (hne : s.1 ∉ chainEnds P) :
    ∃ d : ↑(chainGraph P), d.1.1 = s.1 := by
  have hout : outV (chainGraph P) s.1 ≠ ∅ := by
    intro he
    apply hne
    exact mem_chainEnds.mpr ⟨(mem_chainStarts.mp s.2).1, he⟩
  obtain ⟨d, hd⟩ := Finset.nonempty_iff_ne_empty.mpr hout
  rw [outV, mem_out] at hd
  exact ⟨⟨d, hd.1⟩, Finset.mem_singleton.mp hd.2⟩

/-- If every direct nonterminal slot from a selected source lands in `bad`,
selected sources are bounded by bad targets, internal edges, and the last slot. -/
theorem actual_selected_start_count
    (hP : P.IsHamiltonian) (hk : 2 ≤ k)
    (selected : Finset {v : Vtx k // v ∈ chainStarts P})
    (bad : Finset (ActualComponent P))
    (habsorb : ∀ s ∈ selected, ∀ he : s.1 ∈ chainEnds P,
      ∀ hn : s.1 ≠ P.last, actualEndTarget hP hk ⟨s.1, he, hn⟩ ∈ bad) :
    (selected.card : ℤ) ≤ (bad.card : ℤ) + actualXi P + actualIndicator P := by
  let continuing := selected.filter fun s => s.1 ∉ chainEnds P
  let ending := selected.filter fun s => s.1 ∈ chainEnds P
  let exiting := ending.filter fun s => s.1 ≠ P.last
  let finishing := ending.filter fun s => s.1 = P.last
  have hpartition : continuing.card + ending.card = selected.card := by
    simpa [continuing, ending, Nat.add_comm] using
      Finset.card_filter_add_card_filter_not (s := selected)
        (fun s => s.1 ∈ chainEnds P)
  have hendpart : exiting.card + finishing.card = ending.card := by
    simpa [exiting, finishing, Nat.add_comm] using
      Finset.card_filter_add_card_filter_not (s := ending)
        (fun s => s.1 = P.last)
  have hcontinuing : continuing.card ≤ (chainGraph P).card := by
    let f : ↑continuing → ↑(chainGraph P) := fun s =>
      Classical.choose (continuing_start_has_edge s.1 (Finset.mem_filter.mp s.2).2)
    have hf : ∀ s : ↑continuing, (f s).1.1 = s.1.1 := fun s =>
      Classical.choose_spec (continuing_start_has_edge s.1 (Finset.mem_filter.mp s.2).2)
    have hinj : Function.Injective f := by
      intro s t heq
      apply Subtype.ext
      apply Subtype.ext
      calc s.1.1 = (f s).1.1 := (hf s).symm
           _ = (f t).1.1 := by rw [heq]
           _ = t.1.1 := hf t
    simpa using Fintype.card_le_of_injective f hinj
  have hexiting : exiting.card ≤ bad.card := by
    let endOf : ↑exiting → {v : Vtx k // v ∈ chainEnds P ∧ v ≠ P.last} := fun s =>
      ⟨s.1.1, (Finset.mem_filter.mp (Finset.mem_filter.mp s.2).1).2,
        (Finset.mem_filter.mp s.2).2⟩
    let f : ↑exiting → ↑bad := fun s =>
      ⟨actualEndTarget hP hk (endOf s), habsorb s.1
        (Finset.mem_filter.mp (Finset.mem_filter.mp s.2).1).1
        (endOf s).2.1 (endOf s).2.2⟩
    have hinj : Function.Injective f := by
      intro s t heq
      have ht : actualEndTarget hP hk (endOf s) = actualEndTarget hP hk (endOf t) :=
        congrArg (fun x : ↑bad => (x.1 : ActualComponent P)) heq
      have he := actualEndTarget_injective hP hk ht
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun v : {v : Vtx k // v ∈ chainEnds P ∧ v ≠ P.last} => v.1) he
    simpa using Fintype.card_le_of_injective f hinj
  have hfinishing : finishing.card ≤ indicatorI P (Sset P) := by
    by_cases hlast : P.last ∈ Sset P
    · have hone : finishing.card ≤ 1 := by
        rw [Finset.card_le_one]
        intro s hs t ht
        apply Subtype.ext
        exact (Finset.mem_filter.mp hs).2.trans (Finset.mem_filter.mp ht).2.symm
      simpa [indicatorI, hlast] using hone
    · have hempty : finishing = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro s hs
        have heq := (Finset.mem_filter.mp hs).2
        apply hlast
        rw [← heq]
        exact (mem_chainStarts.mp s.2).1
      simp [hempty]
  have hxi := actual_xi_bounds_internal_count (P := P) (by omega : 1 ≤ k)
  unfold actualIndicator
  omega

/-- Every selected component with a genuinely new head corresponds to one
selected start slot, and no two components use the same source slot. -/
theorem actual_source_image_eq
    (hP : P.IsHamiltonian) (hk : 2 ≤ k)
    (good : Finset (ActualComponent P))
    (hnew : ∀ C ∈ good, actualComponentHead hP C ≠ P.last) :
    ((Finset.univ.filter fun s : {v : Vtx k // v ∈ chainStarts P} =>
      actualChainSourceComponent hP hk s ∈ good).image
      (actualChainSourceComponent hP hk)) = good := by
  ext C
  constructor
  · intro hc
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hc
    exact (Finset.mem_filter.mp hs).2
  · intro hc
    have hhead : actualComponentHead hP C ∈ heads (F P) \ heads P.edges := by
      apply Finset.mem_sdiff.mpr
      refine ⟨actualComponentHead_mem_heads hP C, ?_⟩
      rw [Hunter.ProofsWP.heads_edges_ham hP, Finset.mem_singleton]
      exact hnew C hc
    obtain ⟨s, hs⟩ := chainSourceHead_surjective hP ⟨actualComponentHead hP C, hhead⟩
    have hC : actualChainSourceComponent hP hk s = C := by
      apply actualComponentHead_injective hP
      rw [actualChainSourceComponent_head hP hk]
      exact congrArg Subtype.val hs
    apply Finset.mem_image.mpr
    exact ⟨s, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rwa [hC]⟩, hC⟩

theorem actual_good_component_count
    (hP : P.IsHamiltonian) (hk : 2 ≤ k)
    (good bad : Finset (ActualComponent P))
    (hnew : ∀ C ∈ good, actualComponentHead hP C ≠ P.last)
    (habsorb : ∀ s : {v : Vtx k // v ∈ chainStarts P},
      actualChainSourceComponent hP hk s ∈ good →
      ∀ he : s.1 ∈ chainEnds P, ∀ hn : s.1 ≠ P.last,
        actualEndTarget hP hk ⟨s.1, he, hn⟩ ∈ bad) :
    (good.card : ℤ) ≤ (bad.card : ℤ) + actualXi P + actualIndicator P := by
  let selected := Finset.univ.filter fun s : {v : Vtx k // v ∈ chainStarts P} =>
    actualChainSourceComponent hP hk s ∈ good
  have hc : selected.card = good.card := by
    rw [← actual_source_image_eq hP hk good hnew,
      Finset.card_image_of_injective _ (actualChainSourceComponent_injective hP hk)]
  rw [← hc]
  apply actual_selected_start_count hP hk selected bad
  intro s hs he hn
  exact habsorb s (Finset.mem_filter.mp hs).2 he hn

end Haruhi
