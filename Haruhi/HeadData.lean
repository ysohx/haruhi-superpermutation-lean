import Haruhi.GraphAccounting

/-! # Actual selected head data and the exact corrected residual budget -/
namespace Haruhi
open Hunter PreimageChain
open scoped Classical BigOperators
variable {k : ℕ} {P : HPath k}

noncomputable def actualNewHead (hP : P.IsHamiltonian)
    (C : ActualComponent P) (hne : actualComponentHead hP C ≠ P.last) :
    {b : Vtx k // b ∈ heads (F P) \ heads P.edges} := by
  refine ⟨actualComponentHead hP C, Finset.mem_sdiff.mpr
    ⟨actualComponentHead_mem_heads hP C, ?_⟩⟩
  rwa [Hunter.ProofsWP.heads_edges_ham hP, Finset.mem_singleton]

noncomputable def actualHeadSlot (hP : P.IsHamiltonian) (_hk : 2 ≤ k)
    (C : ActualComponent P) (hne : actualComponentHead hP C ≠ P.last) :
    {v : Vtx k // v ∈ chainStarts P} :=
  (chainSourceHeadEquiv hP).symm (actualNewHead hP C hne)

theorem actualHeadSlot_source (hP : P.IsHamiltonian) (hk : 2 ≤ k)
    (C : ActualComponent P) (hne : actualComponentHead hP C ≠ P.last) :
    (chainSourceHead hP (actualHeadSlot hP hk C hne)).1 = actualComponentHead hP C :=
  congrArg Subtype.val ((chainSourceHeadEquiv hP).apply_symm_apply (actualNewHead hP C hne))

theorem actualHeadSlot_edge (hP : P.IsHamiltonian) (hk : 2 ≤ k)
    (C : ActualComponent P) (hne : actualComponentHead hP C ≠ P.last) :
    (actualComponentHead hP C, sigma (actualHeadSlot hP hk C hne).1) ∈ P.edges := by
  have he := chainSourceHead_spec hP (actualHeadSlot hP hk C hne)
  rw [actualHeadSlot_source] at he
  exact E2removed_subset P (Sset P) he

noncomputable def actualNewHeadEquiv (hP : P.IsHamiltonian) (hk : 2 ≤ k) :
    {C : ActualComponent P // actualComponentHead hP C ≠ P.last} ≃
      {b : Vtx k // b ∈ heads (F P) \ heads P.edges} := by
  apply Equiv.ofBijective (fun C => actualNewHead hP C.1 C.2)
  constructor
  · intro C D heq
    apply Subtype.ext
    apply actualComponentHead_injective hP
    exact congrArg Subtype.val heq
  · intro b
    let C := (actualComponentHeadEquiv hP hk).symm
      ⟨b.1, (Finset.mem_sdiff.mp b.2).1⟩
    have hhead : actualComponentHead hP C = b.1 :=
      congrArg Subtype.val ((actualComponentHeadEquiv hP hk).apply_symm_apply
        ⟨b.1, (Finset.mem_sdiff.mp b.2).1⟩)
    have hne : actualComponentHead hP C ≠ P.last := by
      rw [hhead]
      have hb := (Finset.mem_sdiff.mp b.2).2
      simpa only [Hunter.ProofsWP.heads_edges_ham hP, Finset.mem_singleton] using hb
    refine ⟨⟨C, hne⟩, ?_⟩
    apply Subtype.ext
    exact hhead

noncomputable def actualHeadSlotEquiv (hP : P.IsHamiltonian) (hk : 2 ≤ k) :
    {C : ActualComponent P // actualComponentHead hP C ≠ P.last} ≃
      {v : Vtx k // v ∈ chainStarts P} :=
  (actualNewHeadEquiv hP hk).trans (chainSourceHeadEquiv hP).symm

@[simp] theorem actualHeadSlotEquiv_apply (hP : P.IsHamiltonian) (hk : 2 ≤ k)
    (C : {C : ActualComponent P // actualComponentHead hP C ≠ P.last}) :
    actualHeadSlotEquiv hP hk C = actualHeadSlot hP hk C.1 C.2 := rfl

noncomputable def actualHeadExcess {P : HPath 14} (hP : P.IsHamiltonian)
    (C : ActualComponent P) : ℤ :=
  if hc : actualComponentHead hP C = P.last then 0 else
    (ew 14 (actualComponentHead hP C) (sigma (actualHeadSlot hP (by decide) C hc).1) : ℤ) - 2

theorem actualHeadExcess_eq_weight {P : HPath 14} (hP : P.IsHamiltonian)
    (C : ActualComponent P) (hne : actualComponentHead hP C ≠ P.last) :
    actualHeadExcess hP C =
      (ew 14 (actualComponentHead hP C) (sigma (actualHeadSlot hP (by decide) C hne).1) : ℤ) - 2 := by
  exact dif_neg hne

theorem actualHeadExcess_nonneg {P : HPath 14} (hP : P.IsHamiltonian)
    (C : ActualComponent P) : 0 ≤ actualHeadExcess hP C := by
  unfold actualHeadExcess
  split
  · omega
  · rename_i hc
    have h := chainEntry_excess_nonneg hP (by decide : 2 ≤ 14)
      (actualHeadSlot hP (by decide) C hc)
    rwa [actualHeadSlot_source] at h

theorem actualHeadExcess_sum {P : HPath 14} (hP : P.IsHamiltonian) :
    (∑ C : ActualComponent P, actualHeadExcess hP C) = actualTheta hP := by
  unfold actualHeadExcess
  have hsplit := sum_dite_zero_eq_subtype
    (fun C : ActualComponent P => actualComponentHead hP C = P.last)
    (fun C => (ew 14 (actualComponentHead hP C.1)
      (sigma (actualHeadSlot hP (by decide) C.1 C.2).1) : ℤ) - 2)
  calc
    _ = ∑ C : {C : ActualComponent P // actualComponentHead hP C ≠ P.last},
      ((ew 14 (actualComponentHead hP C.1)
        (sigma (actualHeadSlot hP (by decide) C.1 C.2).1) : ℤ) - 2) := by
      convert hsplit using 1 <;> apply Finset.sum_congr
      all_goals first | (ext; simp) | (intro C _; first | rfl | (split_ifs <;> rfl))
    _ = actualTheta hP := by
      unfold actualTheta
      apply Fintype.sum_equiv (actualHeadSlotEquiv hP (by decide))
      intro C
      rw [actualHeadSlotEquiv_apply, actualHeadSlot_source]

noncomputable def actualOriginalHeadBit {P : HPath 14} (hP : P.IsHamiltonian)
    (C : ActualComponent P) : ℤ := if actualComponentHead hP C = P.last then 1 else 0

theorem actualOriginalHeadBit_sum {P : HPath 14} (hP : P.IsHamiltonian) :
    (∑ C : ActualComponent P, actualOriginalHeadBit hP C) = 1 - actualIndicator P := by
  have hnew : (∑ C : ActualComponent P,
      if actualComponentHead hP C = P.last then (0 : ℤ) else 1) =
      (numComps (F P) : ℤ) - 1 + actualIndicator P := by
    have hs := sum_dite_zero_eq_subtype
      (fun C : ActualComponent P => actualComponentHead hP C = P.last) (fun _ => (1 : ℤ))
    have hcast : (Fintype.card {C : ActualComponent P // actualComponentHead hP C ≠ P.last} : ℤ) =
        (numComps (F P) : ℤ) - 1 + actualIndicator P := by
      rw [Fintype.card_congr (actualHeadSlotEquiv hP (by decide))]
      exact actual_start_count_int hP (by decide)
    calc
      _ = ∑ _C : {C : ActualComponent P // actualComponentHead hP C ≠ P.last}, (1 : ℤ) := by
        convert hs using 1 <;> apply Finset.sum_congr
        all_goals first | (ext; simp) | (intro C _; first | rfl | (split_ifs <;> rfl))
      _ = _ := by simpa using hcast
  have hsum : (∑ C : ActualComponent P, actualOriginalHeadBit hP C) +
      (∑ C : ActualComponent P, if actualComponentHead hP C = P.last then (0 : ℤ) else 1) =
      (numComps (F P) : ℤ) := by
    rw [← Finset.sum_add_distrib]
    have hp : ∀ C : ActualComponent P, actualOriginalHeadBit hP C +
        (if actualComponentHead hP C = P.last then (0 : ℤ) else 1) = 1 := by
      intro C
      unfold actualOriginalHeadBit
      split_ifs <;> norm_num
    simp_rw [hp]
    simp [ActualComponent, numComps]
  linarith

noncomputable def actualResidual {P : HPath 14} (hP : P.IsHamiltonian)
    (C : ActualComponent P) : ℤ :=
  6 * actualAugmentedLoss hP C + 6 + 6 * actualOriginalHeadBit hP C -
    actualAugmentedX hP C - 65 * actualAugmentedEta hP C + 6 * actualHeadExcess hP C

theorem actualResidual_sum {P : HPath 14} (hP : P.IsHamiltonian) :
    (∑ C : ActualComponent P, actualResidual hP C) =
      6 * (∑ C : ActualComponent P, actualAugmentedLoss hP C) +
        6 * (numComps (F P) : ℤ) + 6 - 6 * actualIndicator P -
        (∑ C : ActualComponent P, actualAugmentedX hP C) -
        65 * (∑ C : ActualComponent P, actualAugmentedEta hP C) + 6 * actualTheta hP := by
  simp only [actualResidual, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [actualOriginalHeadBit_sum hP, actualHeadExcess_sum hP]
  simp only [ActualComponent, Fintype.card_coe, numComps]
  ring

theorem actual_exact_budget {P : HPath 14} (hP : P.IsHamiltonian) :
    77 * actualDelta P - 479001600 + 12 =
      (∑ C : ActualComponent P, actualResidual hP C) +
        65 * (∑ C : ActualComponent P, actualAugmentedEta hP C) +
        71 * actualTheta hP + 77 * actualXi P + 83 * actualIndicator P := by
  exact exact_budget_int (actual_augmented_x_sum hP) (actual_augmented_master hP)
    (actualResidual_sum hP) rfl

/-- A standard component has a genuinely new cheap head and zero local charge. -/
def actualStandard {P : HPath 14} (hP : P.IsHamiltonian) (C : ActualComponent P) : Prop :=
  actualComponentHead hP C ≠ P.last ∧ actualResidual hP C = 0 ∧
    actualAugmentedEta hP C = 0 ∧ actualHeadExcess hP C = 0

noncomputable def actualGood {P : HPath 14} (hP : P.IsHamiltonian) : Finset (ActualComponent P) :=
  Finset.univ.filter (actualStandard hP)

noncomputable def actualBad {P : HPath 14} (hP : P.IsHamiltonian) : Finset (ActualComponent P) :=
  Finset.univ \ actualGood hP

@[simp] theorem mem_actualGood {P : HPath 14} (hP : P.IsHamiltonian) (C : ActualComponent P) :
    C ∈ actualGood hP ↔ actualStandard hP C := by simp [actualGood]

@[simp] theorem mem_actualBad {P : HPath 14} (hP : P.IsHamiltonian) (C : ActualComponent P) :
    C ∈ actualBad hP ↔ ¬ actualStandard hP C := by simp [actualBad]

theorem actual_good_bad_partition {P : HPath 14} (hP : P.IsHamiltonian) :
    (numComps (F P) : ℤ) = ((actualGood hP).card : ℤ) + ((actualBad hP).card : ℤ) := by
  have hc : (actualGood hP).card + (actualBad hP).card = Fintype.card (ActualComponent P) := by
    have hh := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ (actualGood hP))
    simpa only [actualBad, Finset.card_univ, Nat.add_comm] using hh
  have hcast : ((actualGood hP).card : ℤ) + ((actualBad hP).card : ℤ) =
      (Fintype.card (ActualComponent P) : ℤ) := by exact_mod_cast hc
  simpa only [ActualComponent, Fintype.card_coe, numComps] using hcast.symm

/-- Each nonstandard component pays at least one unit, except the original head
which pays its unique endpoint bit. Residual nonnegativity is supplied by actual
component capacity, so this counting lemma introduces no geometric premise. -/
theorem actual_bad_count {P : HPath 14} (hP : P.IsHamiltonian)
    (hres : ∀ C : ActualComponent P, 0 ≤ actualResidual hP C) :
    ((actualBad hP).card : ℤ) ≤
      (∑ C : ActualComponent P, actualResidual hP C) +
        (∑ C : ActualComponent P, actualAugmentedEta hP C) +
        actualTheta hP + 1 - actualIndicator P := by
  have hpoint : ∀ C : ActualComponent P,
      (if C ∈ actualBad hP then (1 : ℤ) else 0) ≤
      actualResidual hP C + actualAugmentedEta hP C +
        actualHeadExcess hP C + actualOriginalHeadBit hP C := by
    intro C
    have hr := hres C
    have he := actualAugmentedEta_nonneg hP C
    have hq := actualHeadExcess_nonneg hP C
    have ho : 0 ≤ actualOriginalHeadBit hP C := by
      unfold actualOriginalHeadBit
      split_ifs <;> omega
    by_cases hb : C ∈ actualBad hP
    · rw [if_pos hb]
      have hnot := (mem_actualBad hP C).mp hb
      by_cases hc : actualComponentHead hP C = P.last
      · have hbit : actualOriginalHeadBit hP C = 1 := by simp [actualOriginalHeadBit, hc]
        omega
      · have hbit : actualOriginalHeadBit hP C = 0 := by simp [actualOriginalHeadBit, hc]
        by_contra hn
        have hr0 : actualResidual hP C = 0 := by omega
        have he0 : actualAugmentedEta hP C = 0 := by omega
        have hq0 : actualHeadExcess hP C = 0 := by omega
        exact hnot ⟨hc, hr0, he0, hq0⟩
    · rw [if_neg hb]
      omega
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun C _ => hpoint C)
  have hind : (∑ C : ActualComponent P,
      if C ∈ actualBad hP then (1 : ℤ) else 0) = ((actualBad hP).card : ℤ) := by
    rw [← Finset.sum_filter]
    have hf : Finset.univ.filter (fun C : ActualComponent P => C ∈ actualBad hP) = actualBad hP := by
      ext C
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hf]
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
  rw [hind] at hsum
  simp only [Finset.sum_add_distrib] at hsum
  rw [actualHeadExcess_sum hP, actualOriginalHeadBit_sum hP] at hsum
  linarith

end Haruhi
