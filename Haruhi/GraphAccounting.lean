import Haruhi.Arithmetic
import Haruhi.ActualAugmentation
import PreimageChain.EdgePartition
import PreimageChain.PathwiseAssemblyCore

/-!
# Exact accounting for the actual Hunter transformation

These results start with an actual Hamiltonian permutation path. The orbit
augmentation is constructed in `ActualAugmentation`; the final sums and
master identity use those actual paths without supplied accounting data.
-/

namespace Haruhi

open Hunter PreimageChain
open scoped BigOperators Classical

variable {k : ℕ}

/-- Excess on the actual deleted outgoing edges of new component heads. -/
noncomputable def actualTheta {P : HPath k} (hP : P.IsHamiltonian) : ℤ :=
  ∑ v : {v : Vtx k // v ∈ chainStarts P},
    ((ew k (chainSourceHead hP v).1 (sigma v.1) : ℤ) - 2)

/-- Charge on the actual unselected Step-1 edges, indexed by the chain graph. -/
noncomputable def actualXi (P : HPath k) : ℤ :=
  ∑ d ∈ chainGraph P, ((ew k d.1 (sigma d.2) : ℤ) - 1)

/-- Excess above two on the actual edges entering new component tails. -/
noncomputable def actualTailExcess {P : HPath k} (hP : P.IsHamiltonian) : ℤ :=
  ∑ v : {v : Vtx k // v ∈ chainEnds P ∧ v ≠ P.last},
    ((ew k v.1 (chainTargetTail hP v).1 : ℤ) - 2)

noncomputable def actualIndicator (P : HPath k) : ℤ :=
  (indicatorI P (Sset P) : ℤ)

theorem actual_theta_nonneg {P : HPath k}
    (hP : P.IsHamiltonian) (hk : 2 ≤ k) : 0 ≤ actualTheta hP := by
  unfold actualTheta
  exact Finset.sum_nonneg fun v _ => chainEntry_excess_nonneg hP hk v

theorem actual_xi_nonneg {P : HPath k}
    (hk : 1 ≤ k) : 0 ≤ actualXi P := by
  unfold actualXi
  exact Finset.sum_nonneg fun d hd => chainInternal_excess_nonneg hk hd

theorem actual_indicator_nonneg (P : HPath k) : 0 ≤ actualIndicator P := by
  unfold actualIndicator
  exact Int.natCast_nonneg _

/-- Every original edge deleted at a transformation slot has weight at least two. -/
theorem two_le_weight_of_actual_E1
    {P : HPath k} (hk : 1 ≤ k) {e : Vtx k × Vtx k}
    (he : e ∈ E1removed P (Sset P)) : 2 ≤ ew k e.1 e.2 := by
  obtain ⟨heP, heS⟩ := Finset.mem_filter.mp he
  have hpos : 1 ≤ ew k e.1 e.2 :=
    Hunter.ProofsExitless.ew_ge_one hk _ _
  have hne : ew k e.1 e.2 ≠ 1 := by
    intro hone
    have heq : e.2 = sigma e.1 :=
      (Hunter.ProofsExitless.ew_eq_one_iff hk).mp hone
    change (e.1, e.2) ∈ P.edges at heP
    rw [heq] at heP
    exact (Hunter.sset_sPrecond P e.1 heS) heP
  omega

theorem actual_tail_excess_nonneg {P : HPath k}
    (hP : P.IsHamiltonian) (hk : 1 ≤ k) : 0 ≤ actualTailExcess hP := by
  unfold actualTailExcess
  apply Finset.sum_nonneg
  intro v _
  have hw := two_le_weight_of_actual_E1 hk (chainTargetTail_spec hP v)
  exact sub_nonneg.mpr (by exact_mod_cast hw)

/-- Each internal preimage-graph edge consumes at least one unit of xi. -/
theorem actual_xi_bounds_internal_count {P : HPath k}
    (hk : 1 ≤ k) : ((chainGraph P).card : ℤ) ≤ actualXi P := by
  unfold actualXi
  have hsum : (∑ _d ∈ chainGraph P, (1 : ℤ)) ≤
      ∑ d ∈ chainGraph P, ((ew k d.1 (sigma d.2) : ℤ) - 1) := by
    apply Finset.sum_le_sum
    intro d hd
    obtain ⟨hdS, _, hdP⟩ := mem_chainGraph.mp hd
    have he : (d.1, sigma d.2) ∈ E1removed P (Sset P) := by
      exact Finset.mem_filter.mpr ⟨hdP, hdS⟩
    have hw := two_le_weight_of_actual_E1 hk he
    have hwZ : (2 : ℤ) ≤ (ew k d.1 (sigma d.2) : ℤ) := by
      exact_mod_cast hw
    linarith
  simpa using hsum

theorem actual_start_count_int {P : HPath k}
    (hP : P.IsHamiltonian) (hk : 2 ≤ k) :
    (Fintype.card {v : Vtx k // v ∈ chainStarts P} : ℤ) =
      (numComps (F P) : ℤ) - 1 + actualIndicator P := by
  rw [Fintype.card_coe]
  have hc := card_chainStarts hP hk
  have hi := Hunter.ProofsWP.indicatorI_eq_ite hP
  unfold actualIndicator
  by_cases hh : P.last ∈ heads (F P)
  · simp only [hh, if_true] at hc hi
    omega
  · simp only [hh, if_false] at hc hi
    omega

theorem actual_end_count_int {P : HPath k}
    (hP : P.IsHamiltonian) (hk : 2 ≤ k) :
    (Fintype.card {v : Vtx k // v ∈ chainEnds P ∧ v ≠ P.last} : ℤ) =
      (numComps (F P) : ℤ) - 1 := by
  have hc := card_nonterminal_chainEnds hP hk
  omega

/-- Exact edge ledger for an actual Hamiltonian path; no augmented paths assumed. -/
theorem actual_weight_ledger {P : HPath k}
    (hP : P.IsHamiltonian) (hk : 2 ≤ k) :
    (P.wtP : ℤ) = (wEdges (F P) : ℤ) +
      3 * (numComps (F P) : ℤ) - 3 + actualIndicator P +
      actualTheta hP + actualXi P + actualTailExcess hP := by
  have hend := actual_end_count_int hP hk
  have hstart := actual_start_count_int hP hk
  have hexit :
      (∑ v : {v : Vtx k // v ∈ chainEnds P ∧ v ≠ P.last},
        ((ew k v.1 (chainTargetTail hP v).1 : ℤ) - 1)) =
      (numComps (F P) : ℤ) - 1 + actualTailExcess hP := by
    unfold actualTailExcess
    simp only [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul,
      Finset.card_univ]
    linarith
  have hbook := actual_preimage_edge_bookkeeping hP (by omega : 1 ≤ k)
  rw [hexit, sum_chainEntries_eq_baseline_surplus hP] at hbook
  change (P.wtP : ℤ) = (wEdges (F P) : ℤ) +
    (actualXi P + ((numComps (F P) : ℤ) - 1 + actualTailExcess hP)) -
    actualIndicator P +
    (2 * (Fintype.card {v : Vtx k // v ∈ chainStarts P} : ℤ) + actualTheta hP)
    at hbook
  linarith

/-- The actual fourteen-symbol components contain exactly thirteen-factorial classes. -/
theorem actual_class_sum_fourteen {P : HPath 14} (hP : P.IsHamiltonian) :
    (∑ C : ActualComponents P,
      (componentClassCount (actualComponentPath hP C) : ℤ)) = 6227020800 := by
  have hnat := sum_actual_component_classCount_nat hP (by decide : 2 ≤ 14)
  norm_num [Nat.factorial] at hnat
  exact_mod_cast hnat

/-- Actual component weights sum to the image-graph weight. -/
theorem actual_weight_sum {P : HPath k} (hP : P.IsHamiltonian) :
    (∑ C : ActualComponents P, ((actualComponentPath hP C).wtP : ℤ)) =
      (wEdges (F P) : ℤ) :=
  sum_actual_component_weight_int hP

/-- Algebraic helper for the x-ledger. The supplied identity is proved for the
constructed augmentation in `actual_augmented_x_sum` below. -/
theorem actual_x_ledger_from_augmentation {P : HPath 14}
    (hP : P.IsHamiltonian) {δ sumX : ℤ}
    (hδ : δ = (P.wtP : ℤ) + 14 - 93884313611)
    (haugmentedX : sumX = (wEdges (F P) : ℤ) -
      15 * 6227020800 + 3 * (numComps (F P) : ℤ) + actualTailExcess hP) :
    sumX = 479001600 + δ - actualIndicator P - actualTheta hP - actualXi P := by
  have hw := actual_weight_ledger hP (by decide : 2 ≤ 14)
  linarith

theorem sum_dite_zero_eq_subtype {α : Type*} [Fintype α]
    (p : α → Prop) (f : {x : α // ¬ p x} → ℤ) :
    (∑ x : α, if hx : p x then 0 else f ⟨x, hx⟩) =
      ∑ x : {x : α // ¬ p x}, f x := by
  rw [← Fintype.sum_subtype_add_sum_subtype (fun x : α => ¬ p x)]
  have heq : ∀ x : {x : α // ¬¬ p x}, p x.1 := fun x => not_not.mp x.2
  simp only [heq, dif_pos, Finset.sum_const_zero, add_zero]
  apply Finset.sum_congr rfl
  intro x _
  exact dif_neg x.2

theorem sum_except_one_int {α : Type*} [Fintype α] (a : α) :
    (∑ x : α, if x = a then (0 : ℤ) else 1) = (Fintype.card α : ℤ) - 1 := by
  have heq : (∑ x : α, if x = a then (0 : ℤ) else 1) + 1 =
      (Fintype.card α : ℤ) := by
    calc
      _ = ∑ x : α, ((if x = a then (0 : ℤ) else 1) + if x = a then 1 else 0) := by
        simp [Finset.sum_add_distrib]
      _ = ∑ _x : α, (1 : ℤ) := by
        apply Finset.sum_congr rfl
        intro x hx
        split_ifs <;> norm_num
      _ = _ := by simp
  omega

/-- The actual augmentation adds one class at every non-root component. -/
theorem actual_augmented_class_sum {P : HPath k}
    (hP : P.IsHamiltonian) (hk : 2 ≤ k) :
    (∑ C : ActualComponent P,
      (componentClassCount (actualAugmentedPath hP hk C) : ℤ)) =
      ((k - 1).factorial : ℤ) + (numComps (F P) : ℤ) - 1 := by
  have hpoint : ∀ C : ActualComponent P,
      (componentClassCount (actualAugmentedPath hP hk C) : ℤ) =
      (componentClassCount (actualComponentPath hP C) : ℤ) +
        if C = actualRootComponent hP hk then 0 else 1 := by
    intro C
    rw [actualAugmentedPath_classCount hP hk C, Nat.cast_add]
    split_ifs <;> simp
  simp_rw [hpoint]
  have hone : (∑ C : ActualComponent P,
      if C = actualRootComponent hP hk then (0 : ℤ) else 1) =
      (Fintype.card (ActualComponent P) : ℤ) - 1 := by
    convert sum_except_one_int (actualRootComponent hP hk) using 1
    apply Finset.sum_congr
    · ext; simp
    · intro C _; split_ifs <;> rfl
  rw [Finset.sum_add_distrib, hone]
  have hnat := sum_actual_component_classCount_nat hP hk
  have hcast : (∑ C : ActualComponent P,
      (componentClassCount (actualComponentPath hP C) : ℤ)) =
      ((k - 1).factorial : ℤ) := by exact_mod_cast hnat
  rw [hcast]
  simp [ActualComponent, numComps]
  ring

/-- Selected augmentation seams enumerate every nonterminal preimage-chain end. -/
theorem actual_augmented_seam_excess_sum {P : HPath k}
    (hP : P.IsHamiltonian) (hk : 2 ≤ k) :
    (∑ C : {C : ActualComponent P // C ≠ actualRootComponent hP hk},
      ((ew k (actualEntrySlot hP hk C.1 C.2).1 (actualComponentTail hP C.1) : ℤ) - 2)) =
      actualTailExcess hP := by
  unfold actualTailExcess
  apply Fintype.sum_equiv (actualEntrySlotEquiv hP hk)
  intro C
  rw [actualEntrySlotEquiv_apply, actualEntrySlot_target]

/-- Exact total weight added by the actual orbit-prepend construction. -/
theorem actual_augmented_weight_sum {P : HPath k}
    (hP : P.IsHamiltonian) (hk : 2 ≤ k) :
    (∑ C : ActualComponent P, ((actualAugmentedPath hP hk C).wtP : ℤ)) =
      (wEdges (F P) : ℤ) + ((k : ℤ) + 1) * ((numComps (F P) : ℤ) - 1) +
        actualTailExcess hP := by
  have hpoint : ∀ C : ActualComponent P,
      ((actualAugmentedPath hP hk C).wtP : ℤ) =
      ((actualComponentPath hP C).wtP : ℤ) +
      if hc : C = actualRootComponent hP hk then 0 else
        ((k : ℤ) + 1) +
          ((ew k (actualEntrySlot hP hk C hc).1 (actualComponentTail hP C) : ℤ) - 2) := by
    intro C
    rw [actualAugmentedPath_weight hP hk C, Nat.cast_add]
    by_cases hc : C = actualRootComponent hP hk
    · simp only [dif_pos hc, Nat.cast_zero, add_zero]
    · simp only [dif_neg hc, Nat.cast_add, Nat.cast_sub (by omega : 1 ≤ k), Nat.cast_one]
      ring
  simp_rw [hpoint]
  have hsplit : (∑ C : ActualComponent P,
      if hc : C = actualRootComponent hP hk then (0 : ℤ) else
        ((k : ℤ) + 1) +
          ((ew k (actualEntrySlot hP hk C hc).1 (actualComponentTail hP C) : ℤ) - 2)) =
      ∑ C : {C : ActualComponent P // C ≠ actualRootComponent hP hk},
        (((k : ℤ) + 1) +
          ((ew k (actualEntrySlot hP hk C.1 C.2).1 (actualComponentTail hP C.1) : ℤ) - 2)) := by
    convert sum_dite_zero_eq_subtype (fun C : ActualComponent P => C = actualRootComponent hP hk)
      (fun C => ((k : ℤ) + 1) +
        ((ew k (actualEntrySlot hP hk C.1 C.2).1 (actualComponentTail hP C.1) : ℤ) - 2)) using 1
    all_goals
      apply Finset.sum_congr
      · ext; simp
      · intro C _; first | rfl | (split_ifs <;> rfl)
  rw [Finset.sum_add_distrib, actual_weight_sum hP, hsplit]
  rw [Finset.sum_add_distrib, actual_augmented_seam_excess_sum hP hk]
  have hcard : (Fintype.card {C : ActualComponent P // C ≠ actualRootComponent hP hk} : ℤ) =
      (numComps (F P) : ℤ) - 1 := by
    have hc := Fintype.card_congr (actualEntrySlotEquiv hP hk)
    rw [hc]
    exact actual_end_count_int hP hk
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [hcard]
  ring

/-- Actual run-plus-heavy-excess parameter, represented by the exact weight ledger. -/
noncomputable def actualAugmentedX {P : HPath 14} (hP : P.IsHamiltonian)
    (C : ActualComponent P) : ℤ :=
  ((actualAugmentedPath hP (by decide) C).wtP : ℤ) -
    15 * (componentClassCount (actualAugmentedPath hP (by decide) C) : ℤ) + 3

noncomputable def actualAugmentedLoss {P : HPath 14} (hP : P.IsHamiltonian)
    (C : ActualComponent P) : ℤ :=
  13 * actualAugmentedX hP C -
    (componentClassCount (actualAugmentedPath hP (by decide) C) : ℤ)

noncomputable def actualAugmentedEta {P : HPath 14} (hP : P.IsHamiltonian)
    (C : ActualComponent P) : ℤ :=
  (componentSeamResidual (actualAugmentedPath hP (by decide) C) : ℤ)

theorem actualAugmentedEta_nonneg {P : HPath 14} (hP : P.IsHamiltonian)
    (C : ActualComponent P) : 0 ≤ actualAugmentedEta hP C :=
  Int.natCast_nonneg _

/-- The weight-defined x is the actual number of pieces plus heavy-seam excess. -/
theorem actualAugmentedX_eq_pieceCount_add_eta {P : HPath 14}
    (hP : P.IsHamiltonian) (C : ActualComponent P) :
    actualAugmentedX hP C =
      (componentPieceCount (actualAugmentedPath hP (by decide) C) : ℤ) +
        actualAugmentedEta hP C := by
  let p := actualAugmentedPath hP (by decide) C
  have hp : p.StronglyExitless := actualAugmentedPath_stronglyExitless hP (by decide) C
  have hw := actual_component_weight_formula (by decide : 3 ≤ 14) hp
  have hb := componentClassCount_pos (by decide : 1 ≤ 14) hp
  have hnat : p.wtP + 3 =
      15 * componentClassCount p + componentPieceCount p + componentSeamResidual p := by
    norm_num only at hw
    omega
  have hz : (p.wtP : ℤ) + 3 =
      15 * (componentClassCount p : ℤ) +
        (componentPieceCount p : ℤ) + (componentSeamResidual p : ℤ) := by
    exact_mod_cast hnat
  unfold actualAugmentedX actualAugmentedEta
  change (p.wtP : ℤ) - 15 * (componentClassCount p : ℤ) + 3 =
    (componentPieceCount p : ℤ) + (componentSeamResidual p : ℤ)
  linarith

theorem actualAugmentedLoss_eq_deficit_add_eta {P : HPath 14}
    (hP : P.IsHamiltonian) (C : ActualComponent P) :
    actualAugmentedLoss hP C =
      (componentPieceDeficit (actualAugmentedPath hP (by decide) C) : ℤ) +
        13 * actualAugmentedEta hP C := by
  have hb := componentClassCount_int_eq (by decide : 4 ≤ 14)
    (actualAugmentedPath_stronglyExitless hP (by decide) C)
  unfold actualAugmentedLoss
  rw [actualAugmentedX_eq_pieceCount_add_eta hP C]
  norm_num only at hb
  linarith

noncomputable def actualDelta (P : HPath 14) : ℤ :=
  (P.wtP : ℤ) + 14 - 93884313611

/-- Unconditional x-sum identity for the constructed actual augmented paths. -/
theorem actual_augmented_x_sum {P : HPath 14} (hP : P.IsHamiltonian) :
    (∑ C : ActualComponent P, actualAugmentedX hP C) =
      479001600 + actualDelta P - actualIndicator P - actualTheta hP - actualXi P := by
  apply actual_x_ledger_from_augmentation hP (δ := actualDelta P) rfl
  simp only [actualAugmentedX, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [actual_augmented_weight_sum hP (by decide), actual_augmented_class_sum hP (by decide)]
  norm_num [Nat.factorial, ActualComponent, numComps]
  ring

/-- The master identity uses actual augmented class counts, not supplied data. -/
theorem actual_augmented_master {P : HPath 14} (hP : P.IsHamiltonian) :
    13 * actualDelta P =
      13 * (actualIndicator P + actualTheta hP + actualXi P) +
        (∑ C : ActualComponent P, actualAugmentedLoss hP C) +
        (numComps (F P) : ℤ) - 1 := by
  have hx := actual_augmented_x_sum hP
  have hb := actual_augmented_class_sum hP (by decide : 2 ≤ 14)
  norm_num only [Nat.factorial] at hb
  simp only [actualAugmentedLoss, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [hx, hb]
  ring

end Haruhi
