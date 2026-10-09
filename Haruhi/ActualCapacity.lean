import Haruhi.ZeroRigidity
import Haruhi.HeadData

/-! # Refined capacity for every actual augmented component -/
namespace Haruhi

open Hunter PreimageChain
open scoped Classical BigOperators

set_option maxHeartbeats 1600000

/-- The cheap terminal-full exception has strictly positive residual. -/
theorem cheap_thirteen_class_capacity
    {p : HPath 14} (hp : p.StronglyExitless)
    (hclass : componentClassCount p = 13) :
    let ρ : ℤ := 6 * ((componentPieceDeficit p : ℤ) +
      2 * componentSeamResidual p + 1) - componentPieceCount p
    5 ≤ ρ ∧ 9 * (componentClassCount p : ℤ) ≤
      1577 * ρ + 1404 * ((componentSeamResidual p : ℤ) + 1) := by
  have hcount := componentClassCount_int_eq (by decide : 4 ≤ 14) hp
  rw [hclass] at hcount
  norm_num at hcount
  have hR : (1 : ℤ) ≤ componentPieceCount p := by
    have hRNat : 1 ≤ componentPieceCount p := by
      unfold componentPieceCount
      omega
    exact_mod_cast hRNat
  have hη : (0 : ℤ) ≤ componentSeamResidual p := by positivity
  dsimp only
  rw [hclass]
  norm_num only [Nat.cast_ofNat]
  constructor <;> linarith

/-- Capacity with the cheap endpoint allowance for an actual selected
weight-two head. The full-terminal exceptional case is discharged explicitly. -/
theorem actual_augmented_cheap_capacity
    {P : HPath 14} (hP : P.IsHamiltonian) (hred : Sigma2Reduced P)
    (C : ActualComponent P) {y : Vtx 14}
    (hedge : (actualComponentHead hP C, y) ∈ P.edges)
    (hweight : ew 14 (actualComponentHead hP C) y = 2) :
    let p := actualAugmentedPath hP (by decide) C
    let ρ : ℤ := 6 * ((componentPieceDeficit p : ℤ) +
      2 * componentSeamResidual p + 1) - componentPieceCount p
    0 ≤ ρ ∧ 9 * (componentClassCount p : ℤ) ≤
      1577 * ρ + 1404 * ((componentSeamResidual p : ℤ) + 1) := by
  let p := actualAugmentedPath hP (by decide) C
  have hp : p.StronglyExitless := actualAugmentedPath_stronglyExitless hP (by decide) C
  by_cases hc : componentClassCount p = 13
  · have h := cheap_thirteen_class_capacity hp hc
    exact ⟨by linarith [h.1], h.2⟩
  · have hlast : componentLastFullBit p (by decide) hp = 0 :=
      actual_augmented_cheap_head_lastFullBit_zero hP (by decide : 5 ≤ 14)
        hred C hedge hweight hc
    apply actual_component_refined_capacity hp 1
    rw [hlast, Nat.cast_zero, add_zero]
    exact_mod_cast componentFirstFullBit_le_one p (by decide) hp

/-- The corrected residual expressed entirely in actual interval-piece counts. -/
theorem actualResidual_eq_counts
    {P : HPath 14} (hP : P.IsHamiltonian) (C : ActualComponent P) :
    actualResidual hP C =
      6 * ((componentPieceDeficit (actualAugmentedPath hP (by decide) C) : ℤ) +
        2 * actualAugmentedEta hP C + 1) -
      componentPieceCount (actualAugmentedPath hP (by decide) C) +
        6 * actualOriginalHeadBit hP C + 6 * actualHeadExcess hP C := by
  unfold actualResidual
  rw [actualAugmentedLoss_eq_deficit_add_eta, actualAugmentedX_eq_pieceCount_add_eta]
  ring

/-- Every actual augmented component has nonnegative corrected residual and
satisfies the refined capacity estimate. -/
theorem actual_residual_capacity
    {P : HPath 14} (hP : P.IsHamiltonian) (hred : Sigma2Reduced P)
    (C : ActualComponent P) :
    0 ≤ actualResidual hP C ∧
      9 * (componentClassCount (actualAugmentedPath hP (by decide) C) : ℤ) ≤
        1577 * actualResidual hP C + 1404 * (actualAugmentedEta hP C + 1) := by
  let p := actualAugmentedPath hP (by decide) C
  have hp : p.StronglyExitless := actualAugmentedPath_stronglyExitless hP (by decide) C
  have hq := actualHeadExcess_nonneg hP C
  have hr := actualResidual_eq_counts hP C
  have hη : actualAugmentedEta hP C = (componentSeamResidual p : ℤ) := rfl
  have huniversal := actual_component_refined_capacity hp 2 (by
    have hf := componentFirstFullBit_le_one p (by decide) hp
    have hl := componentLastFullBit_le_one p (by decide) hp
    omega)
  dsimp only at huniversal
  change 0 ≤ actualResidual hP C ∧
    9 * (componentClassCount p : ℤ) ≤
      1577 * actualResidual hP C + 1404 * (actualAugmentedEta hP C + 1)
  change actualResidual hP C =
    6 * ((componentPieceDeficit p : ℤ) + 2 * actualAugmentedEta hP C + 1) -
      componentPieceCount p + 6 * actualOriginalHeadBit hP C +
        6 * actualHeadExcess hP C at hr
  rw [hη] at hr ⊢
  by_cases hh : actualComponentHead hP C = P.last
  · have hbit : actualOriginalHeadBit hP C = 1 := by simp [actualOriginalHeadBit, hh]
    rw [hbit] at hr
    constructor <;> linarith [huniversal.1, huniversal.2]
  · have hbit : actualOriginalHeadBit hP C = 0 := by simp [actualOriginalHeadBit, hh]
    rw [hbit] at hr
    by_cases hqzero : actualHeadExcess hP C = 0
    · have hweight : ew 14 (actualComponentHead hP C)
          (sigma (actualHeadSlot hP (by decide) C hh).1) = 2 := by
        have heq := actualHeadExcess_eq_weight hP C hh
        omega
      have hcheap := actual_augmented_cheap_capacity hP hred C
        (actualHeadSlot_edge hP (by decide) C hh) hweight
      change 0 ≤ 6 * ((componentPieceDeficit p : ℤ) +
        2 * componentSeamResidual p + 1) - componentPieceCount p ∧
        9 * (componentClassCount p : ℤ) ≤
          1577 * (6 * ((componentPieceDeficit p : ℤ) +
            2 * componentSeamResidual p + 1) - componentPieceCount p) +
              1404 * ((componentSeamResidual p : ℤ) + 1) at hcheap
      constructor <;> linarith [hcheap.1, hcheap.2]
    · have hqpos : 1 ≤ actualHeadExcess hP C := by omega
      constructor <;> linarith [huniversal.1, huniversal.2]

theorem actualResidual_nonneg
    {P : HPath 14} (hP : P.IsHamiltonian) (hred : Sigma2Reduced P)
    (C : ActualComponent P) : 0 ≤ actualResidual hP C :=
  (actual_residual_capacity hP hred C).1

theorem actualResidual_capacity
    {P : HPath 14} (hP : P.IsHamiltonian) (hred : Sigma2Reduced P)
    (C : ActualComponent P) :
    9 * (componentClassCount (actualAugmentedPath hP (by decide) C) : ℤ) ≤
      1577 * actualResidual hP C + 1404 * (actualAugmentedEta hP C + 1) :=
  (actual_residual_capacity hP hred C).2

/-- A new-head component with zero local charges has exactly the geometry
needed by the terminal-visit obstruction. -/
theorem actual_residual_zero_geometry
    {P : HPath 14} (hP : P.IsHamiltonian) (hred : Sigma2Reduced P)
    (C : ActualComponent P)
    (hnew : actualComponentHead hP C ≠ P.last)
    (hη : actualAugmentedEta hP C = 0)
    (hq : actualHeadExcess hP C = 0)
    (hr : actualResidual hP C = 0) :
    componentSeamResidual (actualAugmentedPath hP (by decide) C) = 0 ∧
      componentLastFullBit (actualAugmentedPath hP (by decide) C) (by decide)
        (actualAugmentedPath_stronglyExitless hP (by decide) C) = 0 ∧
      (6 * ((componentPieceDeficit (actualAugmentedPath hP (by decide) C) : ℤ) + 1) -
        componentPieceCount (actualAugmentedPath hP (by decide) C) = 0) ∧
      componentFirstFullBit (actualAugmentedPath hP (by decide) C) (by decide)
        (actualAugmentedPath_stronglyExitless hP (by decide) C) = 1 ∧
      componentClassCount (actualAugmentedPath hP (by decide) C) = 155 := by
  let p := actualAugmentedPath hP (by decide) C
  have hp : p.StronglyExitless := actualAugmentedPath_stronglyExitless hP (by decide) C
  have hηNat : componentSeamResidual p = 0 := by
    change (componentSeamResidual p : ℤ) = 0 at hη
    exact_mod_cast hη
  have hzero : 6 * ((componentPieceDeficit p : ℤ) + 1) -
      componentPieceCount p = 0 := by
    have heq := actualResidual_eq_counts hP C
    rw [hr, hq, hη] at heq
    simp only [actualOriginalHeadBit, if_neg hnew] at heq
    change 0 = 6 * ((componentPieceDeficit p : ℤ) + 2 * 0 + 1) -
      componentPieceCount p + 6 * 0 + 6 * 0 at heq
    linarith
  have hweight : ew 14 (actualComponentHead hP C)
      (sigma (actualHeadSlot hP (by decide) C hnew).1) = 2 := by
    have heq := actualHeadExcess_eq_weight hP C hnew
    omega
  have hclass : componentClassCount p ≠ 13 := by
    intro hc
    have hbad := (cheap_thirteen_class_capacity hp hc).1
    rw [hηNat] at hbad
    norm_num at hbad
    linarith
  have hlast : componentLastFullBit p (by decide) hp = 0 :=
    actual_augmented_cheap_head_lastFullBit_zero hP (by decide) hred C
      (actualHeadSlot_edge hP (by decide) C hnew) hweight hclass
  have hshape := actual_component_zero_shape hp hηNat hlast hzero
  exact ⟨hηNat, hlast, hzero, hshape.1, hshape.2.2.2⟩

/-- The actual corrected residual's zero case yields the retained `psi` visit. -/
theorem actual_residual_zero_certificate
    {P : HPath 14} (hP : P.IsHamiltonian) (hred : Sigma2Reduced P)
    (C : ActualComponent P)
    (hnew : actualComponentHead hP C ≠ P.last)
    (hη : actualAugmentedEta hP C = 0)
    (hq : actualHeadExcess hP C = 0)
    (hr : actualResidual hP C = 0) : TerminalFullVisitCertificate hP C := by
  have hg := actual_residual_zero_geometry hP hred C hnew hη hq hr
  exact actual_augmented_zero_residual_certificate hP C hg.1 hg.2.1 hg.2.2.1

end Haruhi
