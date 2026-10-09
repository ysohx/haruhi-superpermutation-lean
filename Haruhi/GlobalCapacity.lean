import Haruhi.ActualCapacity

/-! # Summing capacities of the actual augmented components -/
namespace Haruhi
open Hunter PreimageChain
open scoped Classical BigOperators

/-- All local capacities are evaluated on the constructed actual paths. -/
theorem actual_augmented_capacity_sum {P : HPath 14}
    (hP : P.IsHamiltonian) (hred : Sigma2Reduced P) :
    9 * (∑ C : ActualComponent P,
      (componentClassCount (actualAugmentedPath hP (by decide) C) : ℤ)) ≤
      1577 * (∑ C : ActualComponent P, actualResidual hP C) +
        1404 * ((∑ C : ActualComponent P, actualAugmentedEta hP C) +
          (numComps (F P) : ℤ)) := by
  have hsum := Finset.sum_le_sum (s := Finset.univ)
    (fun C _ => actualResidual_capacity hP hred C)
  simp only [← Finset.mul_sum, Finset.sum_add_distrib,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at hsum
  simpa only [ActualComponent, Fintype.card_coe, numComps] using hsum

/-- Remove exactly the `h−1` classes added by augmentation. -/
theorem actual_capacity_without_augmentation {P : HPath 14}
    (hP : P.IsHamiltonian) (hred : Sigma2Reduced P) :
    9 * 6227020800 ≤
      1577 * (∑ C : ActualComponent P, actualResidual hP C) +
        1404 * (∑ C : ActualComponent P, actualAugmentedEta hP C) +
        1395 * (numComps (F P) : ℤ) + 9 := by
  have hb := actual_augmented_class_sum hP (by decide : 2 ≤ 14)
  norm_num only [Nat.factorial] at hb
  exact remove_augmentation_int hb (actual_augmented_capacity_sum hP hred)

theorem actual_bad_count_reduced {P : HPath 14}
    (hP : P.IsHamiltonian) (hred : Sigma2Reduced P) :
    ((actualBad hP).card : ℤ) ≤
      (∑ C : ActualComponent P, actualResidual hP C) +
        (∑ C : ActualComponent P, actualAugmentedEta hP C) +
        actualTheta hP + 1 - actualIndicator P :=
  actual_bad_count hP (actualResidual_nonneg hP hred)

/-- This final assembly exposes only the remaining direct-head counting theorem.
All geometric capacities and accounting terms are actual constructed data. -/
theorem actual_global_capacity_of_good_count {P : HPath 14}
    (hP : P.IsHamiltonian) (hred : Sigma2Reduced P)
    (hgood : ((actualGood hP).card : ℤ) ≤
      ((actualBad hP).card : ℤ) + actualXi P + actualIndicator P) :
    9 * 6227020800 ≤
      4367 * (77 * actualDelta P - 479001600 + 12) + 2799 := by
  have hheads := head_count_int (actual_good_bad_partition hP) hgood
    (actual_bad_count_reduced hP hred)
  exact global_capacity_int (actual_capacity_without_augmentation hP hred)
    hheads (actual_exact_budget hP)
    (Finset.sum_nonneg (fun C _ => actualAugmentedEta_nonneg hP C))
    (actual_theta_nonneg hP (by decide)) (actual_xi_nonneg (by decide))
    (actual_indicator_nonneg P)

end Haruhi
