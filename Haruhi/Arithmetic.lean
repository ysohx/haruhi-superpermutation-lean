import Mathlib

/-!
# Conditional accounting and numerical consequences for the Haruhi argument

The theorems in this file consume explicit counting/accounting hypotheses.
They do not assert that every superpermutation satisfies those hypotheses;
the graph-theoretic construction must supply that bridge separately.
-/

namespace Haruhi

/-- The corrected residual is nonnegative for either kind of new head. -/
theorem new_head_residual_nonneg_int
    {loss x η q r : ℤ}
    (hq : 0 ≤ q)
    (huniversal : 6 * loss ≥ x - 12 + 65 * η)
    (hcheap : q = 0 → 6 * (loss + 1) ≥ x + 65 * η)
    (hr : r = 6 * loss + 6 - x - 65 * η + 6 * q) :
    0 ≤ r := by
  by_cases hzero : q = 0
  · have hc := hcheap hzero
    linarith
  · have hpositive : 1 ≤ q := by omega
    linarith

/-- Nonnegativity of the universal/original-head residual. -/
theorem original_head_residual_nonneg_int
    {loss x η r : ℤ}
    (huniversal : 6 * loss ≥ x - 12 + 65 * η)
    (hr : r = 6 * loss + 12 - x - 65 * η) :
    0 ≤ r := by
  linarith

/-- Exact retained budget, derived from the three explicit accounting identities.

`residualSum` includes the endpoint correction: its constant term is `6*h+6`
when `I=0`, and `6*h` when `I=1`. The displayed identity encodes both cases.
-/
theorem exact_budget_int
    {δ M I θ ξ H h sumX sumLambda residualSum T : ℤ}
    (hx : sumX = M + δ - I - θ - ξ)
    (hmaster : 13 * δ = 13 * (I + θ + ξ) + sumLambda + h - 1)
    (hr : residualSum =
      6 * sumLambda + 6 * h + 6 - 6 * I - sumX - 65 * H + 6 * θ)
    (hT : T = 77 * δ - M + 12) :
    T = residualSum + 65 * H + 71 * θ + 77 * ξ + 83 * I := by
  linarith

/-- The component count from an injective direct-slot map and explicit exceptions. -/
theorem head_count_int
    {h good bad residualSum H θ ξ I : ℤ}
    (hpartition : h = good + bad)
    (hgood : good ≤ bad + ξ + I)
    (hbad : bad ≤ residualSum + H + θ + 1 - I) :
    h ≤ 2 * residualSum + 2 * H + 2 * θ + ξ + 2 - I := by
  linarith

/-- Sum capacities and remove the exactly `h-1` artificially prepended blocks. -/
theorem remove_augmentation_int
    {N augmentedBlocks h residualSum H : ℤ}
    (haugmentation : augmentedBlocks = N + h - 1)
    (hcapacity : 9 * augmentedBlocks ≤
      1577 * residualSum + 1404 * (H + h)) :
    9 * N ≤ 1577 * residualSum + 1404 * H + 1395 * h + 9 := by
  linarith

/-- Retain the exact rational local coefficient and the augmentation correction. -/
theorem global_capacity_int
    {N residualSum H θ ξ I h T : ℤ}
    (hcapacity : 9 * N ≤
      1577 * residualSum + 1404 * H + 1395 * h + 9)
    (hheads : h ≤ 2 * residualSum + 2 * H + 2 * θ + ξ + 2 - I)
    (hbudget : T = residualSum + 65 * H + 71 * θ + 77 * ξ + 83 * I)
    (hH : 0 ≤ H) (hθ : 0 ≤ θ) (hξ : 0 ≤ ξ) (hI : 0 ≤ I) :
    9 * N ≤ 4367 * T + 2799 := by
  have hraw : 9 * N ≤ 4367 * residualSum + 4194 * H +
      2790 * θ + 1395 * ξ + 2799 - 1395 * I := by
    linarith only [hcapacity, hheads]
  linarith only [hraw, hbudget, hH, hθ, hξ, hI]

/-- Exact factorial constants, independently normalized by Lean. -/
theorem factorial_thirteen : Nat.factorial 13 = 6227020800 := by
  norm_num [Nat.factorial]

theorem factorial_twelve : Nat.factorial 12 = 479001600 := by
  norm_num [Nat.factorial]

theorem baseline_fourteen :
    Nat.factorial 14 + Nat.factorial 13 + Nat.factorial 12 + 11 =
      93884313611 := by
  norm_num [Nat.factorial]

/-- Integer rounding of the global capacity inequality. -/
theorem budget_lower_bound_int
    {T : ℤ} (hcapacity : 9 * 6227020800 ≤ 4367 * T + 2799) :
    12833338 ≤ T := by
  omega

/-- Integer rounding of the defect definition after the budget lower bound. -/
theorem defect_lower_bound_int
    {δ T : ℤ} (hT : T = 77 * δ - 479001600 + 12)
    (hcapacity : 9 * 6227020800 ≤ 4367 * T + 2799) :
    6387467 ≤ δ := by
  have hbound := budget_lower_bound_int hcapacity
  omega

/-- Numerical conclusion conditional on the explicitly supplied global capacity.

This is an arithmetic helper, not a theorem about all superpermutations.
-/
theorem length_lower_bound_from_global_capacity_int
    {length δ T : ℤ}
    (hlength : length = 93884313611 + δ)
    (hT : T = 77 * δ - 479001600 + 12)
    (hcapacity : 9 * 6227020800 ≤ 4367 * T + 2799) :
    93890701078 ≤ length := by
  have hdefect := defect_lower_bound_int hT hcapacity
  linarith

/-- Natural-length wrapper for the same conditional arithmetic consequence. -/
theorem length_lower_bound_from_global_capacity_nat
    {length : ℕ} {δ T : ℤ}
    (hlength : (length : ℤ) = 93884313611 + δ)
    (hT : T = 77 * δ - 479001600 + 12)
    (hcapacity : 9 * 6227020800 ≤ 4367 * T + 2799) :
    93890701078 ≤ length := by
  have h := length_lower_bound_from_global_capacity_int hlength hT hcapacity
  exact_mod_cast h

/-- Reproducible check that the immediately preceding defect value is excluded. -/
theorem preceding_defect_is_excluded :
    4367 * (77 * (6387466 : ℤ) - 479001600 + 12) + 2799 <
      9 * 6227020800 := by
  norm_num

end Haruhi
