import Mathlib

/-!
# Arithmetic consequences of explicit local run-count hypotheses

This file does not assert that an arbitrary superpermutation supplies the
hypotheses below.  Those combinatorial bridges must be proved separately.
All statements here are arithmetic consequences, with no additional axioms.
-/

namespace Haruhi

/-- A light segment's capacity, conditional on the raw portal/run counts.

`c = 2` is the universal endpoint allowance and `c = 1` is the cheap-head
allowance.  The caller must establish `e ≤ c`; in particular, the cheap
single-run exception needs its own elementary treatment.
-/
theorem local_capacity_int
    {K F p Δ E N e c R b ρ : ℤ}
    (hEdef : E = Δ - p)
    (hRdef : R = F + p)
    (hincidence : 2 * K ≤ Δ + e)
    (hfull : F ≤ 10 * K + e + N)
    (hlong : 11 * N ≤ 2 * E)
    (hchains : K ≤ E + 1)
    (hEnonneg : 0 ≤ E)
    (hendpoints : e ≤ c)
    (hc : c ≤ 2)
    (hρdef : ρ = 6 * (Δ + c) - R)
    (hbdef : b = 13 * R - Δ) :
    0 ≤ ρ ∧ 9 * b ≤ 1577 * ρ + 1404 := by
  let A : ℤ := Δ + e - 2 * K
  let Q : ℤ := 10 * K + e + N - F
  let ρe : ℤ := 6 * (Δ + e) - R
  have hA : 0 ≤ A := by dsimp [A]; linarith only [hincidence]
  have hQ : 0 ≤ Q := by dsimp [Q]; linarith only [hfull]
  have hρe : ρe = 5 * A + E - N + Q := by
    dsimp [ρe, A, Q]
    linarith only [hEdef, hRdef]
  have hEbound : 9 * E ≤ 11 * ρe - 55 * A := by
    linarith only [hρe, hQ, hlong]
  have hρenonneg : 0 ≤ ρe := by
    linarith only [hEbound, hEnonneg, hA]
  have hρele : ρe ≤ ρ := by
    dsimp [ρe]
    linarith only [hρdef, hendpoints]
  have he : e ≤ 2 := le_trans hendpoints hc
  have hb : b = 154 * K + 77 * A + e - 13 * ρe := by
    dsimp [A, ρe]
    linarith only [hbdef]
  have hcap : 9 * b ≤ 1577 * ρe + 1404 := by
    linarith only [hb, hchains, hEbound, hA, he]
  constructor
  · exact le_trans hρenonneg hρele
  · linarith only [hcap, hρele]

/-- The intentionally rounded capacity used in the intermediate research note. -/
theorem local_capacity_rounded_int
    {b ρ : ℤ} (hρ : 0 ≤ ρ) (hcap : 9 * b ≤ 1577 * ρ + 1404) :
    b ≤ 156 + 176 * ρ := by
  linarith

/-- Equality in the local endpoint capacity forces the standard numerical shape.

For `c=1`, this says eleven full runs and one deficit-one partial run.
For `c=2`, this says twelve full runs and no partial runs.  The geometric
ordering of these runs remains a separate obligation for the caller.
-/
theorem local_zero_residual_int
    {K F p Δ E N e c R b ρ : ℤ}
    (hEdef : E = Δ - p)
    (hRdef : R = F + p)
    (hincidence : 2 * K ≤ Δ + e)
    (hfull : F ≤ 10 * K + e + N)
    (hlong : 11 * N ≤ 2 * E)
    (hchains : K ≤ E + 1)
    (hEnonneg : 0 ≤ E)
    (hΔnonneg : 0 ≤ Δ)
    (hendpoints : e ≤ c)
    (hcLower : 1 ≤ c)
    (hcUpper : c ≤ 2)
    (hρdef : ρ = 6 * (Δ + c) - R)
    (hbdef : b = 13 * R - Δ)
    (hzero : ρ = 0) :
    e = c ∧ E = 0 ∧ K = 1 ∧ Δ = 2 - c ∧ p = 2 - c ∧
      F = 10 + c ∧ R = 12 ∧ b = 154 + c := by
  let A : ℤ := Δ + e - 2 * K
  let Q : ℤ := 10 * K + e + N - F
  let ρe : ℤ := 6 * (Δ + e) - R
  have hA : 0 ≤ A := by dsimp [A]; linarith only [hincidence]
  have hQ : 0 ≤ Q := by dsimp [Q]; linarith only [hfull]
  have hrepr : ρe = 5 * A + E - N + Q := by
    dsimp [ρe, A, Q]
    linarith only [hEdef, hRdef]
  have hslack : 55 * A + 9 * E + 11 * Q ≤ 11 * ρe := by
    linarith only [hrepr, hlong]
  have hρenonneg : 0 ≤ ρe := by
    linarith only [hslack, hA, hEnonneg, hQ]
  have heq : e = c := by
    dsimp [ρe] at hρenonneg
    linarith only [hρenonneg, hρdef, hzero, hendpoints]
  have hρezero : ρe = 0 := by
    dsimp [ρe]
    linarith only [heq, hρdef, hzero]
  have hEzero : E = 0 := by
    linarith only [hslack, hρezero, hA, hEnonneg, hQ]
  have hAzero : A = 0 := by
    linarith only [hslack, hρezero, hA, hEnonneg, hQ]
  have hΔeq : Δ = 2 * K - c := by
    dsimp [A] at hAzero
    linarith only [hAzero, heq]
  have hKone : K = 1 := by
    omega
  refine ⟨heq, hEzero, hKone, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith

/-- The zero-excess cheap-head exception is a single run of at most 13 blocks. -/
theorem cheap_single_run_capacity_int
    {b ρ : ℤ} (hb : b ≤ 13) (hρ : 0 ≤ ρ) :
    9 * b ≤ 1577 * ρ + 1404 := by
  linarith

/-- Sum independently established light-segment capacities. -/
theorem sum_light_capacity_int
    {ι : Type*} (s : Finset ι) (b ρ : ι → ℤ)
    (hcap : ∀ i ∈ s, 9 * b i ≤ 1577 * ρ i + 1404) :
    9 * (∑ i ∈ s, b i) ≤
      1577 * (∑ i ∈ s, ρ i) + 1404 * (s.card : ℤ) := by
  calc
    9 * (∑ i ∈ s, b i) = ∑ i ∈ s, 9 * b i := by
      rw [Finset.mul_sum]
    _ ≤ ∑ i ∈ s, (1577 * ρ i + 1404) := by
      exact Finset.sum_le_sum hcap
    _ = 1577 * (∑ i ∈ s, ρ i) + 1404 * (s.card : ℤ) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      simp [mul_comm]

/-- Allocate segment residuals and account for at most `η+1` segments. -/
theorem component_capacity_int
    {b segmentResidual segmentCount r η : ℤ}
    (hsegments : 9 * b ≤ 1577 * segmentResidual + 1404 * segmentCount)
    (hresidual : segmentResidual ≤ r)
    (hcount : segmentCount ≤ η + 1) :
    9 * b ≤ 1577 * r + 1404 * (η + 1) := by
  linarith

/-- Universal residuals of light segments fit inside the component residual. -/
theorem universal_segment_residual_budget_int
    {Δ R η x loss segmentCount segmentResidual r : ℤ}
    (hx : x = R + η)
    (hloss : loss = Δ + 13 * η)
    (hcount : segmentCount ≤ η + 1)
    (hsegments : segmentResidual = 6 * Δ - R + 12 * segmentCount)
    (hr : r = 6 * loss - x + 12 - 65 * η) :
    segmentResidual ≤ r := by
  linarith

/-- The terminal cheap light segment uses the endpoint allowance six. -/
theorem cheap_segment_residual_budget_int
    {Δ R η x loss segmentCount segmentResidual r : ℤ}
    (hx : x = R + η)
    (hloss : loss = Δ + 13 * η)
    (hcount : segmentCount ≤ η + 1)
    (hsegments : segmentResidual = 6 * Δ - R + 12 * segmentCount - 6)
    (hr : r = 6 * loss + 6 - x - 65 * η) :
    segmentResidual ≤ r := by
  linarith

/-- Noncheap new-head residuals dominate the universal residual. -/
theorem noncheap_residual_dominates_int
    {loss x η q r : ℤ}
    (hq : 1 ≤ q)
    (hr : r = 6 * loss + 6 - x - 65 * η + 6 * q) :
    6 * loss - x + 12 - 65 * η ≤ r := by
  linarith

/-- Distinct internal gaps with positive-excess witnesses consume distinct units.

This is a finite counting helper.  Constructing the witness map from actual
consecutive runs is a separate combinatorial theorem.
-/
theorem gap_witness_excess_nat
    {α β : Type*} [DecidableEq β]
    (gaps : Finset α) (partials : Finset β)
    (witness : α → β) (excess : β → ℕ)
    (hinjective : Set.InjOn witness (gaps : Set α))
    (hmem : ∀ i ∈ gaps, witness i ∈ partials)
    (hpositive : ∀ i ∈ gaps, 1 ≤ excess (witness i)) :
    gaps.card ≤ ∑ j ∈ partials, excess j := by
  have hsubset : gaps.image witness ⊆ partials := by
    intro j hj
    rcases Finset.mem_image.mp hj with ⟨i, hi, rfl⟩
    exact hmem i hi
  calc
    gaps.card = (gaps.image witness).card :=
      (Finset.card_image_of_injOn hinjective).symm
    _ = ∑ j ∈ gaps.image witness, (1 : ℕ) := by simp
    _ ≤ ∑ j ∈ gaps.image witness, excess j := by
      apply Finset.sum_le_sum
      intro j hj
      rcases Finset.mem_image.mp hj with ⟨i, hi, rfl⟩
      exact hpositive i hi
    _ ≤ ∑ j ∈ partials, excess j := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
      intro j _ _
      exact Nat.zero_le _

/-- Convert the count of internal gaps into the full-chain count. -/
theorem full_chain_count_of_gap_excess_nat
    {K gapCount E : ℕ}
    (hgapCount : gapCount = K - 1)
    (hexcess : gapCount ≤ E) :
    K ≤ E + 1 := by
  omega

end Haruhi
