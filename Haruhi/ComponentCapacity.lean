import Haruhi.GapBridge

/-!
# Capacity of actual strongly-exitless components

Every numerical hypothesis is obtained from the actual interval-piece
partition. The endpoint allowance `c` records which outer endpoints are full.
-/

namespace Haruhi

open Hunter PreimageChain
open scoped Classical BigOperators

set_option maxHeartbeats 1600000

private theorem sum_map_natCast {α : Type*} (xs : List α) (f : α → ℕ) :
    (xs.map fun x => (f x : ℤ)).sum = ((xs.map f).sum : ℤ) := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [ih]

/-- The actual endpoint residual of one exact-three chain. -/
def actualChainResidual {p : HPath 14}
    (chain : ExactWeightThreePieceChain p) : ℤ :=
  6 * ((exactChainTotalDeficit chain : ℤ) +
    chainFirstFullBit chain + chainLastFullBit chain) -
      exactChainPieceCount chain

theorem actualChainResidual_capacity
    {p : HPath 14} (hp : p.StronglyExitless)
    (chain : ExactWeightThreePieceChain p) :
    0 ≤ actualChainResidual chain ∧
      9 * (pieceListTotalSize chain.pieces : ℤ) ≤
        1577 * actualChainResidual chain + 1404 := by
  have hc : (chainFirstFullBit chain + chainLastFullBit chain : ℤ) ≤ 2 := by
    have hfirst := chainFirstFullBit_le_one chain
    have hlast := chainLastFullBit_le_one chain
    omega
  simpa [actualChainResidual, add_assoc] using
    actual_light_chain_capacity hp chain
      (chainFirstFullBit chain + chainLastFullBit chain) (le_refl _) hc

private theorem actual_chain_capacity_sum
    {p : HPath 14} (hp : p.StronglyExitless)
    (chains : List (ExactWeightThreePieceChain p)) :
    0 ≤ (chains.map actualChainResidual).sum ∧
      9 * (chains.map fun chain => (pieceListTotalSize chain.pieces : ℤ)).sum ≤
        1577 * (chains.map actualChainResidual).sum + 1404 * chains.length := by
  induction chains with
  | nil => simp
  | cons chain chains ih =>
      have hc := actualChainResidual_capacity hp chain
      simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_add,
        Nat.cast_one]
      constructor <;> linarith [hc.1, hc.2, ih.1, ih.2]

private theorem actual_chain_residual_sum
    {p : HPath 14} (chains : List (ExactWeightThreePieceChain p)) :
    (chains.map actualChainResidual).sum =
      6 * ((chains.map fun chain => (exactChainTotalDeficit chain : ℤ)).sum +
        (chains.map fun chain =>
          (chainFirstFullBit chain + chainLastFullBit chain : ℤ)).sum) -
        (chains.map fun chain => (exactChainPieceCount chain : ℤ)).sum := by
  induction chains with
  | nil => simp
  | cons chain chains ih =>
      simp only [List.map_cons, List.sum_cons, actualChainResidual] at *
      linarith

/-- Full actual component capacity, with any allowance that bounds its actual
outer full endpoints. In particular `c=2` always works and `c=1` works if the
last interval piece is partial. -/
theorem actual_component_refined_capacity
    {p : HPath 14} (hp : p.StronglyExitless)
    (c : ℤ)
    (hendpoints :
      (componentFirstFullBit p (by decide) hp : ℤ) +
        componentLastFullBit p (by decide) hp ≤ c) :
    let ρ : ℤ :=
      6 * ((componentPieceDeficit p : ℤ) +
        2 * componentSeamResidual p + c) - componentPieceCount p
    0 ≤ ρ ∧
      9 * (componentClassCount p : ℤ) ≤
        1577 * ρ + 1404 * ((componentSeamResidual p : ℤ) + 1) := by
  classical
  obtain ⟨chains, hflatten, hlength⟩ :=
    exists_componentExactWeightThreeChainPartition p (by decide : 1 ≤ 14) hp
  let cert : ∀ chain : ExactWeightThreePieceChain p,
      ExactWeightThreeChainRunCertificate chain := fun chain =>
    (strongActualChainCapacityPackage hp chain).certificate
  have heq : ∀ chain ∈ chains,
      (cert chain).endpointFullCount =
        chainFirstFullBit chain + chainLastFullBit chain := by
    intro chain _
    exact (strongActualChainCapacityPackage hp chain).endpoint_eq
  have heBudget := actualComponent_standardEndpointBudget
    (by decide : 1 ≤ 14) hp chains hflatten hlength cert heq
  have heNat : (chains.map fun chain =>
      chainFirstFullBit chain + chainLastFullBit chain).sum ≤
        2 * componentSeamResidual p +
          componentFirstFullBit p (by decide) hp +
            componentLastFullBit p (by decide) hp := by
    convert heBudget using 1
    apply congrArg List.sum
    apply List.map_congr_left
    intro chain hmem
    exact (heq chain hmem).symm
  have heInt :
      (chains.map fun chain =>
        (chainFirstFullBit chain + chainLastFullBit chain : ℤ)).sum ≤
      2 * (componentSeamResidual p : ℤ) +
        (componentFirstFullBit p (by decide) hp : ℤ) +
          componentLastFullBit p (by decide) hp := by
    calc
      _ = ((chains.map fun chain =>
          chainFirstFullBit chain + chainLastFullBit chain).sum : ℤ) := by
        simpa only [Nat.cast_add] using sum_map_natCast chains
          (fun chain => chainFirstFullBit chain + chainLastFullBit chain)
      _ ≤ _ := by exact_mod_cast heNat
  have hcountNat : chains.length ≤ componentSeamResidual p + 1 := by
    rw [hlength]
    have h := componentPositiveSeams_card_le_residual (p := p)
    omega
  have hcount : (chains.length : ℤ) ≤ (componentSeamResidual p : ℤ) + 1 := by
    exact_mod_cast hcountNat
  have hbNat := exactWeightThreeChainPartition_totalSize_sum p
    (by decide : 1 ≤ 14) hp chains hflatten
  have hb :
      (chains.map fun chain => (pieceListTotalSize chain.pieces : ℤ)).sum =
        (componentClassCount p : ℤ) := by
    rw [sum_map_natCast, hbNat]
  have hdNat : (chains.map exactChainTotalDeficit).sum = componentPieceDeficit p := by
    exact exactWeightThreeChainPartition_totalDeficit_sum
      (by decide : 4 ≤ 14) hp chains hflatten
  have hd :
      (chains.map fun chain => (exactChainTotalDeficit chain : ℤ)).sum =
        (componentPieceDeficit p : ℤ) := by
    rw [sum_map_natCast, hdNat]
  have hrNat : (chains.map exactChainPieceCount).sum = componentPieceCount p :=
    exactWeightThreeChainPartition_pieceCount_sum p
      (by decide : 1 ≤ 14) hp chains hflatten
  have hr :
      (chains.map fun chain => (exactChainPieceCount chain : ℤ)).sum =
        (componentPieceCount p : ℤ) := by
    rw [sum_map_natCast, hrNat]
  have hsum := actual_chain_residual_sum chains
  rw [hd, hr] at hsum
  have hcap := actual_chain_capacity_sum hp chains
  rw [hb] at hcap
  dsimp only
  constructor <;> linarith [hcap.1, hcap.2]

/-- Zero cheap residual with no heavy seams forces the exact component counts
and a full initial piece. The terminal piece is partial by hypothesis. -/
theorem actual_component_zero_shape
    {p : HPath 14} (hp : p.StronglyExitless)
    (hη : componentSeamResidual p = 0)
    (hlast : componentLastFullBit p (by decide) hp = 0)
    (hzero : 6 * ((componentPieceDeficit p : ℤ) + 1) -
      componentPieceCount p = 0) :
    componentFirstFullBit p (by decide) hp = 1 ∧
      componentPieceDeficit p = 1 ∧ componentPieceCount p = 12 ∧
        componentClassCount p = 155 := by
  let chain := componentExactWeightThreeChain_of_residual_zero p (by decide) hp hη
  have hpieces : chain.pieces = componentIntervalPieces p (by decide) hp := rfl
  have hΔ : exactChainTotalDeficit chain = componentPieceDeficit p := by
    change pieceListTotalDeficit chain.pieces = _
    rw [hpieces]
    exact componentIntervalPieces_totalDeficit (by decide : 4 ≤ 14) hp
  have hR : exactChainPieceCount chain = componentPieceCount p := by
    change chain.pieces.length = _
    rw [hpieces, componentIntervalPieces_length]
  have hb : pieceListTotalSize chain.pieces = componentClassCount p := by
    rw [hpieces]
    exact componentIntervalPieces_totalSize p (by decide) hp
  have hfirst : chainFirstFullBit chain =
      componentFirstFullBit p (by decide) hp := rfl
  have hlast' : chainLastFullBit chain = 0 := hlast
  have hzero' : 6 * ((exactChainTotalDeficit chain : ℤ) + 1) -
      exactChainPieceCount chain = 0 := by
    rw [hΔ, hR]
    exact hzero
  have hshape := actual_light_chain_zero_shape hp chain hlast' hzero'
  simpa only [hfirst, hΔ, hR, hb] using hshape

end Haruhi
