import Haruhi.HeadCount
import Haruhi.ActualCapacity
import Haruhi.FirstSeam

/-! # The global obstruction between actual standard components -/
namespace Haruhi
open Hunter PreimageChain
open scoped Classical BigOperators

/-- An actual direct slot from a standard component cannot target another
standard component. Both local geometric hypotheses are proved from the
concrete residual, and both connecting edges belong to the original path. -/
theorem actual_standard_direct_target_bad
    {P : HPath 14} (hP : P.IsHamiltonian) (hred : Sigma2Reduced P)
    (s : {v : Vtx 14 // v ∈ chainStarts P})
    (hgood : actualChainSourceComponent hP (by decide) s ∈ actualGood hP)
    (he : s.1 ∈ chainEnds P) (hn : s.1 ≠ P.last) :
    actualEndTarget hP (by decide) ⟨s.1, he, hn⟩ ∈ actualBad hP := by
  let C := actualChainSourceComponent hP (by decide) s
  let e : {v : Vtx 14 // v ∈ chainEnds P ∧ v ≠ P.last} := ⟨s.1, he, hn⟩
  let A := actualEndTarget hP (by decide) e
  have hc : actualStandard hP C := (mem_actualGood hP C).mp hgood
  apply (mem_actualBad hP A).mpr
  intro ha
  have gc := actual_residual_zero_geometry hP hred C hc.1 hc.2.2.1 hc.2.2.2 hc.2.1
  have ga := actual_residual_zero_geometry hP hred A ha.1 ha.2.2.1 ha.2.2.2 ha.2.1
  have hneA : A ≠ actualRootComponent hP (by decide) :=
    ((actualEntrySlotEquiv hP (by decide)).symm e).2
  have hslotA : actualEntrySlot hP (by decide) A hneA = e :=
    (actualEntrySlotEquiv hP (by decide)).apply_symm_apply e
  have hslotC : actualHeadSlot hP (by decide) C hc.1 = s := by
    apply chainSourceHead_injective hP
    apply Subtype.ext
    rw [actualHeadSlot_source]
    exact actualChainSourceComponent_head hP (by decide) s
  have hedge : (actualComponentHead hP C, sigma s.1) ∈ P.edges := by
    have h := actualHeadSlot_edge hP (by decide) C hc.1
    rwa [hslotC] at h
  have hweight : ew 14 (actualComponentHead hP C) (sigma s.1) = 2 := by
    have h := actualHeadExcess_eq_weight hP C hc.1
    rw [hslotC] at h
    have hq := hc.2.2.2
    omega
  apply actual_zero_residual_source_target_incompatible hP hred C A hneA
    gc.1 gc.2.1 gc.2.2.1 ga.1 ga.2.1 ga.2.2.1
  · simpa only [hslotA] using hedge
  · simpa only [hslotA] using hweight

/-- The required actual component-count inequality. There is no assumed
matching, no extra geometric certificate, and no numerical capacity hypothesis. -/
theorem actual_standard_count
    {P : HPath 14} (hP : P.IsHamiltonian) (hred : Sigma2Reduced P) :
    ((actualGood hP).card : ℤ) ≤ ((actualBad hP).card : ℤ) +
      actualXi P + actualIndicator P := by
  apply actual_good_component_count hP (by decide) (actualGood hP) (actualBad hP)
  · intro C hc
    exact ((mem_actualGood hP C).mp hc).1
  · intro s hs he hn
    exact actual_standard_direct_target_bad hP hred s hs he hn

end Haruhi
