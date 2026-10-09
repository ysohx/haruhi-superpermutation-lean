import Haruhi.AugmentedTerminal
import Haruhi.ComponentCapacity

/-! Zero-residual geometry for an actual augmented Hunter component. -/
namespace Haruhi
open Hunter PreimageChain
open scoped Classical

/-- A zero cheap residual and no heavy seams force a retained `psi` visit
inside the original component. All counts refer to its actual augmented path. -/
theorem actual_augmented_zero_residual_certificate
    {P : HPath 14} (hP : P.IsHamiltonian) (C : ActualComponent P)
    (hη : componentSeamResidual (actualAugmentedPath hP (by decide) C) = 0)
    (hlast : componentLastFullBit (actualAugmentedPath hP (by decide) C) (by decide)
      (actualAugmentedPath_stronglyExitless hP (by decide) C) = 0)
    (hzero : 6 * ((componentPieceDeficit (actualAugmentedPath hP (by decide) C) : ℤ) + 1) -
      componentPieceCount (actualAugmentedPath hP (by decide) C) = 0) :
    TerminalFullVisitCertificate hP C := by
  have hp := actualAugmentedPath_stronglyExitless hP (by decide) C
  obtain ⟨_, hdeficit, _, hcount⟩ := actual_component_zero_shape hp hη hlast hzero
  obtain ⟨start, hend, hdoors⟩ :=
    component_deficit_one_terminal_segment (by decide : 4 ≤ 14) hp hdeficit hlast
  apply actual_augmented_terminal_door_segment_certificate hP (by decide) C
    (start := start) _ hend hdoors
  omega

/-- The actual selected weight-two connector cannot leave a zero-residual
source and land at a component tail through another selected weight-two edge. -/
theorem actual_augmented_zero_residual_no_direct_connector
    {P : HPath 14} (hP : P.IsHamiltonian) (hred : Sigma2Reduced P)
    (C A : ActualComponent P) (slot : Vtx 14)
    (hη : componentSeamResidual (actualAugmentedPath hP (by decide) C) = 0)
    (hlast : componentLastFullBit (actualAugmentedPath hP (by decide) C) (by decide)
      (actualAugmentedPath_stronglyExitless hP (by decide) C) = 0)
    (hzero : 6 * ((componentPieceDeficit (actualAugmentedPath hP (by decide) C) : ℤ) + 1) -
      componentPieceCount (actualAugmentedPath hP (by decide) C) = 0)
    (hentryEdge : (actualComponentHead hP C, sigma slot) ∈ P.edges)
    (hentryWeight : ew 14 (actualComponentHead hP C) (sigma slot) = 2)
    (hexitEdge : (slot, actualComponentTail hP A) ∈ P.edges)
    (hexitWeight : ew 14 slot (actualComponentTail hP A) = 2) : False := by
  exact actual_rigid_source_no_direct_connector_reduced hP (by decide) hred C A slot
    (actual_augmented_zero_residual_certificate hP C hη hlast hzero)
    hentryEdge hentryWeight hexitEdge hexitWeight

end Haruhi
