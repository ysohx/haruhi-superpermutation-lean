import PreimageChain.RotationProgress
import Hunter.ProofsLstar

/-!
# Lifting reduced Hamiltonian path bounds to superpermutation words

These implications do not assume a numerical conclusion. The final theorem
must supply its actual proof for every reduced Hamiltonian path.
-/
namespace Haruhi
open Hunter PreimageChain
open scoped Classical

/-- A bound for all reduced Hamiltonian paths holds for every Hamiltonian
path because the proved reduction never increases total overlap weight. -/
theorem hamiltonian_bound_of_reduced
    {k B : ℕ} (hk : 3 ≤ k)
    (hbound : ∀ P : HPath k, P.IsHamiltonian → Sigma2Reduced P → B ≤ P.wtP + k)
    {P : HPath k} (hP : P.IsHamiltonian) : B ≤ P.wtP + k := by
  obtain ⟨Q, hQ, hred, hweight⟩ := sigma2_reduced_normal_form hk hP
  have h := hbound Q hQ hred
  omega

/-- Take the actual minimum over Hamiltonian paths. -/
theorem graph_minimum_bound_of_reduced
    {k B : ℕ} (hk : 3 ≤ k)
    (hbound : ∀ P : HPath k, P.IsHamiltonian → Sigma2Reduced P → B ≤ P.wtP + k) :
    B ≤ L k + k := by
  have hset : {m : ℕ | ∃ P : HPath k, P.IsHamiltonian ∧ P.wtP = m}.Nonempty := by
    obtain ⟨P, hP⟩ := Hunter.ProofsSpine.exists_ham k
    exact ⟨P.wtP, P, hP, rfl⟩
  have hmin : L k ∈ {m : ℕ | ∃ P : HPath k, P.IsHamiltonian ∧ P.wtP = m} := by
    unfold L
    exact Nat.sInf_mem hset
  obtain ⟨P, hP, hweight⟩ := hmin
  have h := hamiltonian_bound_of_reduced hk hbound hP
  simpa only [hweight] using h

/-- Every literal superpermutation word obeys the reduced-path lower bound,
using Hunter's proved word-to-graph overlap bridge. -/
theorem superpermutation_word_bound_of_reduced
    {k B : ℕ} (hk : 3 ≤ k)
    (hbound : ∀ P : HPath k, P.IsHamiltonian → Sigma2Reduced P → B ≤ P.wtP + k)
    {w : List ℕ} (hw : IsSuperperm k w) : B ≤ w.length := by
  exact (graph_minimum_bound_of_reduced hk hbound).trans
    (Hunter.ProofsLstar.dirA (by omega) hw)

/-- The minimum superpermutation length obeys the same bound. -/
theorem superpermutation_minimum_bound_of_reduced
    {k B : ℕ} (hk : 3 ≤ k)
    (hbound : ∀ P : HPath k, P.IsHamiltonian → Sigma2Reduced P → B ≤ P.wtP + k) :
    B ≤ Ssuper k := by
  rw [← Hunter.Proved.bridge_Lstar_eq_Ssuper (by omega : 1 ≤ k)]
  change B ≤ L k + k
  exact graph_minimum_bound_of_reduced hk hbound

/-- Specialized entry point for the fourteen-episode theorem. -/
theorem superpermutation_fourteen_bounds_of_reduced
    {B : ℕ}
    (hbound : ∀ P : HPath 14, P.IsHamiltonian → Sigma2Reduced P → B ≤ P.wtP + 14) :
    (∀ w : List ℕ, IsSuperperm 14 w → B ≤ w.length) ∧ B ≤ Ssuper 14 := by
  constructor
  · intro w hw
    exact superpermutation_word_bound_of_reduced (by decide) hbound hw
  · exact superpermutation_minimum_bound_of_reduced (by decide) hbound

end Haruhi
