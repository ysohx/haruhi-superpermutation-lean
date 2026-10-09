import Haruhi.StandardMatching
import Haruhi.GlobalCapacity
import Haruhi.Lifting

/-!
# A lower bound for fourteen-symbol superpermutations

The final word theorem assumes only the ordinary superpermutation property.
All path reductions, finite counting, and local geometric capacities are
proved in the imported files. No numerical capacity premise is supplied.
-/
namespace Haruhi
open Hunter PreimageChain

/-- Every reduced Hamiltonian path obeys the new numerical bound. -/
theorem reduced_hamiltonian_fourteen_lower_bound
    (P : HPath 14) (hP : P.IsHamiltonian) (hred : Sigma2Reduced P) :
    93890701078 ≤ P.wtP + 14 := by
  have hcapacity := actual_global_capacity_of_good_count hP hred
    (actual_standard_count hP hred)
  apply length_lower_bound_from_global_capacity_nat
    (δ := actualDelta P) (T := 77 * actualDelta P - 479001600 + 12)
  · unfold actualDelta
    push_cast
    ring
  · rfl
  · exact hcapacity

/-- Every word containing all fourteen-symbol permutations as contiguous
subwords has at least 93,890,701,078 symbols. -/
theorem superpermutation_fourteen_lower_bound
    (w : List ℕ) (hw : IsSuperperm 14 w) :
    93890701078 ≤ w.length := by
  exact superpermutation_word_bound_of_reduced (by decide : 3 ≤ 14)
    reduced_hamiltonian_fourteen_lower_bound hw

/-- The minimum superpermutation length on fourteen symbols obeys the bound. -/
theorem minimum_superpermutation_fourteen_lower_bound :
    93890701078 ≤ Ssuper 14 := by
  exact superpermutation_minimum_bound_of_reduced (by decide : 3 ≤ 14)
    reduced_hamiltonian_fourteen_lower_bound

end Haruhi
