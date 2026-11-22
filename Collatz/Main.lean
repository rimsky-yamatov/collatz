import Collatz.Sieve

/-!
# 対数エネルギー形でのコラッツ予想(厳密な同値)
-/

namespace Collatz

/-- コラッツ予想 ⟺ すべての n>1 で、ある k>0 について軌道のエネルギー `E = log` が
初期値より下がる(`3^a·n + c < 2^b·n`)。 -/
theorem conjecture_iff_energyDrop :
    Conjecture ↔ ∀ n, 1 < n → ∃ k, 0 < k ∧ EnergyDrop n k := by
  rw [conjecture_iff_descent]
  exact ⟨fun h n hn => (hasDescent_iff_energyDrop n).1 (h n hn),
         fun h n hn => (hasDescent_iff_energyDrop n).2 (h n hn)⟩

end Collatz
