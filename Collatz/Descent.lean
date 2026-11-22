import Collatz.Basic

/-!
# 降下基準(停止時間)

コラッツ予想は「1 より大きいすべての `n` が、いつか自分より小さい値に降りる」
ことと同値。ここから先の議論はすべて「降下を示す」問題に帰着する。
-/

namespace Collatz

/-- `n` は有限回の後、自分自身より小さくなる(停止時間が有限)。 -/
def HasDescent (n : Nat) : Prop := ∃ k, 0 < k ∧ iter k n < n

/-- 降下基準 ⇒ コラッツ予想(強い帰納法)。 -/
theorem conjecture_of_descent (h : ∀ n, 1 < n → HasDescent n) : Conjecture := by
  intro n hn
  induction n using Nat.strongRecOn with
  | _ n ih =>
    by_cases h1 : n = 1
    · subst h1; exact reachesOne_one
    · obtain ⟨k, _, hk⟩ := h n (by omega)
      exact ReachesOne.of_iter k (ih _ hk (iter_pos hn k))

/-- コラッツ予想 ⇒ 降下基準。 -/
theorem descent_of_conjecture (h : Conjecture) : ∀ n, 1 < n → HasDescent n := by
  intro n hn
  obtain ⟨k, hk⟩ := h n (by omega)
  refine ⟨k, ?_, by omega⟩
  rcases Nat.eq_zero_or_pos k with rfl | hpos
  · simp at hk; omega
  · exact hpos

/-- コラッツ予想 ⟺ 全ての n > 1 に降下がある。 -/
theorem conjecture_iff_descent : Conjecture ↔ ∀ n, 1 < n → HasDescent n :=
  ⟨descent_of_conjecture, conjecture_of_descent⟩

end Collatz
