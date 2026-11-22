import Collatz.Verify

/-!
# 壁: 有限のふるいでは終わらない

`n = 2^K·m − 1` は、最初の `2K` ステップでは一度も `n` を下回らない
(軌道は `3^j·2^(K−j)·m − 1` と上昇し続ける)。
したがって、`n mod 2^K` だけで決まる有限のふるいは、`K` をいくら大きくしても
すべての剰余類を覆えない(`2^K − 1` の類は降下が `K` ステップ以内に見えない)。
降下が起きるタイミングは、`n` の上位ビットに依存する。
-/

namespace Collatz

/-- 2 ステップずつの閉じた形: `iter (2j) (2^(j+e)·m − 1) = 3^j·2^e·m − 1`。 -/
theorem iter_two_pow_sub_one (m : Nat) (hm : 0 < m) :
    ∀ j e, iter (2 * j) (2 ^ (j + e) * m - 1) = 3 ^ j * 2 ^ e * m - 1 := by
  intro j
  induction j with
  | zero => intro e; simp
  | succ j ih =>
    intro e
    have e1 : j + 1 + e = j + (e + 1) := by omega
    have h2 : 2 * (j + 1) = 2 * j + 2 := by omega
    rw [e1, h2, iter_add, ih (e + 1)]
    have hQ : 0 < 3 ^ j * 2 ^ e * m :=
      Nat.mul_pos (Nat.mul_pos (Nat.pow_pos (by decide)) (Nat.pow_pos (by decide))) hm
    have a1 : 3 ^ j * 2 ^ (e + 1) * m = 2 * (3 ^ j * 2 ^ e * m) := by
      rw [Nat.pow_succ]; simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    have a2 : 3 ^ (j + 1) * 2 ^ e * m = 3 * (3 ^ j * 2 ^ e * m) := by
      rw [Nat.pow_succ]; simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    rw [a1, a2]
    generalize 3 ^ j * 2 ^ e * m = Q at *
    show step (step (2 * Q - 1)) = 3 * Q - 1
    have o : step (2 * Q - 1) = 3 * (2 * Q - 1) + 1 := step_odd (by omega)
    have o2 : step (3 * (2 * Q - 1) + 1) = (3 * (2 * Q - 1) + 1) / 2 := step_even (by omega)
    rw [o, o2]
    omega

end Collatz
