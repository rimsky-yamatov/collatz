import Collatz.Wall

/-!
# 閉路

* 閉路上では総エネルギー変化がゼロ: `2^b·n = 3^a·n + c`。
* 検証済みの範囲 `N` 以下に、自明な閉路 `{1, 2, 4}` 以外の閉路は存在しない。
-/

namespace Collatz

/-- 閉路のエネルギー収支: `iter k n = n` なら `3^a·n + c = 2^b·n`。 -/
theorem cycle_energy_balance {n k : Nat} (h : iter k n = n) :
    3 ^ (stat n k).a * n + (stat n k).c = 2 ^ (stat n k).b * n := by
  have := energy_identity n k
  rw [h] at this
  omega

theorem orbit_one (t : Nat) : iter t 1 = 1 ∨ iter t 1 = 4 ∨ iter t 1 = 2 := by
  induction t with
  | zero => left; rfl
  | succ t ih =>
    rw [iter_succ']
    rcases ih with h | h | h <;> rw [h] <;> decide

theorem iter_mul_of_cycle {n k : Nat} (h : iter k n = n) : ∀ q, iter (q * k) n = n := by
  intro q
  induction q with
  | zero => simp
  | succ q ih =>
    have : (q + 1) * k = k + q * k := by rw [Nat.succ_mul, Nat.add_comm]
    rw [this, iter_add, h, ih]

/-- 検証済み範囲 `N` に含まれる閉路上の点は `1, 2, 4` のみ。 -/
theorem cycle_trivial_of_verified {N : Nat} (hv : ∀ n, 0 < n → n ≤ N → ReachesOne n)
    {n k : Nat} (hk : 0 < k) (hn : 0 < n) (hnN : n ≤ N) (hc : iter k n = n) :
    n = 1 ∨ n = 2 ∨ n = 4 := by
  obtain ⟨j, hj⟩ := hv n hn hnN
  have hq := iter_mul_of_cycle hc (j + 1)
  have hle : j ≤ (j + 1) * k := by
    have : (j + 1) * 1 ≤ (j + 1) * k := Nat.mul_le_mul_left (j + 1) hk
    omega
  obtain ⟨t, ht⟩ : ∃ t, (j + 1) * k = j + t := ⟨(j + 1) * k - j, by omega⟩
  rw [ht, iter_add, hj] at hq
  rcases orbit_one t with h | h | h <;> rw [h] at hq <;> omega

theorem no_small_cycles :
    ∀ n k, 0 < k → 0 < n → n ≤ 1000000 → iter k n = n → n = 1 ∨ n = 2 ∨ n = 4 :=
  fun _ _ hk hn hnN hc => cycle_trivial_of_verified verified_1000000 hk hn hnN hc

end Collatz
