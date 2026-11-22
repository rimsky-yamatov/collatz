import Collatz.Descent

/-!
# 対数エネルギーの厳密な記帳

エネルギーを `E(x) = log x` とする。コア Lean には `Real.log` が無いので、
対数不等式はすべて指数化した形(整数の不等式)で書く。

`k` ステップの間に、奇数ステップが `a` 回、偶数ステップが `b` 回あったとき、
3n+1 の「+1」の累積を `c` として次の厳密な関係が成り立つ:

    2^b * x_k = 3^a * n + c        (x_k = iter k n)

両辺の対数を取ると
    E(x_k) − E(n) = a·log 3 − b·log 2 + log(1 + c / (3^a n))
で、右辺第 3 項が「+1 の補正」。
-/

namespace Collatz

/-- 軌道の統計: 奇数ステップ数 `a`、偶数ステップ数 `b`、「+1」の累積 `c`。 -/
structure Stat where
  a : Nat
  b : Nat
  c : Nat

/-- `n` から `k` ステップ進んだ時点までの統計。 -/
def stat (n : Nat) : Nat → Stat
  | 0 => ⟨0, 0, 0⟩
  | k + 1 =>
    let s := stat n k
    if iter k n % 2 = 0 then ⟨s.a, s.b + 1, s.c⟩
    else ⟨s.a + 1, s.b, 3 * s.c + 2 ^ s.b⟩

theorem iter_succ' (k n : Nat) : iter (k + 1) n = step (iter k n) := by
  rw [iter_succ, iter_step_comm]

/-- 厳密なエネルギー恒等式: `2^b · x_k = 3^a · n + c`。 -/
theorem energy_identity (n : Nat) : ∀ k,
    2 ^ (stat n k).b * iter k n = 3 ^ (stat n k).a * n + (stat n k).c := by
  intro k
  induction k with
  | zero => simp [stat]
  | succ k ih =>
    rw [iter_succ']
    by_cases h : iter k n % 2 = 0
    · have hs : stat n (k + 1) = ⟨(stat n k).a, (stat n k).b + 1, (stat n k).c⟩ := by
        simp [stat, h]
      rw [hs, step_even h]
      have hx : 2 * (iter k n / 2) = iter k n := by omega
      show 2 ^ ((stat n k).b + 1) * (iter k n / 2) = _
      rw [Nat.pow_succ, Nat.mul_assoc, hx]
      exact ih
    · have h' : iter k n % 2 = 1 := by omega
      have hs : stat n (k + 1) =
          ⟨(stat n k).a + 1, (stat n k).b, 3 * (stat n k).c + 2 ^ (stat n k).b⟩ := by
        simp [stat, h]
      rw [hs, step_odd h']
      show 2 ^ (stat n k).b * (3 * iter k n + 1)
          = 3 ^ ((stat n k).a + 1) * n + (3 * (stat n k).c + 2 ^ (stat n k).b)
      rw [Nat.pow_succ, Nat.mul_add, Nat.mul_left_comm, ih]
      rw [Nat.mul_add, Nat.mul_comm (3 ^ (stat n k).a) 3, Nat.mul_assoc]
      omega

end Collatz
