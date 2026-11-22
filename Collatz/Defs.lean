/-!
# 基本定義

コラッツ写像 `collatz`、反復 `iter`、「1 に到達する」という述語 `ReachesOne`。
-/

namespace Collatz

/-- コラッツ写像: 偶数なら半分、奇数なら 3n+1。 -/
def step (n : Nat) : Nat :=
  if n % 2 = 0 then n / 2 else 3 * n + 1

/-- `step` を `k` 回適用する。 -/
def iter : Nat → Nat → Nat
  | 0, n => n
  | k + 1, n => iter k (step n)

/-- `n` が有限回の反復で 1 に到達する。 -/
def ReachesOne (n : Nat) : Prop := ∃ k, iter k n = 1

/-- コラッツ予想: すべての正の整数は 1 に到達する。 -/
def Conjecture : Prop := ∀ n, 0 < n → ReachesOne n

end Collatz
