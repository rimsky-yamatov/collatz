import Collatz.Energy

/-!
# 「+1 の累積」c の評価と、エネルギー降下条件
-/

namespace Collatz

theorem two_pow_le_mul_three_pow (a b : Nat) : 2 ^ b ≤ 2 ^ b * 3 ^ a := by
  have : 1 ≤ 3 ^ a := Nat.one_le_pow _ _ (by decide)
  calc 2 ^ b = 2 ^ b * 1 := (Nat.mul_one _).symm
    _ ≤ 2 ^ b * 3 ^ a := Nat.mul_le_mul_left _ this

theorem pow_mul_succ_left (a b : Nat) : 2 ^ (b + 1) * 3 ^ a = 2 * (2 ^ b * 3 ^ a) := by
  rw [Nat.pow_succ, Nat.mul_comm (2 ^ b) 2, Nat.mul_assoc]

theorem pow_mul_succ_right (a b : Nat) : 2 ^ b * 3 ^ (a + 1) = 3 * (2 ^ b * 3 ^ a) := by
  rw [Nat.pow_succ, Nat.mul_comm (3 ^ a) 3, Nat.mul_left_comm]

/-- 補正項の上界: `2c + 2^b ≤ 2^b · 3^a`。 -/
theorem correction_bound (n : Nat) : ∀ k,
    2 * (stat n k).c + 2 ^ (stat n k).b ≤ 2 ^ (stat n k).b * 3 ^ (stat n k).a := by
  intro k
  induction k with
  | zero => simp [stat]
  | succ k ih =>
    by_cases h : iter k n % 2 = 0
    · have hs : stat n (k + 1) = ⟨(stat n k).a, (stat n k).b + 1, (stat n k).c⟩ := by
        simp [stat, h]
      rw [hs]
      show 2 * (stat n k).c + 2 ^ ((stat n k).b + 1) ≤ 2 ^ ((stat n k).b + 1) * 3 ^ (stat n k).a
      have h1 := two_pow_le_mul_three_pow (stat n k).a (stat n k).b
      rw [pow_mul_succ_left, Nat.pow_succ]
      omega
    · have hs : stat n (k + 1) =
          ⟨(stat n k).a + 1, (stat n k).b, 3 * (stat n k).c + 2 ^ (stat n k).b⟩ := by
        simp [stat, h]
      rw [hs]
      show 2 * (3 * (stat n k).c + 2 ^ (stat n k).b) + 2 ^ (stat n k).b
          ≤ 2 ^ (stat n k).b * 3 ^ ((stat n k).a + 1)
      rw [pow_mul_succ_right]
      omega

/-- エネルギーの下界(指数化): `3^a · n ≤ 2^b · x_k`。
`log` を取れば `E(x_k) ≥ E(n) + a·log 3 − b·log 2`。 -/
theorem energy_lower (n k : Nat) :
    3 ^ (stat n k).a * n ≤ 2 ^ (stat n k).b * iter k n := by
  rw [energy_identity]; omega

end Collatz
