import Collatz.Bounds

/-!
# 合同の伝播

`n ≡ r (mod 2^t)` のとき、1 ステップ後は
* 偶数ステップ: `n/2 ≡ r/2 (mod 2^(t-1))`
* 奇数ステップ: `3n+1 ≡ 3r+1 (mod 2^t)`
-/

namespace Collatz

theorem mod_two_of_mod_pow {x y t : Nat} (ht : 1 ≤ t) (h : x % 2 ^ t = y % 2 ^ t) :
    x % 2 = y % 2 := by
  have hd : 2 ∣ 2 ^ t := by
    obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
    exact ⟨2 ^ s, by rw [Nat.pow_succ, Nat.mul_comm]⟩
  rw [← Nat.mod_mod_of_dvd x hd, ← Nat.mod_mod_of_dvd y hd, h]

theorem mod_half {x y s : Nat} (hx : x % 2 = 0) (hy : y % 2 = 0)
    (h : x % 2 ^ (s + 1) = y % 2 ^ (s + 1)) : (x / 2) % 2 ^ s = (y / 2) % 2 ^ s := by
  have ex : x = 2 * (x / 2) := by omega
  have ey : y = 2 * (y / 2) := by omega
  rw [Nat.pow_succ, Nat.mul_comm (2 ^ s) 2] at h
  rw [ex, ey] at h
  rw [Nat.mul_mod_mul_left, Nat.mul_mod_mul_left] at h
  omega

theorem mod_three_mul_add_one {x y M : Nat} (h : x % M = y % M) :
    (3 * x + 1) % M = (3 * y + 1) % M := by
  rw [Nat.add_mod (3 * x), Nat.mul_mod 3 x, h, ← Nat.mul_mod, ← Nat.add_mod]

end Collatz
