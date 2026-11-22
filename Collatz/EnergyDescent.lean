import Collatz.Bounds

/-!
# エネルギー降下基準

`x_k < n` を指数化したエネルギー条件 `3^a·n + c < 2^b·n` に厳密に言い換える。
(`log` を取れば `E(x_k) < E(n)`。)
-/

namespace Collatz

/-- 軌道が `k` ステップ目までに「エネルギーを下げた」:
`E(x_k) < E(n)` の指数化形 `3^a·n + c < 2^b·n`。 -/
def EnergyDrop (n k : Nat) : Prop :=
  3 ^ (stat n k).a * n + (stat n k).c < 2 ^ (stat n k).b * n

/-- 厳密な言い換え: `x_k < n ⟺ エネルギーが下がる`。 -/
theorem iter_lt_iff_energyDrop (n k : Nat) :
    iter k n < n ↔ EnergyDrop n k := by
  unfold EnergyDrop
  rw [← energy_identity]
  exact (Nat.mul_lt_mul_left (Nat.pow_pos (by decide))).symm

/-- 降下 ⟺ エネルギー降下(ステップ数 k > 0 付き)。 -/
theorem hasDescent_iff_energyDrop (n : Nat) :
    HasDescent n ↔ ∃ k, 0 < k ∧ EnergyDrop n k := by
  constructor
  · rintro ⟨k, hk, h⟩; exact ⟨k, hk, (iter_lt_iff_energyDrop n k).1 h⟩
  · rintro ⟨k, hk, h⟩; exact ⟨k, hk, (iter_lt_iff_energyDrop n k).2 h⟩

/-- 十分条件(負のドリフト + 補正が小さい):
`2·3^a·n + 2^b·3^a ≤ 2·2^b·n` なら降下する。
`log` で見ると「`a·log 3 − b·log 2` が十分負で、`n` が `3^a` に比べ大きい」こと。 -/
theorem energyDrop_of_drift (n k : Nat)
    (h : 2 * 3 ^ (stat n k).a * n + 2 ^ (stat n k).b * 3 ^ (stat n k).a
        ≤ 2 * 2 ^ (stat n k).b * n) :
    EnergyDrop n k := by
  have h1 := correction_bound n k
  unfold EnergyDrop
  -- 2c < 2^b·3^a  なので  2(3^a n + c) < 2·3^a n + 2^b 3^a ≤ 2·2^b n
  have hpos : 0 < 2 ^ (stat n k).b := Nat.pow_pos (by decide)
  have h2 : (stat n k).c * 2 + 2 ^ (stat n k).b ≤ 2 ^ (stat n k).b * 3 ^ (stat n k).a := by omega
  have e1 : 2 * 3 ^ (stat n k).a * n = 2 * (3 ^ (stat n k).a * n) := Nat.mul_assoc _ _ _
  have e2 : 2 * 2 ^ (stat n k).b * n = 2 * (2 ^ (stat n k).b * n) := Nat.mul_assoc _ _ _
  omega

end Collatz
