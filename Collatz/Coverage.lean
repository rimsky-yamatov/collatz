import Collatz.Certify

/-!
# 剰余類ふるいの被覆

`badClasses K` は `certify` で降下を確定できなかった剰余類(mod 2^K)の一覧。
それ以外のクラスに属する n は、すべて降下する。
-/

namespace Collatz

/-- 証明書が通らなかった剰余類。 -/
def badClasses (K : Nat) : List Nat :=
  (List.range (2 ^ K)).filter (fun r => !certify K r)

theorem descent_off_bad {K n : Nat} (h : n % 2 ^ K ∉ badClasses K) : HasDescent n := by
  by_cases hc : certify K (n % 2 ^ K) = true
  · exact descent_of_certify hc
  · exfalso
    apply h
    unfold badClasses
    rw [List.mem_filter, List.mem_range]
    exact ⟨Nat.mod_lt _ (Nat.pow_pos (by decide)), by simpa using hc⟩

/-- mod 256 で未確定の剰余類(0 と 1 を含む)。 -/
theorem badClasses_8 : badClasses 8 =
    [0, 1, 27, 31, 47, 63, 71, 91, 103, 111, 127, 155, 159, 167, 191, 207, 223, 231, 239, 251, 255] := by
  decide +kernel

theorem badClasses_12_length : (badClasses 12).length = 228 := by decide +kernel

/-- 末尾再帰の個数カウント(巨大なリストを作らない)。 -/
def countBad (K : Nat) : Nat → Nat → Nat
  | 0, acc => acc
  | i + 1, acc => countBad K i (if certify K i then acc else acc + 1)

theorem countBad_12 : countBad 12 (2 ^ 12) 0 = 228 := by decide +kernel

end Collatz
