import Collatz.Main

/-!
# 未解決部分(ここが壁)

`energy_drop_open` は **証明されていない**(`sorry`)。これはコラッツ予想そのものと同値であり、
ここまでの形式化は「予想を厳密にエネルギー降下の問題へ還元した」ところまで。

エネルギーの議論が止まる理由:
* 平均的には 奇数ステップで `+log(3/2)`、偶数ステップで `−log 2` で、ドリフトは負(確率的ヒューリスティック)。
* しかし個々の軌道で `a·log 3 − b·log 2 < 0` になる窓が存在すること、および
  補正項 `c` が `3^a·n` に比べて小さいこと(`energyDrop_of_drift` の仮定)は、
  `n` の 2 進展開(= 軌道そのもの)の情報なしには示せない。
  この情報を得る手段が、まさに未解決の部分である。
-/

namespace Collatz

/-- OPEN: コラッツ予想と同値なエネルギー降下命題。未証明。 -/
theorem energy_drop_open : ∀ n, 1 < n → ∃ k, 0 < k ∧ EnergyDrop n k := by
  sorry

/-- `energy_drop_open` を仮定した場合のコラッツ予想(`sorry` を経由する)。 -/
theorem collatz_conjecture : Conjecture :=
  conjecture_iff_energyDrop.2 energy_drop_open

end Collatz
