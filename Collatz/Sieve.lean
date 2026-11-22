import Collatz.EnergyDescent

/-!
# 剰余類によるふるい(証明できる部分結果)

`n` を 2 の冪で割った余りだけで決まる初期の軌道を追えば、降下が証明できる剰余類がある。
-/

namespace Collatz

/-- n ≡ 0 (mod 2): 1 ステップで n/2 < n。 -/
theorem descent_mod2 {n : Nat} (hn : 1 < n) (h : n % 2 = 0) : HasDescent n := by
  refine ⟨1, by decide, ?_⟩
  have s1 : step (n) = (n) / 2 := step_even (by omega)
  simp only [iter, s1]
  omega

/-- n ≡ 1 (mod 4), n>1: 3 ステップで (3n+1)/4 < n。 -/
theorem descent_mod4 {n : Nat} (hn : 1 < n) (h : n % 4 = 1) : HasDescent n := by
  refine ⟨3, by decide, ?_⟩
  have s1 : step (n) = 3 * (n) + 1 := step_odd (by omega)
  have s2 : step (3 * (n) + 1) = (3 * (n) + 1) / 2 := step_even (by omega)
  have s3 : step ((3 * (n) + 1) / 2) = ((3 * (n) + 1) / 2) / 2 := step_even (by omega)
  simp only [iter, s1, s2, s3]
  omega

/-- n ≡ 3 (mod 16): 6 ステップで降下。 -/
theorem descent_mod16 {n : Nat} (hn : 1 < n) (h : n % 16 = 3) : HasDescent n := by
  refine ⟨6, by decide, ?_⟩
  have s1 : step (n) = 3 * (n) + 1 := step_odd (by omega)
  have s2 : step (3 * (n) + 1) = (3 * (n) + 1) / 2 := step_even (by omega)
  have s3 : step ((3 * (n) + 1) / 2) = 3 * ((3 * (n) + 1) / 2) + 1 := step_odd (by omega)
  have s4 : step (3 * ((3 * (n) + 1) / 2) + 1) = (3 * ((3 * (n) + 1) / 2) + 1) / 2 := step_even (by omega)
  have s5 : step ((3 * ((3 * (n) + 1) / 2) + 1) / 2) = ((3 * ((3 * (n) + 1) / 2) + 1) / 2) / 2 := step_even (by omega)
  have s6 : step (((3 * ((3 * (n) + 1) / 2) + 1) / 2) / 2) = (((3 * ((3 * (n) + 1) / 2) + 1) / 2) / 2) / 2 := step_even (by omega)
  simp only [iter, s1, s2, s3, s4, s5, s6]
  omega

/-- n ≡ 11 (mod 32): 降下する。 -/
theorem descent_mod32_11 {n : Nat} (hn : 1 < n) (h : n % 32 = 11) : HasDescent n := by
  refine ⟨8, by decide, ?_⟩
  have s1 : step (n) = 3 * (n) + 1 := step_odd (by omega)
  have s2 : step (3 * (n) + 1) = (3 * (n) + 1) / 2 := step_even (by omega)
  have s3 : step ((3 * (n) + 1) / 2) = 3 * ((3 * (n) + 1) / 2) + 1 := step_odd (by omega)
  have s4 : step (3 * ((3 * (n) + 1) / 2) + 1) = (3 * ((3 * (n) + 1) / 2) + 1) / 2 := step_even (by omega)
  have s5 : step ((3 * ((3 * (n) + 1) / 2) + 1) / 2) = ((3 * ((3 * (n) + 1) / 2) + 1) / 2) / 2 := step_even (by omega)
  have s6 : step (((3 * ((3 * (n) + 1) / 2) + 1) / 2) / 2) = 3 * (((3 * ((3 * (n) + 1) / 2) + 1) / 2) / 2) + 1 := step_odd (by omega)
  have s7 : step (3 * (((3 * ((3 * (n) + 1) / 2) + 1) / 2) / 2) + 1) = (3 * (((3 * ((3 * (n) + 1) / 2) + 1) / 2) / 2) + 1) / 2 := step_even (by omega)
  have s8 : step ((3 * (((3 * ((3 * (n) + 1) / 2) + 1) / 2) / 2) + 1) / 2) = ((3 * (((3 * ((3 * (n) + 1) / 2) + 1) / 2) / 2) + 1) / 2) / 2 := step_even (by omega)
  simp only [iter, s1, s2, s3, s4, s5, s6, s7, s8]
  omega

end Collatz
