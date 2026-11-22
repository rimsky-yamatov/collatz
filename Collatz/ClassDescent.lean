import Collatz.Congruence
import Collatz.EnergyDescent

/-!
# 剰余類からの降下(一般定理)

`n ≡ r (mod 2^K)` で、`r` 自身の軌道の先頭 `k` ステップにおける偶数ステップ数が常に `K` 未満なら、
`n` と `r` は先頭 `k` ステップで同じパリティ列(= 同じ統計 `a, b, c`)をたどる。
`r` で `3^a·r + c < 2^b·r`(エネルギー降下)なら、`n ≥ r` でも降下する。
-/

namespace Collatz

theorem sync (K r n : Nat) (hn : n % 2 ^ K = r % 2 ^ K) : ∀ k,
    (∀ j, j < k → (stat r j).b < K) →
    stat n k = stat r k ∧
    iter k n % 2 ^ (K - (stat r k).b) = iter k r % 2 ^ (K - (stat r k).b) := by
  intro k
  induction k with
  | zero => intro _; simpa [stat] using hn
  | succ k ih =>
    intro hb
    obtain ⟨heq, hcong⟩ := ih (fun j hj => hb j (by omega))
    have hbk : (stat r k).b < K := hb k (by omega)
    have hpar : iter k n % 2 = iter k r % 2 :=
      mod_two_of_mod_pow (by omega) hcong
    by_cases h : iter k n % 2 = 0
    · have h' : iter k r % 2 = 0 := by omega
      have hs_n : stat n (k + 1) = ⟨(stat n k).a, (stat n k).b + 1, (stat n k).c⟩ := by
        simp [stat, h]
      have hs_r : stat r (k + 1) = ⟨(stat r k).a, (stat r k).b + 1, (stat r k).c⟩ := by
        simp [stat, h']
      refine ⟨by rw [hs_n, hs_r, heq], ?_⟩
      rw [hs_r]
      show iter (k + 1) n % 2 ^ (K - ((stat r k).b + 1)) = iter (k + 1) r % 2 ^ (K - ((stat r k).b + 1))
      rw [iter_succ', iter_succ', step_even h, step_even h']
      obtain ⟨s, hs⟩ : ∃ s, K - (stat r k).b = s + 1 := ⟨K - (stat r k).b - 1, by omega⟩
      have e : K - ((stat r k).b + 1) = s := by omega
      rw [e]
      rw [hs] at hcong
      exact mod_half h h' hcong
    · have h1 : iter k n % 2 = 1 := by omega
      have h1' : iter k r % 2 = 1 := by omega
      have hs_n : stat n (k + 1) =
          ⟨(stat n k).a + 1, (stat n k).b, 3 * (stat n k).c + 2 ^ (stat n k).b⟩ := by
        simp [stat, h]
      have hs_r : stat r (k + 1) =
          ⟨(stat r k).a + 1, (stat r k).b, 3 * (stat r k).c + 2 ^ (stat r k).b⟩ := by
        simp [stat, show ¬ (iter k r % 2 = 0) by omega]
      refine ⟨by rw [hs_n, hs_r, heq], ?_⟩
      rw [hs_r]
      show iter (k + 1) n % 2 ^ (K - (stat r k).b) = iter (k + 1) r % 2 ^ (K - (stat r k).b)
      rw [iter_succ', iter_succ', step_odd h1, step_odd h1']
      exact mod_three_mul_add_one hcong

/-- 一般の剰余類降下定理。 -/
theorem descent_of_class {K r k n : Nat} (hk : 0 < k)
    (hb : ∀ j, j < k → (stat r j).b < K) (hdrop : EnergyDrop r k)
    (hr : r < 2 ^ K) (hn : n % 2 ^ K = r) : HasDescent n := by
  have hn' : n % 2 ^ K = r % 2 ^ K := by rw [hn, Nat.mod_eq_of_lt hr]
  obtain ⟨hsn, _⟩ := sync K r n hn' k hb
  refine ⟨k, hk, ?_⟩
  rw [iter_lt_iff_energyDrop]
  have hrn : r ≤ n := by have := Nat.mod_le n (2 ^ K); omega
  unfold EnergyDrop at hdrop ⊢
  rw [hsn]
  generalize (stat r k).a = a at *
  generalize (stat r k).b = b at *
  generalize (stat r k).c = c at *
  have hlt : 3 ^ a < 2 ^ b := by
    by_cases hr0 : r = 0
    · subst hr0; simp at hdrop
    · exact Nat.lt_of_mul_lt_mul_right (a := r) (by omega)
  obtain ⟨d, hd⟩ : ∃ d, 2 ^ b = 3 ^ a + d := ⟨2 ^ b - 3 ^ a, by omega⟩
  have h1 : d * r ≤ d * n := Nat.mul_le_mul_left d hrn
  rw [hd, Nat.add_mul] at hdrop ⊢
  omega

end Collatz
