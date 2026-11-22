import Collatz.ClassDescent

/-!
# 剰余類ふるいの証明書チェッカ

`certify K r` は `r` (< 2^K) の軌道を追跡し、`b < K` を保ったままエネルギー降下
`3^a·r + c < 2^b·r` に到達できるかを判定する計算可能関数。
その健全性(`certify K r = true` ⇒ `n ≡ r (mod 2^K)` の全ての n が降下する)を証明する。
-/

namespace Collatz

/-- 状態 `(j, x, a, b, c)` から先を追跡する(`f` は停止性のための燃料)。 -/
def go (K r : Nat) : Nat → Nat → Nat → Nat → Nat → Nat → Bool
  | 0, _, _, _, _, _ => false
  | f + 1, j, x, a, b, c =>
    if 0 < j ∧ 3 ^ a * r + c < 2 ^ b * r then true
    else if b < K then
      (if x % 2 = 0 then go K r f (j + 1) (x / 2) a (b + 1) c
       else go K r f (j + 1) (3 * x + 1) (a + 1) b (3 * c + 2 ^ b))
    else false

/-- 証明書: 燃料 400 で追跡。 -/
def certify (K r : Nat) : Bool := go K r 400 0 r 0 0 0

/-- 状態が実際の軌道・統計と一致している。 -/
def Inv (r j x a b c : Nat) : Prop :=
  x = iter j r ∧ a = (stat r j).a ∧ b = (stat r j).b ∧ c = (stat r j).c

theorem go_sound (K r : Nat) : ∀ f j x a b c,
    Inv r j x a b c → (∀ i, i < j → (stat r i).b < K) →
    go K r f j x a b c = true →
    ∃ k, 0 < k ∧ (∀ i, i < k → (stat r i).b < K) ∧ EnergyDrop r k := by
  intro f
  induction f with
  | zero => intro j x a b c _ _ h; simp [go] at h
  | succ f ih =>
    intro j x a b c hI hb h
    obtain ⟨hx, ha, hbb, hc⟩ := hI
    unfold go at h
    by_cases hd : 0 < j ∧ 3 ^ a * r + c < 2 ^ b * r
    · refine ⟨j, hd.1, hb, ?_⟩
      unfold EnergyDrop
      rw [← ha, ← hbb, ← hc]
      exact hd.2
    · rw [if_neg hd] at h
      by_cases hbK : b < K
      · rw [if_pos hbK] at h
        have hbj : ∀ i, i < j + 1 → (stat r i).b < K := by
          intro i hi
          by_cases hij : i < j
          · exact hb i hij
          · have : i = j := by omega
            subst this; rw [← hbb]; exact hbK
        by_cases hp : x % 2 = 0
        · rw [if_pos hp] at h
          have hp' : iter j r % 2 = 0 := by rw [← hx]; exact hp
          refine ih (j + 1) (x / 2) a (b + 1) c ⟨?_, ?_, ?_, ?_⟩ hbj h
          · rw [iter_succ', step_even hp', hx]
          · simp [stat, hp', ha]
          · simp [stat, hp', hbb]
          · simp [stat, hp', hc]
        · rw [if_neg hp] at h
          have hp' : ¬ (iter j r % 2 = 0) := by rw [← hx]; exact hp
          refine ih (j + 1) (3 * x + 1) (a + 1) b (3 * c + 2 ^ b) ⟨?_, ?_, ?_, ?_⟩ hbj h
          · rw [iter_succ', step_odd (by omega), hx]
          · simp [stat, hp', ha]
          · simp [stat, hp', hbb]
          · simp [stat, hp', hc, hbb]
      · rw [if_neg hbK] at h; simp at h

theorem certify_sound {K r : Nat} (h : certify K r = true) :
    ∃ k, 0 < k ∧ (∀ i, i < k → (stat r i).b < K) ∧ EnergyDrop r k :=
  go_sound K r 400 0 r 0 0 0 ⟨by simp, by simp [stat], by simp [stat], by simp [stat]⟩
    (by intro i hi; omega) h

/-- ふるいの健全性: `certify K (n % 2^K) = true` なら `n > 0` の降下が確定する。 -/
theorem descent_of_certify {K n : Nat} (h : certify K (n % 2 ^ K) = true) : HasDescent n := by
  obtain ⟨k, hk, hb, hdrop⟩ := certify_sound h
  exact descent_of_class hk hb hdrop (Nat.mod_lt _ (Nat.pow_pos (by decide))) rfl

end Collatz
