import Collatz.Coverage

/-!
# 有限検証: N 以下のすべての n が 1 に到達する

各 `n ≤ N` について「自分より小さくなる時点」を計算し、降下基準 + 強い帰納法で
`ReachesOne` を結論する。
-/

namespace Collatz

/-- 初期値 `n` について、現在値 `x` から先に `n` より小さくなる点があるか(燃料つき)。 -/
def desc (n : Nat) : Nat → Nat → Bool
  | 0, _ => false
  | f + 1, x => if step x < n then true else desc n f (step x)

theorem desc_sound (n : Nat) : ∀ f j x, x = iter j n → desc n f x = true →
    ∃ k, 0 < k ∧ iter k n < n := by
  intro f
  induction f with
  | zero => intro j x _ h; simp [desc] at h
  | succ f ih =>
    intro j x hx h
    unfold desc at h
    by_cases hlt : step x < n
    · refine ⟨j + 1, by omega, ?_⟩
      rw [iter_succ', ← hx]; exact hlt
    · rw [if_neg hlt] at h
      exact ih (j + 1) (step x) (by rw [iter_succ', hx]) h

/-- `i` 以上 `i + f` 未満のすべての n を調べる。 -/
def allDesc : Nat → Nat → Bool
  | 0, _ => true
  | f + 1, i => desc i 5000 i && allDesc f (i + 1)

theorem allDesc_sound : ∀ f i, 2 ≤ i → allDesc f i = true →
    ∀ n, i ≤ n → n < i + f → HasDescent n := by
  intro f
  induction f with
  | zero => intro i _ _ n h1 h2; omega
  | succ f ih =>
    intro i hi h n h1 h2
    unfold allDesc at h
    rw [Bool.and_eq_true] at h
    by_cases hn : n = i
    · subst hn
      exact desc_sound n 5000 0 n rfl h.1
    · exact ih (i + 1) (by omega) h.2 n (by omega) (by omega)

/-- N 以下の降下がすべて確認できれば、N 以下はすべて 1 に到達する。 -/
theorem reachesOne_le_of_allDesc {N : Nat} (h : allDesc (N - 1) 2 = true) :
    ∀ n, 0 < n → n ≤ N → ReachesOne n := by
  intro n hn hnN
  induction n using Nat.strongRecOn with
  | _ n ih =>
    by_cases h1 : n = 1
    · subst h1; exact reachesOne_one
    · obtain ⟨k, _, hk⟩ := allDesc_sound (N - 1) 2 (by omega) h n (by omega) (by omega)
      exact ReachesOne.of_iter k (ih _ hk (iter_pos hn k) (by omega))

theorem chunk_2 : allDesc 10000 2 = true := by decide +kernel

theorem chunk_10002 : allDesc 10000 10002 = true := by decide +kernel

theorem chunk_20002 : allDesc 10000 20002 = true := by decide +kernel

theorem chunk_30002 : allDesc 10000 30002 = true := by decide +kernel

theorem chunk_40002 : allDesc 10000 40002 = true := by decide +kernel

theorem chunk_50002 : allDesc 10000 50002 = true := by decide +kernel

theorem chunk_60002 : allDesc 10000 60002 = true := by decide +kernel

theorem chunk_70002 : allDesc 10000 70002 = true := by decide +kernel

theorem chunk_80002 : allDesc 10000 80002 = true := by decide +kernel

theorem chunk_90002 : allDesc 9999 90002 = true := by decide +kernel

/-- 区間チェックから個別の降下を取り出す。 -/
theorem descent_of_chunk {f i : Nat} (hi : 2 ≤ i) (h : allDesc f i = true) {n : Nat}
    (h1 : i ≤ n) (h2 : n < i + f) : HasDescent n := allDesc_sound f i hi h n h1 h2

theorem allDesc_all (n : Nat) (h1 : 2 ≤ n) (h2 : n ≤ 100000) : HasDescent n := by
  by_cases c2 : n ≤ 10001
  · exact descent_of_chunk (by omega) chunk_2 (by omega) (by omega)
  by_cases c10002 : n ≤ 20001
  · exact descent_of_chunk (by omega) chunk_10002 (by omega) (by omega)
  by_cases c20002 : n ≤ 30001
  · exact descent_of_chunk (by omega) chunk_20002 (by omega) (by omega)
  by_cases c30002 : n ≤ 40001
  · exact descent_of_chunk (by omega) chunk_30002 (by omega) (by omega)
  by_cases c40002 : n ≤ 50001
  · exact descent_of_chunk (by omega) chunk_40002 (by omega) (by omega)
  by_cases c50002 : n ≤ 60001
  · exact descent_of_chunk (by omega) chunk_50002 (by omega) (by omega)
  by_cases c60002 : n ≤ 70001
  · exact descent_of_chunk (by omega) chunk_60002 (by omega) (by omega)
  by_cases c70002 : n ≤ 80001
  · exact descent_of_chunk (by omega) chunk_70002 (by omega) (by omega)
  by_cases c80002 : n ≤ 90001
  · exact descent_of_chunk (by omega) chunk_80002 (by omega) (by omega)
  by_cases c90002 : n ≤ 100000
  · exact descent_of_chunk (by omega) chunk_90002 (by omega) (by omega)
  omega

theorem verified_100000 : ∀ n, 0 < n → n ≤ 100000 → ReachesOne n := by
  intro n hn hnN
  induction n using Nat.strongRecOn with
  | _ n ih =>
    by_cases h1 : n = 1
    · subst h1; exact reachesOne_one
    · obtain ⟨k, _, hk⟩ := allDesc_all n (by omega) hnN
      exact ReachesOne.of_iter k (ih _ hk (iter_pos hn k) (by omega))

end Collatz
