import Collatz.Defs

/-!
# 基本補題
-/

namespace Collatz

theorem step_even {n : Nat} (h : n % 2 = 0) : step n = n / 2 := by
  simp [step, h]

theorem step_odd {n : Nat} (h : n % 2 = 1) : step n = 3 * n + 1 := by
  simp [step, h]

@[simp] theorem iter_zero (n : Nat) : iter 0 n = n := rfl

@[simp] theorem iter_succ (k n : Nat) : iter (k + 1) n = iter k (step n) := rfl

theorem iter_add (j k n : Nat) : iter (j + k) n = iter k (iter j n) := by
  induction j generalizing n with
  | zero => simp
  | succ j ih =>
    rw [Nat.succ_add, iter_succ, iter_succ, ih]

theorem iter_step_comm (k n : Nat) : iter k (step n) = step (iter k n) := by
  induction k generalizing n with
  | zero => rfl
  | succ k ih => simp [ih]

/-- 正の数は正のまま。 -/
theorem step_pos {n : Nat} (h : 0 < n) : 0 < step n := by
  unfold step
  split <;> omega

theorem iter_pos {n : Nat} (h : 0 < n) : ∀ k, 0 < iter k n := by
  intro k
  induction k generalizing n with
  | zero => simpa using h
  | succ k ih => simpa using ih (step_pos h)

/-- 既知の 4 → 2 → 1 → 4 の閉路。 -/
theorem cycle_one : iter 3 1 = 1 := by decide

theorem reachesOne_one : ReachesOne 1 := ⟨0, rfl⟩

/-- 1 に到達する点の `step` 像も 1 に到達する。 -/
theorem ReachesOne.of_step {n : Nat} (h : ReachesOne (step n)) : ReachesOne n := by
  obtain ⟨k, hk⟩ := h
  exact ⟨k + 1, by simpa using hk⟩

/-- 軌道上で `ReachesOne` は伝播する。 -/
theorem ReachesOne.of_iter {n : Nat} (k : Nat) (h : ReachesOne (iter k n)) : ReachesOne n := by
  obtain ⟨j, hj⟩ := h
  exact ⟨k + j, by rw [iter_add]; exact hj⟩

end Collatz
