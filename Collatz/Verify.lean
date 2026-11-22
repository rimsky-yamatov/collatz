import Collatz.VerifyCore
import Collatz.Verify.Part0
import Collatz.Verify.Part1
import Collatz.Verify.Part2
import Collatz.Verify.Part3
import Collatz.Verify.Part4
import Collatz.Verify.Part5
import Collatz.Verify.Part6
import Collatz.Verify.Part7
import Collatz.Verify.Part8
import Collatz.Verify.Part9

/-!
# 有限検証: 10^6 以下のすべての n が 1 に到達する
-/

namespace Collatz

theorem descent_le (n : Nat) (h1 : 2 ≤ n) (h2 : n ≤ 1000000) : HasDescent n := by
  by_cases p0 : n ≤ 100000
  · exact descent_part0 n (by omega) (by omega)
  by_cases p1 : n ≤ 200000
  · exact descent_part1 n (by omega) (by omega)
  by_cases p2 : n ≤ 300000
  · exact descent_part2 n (by omega) (by omega)
  by_cases p3 : n ≤ 400000
  · exact descent_part3 n (by omega) (by omega)
  by_cases p4 : n ≤ 500000
  · exact descent_part4 n (by omega) (by omega)
  by_cases p5 : n ≤ 600000
  · exact descent_part5 n (by omega) (by omega)
  by_cases p6 : n ≤ 700000
  · exact descent_part6 n (by omega) (by omega)
  by_cases p7 : n ≤ 800000
  · exact descent_part7 n (by omega) (by omega)
  by_cases p8 : n ≤ 900000
  · exact descent_part8 n (by omega) (by omega)
  by_cases p9 : n ≤ 1000000
  · exact descent_part9 n (by omega) (by omega)
  omega

theorem verified_1000000 : ∀ n, 0 < n → n ≤ 1000000 → ReachesOne n := by
  intro n hn hnN
  induction n using Nat.strongRecOn with
  | _ n ih =>
    by_cases h1 : n = 1
    · subst h1; exact reachesOne_one
    · obtain ⟨k, _, hk⟩ := descent_le n (by omega) hnN
      exact ReachesOne.of_iter k (ih _ hk (iter_pos hn k) (by omega))

end Collatz
