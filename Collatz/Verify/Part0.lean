import Collatz.VerifyCore

namespace Collatz

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

theorem descent_part0 (n : Nat) (h1 : 2 ≤ n) (h2 : n ≤ 100000) : HasDescent n := by
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

end Collatz
