import Collatz.VerifyCore

namespace Collatz

theorem chunk_900001 : allDesc 10000 900001 = true := by decide +kernel

theorem chunk_910001 : allDesc 10000 910001 = true := by decide +kernel

theorem chunk_920001 : allDesc 10000 920001 = true := by decide +kernel

theorem chunk_930001 : allDesc 10000 930001 = true := by decide +kernel

theorem chunk_940001 : allDesc 10000 940001 = true := by decide +kernel

theorem chunk_950001 : allDesc 10000 950001 = true := by decide +kernel

theorem chunk_960001 : allDesc 10000 960001 = true := by decide +kernel

theorem chunk_970001 : allDesc 10000 970001 = true := by decide +kernel

theorem chunk_980001 : allDesc 10000 980001 = true := by decide +kernel

theorem chunk_990001 : allDesc 10000 990001 = true := by decide +kernel

theorem descent_part9 (n : Nat) (h1 : 900001 ≤ n) (h2 : n ≤ 1000000) : HasDescent n := by
  by_cases c900001 : n ≤ 910000
  · exact descent_of_chunk (by omega) chunk_900001 (by omega) (by omega)
  by_cases c910001 : n ≤ 920000
  · exact descent_of_chunk (by omega) chunk_910001 (by omega) (by omega)
  by_cases c920001 : n ≤ 930000
  · exact descent_of_chunk (by omega) chunk_920001 (by omega) (by omega)
  by_cases c930001 : n ≤ 940000
  · exact descent_of_chunk (by omega) chunk_930001 (by omega) (by omega)
  by_cases c940001 : n ≤ 950000
  · exact descent_of_chunk (by omega) chunk_940001 (by omega) (by omega)
  by_cases c950001 : n ≤ 960000
  · exact descent_of_chunk (by omega) chunk_950001 (by omega) (by omega)
  by_cases c960001 : n ≤ 970000
  · exact descent_of_chunk (by omega) chunk_960001 (by omega) (by omega)
  by_cases c970001 : n ≤ 980000
  · exact descent_of_chunk (by omega) chunk_970001 (by omega) (by omega)
  by_cases c980001 : n ≤ 990000
  · exact descent_of_chunk (by omega) chunk_980001 (by omega) (by omega)
  by_cases c990001 : n ≤ 1000000
  · exact descent_of_chunk (by omega) chunk_990001 (by omega) (by omega)
  omega

end Collatz
