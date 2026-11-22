import Collatz.VerifyCore

namespace Collatz

theorem chunk_400001 : allDesc 10000 400001 = true := by decide +kernel

theorem chunk_410001 : allDesc 10000 410001 = true := by decide +kernel

theorem chunk_420001 : allDesc 10000 420001 = true := by decide +kernel

theorem chunk_430001 : allDesc 10000 430001 = true := by decide +kernel

theorem chunk_440001 : allDesc 10000 440001 = true := by decide +kernel

theorem chunk_450001 : allDesc 10000 450001 = true := by decide +kernel

theorem chunk_460001 : allDesc 10000 460001 = true := by decide +kernel

theorem chunk_470001 : allDesc 10000 470001 = true := by decide +kernel

theorem chunk_480001 : allDesc 10000 480001 = true := by decide +kernel

theorem chunk_490001 : allDesc 10000 490001 = true := by decide +kernel

theorem descent_part4 (n : Nat) (h1 : 400001 ≤ n) (h2 : n ≤ 500000) : HasDescent n := by
  by_cases c400001 : n ≤ 410000
  · exact descent_of_chunk (by omega) chunk_400001 (by omega) (by omega)
  by_cases c410001 : n ≤ 420000
  · exact descent_of_chunk (by omega) chunk_410001 (by omega) (by omega)
  by_cases c420001 : n ≤ 430000
  · exact descent_of_chunk (by omega) chunk_420001 (by omega) (by omega)
  by_cases c430001 : n ≤ 440000
  · exact descent_of_chunk (by omega) chunk_430001 (by omega) (by omega)
  by_cases c440001 : n ≤ 450000
  · exact descent_of_chunk (by omega) chunk_440001 (by omega) (by omega)
  by_cases c450001 : n ≤ 460000
  · exact descent_of_chunk (by omega) chunk_450001 (by omega) (by omega)
  by_cases c460001 : n ≤ 470000
  · exact descent_of_chunk (by omega) chunk_460001 (by omega) (by omega)
  by_cases c470001 : n ≤ 480000
  · exact descent_of_chunk (by omega) chunk_470001 (by omega) (by omega)
  by_cases c480001 : n ≤ 490000
  · exact descent_of_chunk (by omega) chunk_480001 (by omega) (by omega)
  by_cases c490001 : n ≤ 500000
  · exact descent_of_chunk (by omega) chunk_490001 (by omega) (by omega)
  omega

end Collatz
