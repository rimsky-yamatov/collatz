import Collatz.VerifyCore

namespace Collatz

theorem chunk_100001 : allDesc 10000 100001 = true := by decide +kernel

theorem chunk_110001 : allDesc 10000 110001 = true := by decide +kernel

theorem chunk_120001 : allDesc 10000 120001 = true := by decide +kernel

theorem chunk_130001 : allDesc 10000 130001 = true := by decide +kernel

theorem chunk_140001 : allDesc 10000 140001 = true := by decide +kernel

theorem chunk_150001 : allDesc 10000 150001 = true := by decide +kernel

theorem chunk_160001 : allDesc 10000 160001 = true := by decide +kernel

theorem chunk_170001 : allDesc 10000 170001 = true := by decide +kernel

theorem chunk_180001 : allDesc 10000 180001 = true := by decide +kernel

theorem chunk_190001 : allDesc 10000 190001 = true := by decide +kernel

theorem descent_part1 (n : Nat) (h1 : 100001 ≤ n) (h2 : n ≤ 200000) : HasDescent n := by
  by_cases c100001 : n ≤ 110000
  · exact descent_of_chunk (by omega) chunk_100001 (by omega) (by omega)
  by_cases c110001 : n ≤ 120000
  · exact descent_of_chunk (by omega) chunk_110001 (by omega) (by omega)
  by_cases c120001 : n ≤ 130000
  · exact descent_of_chunk (by omega) chunk_120001 (by omega) (by omega)
  by_cases c130001 : n ≤ 140000
  · exact descent_of_chunk (by omega) chunk_130001 (by omega) (by omega)
  by_cases c140001 : n ≤ 150000
  · exact descent_of_chunk (by omega) chunk_140001 (by omega) (by omega)
  by_cases c150001 : n ≤ 160000
  · exact descent_of_chunk (by omega) chunk_150001 (by omega) (by omega)
  by_cases c160001 : n ≤ 170000
  · exact descent_of_chunk (by omega) chunk_160001 (by omega) (by omega)
  by_cases c170001 : n ≤ 180000
  · exact descent_of_chunk (by omega) chunk_170001 (by omega) (by omega)
  by_cases c180001 : n ≤ 190000
  · exact descent_of_chunk (by omega) chunk_180001 (by omega) (by omega)
  by_cases c190001 : n ≤ 200000
  · exact descent_of_chunk (by omega) chunk_190001 (by omega) (by omega)
  omega

end Collatz
