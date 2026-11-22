import Collatz.VerifyCore

namespace Collatz

theorem chunk_800001 : allDesc 10000 800001 = true := by decide +kernel

theorem chunk_810001 : allDesc 10000 810001 = true := by decide +kernel

theorem chunk_820001 : allDesc 10000 820001 = true := by decide +kernel

theorem chunk_830001 : allDesc 10000 830001 = true := by decide +kernel

theorem chunk_840001 : allDesc 10000 840001 = true := by decide +kernel

theorem chunk_850001 : allDesc 10000 850001 = true := by decide +kernel

theorem chunk_860001 : allDesc 10000 860001 = true := by decide +kernel

theorem chunk_870001 : allDesc 10000 870001 = true := by decide +kernel

theorem chunk_880001 : allDesc 10000 880001 = true := by decide +kernel

theorem chunk_890001 : allDesc 10000 890001 = true := by decide +kernel

theorem descent_part8 (n : Nat) (h1 : 800001 ≤ n) (h2 : n ≤ 900000) : HasDescent n := by
  by_cases c800001 : n ≤ 810000
  · exact descent_of_chunk (by omega) chunk_800001 (by omega) (by omega)
  by_cases c810001 : n ≤ 820000
  · exact descent_of_chunk (by omega) chunk_810001 (by omega) (by omega)
  by_cases c820001 : n ≤ 830000
  · exact descent_of_chunk (by omega) chunk_820001 (by omega) (by omega)
  by_cases c830001 : n ≤ 840000
  · exact descent_of_chunk (by omega) chunk_830001 (by omega) (by omega)
  by_cases c840001 : n ≤ 850000
  · exact descent_of_chunk (by omega) chunk_840001 (by omega) (by omega)
  by_cases c850001 : n ≤ 860000
  · exact descent_of_chunk (by omega) chunk_850001 (by omega) (by omega)
  by_cases c860001 : n ≤ 870000
  · exact descent_of_chunk (by omega) chunk_860001 (by omega) (by omega)
  by_cases c870001 : n ≤ 880000
  · exact descent_of_chunk (by omega) chunk_870001 (by omega) (by omega)
  by_cases c880001 : n ≤ 890000
  · exact descent_of_chunk (by omega) chunk_880001 (by omega) (by omega)
  by_cases c890001 : n ≤ 900000
  · exact descent_of_chunk (by omega) chunk_890001 (by omega) (by omega)
  omega

end Collatz
