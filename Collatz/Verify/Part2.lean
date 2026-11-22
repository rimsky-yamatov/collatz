import Collatz.VerifyCore

namespace Collatz

theorem chunk_200001 : allDesc 10000 200001 = true := by decide +kernel

theorem chunk_210001 : allDesc 10000 210001 = true := by decide +kernel

theorem chunk_220001 : allDesc 10000 220001 = true := by decide +kernel

theorem chunk_230001 : allDesc 10000 230001 = true := by decide +kernel

theorem chunk_240001 : allDesc 10000 240001 = true := by decide +kernel

theorem chunk_250001 : allDesc 10000 250001 = true := by decide +kernel

theorem chunk_260001 : allDesc 10000 260001 = true := by decide +kernel

theorem chunk_270001 : allDesc 10000 270001 = true := by decide +kernel

theorem chunk_280001 : allDesc 10000 280001 = true := by decide +kernel

theorem chunk_290001 : allDesc 10000 290001 = true := by decide +kernel

theorem descent_part2 (n : Nat) (h1 : 200001 ≤ n) (h2 : n ≤ 300000) : HasDescent n := by
  by_cases c200001 : n ≤ 210000
  · exact descent_of_chunk (by omega) chunk_200001 (by omega) (by omega)
  by_cases c210001 : n ≤ 220000
  · exact descent_of_chunk (by omega) chunk_210001 (by omega) (by omega)
  by_cases c220001 : n ≤ 230000
  · exact descent_of_chunk (by omega) chunk_220001 (by omega) (by omega)
  by_cases c230001 : n ≤ 240000
  · exact descent_of_chunk (by omega) chunk_230001 (by omega) (by omega)
  by_cases c240001 : n ≤ 250000
  · exact descent_of_chunk (by omega) chunk_240001 (by omega) (by omega)
  by_cases c250001 : n ≤ 260000
  · exact descent_of_chunk (by omega) chunk_250001 (by omega) (by omega)
  by_cases c260001 : n ≤ 270000
  · exact descent_of_chunk (by omega) chunk_260001 (by omega) (by omega)
  by_cases c270001 : n ≤ 280000
  · exact descent_of_chunk (by omega) chunk_270001 (by omega) (by omega)
  by_cases c280001 : n ≤ 290000
  · exact descent_of_chunk (by omega) chunk_280001 (by omega) (by omega)
  by_cases c290001 : n ≤ 300000
  · exact descent_of_chunk (by omega) chunk_290001 (by omega) (by omega)
  omega

end Collatz
