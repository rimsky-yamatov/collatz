import Collatz.VerifyCore

namespace Collatz

theorem chunk_500001 : allDesc 10000 500001 = true := by decide +kernel

theorem chunk_510001 : allDesc 10000 510001 = true := by decide +kernel

theorem chunk_520001 : allDesc 10000 520001 = true := by decide +kernel

theorem chunk_530001 : allDesc 10000 530001 = true := by decide +kernel

theorem chunk_540001 : allDesc 10000 540001 = true := by decide +kernel

theorem chunk_550001 : allDesc 10000 550001 = true := by decide +kernel

theorem chunk_560001 : allDesc 10000 560001 = true := by decide +kernel

theorem chunk_570001 : allDesc 10000 570001 = true := by decide +kernel

theorem chunk_580001 : allDesc 10000 580001 = true := by decide +kernel

theorem chunk_590001 : allDesc 10000 590001 = true := by decide +kernel

theorem descent_part5 (n : Nat) (h1 : 500001 ≤ n) (h2 : n ≤ 600000) : HasDescent n := by
  by_cases c500001 : n ≤ 510000
  · exact descent_of_chunk (by omega) chunk_500001 (by omega) (by omega)
  by_cases c510001 : n ≤ 520000
  · exact descent_of_chunk (by omega) chunk_510001 (by omega) (by omega)
  by_cases c520001 : n ≤ 530000
  · exact descent_of_chunk (by omega) chunk_520001 (by omega) (by omega)
  by_cases c530001 : n ≤ 540000
  · exact descent_of_chunk (by omega) chunk_530001 (by omega) (by omega)
  by_cases c540001 : n ≤ 550000
  · exact descent_of_chunk (by omega) chunk_540001 (by omega) (by omega)
  by_cases c550001 : n ≤ 560000
  · exact descent_of_chunk (by omega) chunk_550001 (by omega) (by omega)
  by_cases c560001 : n ≤ 570000
  · exact descent_of_chunk (by omega) chunk_560001 (by omega) (by omega)
  by_cases c570001 : n ≤ 580000
  · exact descent_of_chunk (by omega) chunk_570001 (by omega) (by omega)
  by_cases c580001 : n ≤ 590000
  · exact descent_of_chunk (by omega) chunk_580001 (by omega) (by omega)
  by_cases c590001 : n ≤ 600000
  · exact descent_of_chunk (by omega) chunk_590001 (by omega) (by omega)
  omega

end Collatz
