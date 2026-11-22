import Collatz.VerifyCore

namespace Collatz

theorem chunk_700001 : allDesc 10000 700001 = true := by decide +kernel

theorem chunk_710001 : allDesc 10000 710001 = true := by decide +kernel

theorem chunk_720001 : allDesc 10000 720001 = true := by decide +kernel

theorem chunk_730001 : allDesc 10000 730001 = true := by decide +kernel

theorem chunk_740001 : allDesc 10000 740001 = true := by decide +kernel

theorem chunk_750001 : allDesc 10000 750001 = true := by decide +kernel

theorem chunk_760001 : allDesc 10000 760001 = true := by decide +kernel

theorem chunk_770001 : allDesc 10000 770001 = true := by decide +kernel

theorem chunk_780001 : allDesc 10000 780001 = true := by decide +kernel

theorem chunk_790001 : allDesc 10000 790001 = true := by decide +kernel

theorem descent_part7 (n : Nat) (h1 : 700001 ≤ n) (h2 : n ≤ 800000) : HasDescent n := by
  by_cases c700001 : n ≤ 710000
  · exact descent_of_chunk (by omega) chunk_700001 (by omega) (by omega)
  by_cases c710001 : n ≤ 720000
  · exact descent_of_chunk (by omega) chunk_710001 (by omega) (by omega)
  by_cases c720001 : n ≤ 730000
  · exact descent_of_chunk (by omega) chunk_720001 (by omega) (by omega)
  by_cases c730001 : n ≤ 740000
  · exact descent_of_chunk (by omega) chunk_730001 (by omega) (by omega)
  by_cases c740001 : n ≤ 750000
  · exact descent_of_chunk (by omega) chunk_740001 (by omega) (by omega)
  by_cases c750001 : n ≤ 760000
  · exact descent_of_chunk (by omega) chunk_750001 (by omega) (by omega)
  by_cases c760001 : n ≤ 770000
  · exact descent_of_chunk (by omega) chunk_760001 (by omega) (by omega)
  by_cases c770001 : n ≤ 780000
  · exact descent_of_chunk (by omega) chunk_770001 (by omega) (by omega)
  by_cases c780001 : n ≤ 790000
  · exact descent_of_chunk (by omega) chunk_780001 (by omega) (by omega)
  by_cases c790001 : n ≤ 800000
  · exact descent_of_chunk (by omega) chunk_790001 (by omega) (by omega)
  omega

end Collatz
