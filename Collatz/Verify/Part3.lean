import Collatz.VerifyCore

namespace Collatz

theorem chunk_300001 : allDesc 10000 300001 = true := by decide +kernel

theorem chunk_310001 : allDesc 10000 310001 = true := by decide +kernel

theorem chunk_320001 : allDesc 10000 320001 = true := by decide +kernel

theorem chunk_330001 : allDesc 10000 330001 = true := by decide +kernel

theorem chunk_340001 : allDesc 10000 340001 = true := by decide +kernel

theorem chunk_350001 : allDesc 10000 350001 = true := by decide +kernel

theorem chunk_360001 : allDesc 10000 360001 = true := by decide +kernel

theorem chunk_370001 : allDesc 10000 370001 = true := by decide +kernel

theorem chunk_380001 : allDesc 10000 380001 = true := by decide +kernel

theorem chunk_390001 : allDesc 10000 390001 = true := by decide +kernel

theorem descent_part3 (n : Nat) (h1 : 300001 ≤ n) (h2 : n ≤ 400000) : HasDescent n := by
  by_cases c300001 : n ≤ 310000
  · exact descent_of_chunk (by omega) chunk_300001 (by omega) (by omega)
  by_cases c310001 : n ≤ 320000
  · exact descent_of_chunk (by omega) chunk_310001 (by omega) (by omega)
  by_cases c320001 : n ≤ 330000
  · exact descent_of_chunk (by omega) chunk_320001 (by omega) (by omega)
  by_cases c330001 : n ≤ 340000
  · exact descent_of_chunk (by omega) chunk_330001 (by omega) (by omega)
  by_cases c340001 : n ≤ 350000
  · exact descent_of_chunk (by omega) chunk_340001 (by omega) (by omega)
  by_cases c350001 : n ≤ 360000
  · exact descent_of_chunk (by omega) chunk_350001 (by omega) (by omega)
  by_cases c360001 : n ≤ 370000
  · exact descent_of_chunk (by omega) chunk_360001 (by omega) (by omega)
  by_cases c370001 : n ≤ 380000
  · exact descent_of_chunk (by omega) chunk_370001 (by omega) (by omega)
  by_cases c380001 : n ≤ 390000
  · exact descent_of_chunk (by omega) chunk_380001 (by omega) (by omega)
  by_cases c390001 : n ≤ 400000
  · exact descent_of_chunk (by omega) chunk_390001 (by omega) (by omega)
  omega

end Collatz
