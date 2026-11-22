import Collatz.VerifyCore

namespace Collatz

theorem chunk_600001 : allDesc 10000 600001 = true := by decide +kernel

theorem chunk_610001 : allDesc 10000 610001 = true := by decide +kernel

theorem chunk_620001 : allDesc 10000 620001 = true := by decide +kernel

theorem chunk_630001 : allDesc 10000 630001 = true := by decide +kernel

theorem chunk_640001 : allDesc 10000 640001 = true := by decide +kernel

theorem chunk_650001 : allDesc 10000 650001 = true := by decide +kernel

theorem chunk_660001 : allDesc 10000 660001 = true := by decide +kernel

theorem chunk_670001 : allDesc 10000 670001 = true := by decide +kernel

theorem chunk_680001 : allDesc 10000 680001 = true := by decide +kernel

theorem chunk_690001 : allDesc 10000 690001 = true := by decide +kernel

theorem descent_part6 (n : Nat) (h1 : 600001 ≤ n) (h2 : n ≤ 700000) : HasDescent n := by
  by_cases c600001 : n ≤ 610000
  · exact descent_of_chunk (by omega) chunk_600001 (by omega) (by omega)
  by_cases c610001 : n ≤ 620000
  · exact descent_of_chunk (by omega) chunk_610001 (by omega) (by omega)
  by_cases c620001 : n ≤ 630000
  · exact descent_of_chunk (by omega) chunk_620001 (by omega) (by omega)
  by_cases c630001 : n ≤ 640000
  · exact descent_of_chunk (by omega) chunk_630001 (by omega) (by omega)
  by_cases c640001 : n ≤ 650000
  · exact descent_of_chunk (by omega) chunk_640001 (by omega) (by omega)
  by_cases c650001 : n ≤ 660000
  · exact descent_of_chunk (by omega) chunk_650001 (by omega) (by omega)
  by_cases c660001 : n ≤ 670000
  · exact descent_of_chunk (by omega) chunk_660001 (by omega) (by omega)
  by_cases c670001 : n ≤ 680000
  · exact descent_of_chunk (by omega) chunk_670001 (by omega) (by omega)
  by_cases c680001 : n ≤ 690000
  · exact descent_of_chunk (by omega) chunk_680001 (by omega) (by omega)
  by_cases c690001 : n ≤ 700000
  · exact descent_of_chunk (by omega) chunk_690001 (by omega) (by omega)
  omega

end Collatz
