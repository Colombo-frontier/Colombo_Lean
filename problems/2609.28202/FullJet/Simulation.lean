import FullJet.RareComponent

namespace FullJet

/-- An oracle reply obtained by decoding the revealed row at the query. -/
def decodedOracle {Query Row Reply : Type*} (row : Query → Row)
    (decode : Query → Row → Reply) : Query → Reply := fun q => decode q (row q)

/-- A simulator maintains the entire state of the candidate jet algorithm.
This is deterministic and hence also applies separately to every private seed. -/
def rowSimulation {State Query Row Reply : Type*}
    (query : State → Query) (update : State → Reply → State)
    (row : Query → Row) (decode : Query → Row → Reply) (initial : State) : ℕ → State
  | 0 => initial
  | k + 1 => let s := rowSimulation query update row decode initial k
             update s (decode (query s) (row (query s)))

/-- Pathwise equality for a stronger row oracle, provided the actual replies
factor through the row. The factorization premise is explicit, not assumed as
an axiom about the dense weak hiding construction. -/
theorem row_simulation_exact {State Query Row Reply : Type*}
    (query : State → Query) (update : State → Reply → State)
    (row : Query → Row) (decode : Query → Row → Reply)
    (oracle : Query → Reply) (initial : State)
    (hdecode : ∀ q, oracle q = decode q (row q)) (k : ℕ) :
    rowSimulation query update row decode initial k = oracleRun query update oracle initial k := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [rowSimulation, oracleRun, ih, hdecode]

end FullJet
