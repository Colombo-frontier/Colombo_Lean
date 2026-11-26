import Bilevel.OracleCodeHistory
import Bilevel.OracleCodeConfidence

/-! Existing confidence-amplification code under arbitrary entering history.
Candidates are drawn sequentially with the actual updated history. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace Bilevel.OracleCode.History
set_option autoImplicit false
variable {Q O A H : Space} {E : Type}
  [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  (K : Kernel (Q × H) O) [IsMarkovKernel K]
  (update : (Q × H) × O → H) (hu : Measurable update)

omit [NormedAddCommGroup E] [BorelSpace E] [SecondCountableTopology E] in
theorem denote_collect (c : Code Q O A (of E)) (n : ℕ) :
    denote K update hu (collect c n)=StatefulConfidence.collect (denote K update hu c) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [collect,collectStep,denote,denote_map,ih,StatefulConfidence.collect,StatefulConfidence.step]

theorem denote_amplify (c : Code Q O A (of E)) (q : ℕ) [NeZero q] :
    denote K update hu (amplify c q)=StatefulConfidence.amplify (denote K update hu c) q := by
  simp only [amplify,denote_map,denote_collect,StatefulConfidence.amplify]

end Bilevel.OracleCode.History
