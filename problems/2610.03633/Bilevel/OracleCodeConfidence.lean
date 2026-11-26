import Bilevel.OracleCode
import Bilevel.StatefulConfidence

/-! Actual confidence amplification in the causal oracle syntax: collect
the executed candidates, then apply the checked measurable selector. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace Bilevel.OracleCode
variable {Q O A : Space} {E : Type}
  [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

def collectStep (c : Code Q O A (of E)) (n : ℕ) :
    Code Q O (prod A (of (Fin n → E))) (of (Fin (n+1) → E)) :=
  map (.reparam c Prod.fst measurable_fst) (StatefulConfidence.append n)
    (StatefulConfidence.append_measurable n)

def collect (c : Code Q O A (of E)) : (n : ℕ) → Code Q O A (of (Fin n → E))
  | 0 => .pure (fun _ => Fin.elim0) (by fun_prop)
  | n+1 => .bind (collect c n) (collectStep c n)

def amplify (c : Code Q O A (of E)) (q : ℕ) [NeZero q] : Code Q O A (of E) :=
  map (collect c q) (fun z => ConditionalConfidence.select z.2)
    (ConditionalConfidence.select_measurable (fun z : A × (Fin q → E) => z.2)
      (fun i => (measurable_pi_apply i).comp measurable_snd))

omit [NormedAddCommGroup E] [BorelSpace E] [SecondCountableTopology E] in
theorem denote_collect (K : Kernel Q O) [IsMarkovKernel K] (c : Code Q O A (of E)) (n : ℕ) :
    denote K (collect c n)=StatefulConfidence.collect (denote K c) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [collect,collectStep,denote,denote_map,ih,StatefulConfidence.collect,StatefulConfidence.step]

theorem denote_amplify (K : Kernel Q O) [IsMarkovKernel K] (c : Code Q O A (of E))
    (q : ℕ) [NeZero q] : denote K (amplify c q)=StatefulConfidence.amplify (denote K c) q := by
  simp only [amplify,denote_map,denote_collect,StatefulConfidence.amplify]

end Bilevel.OracleCode
