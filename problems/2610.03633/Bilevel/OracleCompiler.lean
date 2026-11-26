import Bilevel.OracleMachineBind
import Bilevel.OracleMachineChoose
import Bilevel.OracleMachineResult

/-! Constructive compilation of the restricted causal syntax to the shared
BorelAdaptive.Program model. Correctness includes exact stopping and calls,
not merely equality of a desired output distribution. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace Bilevel.OracleCode
variable {Q O A B : Space}

def compile (q₀ : Q) (o₀ : O) : {A B : Space} → Code Q O A B → Machine Q O A B
  | _,_,.pure f hf => Machine.pure q₀ f hf
  | _,_,.call => Machine.call o₀
  | _,_,.bind p q => Machine.bind (compile q₀ o₀ p) (compile q₀ o₀ q)
  | _,_,.reparam p f hf => Machine.reparam (compile q₀ o₀ p) f hf
  | _,_,.choose p n hn => Machine.choose (fun i => compile q₀ o₀ (p i)) n hn

theorem compile_correct (q₀ : Q) (o₀ : O) (c : Code Q O A B) :
    Machine.Correct (compile q₀ o₀ c) c := by
  induction c with
  | pure f hf => exact Machine.pure_correct q₀ f hf
  | call => exact Machine.call_correct o₀
  | bind p q hp hq => exact Machine.bind_correct _ _ _ _ hp hq
  | reparam p f hf hp => exact Machine.reparam_correct _ _ hp f hf
  | choose p n hn hp => exact Machine.choose_correct _ _ hp n hn

theorem compiled_law {Seed : Type} [MeasurableSpace Seed]
    (ν : Measure Seed) [IsProbabilityMeasure ν] (response : Q → Seed → O)
    (hr : Measurable (Function.uncurry response)) (K : Kernel Q O) [IsMarkovKernel K]
    (hK : ∀ q,K q=ν.map (response q)) (q₀ : Q) (o₀ : O) (c : Code Q O A B) (a : A) :
    (IndependentStream.law ν).map (Machine.result (compile q₀ o₀ c) response a)=
      (denote K c).law (a,()) :=
  Machine.result_law _ c (compile_correct q₀ o₀ c) response a ν hr K hK

end Bilevel.OracleCode
