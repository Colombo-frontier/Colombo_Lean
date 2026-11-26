import HeavyTail.AdaptiveKernelExecution
import Mathlib.MeasureTheory.MeasurableSpace.Constructions

/-! Arbitrary time- and history-dependent reply kernels are a special case
of the actual adaptive execution model: the query records the full past.
This imposes no stationarity restriction on the generic online theorem. -/
noncomputable section
open MeasureTheory ProbabilityTheory

namespace HeavyTail.AdaptiveKernel
universe u
variable {Seed Reply : Type u} [MeasurableSpace Seed] [MeasurableSpace Reply]

abbrev FullHistoryQuery (Seed Reply : Type u) := (t : ℕ) × History Seed Reply t

def changingResponseKernel (κ : (t : ℕ) → Kernel (History Seed Reply t) Reply) :
    Kernel (FullHistoryQuery Seed Reply) Reply where
  toFun q := κ q.1 q.2
  measurable' := by
    intro S hS
    change MeasurableSet[⨅ t, (inferInstance : MeasurableSpace (History Seed Reply t)).map (Sigma.mk t)] _
    rw [MeasurableSpace.measurableSet_iInf]
    intro t
    exact (κ t).measurable hS

instance changingResponseKernel_markov (κ : (t : ℕ) → Kernel (History Seed Reply t) Reply)
    [∀ t, IsMarkovKernel (κ t)] : IsMarkovKernel (changingResponseKernel κ) where
  isProbabilityMeasure q := inferInstanceAs (IsProbabilityMeasure (κ q.1 q.2))

def fullHistoryPolicy (T : ℕ) : Policy Seed (FullHistoryQuery Seed Reply) Reply PUnit.{u + 1} T where
  query t h := ⟨t, h⟩
  query_measurable t := Measurable.of_le_map (iInf_le _ t)
  output _ := PUnit.unit
  output_measurable := measurable_const

theorem fullHistoryPolicy_replyKernel (κ : (t : ℕ) → Kernel (History Seed Reply t) Reply)
    (T t : ℕ) : (fullHistoryPolicy T).replyKernel (changingResponseKernel κ) t = κ t := by
  ext h S hS
  rfl

def changingHistoryLaw (P : Measure Seed) (κ : (t : ℕ) → Kernel (History Seed Reply t) Reply) :
    (t : ℕ) → Measure (History Seed Reply t)
  | 0 => P
  | t + 1 => (changingHistoryLaw P κ t).compProd (κ t)

theorem fullHistoryPolicy_historyLaw (P : Measure Seed)
    (κ : (t : ℕ) → Kernel (History Seed Reply t) Reply) (T t : ℕ) :
    (fullHistoryPolicy T).historyLaw P (changingResponseKernel κ) t = changingHistoryLaw P κ t := by
  induction t with
  | zero => rfl
  | succ t ih =>
      rw [Policy.historyLaw_succ, ih, fullHistoryPolicy_replyKernel]
      rfl

instance changingHistoryLaw_probability (P : Measure Seed) [IsProbabilityMeasure P]
    (κ : (t : ℕ) → Kernel (History Seed Reply t) Reply) [∀ t, IsMarkovKernel (κ t)] (t : ℕ) :
    IsProbabilityMeasure (changingHistoryLaw P κ t) := by
  rw [← fullHistoryPolicy_historyLaw P κ t t]
  infer_instance

end HeavyTail.AdaptiveKernel
