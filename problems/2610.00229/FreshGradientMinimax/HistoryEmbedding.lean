import FreshGradientMinimax.Algorithm
import FreshGradientMinimax.KLEmbedding

/-! Appending a response retains all information, even for arbitrary
measurable seed spaces. Its range is described only by the recorded query. -/

set_option autoImplicit false
noncomputable section
namespace FreshGradientMinimax
open MeasureTheory ProbabilityTheory

namespace Algorithm
variable {dx dy : ℕ} {Seed : Type*} [MeasurableSpace Seed] (A : Algorithm dx dy Seed)

def pop (n : ℕ) (t : RunState dx dy Seed (n + 1)) : RunState dx dy Seed n × Joint dx dy :=
  ((t.1, Fin.init t.2), (t.2 (Fin.last n)).2)

theorem pop_measurable (n : ℕ) :
    Measurable (pop (dx := dx) (dy := dy) (Seed := Seed) n) := by
  apply (measurable_fst.prodMk ?_).prodMk
    ((measurable_pi_apply (Fin.last n)).comp measurable_snd).snd
  exact measurable_pi_lambda _ (fun i => (measurable_pi_apply i.castSucc).comp measurable_snd)

theorem pop_append (n : ℕ) : Function.LeftInverse (pop n) (A.append n) := by
  intro sr
  simp [pop, append, Fin.init_snoc]

theorem append_pop {n : ℕ} (t : RunState dx dy Seed (n + 1))
    (ht : (t.2 (Fin.last n)).1 = A.query n (pop n t).1) : A.append n (pop n t) = t := by
  refine Prod.ext ?_ ?_
  · rfl
  change Fin.snoc (Fin.init t.2) (A.query n (pop n t).1, (t.2 (Fin.last n)).2) = t.2
  rw [← ht]
  exact Fin.snoc_init_self t.2

theorem append_range (n : ℕ) :
    Set.range (A.append n) = {t | (t.2 (Fin.last n)).1 = A.query n (pop n t).1} := by
  ext t
  constructor
  · rintro ⟨sr, rfl⟩
    simp [pop, append, Fin.init_snoc]
  · intro ht
    exact ⟨pop n t, A.append_pop t ht⟩

theorem append_measurableEmbedding (n : ℕ) : MeasurableEmbedding (A.append n) := by
  apply MeasurableEmbedding.of_measurable_inverse (A.append_measurable n) ?_
    (pop_measurable n) (A.pop_append n)
  rw [A.append_range]
  exact measurableSet_eq_fun ((measurable_pi_apply (Fin.last n)).comp measurable_snd).fst
    ((A.query_measurable n).comp (pop_measurable n).fst)

def historyLaw (ν : Measure Seed) (K : Kernel (Joint dx dy) (Joint dx dy)) (n : ℕ) :
    Measure (RunState dx dy Seed n) := A.historyKernel K n ∘ₘ ν

instance historyLaw_probability (ν : Measure Seed) [IsProbabilityMeasure ν]
    (K : Kernel (Joint dx dy) (Joint dx dy)) [IsMarkovKernel K] (n : ℕ) :
    IsProbabilityMeasure (A.historyLaw ν K n) := by unfold historyLaw; infer_instance

theorem historyLaw_succ (ν : Measure Seed) [IsProbabilityMeasure ν]
    (K : Kernel (Joint dx dy) (Joint dx dy)) [IsMarkovKernel K] (n : ℕ) :
    A.historyLaw ν K (n + 1) =
      ((A.historyLaw ν K n) ⊗ₘ A.responseKernel K n).map (A.append n) := by
  rw [Measure.compProd_eq_comp_prod, Measure.map_comp _ _ (A.append_measurable n)]
  exact Measure.comp_assoc.symm

theorem outputLaw_historyLaw (ν : Measure Seed)
    (K : Kernel (Joint dx dy) (Joint dx dy)) (n : ℕ) :
    A.outputLaw ν K n = (A.historyLaw ν K n).map (A.output n) := by
  exact (Measure.map_comp ν (A.historyKernel K n) (A.output_measurable n)).symm

end Algorithm
end FreshGradientMinimax
