import FreshGradientMinimax.BatchKernel
import FreshGradientMinimax.KernelTransport

/-! The iid minibatch sum equals a sequential one-sample-at-a-time
accumulator started at zero. -/

set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section
namespace FreshGradientMinimax
open MeasureTheory ProbabilityTheory
variable {d : ℕ}

def addSampleKernel (ν : Measure (Euclid d)) : Kernel (Euclid d) (Euclid d) :=
  (Kernel.id ×ₖ Kernel.const (Euclid d) ν).map (fun z => z.1 + z.2)

instance addSampleKernel_markov (ν : Measure (Euclid d)) [IsProbabilityMeasure ν] :
    IsMarkovKernel (addSampleKernel ν) := Kernel.IsMarkovKernel.map _ (measurable_fst.add measurable_snd)

theorem addSampleKernel_apply (ν : Measure (Euclid d)) [IsProbabilityMeasure ν] (s : Euclid d) :
    addSampleKernel ν s = ν.map (fun r => s + r) := by
  rw [addSampleKernel, Kernel.map_apply _ (measurable_fst.add measurable_snd), Kernel.prod_apply,
    Kernel.id_apply, Kernel.const_apply, Measure.dirac_prod,
    Measure.map_map (measurable_fst.add measurable_snd) measurable_prodMk_left]
  rfl

theorem iidSumKernel_congr_at {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (K : Kernel X (Euclid d)) [IsMarkovKernel K] (L : Kernel Y (Euclid d)) [IsMarkovKernel L]
    (x : X) (y : Y) (h : K x = L y) (n : ℕ) : iidSumKernel K n x = iidSumKernel L n y := by
  induction n with
  | zero => rfl
  | succ n ih => rw [iidSumKernel_succ, iidSumKernel_succ, ih, h]

theorem sequential_sum_kernel (ν : Measure (Euclid d)) [IsProbabilityMeasure ν] (n : ℕ) :
    iterateKernel (addSampleKernel ν) n ∘ₖ Kernel.deterministic (fun _ : Unit => 0) measurable_const =
      iidSumKernel (Kernel.const Unit ν) n := by
  induction n with
  | zero => simp only [iterateKernel, Kernel.id_comp, iidSumKernel]
  | succ n ih =>
    rw [iterateKernel, Kernel.comp_assoc, ih, addSampleKernel, ← Kernel.map_comp,
      Kernel.prod_const_comp, Kernel.id_comp, iidSumKernel]

theorem sequential_sum_apply (ν : Measure (Euclid d)) [IsProbabilityMeasure ν] (n : ℕ) :
    iterateKernel (addSampleKernel ν) n 0 = iidSumKernel (Kernel.const Unit ν) n () := by
  have h := congrArg (fun K : Kernel Unit (Euclid d) => K ()) (sequential_sum_kernel ν n)
  simpa only [Kernel.comp_deterministic_eq_comap, Kernel.comap_apply] using h

end FreshGradientMinimax
