import FreshGradientMinimax.KernelIteration
import Mathlib.Probability.Kernel.Composition.CompMap

/-! Transport of an actual Markov iteration through a measurable state map. -/

set_option autoImplicit false
noncomputable section
namespace FreshGradientMinimax
open MeasureTheory ProbabilityTheory
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

theorem iterateKernel_transport (K : Kernel X X) (L : Kernel Y Y)
    (f : X → Y) (hf : Measurable f) (hstep : L.comap f hf = K.map f) (n : ℕ) :
    (iterateKernel L n).comap f hf = (iterateKernel K n).map f := by
  have hs : L ∘ₖ Kernel.deterministic f hf = Kernel.deterministic f hf ∘ₖ K := by
    rw [Kernel.comp_deterministic_eq_comap, Kernel.deterministic_comp_eq_map, hstep]
  have hn : iterateKernel L n ∘ₖ Kernel.deterministic f hf =
      Kernel.deterministic f hf ∘ₖ iterateKernel K n := by
    induction n with
    | zero => simp only [iterateKernel, Kernel.id_comp, Kernel.comp_id]
    | succ n ih =>
      simp only [iterateKernel]
      rw [Kernel.comp_assoc, ih, ← Kernel.comp_assoc, hs, Kernel.comp_assoc]
  simpa only [Kernel.comp_deterministic_eq_comap, Kernel.deterministic_comp_eq_map] using hn

end FreshGradientMinimax
