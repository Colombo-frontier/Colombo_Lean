import FreshGradientMinimax.CostedTransition
import FreshGradientMinimax.RandomInput

/-! Sequential composition accumulates sampled natural-number costs.
Marginal laws compose exactly, and input-independent mean costs add. -/

set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section
namespace FreshGradientMinimax
open MeasureTheory ProbabilityTheory
variable {X Y Z : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]

def costedCompose (K : Kernel X (Y × ℕ)) (L : Kernel Y (Z × ℕ)) : Kernel X (Z × ℕ) :=
  costedCarryKernel L ∘ₖ K

instance costedCompose_markov (K : Kernel X (Y × ℕ)) [IsMarkovKernel K]
    (L : Kernel Y (Z × ℕ)) [IsMarkovKernel L] : IsMarkovKernel (costedCompose K L) := by
  unfold costedCompose
  infer_instance

theorem costedCompose_first (K : Kernel X (Y × ℕ)) [IsMarkovKernel K]
    (L : Kernel Y (Z × ℕ)) [IsMarkovKernel L] :
    (costedCompose K L).map Prod.fst = L.map Prod.fst ∘ₖ K.map Prod.fst := by
  rw [costedCompose, Kernel.map_comp, costedCarryKernel_first, ← Kernel.comp_map _ _ measurable_fst]

theorem costedCompose_cost (K : Kernel X (Y × ℕ)) [IsMarkovKernel K]
    (L : Kernel Y (Z × ℕ)) [IsMarkovKernel L] (x : X)
    (hK : Integrable costValue (K x)) (hL : ∀ y, Integrable costValue (L y))
    (c : ℝ) (hc : ∀ y, (∫ t, costValue t ∂L y) = c) :
    Integrable costValue (costedCompose K L x) ∧
    (∫ t, costValue t ∂costedCompose K L x) = (∫ t, costValue t ∂K x) + c := by
  have hstep (y : Y × ℕ) := costedCarryKernel_cost L y (hL y.1)
  have hi := (kernel_moment_from_envelope (costedCarryKernel L) (K x) costValue
    costValue_measurable.stronglyMeasurable (fun t => Nat.cast_nonneg t.2)
    (fun y => costValue y + c) (hK.add (integrable_const c))
    (fun y => (hstep y).1) (fun y => by rw [(hstep y).2, hc])).1
  change Integrable costValue (costedCompose K L x) at hi
  refine ⟨hi, ?_⟩
  rw [costedCompose, Kernel.integral_comp hi]
  simp_rw [(hstep _).2, hc]
  rw [integral_add hK (integrable_const c), integral_const, measureReal_univ_eq_one, one_smul]

def costedIterate (K : Kernel X (X × ℕ)) : ℕ → Kernel X (X × ℕ)
  | 0 => taggedKernel Kernel.id 0
  | n + 1 => costedCompose (costedIterate K n) K

instance costedIterate_markov (K : Kernel X (X × ℕ)) [IsMarkovKernel K] (n : ℕ) :
    IsMarkovKernel (costedIterate K n) := by
  induction n with
  | zero => dsimp [costedIterate]; infer_instance
  | succ n ih =>
    letI := ih
    change IsMarkovKernel (costedCompose (costedIterate K n) K)
    infer_instance

theorem costedIterate_first (K : Kernel X (X × ℕ)) [IsMarkovKernel K] (n : ℕ) :
    (costedIterate K n).map Prod.fst = iterateKernel (K.map Prod.fst) n := by
  induction n with
  | zero => exact taggedKernel_first _ _
  | succ n ih => rw [costedIterate, costedCompose_first, ih, iterateKernel]

theorem costedIterate_cost (K : Kernel X (X × ℕ)) [IsMarkovKernel K]
    (hi : ∀ x, Integrable costValue (K x)) (c : ℝ) (hc : ∀ x, (∫ t, costValue t ∂K x) = c)
    (n : ℕ) (x : X) :
    Integrable costValue (costedIterate K n x) ∧
    (∫ t, costValue t ∂costedIterate K n x) = (n : ℝ) * c := by
  induction n with
  | zero =>
    refine ⟨taggedKernel_cost_integrable _ _ _, ?_⟩
    simpa only [Nat.cast_zero, zero_mul] using taggedKernel_mean_cost (Kernel.id : Kernel X X) 0 x
  | succ n ih =>
    obtain ⟨hI, hM⟩ := costedCompose_cost (costedIterate K n) K x ih.1 hi c hc
    refine ⟨hI, ?_⟩
    change (∫ t, costValue t ∂costedCompose (costedIterate K n) K x) = _
    rw [hM, ih.2, Nat.cast_add, Nat.cast_one, add_mul, one_mul]

end FreshGradientMinimax
