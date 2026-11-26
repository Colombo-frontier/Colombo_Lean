import FreshGradientMinimax.CostedBatch
import FreshGradientMinimax.KernelTransport

/-! Measurable state updates preserve sampled costs and may add a known
natural-number cost. No independence between output and cost is assumed. -/

set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section
namespace FreshGradientMinimax
open MeasureTheory ProbabilityTheory
variable {X Y Z : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]

def costedUpdate (f : X × Y → Z) (c : X → ℕ) (t : X × (Y × ℕ)) : Z × ℕ :=
  (f (t.1, t.2.1), c t.1 + t.2.2)

theorem costedUpdate_measurable {f : X × Y → Z} (hf : Measurable f) {c : X → ℕ} (hc : Measurable c) :
    Measurable (costedUpdate f c) :=
  (hf.comp (measurable_fst.prodMk measurable_snd.fst)).prodMk ((hc.comp measurable_fst).add measurable_snd.snd)

def costedUpdateKernel (K : Kernel X (Y × ℕ)) (f : X × Y → Z) (c : X → ℕ) : Kernel X (Z × ℕ) :=
  (Kernel.id ×ₖ K).map (costedUpdate f c)

instance costedUpdateKernel_markov (K : Kernel X (Y × ℕ)) [IsMarkovKernel K]
    (f : X × Y → Z) (hf : Measurable f) (c : X → ℕ) (hc : Measurable c) :
    IsMarkovKernel (costedUpdateKernel K f c) :=
  Kernel.IsMarkovKernel.map _ (costedUpdate_measurable hf hc)

theorem costedUpdateKernel_apply (K : Kernel X (Y × ℕ)) [IsMarkovKernel K]
    (f : X × Y → Z) (hf : Measurable f) (c : X → ℕ) (hc : Measurable c) (x : X) :
    costedUpdateKernel K f c x = (K x).map (fun t => (f (x, t.1), c x + t.2)) := by
  rw [costedUpdateKernel, Kernel.map_apply _ (costedUpdate_measurable hf hc), Kernel.prod_apply,
    Kernel.id_apply, Measure.dirac_prod,
    Measure.map_map (costedUpdate_measurable hf hc) measurable_prodMk_left]
  rfl

theorem costedUpdateKernel_first (K : Kernel X (Y × ℕ)) [IsMarkovKernel K]
    (f : X × Y → Z) (hf : Measurable f) (c : X → ℕ) (hc : Measurable c) :
    (costedUpdateKernel K f c).map Prod.fst = (Kernel.id ×ₖ K.map Prod.fst).map f := by
  apply Kernel.ext
  intro x
  have hfx : Measurable (fun t : Y × ℕ => (f (x, t.1), c x + t.2)) :=
    (hf.comp (measurable_const.prodMk measurable_fst)).prodMk (measurable_const.add measurable_snd)
  rw [Kernel.map_apply _ measurable_fst, costedUpdateKernel_apply K f hf c hc,
    Measure.map_map measurable_fst hfx, Kernel.map_apply _ hf, Kernel.prod_apply, Kernel.id_apply,
    Measure.dirac_prod, Measure.map_map hf measurable_prodMk_left,
    Kernel.map_apply _ measurable_fst,
    Measure.map_map (hf.comp measurable_prodMk_left) measurable_fst]
  rfl

theorem costedUpdateKernel_cost (K : Kernel X (Y × ℕ)) [IsMarkovKernel K]
    (f : X × Y → Z) (hf : Measurable f) (c : X → ℕ) (hc : Measurable c) (x : X)
    (hi : Integrable costValue (K x)) :
    Integrable costValue (costedUpdateKernel K f c x) ∧
    (∫ t, costValue t ∂costedUpdateKernel K f c x) = (c x : ℝ) + ∫ t, costValue t ∂K x := by
  rw [costedUpdateKernel_apply K f hf c hc]
  have hfx : Measurable (fun t : Y × ℕ => (f (x, t.1), c x + t.2)) :=
    (hf.comp (measurable_const.prodMk measurable_fst)).prodMk (measurable_const.add measurable_snd)
  constructor
  · apply (integrable_map_measure (g := costValue) (f := fun t : Y × ℕ => (f (x, t.1), c x + t.2))
      (μ := K x) costValue_measurable.aestronglyMeasurable hfx.aemeasurable).mpr
    simpa only [Function.comp_def, costValue, Nat.cast_add] using (integrable_const (μ := K x) (c x : ℝ)).add hi
  · rw [integral_map (f := costValue) (φ := fun t : Y × ℕ => (f (x, t.1), c x + t.2))
      hfx.aemeasurable costValue_measurable.aestronglyMeasurable]
    simp only [costValue, Nat.cast_add]
    change Integrable (fun t : Y × ℕ => (t.2 : ℝ)) (K x) at hi
    rw [integral_add (integrable_const _) hi, integral_const, measureReal_univ_eq_one, one_smul]

def costedCarryKernel (K : Kernel X (Y × ℕ)) : Kernel (X × ℕ) (Y × ℕ) :=
  costedUpdateKernel (K.comap Prod.fst measurable_fst) Prod.snd Prod.snd

instance costedCarryKernel_markov (K : Kernel X (Y × ℕ)) [IsMarkovKernel K] :
    IsMarkovKernel (costedCarryKernel K) :=
  costedUpdateKernel_markov _ _ measurable_snd _ measurable_snd

theorem costedCarryKernel_first (K : Kernel X (Y × ℕ)) [IsMarkovKernel K] :
    (costedCarryKernel K).map Prod.fst = (K.map Prod.fst).comap Prod.fst measurable_fst := by
  apply Kernel.ext
  intro x
  rw [Kernel.map_apply _ measurable_fst, costedCarryKernel,
    costedUpdateKernel_apply _ _ measurable_snd _ measurable_snd,
    Measure.map_map measurable_fst (measurable_fst.prodMk (measurable_const.add measurable_snd)),
    Kernel.comap_apply, Kernel.comap_apply, Kernel.map_apply _ measurable_fst]
  rfl

theorem costedCarryKernel_cost (K : Kernel X (Y × ℕ)) [IsMarkovKernel K] (x : X × ℕ)
    (hi : Integrable costValue (K x.1)) :
    Integrable costValue (costedCarryKernel K x) ∧
    (∫ t, costValue t ∂costedCarryKernel K x) = costValue x + ∫ t, costValue t ∂K x.1 :=
  costedUpdateKernel_cost _ _ measurable_snd _ measurable_snd x hi

end FreshGradientMinimax
