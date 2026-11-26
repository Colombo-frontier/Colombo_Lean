import FreshGradientMinimax.ProximalSaddle
import FreshGradientMinimax.OracleProgram

/-! Known measurable transformations of one fresh response. In particular,
adding a deterministic gradient correction preserves the noise variance
and gives a genuine oracle for the proximal objective. -/

set_option autoImplicit false
set_option maxHeartbeats 1400000
noncomputable section
namespace FreshGradientMinimax
open MeasureTheory ProbabilityTheory
variable {dx dy : ℕ}

def responseTransformKernel (K : Kernel (Joint dx dy) (Joint dx dy))
    (T : Joint dx dy × Joint dx dy → Joint dx dy) : Kernel (Joint dx dy) (Joint dx dy) :=
  (Kernel.id ×ₖ K).map T

instance responseTransformKernel_markov (K : Kernel (Joint dx dy) (Joint dx dy)) [IsMarkovKernel K]
    (T : Joint dx dy × Joint dx dy → Joint dx dy) (hT : Measurable T) :
    IsMarkovKernel (responseTransformKernel K T) := Kernel.IsMarkovKernel.map _ hT

theorem responseTransformKernel_apply (K : Kernel (Joint dx dy) (Joint dx dy)) [IsMarkovKernel K]
    (T : Joint dx dy × Joint dx dy → Joint dx dy) (hT : Measurable T) (z : Joint dx dy) :
    responseTransformKernel K T z = (K z).map (fun r => T (z, r)) := by
  rw [responseTransformKernel, Kernel.map_apply _ hT, Kernel.prod_apply, Kernel.id_apply,
    Measure.dirac_prod, Measure.map_map hT measurable_prodMk_left]
  rfl

theorem jointNormSq_continuous : Continuous (jointNormSq (dx := dx) (dy := dy)) :=
  (continuous_fst.norm.pow 2).add (continuous_snd.norm.pow 2)

namespace FreshOracle
variable {L μ σ L' μ' : ℝ} {F : NCObjective dx dy L μ} (O : FreshOracle F σ)

def shift (F' : NCObjective dx dy L' μ') (b : Joint dx dy → Joint dx dy) (hb : Measurable b)
    (hgrad : ∀ z, F'.jointGradient z = F.jointGradient z + b z) : FreshOracle F' σ where
  kernel := responseTransformKernel O.kernel (fun p => p.2 + b p.1)
  markov := responseTransformKernel_markov _ _ (measurable_snd.add (hb.comp measurable_fst))
  integrable := by
    intro z
    rw [responseTransformKernel_apply O.kernel (fun p : Joint dx dy × Joint dx dy => p.2 + b p.1) (measurable_snd.add (hb.comp measurable_fst))]
    have hs : Measurable (fun r : Joint dx dy => r + b z) := measurable_id.add measurable_const
    exact (integrable_map_measure (g := id) measurable_id.aestronglyMeasurable hs.aemeasurable).mpr
      ((O.integrable z).add (integrable_const (b z)))
  mean := by
    intro z
    have hs : Measurable (fun r : Joint dx dy => r + b z) := measurable_id.add measurable_const
    rw [responseTransformKernel_apply O.kernel (fun p : Joint dx dy × Joint dx dy => p.2 + b p.1) (measurable_snd.add (hb.comp measurable_fst)),
      integral_map (φ := fun r : Joint dx dy => r + b z) (f := fun r : Joint dx dy => r)
        hs.aemeasurable measurable_id.aestronglyMeasurable]
    change (∫ r, r + b z ∂O.kernel z) = _
    rw [integral_add (f := fun r : Joint dx dy => r) (g := fun _ => b z)
      (O.integrable z) (integrable_const (b z)), integral_const, measureReal_univ_eq_one, one_smul]
    exact (congrArg (fun v => v + b z) (O.mean z)).trans (hgrad z).symm
  square_integrable := by
    intro z
    rw [responseTransformKernel_apply O.kernel (fun p : Joint dx dy × Joint dx dy => p.2 + b p.1) (measurable_snd.add (hb.comp measurable_fst))]
    have hs : Measurable (fun r : Joint dx dy => r + b z) := measurable_id.add measurable_const
    have hm : StronglyMeasurable (fun r : Joint dx dy => jointNormSq (r - F'.jointGradient z)) :=
      (jointNormSq_continuous.comp (continuous_id.sub continuous_const)).stronglyMeasurable
    apply (integrable_map_measure hm.aestronglyMeasurable hs.aemeasurable).mpr
    simpa only [hgrad, Function.comp_def, add_sub_add_right_eq_sub] using O.square_integrable z
  variance_le := by
    intro z
    rw [responseTransformKernel_apply O.kernel (fun p : Joint dx dy × Joint dx dy => p.2 + b p.1) (measurable_snd.add (hb.comp measurable_fst))]
    have hs : Measurable (fun r : Joint dx dy => r + b z) := measurable_id.add measurable_const
    have hm : StronglyMeasurable (fun r : Joint dx dy => jointNormSq (r - F'.jointGradient z)) :=
      (jointNormSq_continuous.comp (continuous_id.sub continuous_const)).stronglyMeasurable
    rw [integral_map hs.aemeasurable hm.aestronglyMeasurable]
    simpa only [hgrad, add_sub_add_right_eq_sub] using O.variance_le z

end FreshOracle

def proximalResponse (L : ℝ) (p : Euclid dx × (Joint dx dy × Joint dx dy)) : Joint dx dy :=
  p.2.2 + ((2 * L) • (p.2.1.1 - p.1), 0)

theorem proximalResponse_continuous (L : ℝ) : Continuous (proximalResponse (dx := dx) (dy := dy) L) :=
  continuous_snd.snd.add ((continuous_const.smul (continuous_snd.fst.fst.sub continuous_fst)).prodMk continuous_const)

namespace FreshOracle
variable {L μ σ : ℝ} {F : NCObjective dx dy L μ} (O : FreshOracle F σ)

def proximal (c : Euclid dx) : FreshOracle (F.proximalObjective c).toNCObjective σ :=
  O.shift (F.proximalObjective c).toNCObjective (fun z => ((2 * L) • (z.1 - c), 0))
    ((measurable_const.smul (measurable_fst.sub measurable_const)).prodMk measurable_const) (by
      intro z
      ext <;> simp [NCObjective.jointGradient, NCObjective.proximalObjective, NCObjective.regularizedX])

theorem proximal_kernel (c : Euclid dx) :
    (O.proximal c).kernel = responseTransformKernel O.kernel (fun p => proximalResponse L (c, p)) := rfl

end FreshOracle
end FreshGradientMinimax

