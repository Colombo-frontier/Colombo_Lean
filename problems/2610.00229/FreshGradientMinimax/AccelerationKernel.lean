import FreshGradientMinimax.AccelerationGeometry
import FreshGradientMinimax.BatchedEstimator

/-! Actual accelerated transition kernels. Finite second moments of the
sampled gradient imply integrability of the next potential; it is not an
extra assumption in the kernel-level F.2 inequality. -/

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
namespace FreshGradientMinimax
open MeasureTheory ProbabilityTheory

variable {d : ℕ}

def accelerationQuery (a : ℝ) (s : Joint d d) : Euclid d := acceleratedY a s.1 s.2

theorem accelerationQuery_continuous (a : ℝ) : Continuous (accelerationQuery (d := d) a) :=
  continuous_const.smul (continuous_fst.add (continuous_const.smul continuous_snd))

def accelerationUpdate (a m H : ℝ) (z : Joint d d × Euclid d) : Joint d d :=
  (accelerationQuery a z.1 - H⁻¹ • z.2,
    acceleratedZ a m z.1.2 (accelerationQuery a z.1) z.2)

theorem accelerationUpdate_continuous (a m H : ℝ) : Continuous (accelerationUpdate (d := d) a m H) := by
  unfold accelerationUpdate acceleratedZ
  exact (((accelerationQuery_continuous a).comp continuous_fst).sub
    (continuous_const.smul continuous_snd)).prodMk
      (((continuous_const.smul continuous_fst.snd).add
        (continuous_const.smul ((accelerationQuery_continuous a).comp continuous_fst))).sub
          (continuous_const.smul continuous_snd))

def accelerationStepKernel (G : Kernel (Euclid d) (Euclid d)) (a m H : ℝ) : Kernel (Joint d d) (Joint d d) :=
  (Kernel.id ×ₖ G.comap (accelerationQuery a) (accelerationQuery_continuous a).measurable).map
    (accelerationUpdate a m H)

instance accelerationStepKernel_markov (G : Kernel (Euclid d) (Euclid d)) [IsMarkovKernel G] (a m H : ℝ) :
    IsMarkovKernel (accelerationStepKernel G a m H) :=
  Kernel.IsMarkovKernel.map _ (accelerationUpdate_continuous a m H).measurable

theorem accelerationStepKernel_apply (G : Kernel (Euclid d) (Euclid d)) [IsMarkovKernel G]
    (a m H : ℝ) (s : Joint d d) :
    accelerationStepKernel G a m H s =
      (G (accelerationQuery a s)).map (fun r => accelerationUpdate a m H (s, r)) := by
  rw [accelerationStepKernel, Kernel.map_apply _ (accelerationUpdate_continuous a m H).measurable,
    Kernel.prod_apply, Kernel.id_apply, Kernel.comap_apply, Measure.dirac_prod,
    Measure.map_map (accelerationUpdate_continuous a m H).measurable measurable_prodMk_left]
  rfl

theorem integrable_affine_square {ν : Measure (Euclid d)} [IsProbabilityMeasure ν]
    (hi : Integrable id ν) (hs : Integrable (fun r => ‖r‖ ^ 2) ν) (c : Euclid d) (t : ℝ) :
    Integrable (fun r => ‖c + t • r‖ ^ 2) ν := by
  have ht : Integrable (fun r : Euclid d => ‖t • r‖ ^ 2) ν := by
    simpa only [norm_smul_sq] using hs.const_mul (t ^ 2)
  simpa only [add_comm] using integrable_square_add_const (hi.smul t) ht c

def statePotential (Q : Euclid d → ℝ) (m : ℝ) (v : Euclid d) (s : Joint d d) : ℝ :=
  acceleratedPotential Q m v s.1 s.2

theorem statePotential_continuous {Q : Euclid d → ℝ} (hQ : Continuous Q) (m : ℝ) (v : Euclid d) :
    Continuous (statePotential Q m v) :=
  ((hQ.comp continuous_fst).sub continuous_const).add
    (continuous_const.mul ((continuous_snd.sub continuous_const).norm.pow 2))

theorem accelerationUpdate_potential_integrable {Q : Euclid d → ℝ} {grad : Euclid d → Euclid d}
    {a m H : ℝ} (model : SmoothStrongModel Q grad m H) (hm : 0 ≤ m)
    (v : Euclid d) (hmin : ∀ t, Q v ≤ Q t) (s : Joint d d)
    {ν : Measure (Euclid d)} [IsProbabilityMeasure ν]
    (hi : Integrable id ν) (hs : Integrable (fun r => ‖r - grad (accelerationQuery a s)‖ ^ 2) ν) :
    Integrable (fun r => statePotential Q m v (accelerationUpdate a m H (s, r))) ν := by
  have hs0 := square_integrable_of_centered hi (grad (accelerationQuery a s)) hs
  have hx := integrable_affine_square hi hs0 (accelerationQuery a s - v) (-H⁻¹)
  have hz := integrable_affine_square hi hs0
    ((1 - a) • s.2 + a • accelerationQuery a s - v) (-(a / m))
  have hfx (r : Euclid d) : accelerationQuery a s - v + (-H⁻¹) • r =
      (accelerationUpdate a m H (s, r)).1 - v := by dsimp [accelerationUpdate]; module
  have hfz (r : Euclid d) : ((1 - a) • s.2 + a • accelerationQuery a s - v) + (-(a / m)) • r =
      (accelerationUpdate a m H (s, r)).2 - v := by dsimp [accelerationUpdate, acceleratedZ]; module
  simp_rw [hfx] at hx
  simp_rw [hfz] at hz
  apply ((hx.const_mul (H / 2)).add (hz.const_mul (m / 2))).mono'
    (((statePotential_continuous model.continuous m v).comp
      ((accelerationUpdate_continuous a m H).comp (continuous_const.prodMk continuous_id))).aestronglyMeasurable)
  apply Filter.Eventually.of_forall
  intro r
  rw [Real.norm_eq_abs]
  change |acceleratedPotential Q m v (accelerationUpdate a m H (s, r)).1
    (accelerationUpdate a m H (s, r)).2| ≤
    H / 2 * ‖(accelerationUpdate a m H (s, r)).1 - v‖ ^ 2 +
      m / 2 * ‖(accelerationUpdate a m H (s, r)).2 - v‖ ^ 2
  rw [abs_of_nonneg (SmoothStrongModel.potential_nonneg hm v hmin _ _)]
  have hb := (model.gap_quadratic_bounds v hmin (accelerationUpdate a m H (s, r)).1).2
  dsimp [statePotential, acceleratedPotential]
  linarith

theorem accelerationStepKernel_potential_integrable {Q : Euclid d → ℝ} {grad : Euclid d → Euclid d}
    {a m H : ℝ} (model : SmoothStrongModel Q grad m H) (hm : 0 ≤ m)
    (v : Euclid d) (hmin : ∀ t, Q v ≤ Q t)
    (G : Kernel (Euclid d) (Euclid d)) [IsMarkovKernel G] (s : Joint d d)
    (hi : Integrable id (G (accelerationQuery a s)))
    (hs : Integrable (fun r => ‖r - grad (accelerationQuery a s)‖ ^ 2) (G (accelerationQuery a s))) :
    Integrable (statePotential Q m v) (accelerationStepKernel G a m H s) := by
  rw [accelerationStepKernel_apply]
  apply (integrable_map_measure (g := statePotential Q m v)
    (statePotential_continuous model.continuous m v).aestronglyMeasurable
    ((accelerationUpdate_continuous a m H).comp (continuous_const.prodMk continuous_id)).measurable.aemeasurable).mpr
  exact accelerationUpdate_potential_integrable model hm v hmin s hi hs

/-- Formula (46) for the actual transition, with next-potential integrability derived. -/
theorem accelerationStepKernel_potential_bound {Q : Euclid d → ℝ} {grad : Euclid d → Euclid d}
    {a m H : ℝ} (model : SmoothStrongModel Q grad m H)
    (hm : 0 < m) (hH : 0 < H) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hscale : a ^ 2 / m = H⁻¹)
    (v : Euclid d) (hmin : ∀ t, Q v ≤ Q t)
    (G : Kernel (Euclid d) (Euclid d)) [IsMarkovKernel G] (s : Joint d d)
    (hi : Integrable id (G (accelerationQuery a s)))
    (hs : Integrable (fun r => ‖r - grad (accelerationQuery a s)‖ ^ 2) (G (accelerationQuery a s))) :
    (∫ t, statePotential Q m v t ∂accelerationStepKernel G a m H s) ≤
      (1 - a / 2) * statePotential Q m v s +
      (∫ r, ‖r - ∫ w, w ∂G (accelerationQuery a s)‖ ^ 2 ∂G (accelerationQuery a s)) / H +
      (2 * a / m) * ‖(∫ r, r ∂G (accelerationQuery a s)) - grad (accelerationQuery a s)‖ ^ 2 := by
  let y := accelerationQuery a s
  have hie : Integrable (fun r : Euclid d => r - grad y) (G y) := hi.sub (integrable_const _)
  have hn := accelerationUpdate_potential_integrable model hm.le v hmin s hi hs
  have heq (r : Euclid d) : grad y + (r - grad y) = r := by abel
  have hnext : Integrable (fun r => acceleratedPotential Q m v
      (acceleratedY a s.1 s.2 - H⁻¹ • (grad (acceleratedY a s.1 s.2) + (r - grad y)))
      (acceleratedZ a m s.2 (acceleratedY a s.1 s.2) (grad (acceleratedY a s.1 s.2) + (r - grad y)))) (G y) := by
    change Integrable (fun r => acceleratedPotential Q m v (y - H⁻¹ • (grad y + (r - grad y)))
      (acceleratedZ a m s.2 y (grad y + (r - grad y)))) (G y)
    simpa only [heq] using hn
  have hb := robust_acceleration model hm hH ha ha1 hscale v s.1 s.2 hmin
    (fun r : Euclid d => r - grad y) hie hs hnext
  have hmean : (∫ r, r - grad y ∂G y) = (∫ r, r ∂G y) - grad y := by
    change Integrable (fun r : Euclid d => r) (G y) at hi
    rw [integral_sub hi (integrable_const _)]
    simp
  have hcenter (r : Euclid d) : (r - grad y) - ((∫ w, w ∂G y) - grad y) = r - ∫ w, w ∂G y := by abel
  rw [hmean] at hb
  simp_rw [hcenter] at hb
  rw [accelerationStepKernel_apply, integral_map (f := statePotential Q m v)
    (φ := fun r => accelerationUpdate a m H (s, r))
    ((accelerationUpdate_continuous a m H).comp (continuous_const.prodMk continuous_id)).measurable.aemeasurable
    (statePotential_continuous model.continuous m v).aestronglyMeasurable]
  dsimp only [y, accelerationQuery] at heq hb
  simp_rw [heq] at hb
  exact hb

end FreshGradientMinimax
