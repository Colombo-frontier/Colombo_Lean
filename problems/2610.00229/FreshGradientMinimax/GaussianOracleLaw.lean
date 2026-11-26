import FreshGradientMinimax.GaussianOracle

/-! The full joint response is a measurable embedding of a scalar Gaussian;
the primal answer and all dual information are preserved exactly. -/

set_option autoImplicit false
noncomputable section
namespace FreshGradientMinimax
open MeasureTheory ProbabilityTheory
open scoped NNReal

theorem realVector_smul_one (t : ℝ) : realVector t = t • realVector 1 := by
  ext i
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  simp [realVector]

theorem realVector_continuous : Continuous realVector := by
  have he : realVector = (fun t : ℝ => t • realVector 1) := funext realVector_smul_one
  rw [he]
  exact continuous_id.smul continuous_const

def realVectorMeasurableEquiv : ℝ ≃ᵐ Euclid 1 where
  toFun := realVector
  invFun := realCoord
  left_inv := realCoord_vector
  right_inv := realVector_coord
  measurable_toFun := realVector_continuous.measurable
  measurable_invFun := by
    change Measurable realCoord
    have he : (realCoordCLM : Euclid 1 → ℝ) = realCoord := funext realCoordCLM_apply
    rw [← he]
    exact realCoordCLM.continuous.measurable

def scalarResponseEmbed {dx : ℕ} (a : Euclid dx) (t : ℝ) : Joint dx 1 := (a, realVector t)

theorem scalarResponseEmbed_measurableEmbedding {dx : ℕ} (a : Euclid dx) :
    MeasurableEmbedding (scalarResponseEmbed a) :=
  (measurableEmbedding_prodMk_left a).comp realVectorMeasurableEquiv.measurableEmbedding

variable {dx : ℕ} {L μ : ℝ} (F : NCObjective dx 1 L μ)

theorem gaussianDualKernel_scalar_law (v : ℝ≥0) (z : Joint dx 1) :
    gaussianDualKernel F v z =
      (gaussianReal (realCoord (F.gradY z.1 z.2)) v).map (scalarResponseEmbed (F.gradX z.1 z.2)) := by
  rw [gaussianDualKernel_apply]
  have ht : (gaussianReal 0 v).map (fun t : ℝ => t + realCoord (F.gradY z.1 z.2)) =
      gaussianReal (realCoord (F.gradY z.1 z.2)) v := by
    simpa only [zero_add] using gaussianReal_map_add_const (μ := 0) (v := v) (realCoord (F.gradY z.1 z.2))
  have hm : Measurable (fun t : ℝ => t + realCoord (F.gradY z.1 z.2)) := measurable_id.add_const _
  rw [← ht, Measure.map_map (scalarResponseEmbed_measurableEmbedding (F.gradX z.1 z.2)).measurable hm]
  congr 1
  funext t
  apply Prod.ext
  · rfl
  · change F.gradY z.1 z.2 + t • realVector 1 = realVector (t + realCoord (F.gradY z.1 z.2))
    rw [← realVector_smul_one]
    apply_fun realCoord using (fun x y h => by rw [← realVector_coord x, ← realVector_coord y, h])
    simp [realCoord, realVector]
    ring

end FreshGradientMinimax
