import FreshGradientMinimax.OracleBatch
import FreshGradientMinimax.KernelIteration

/-! The actual adaptive minibatch iteration in F.1. At each step all b draws
use the fresh oracle at the current point. Finite trajectory moments are
derived by kernel composition and the one-step contraction. -/

set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section
namespace FreshGradientMinimax
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace SCObjective
variable {dx dy : ℕ} {ℓ μ α σ : ℝ} (S : SCObjective dx dy ℓ μ α)

def fastStepKernel (K : FreshOracle S.toNCObjective σ) (b : ℕ) (v : Euclid dy) :
    Kernel (Euclid dx) (Euclid dx) :=
  (Kernel.id ×ₖ (batchKernel K.primalKernel b).comap (fun u => (u, v))
    (measurable_id.prodMk measurable_const)).map (fun z : Euclid dx × Euclid dx => z.1 - ℓ⁻¹ • z.2)

instance fastStepKernel_markov (K : FreshOracle S.toNCObjective σ) (b : ℕ) (v : Euclid dy) :
    IsMarkovKernel (S.fastStepKernel K b v) :=
  Kernel.IsMarkovKernel.map _ (measurable_fst.sub (measurable_const.smul measurable_snd))

theorem fastStepKernel_apply (K : FreshOracle S.toNCObjective σ) (b : ℕ)
    (v : Euclid dy) (u : Euclid dx) :
    S.fastStepKernel K b v u = (batchKernel K.primalKernel b (u, v)).map (fun r => u - ℓ⁻¹ • r) := by
  rw [fastStepKernel, Kernel.map_apply _ (measurable_fst.sub (measurable_const.smul measurable_snd)),
    Kernel.prod_apply, Kernel.id_apply, Kernel.comap_apply, Measure.dirac_prod,
    Measure.map_map (measurable_fst.sub (measurable_const.smul measurable_snd)) measurable_prodMk_left]
  rfl

theorem fastStepKernel_square_integrable (K : FreshOracle S.toNCObjective σ) {b : ℕ} (hb : 0 < b)
    (v : Euclid dy) (u : Euclid dx) :
    Integrable (fun w => ‖w - S.sliceMin v‖ ^ 2) (S.fastStepKernel K b v u) := by
  obtain ⟨hi, hm, hv, hvar⟩ := K.primal_batch_contract (u, v) hb
  have hic : Integrable (fun r => r - S.gradX u v) (batchKernel K.primalKernel b (u, v)) :=
    hi.sub (integrable_const _)
  have his : Integrable (fun r => -ℓ⁻¹ • (r - S.gradX u v)) (batchKernel K.primalKernel b (u, v)) :=
    hic.smul (-ℓ⁻¹)
  have hvs : Integrable (fun r => ‖-ℓ⁻¹ • (r - S.gradX u v)‖ ^ 2) (batchKernel K.primalKernel b (u, v)) := by
    simpa only [norm_smul_sq] using hv.const_mul ((-ℓ⁻¹) ^ 2)
  have ha := integrable_square_add_const his hvs (u - ℓ⁻¹ • S.gradX u v - S.sliceMin v)
  have he (r : Euclid dx) : -ℓ⁻¹ • (r - S.gradX u v) + (u - ℓ⁻¹ • S.gradX u v - S.sliceMin v) =
      u - ℓ⁻¹ • r - S.sliceMin v := by module
  rw [S.fastStepKernel_apply]
  apply (integrable_map_measure (g := fun w : Euclid dx => ‖w - S.sliceMin v‖ ^ 2)
    ((continuous_id.sub continuous_const).norm.pow 2).aestronglyMeasurable
    (measurable_const.sub (measurable_const.smul measurable_id)).aemeasurable).mpr
  simpa only [he, Function.comp_def] using ha

theorem fastStepKernel_contraction (K : FreshOracle S.toNCObjective σ) {b : ℕ} (hb : 0 < b)
    (v : Euclid dy) (u : Euclid dx) :
    (∫ w, ‖w - S.sliceMin v‖ ^ 2 ∂S.fastStepKernel K b v u) ≤
      (1 - α / ℓ) * ‖u - S.sliceMin v‖ ^ 2 + σ ^ 2 / (ℓ ^ 2 * b) := by
  rw [S.fastStepKernel_apply, integral_map (φ := fun r : Euclid dx => u - ℓ⁻¹ • r)
    (f := fun w : Euclid dx => ‖w - S.sliceMin v‖ ^ 2)
    (measurable_const.sub (measurable_const.smul measurable_id)).aemeasurable
    ((continuous_id.sub continuous_const).norm.pow 2).aestronglyMeasurable]
  exact S.fast_batch_contraction K u v hb

def fastRunKernel (K : FreshOracle S.toNCObjective σ) (b : ℕ) (v : Euclid dy) (n : ℕ) :
    Kernel (Euclid dx) (Euclid dx) := iterateKernel (S.fastStepKernel K b v) n

instance fastRunKernel_markov (K : FreshOracle S.toNCObjective σ) (b : ℕ) (v : Euclid dy) (n : ℕ) :
    IsMarkovKernel (S.fastRunKernel K b v n) := by unfold fastRunKernel; infer_instance

theorem fastRunKernel_square_integrable (K : FreshOracle S.toNCObjective σ) {b : ℕ} (hb : 0 < b)
    (v : Euclid dy) (n : ℕ) (u : Euclid dx) :
    Integrable (fun w => ‖w - S.sliceMin v‖ ^ 2) (S.fastRunKernel K b v n u) :=
  iterateKernel_integrable _ _ ((continuous_id.sub continuous_const).norm.pow 2).stronglyMeasurable
    (fun _ => sq_nonneg _) (S.fastStepKernel_square_integrable K hb v)
    (S.fastStepKernel_contraction K hb v) n u

theorem fastRunKernel_error (K : FreshOracle S.toNCObjective σ) {b : ℕ} (hb : 0 < b)
    (hα : α ≤ ℓ) (v : Euclid dy) (n : ℕ) (u : Euclid dx) :
    (∫ w, ‖w - S.sliceMin v‖ ^ 2 ∂S.fastRunKernel K b v n u) ≤
      (1 - α / ℓ) ^ n * ‖u - S.sliceMin v‖ ^ 2 +
        (σ ^ 2 / (ℓ ^ 2 * b)) * ∑ j ∈ Finset.range n, (1 - α / ℓ) ^ j := by
  have hr : 0 ≤ 1 - α / ℓ := sub_nonneg.mpr ((div_le_one S.toNCObjective.L_pos).mpr hα)
  exact iterateKernel_moment _ _ ((continuous_id.sub continuous_const).norm.pow 2).stronglyMeasurable
    (fun _ => sq_nonneg _) (S.fastStepKernel_square_integrable K hb v) hr
    (S.fastStepKernel_contraction K hb v) n u

theorem fastRunKernel_error_floor (K : FreshOracle S.toNCObjective σ) {b : ℕ} (hb : 0 < b)
    (hα : α ≤ ℓ) (v : Euclid dy) (n : ℕ) (u : Euclid dx) :
    (∫ w, ‖w - S.sliceMin v‖ ^ 2 ∂S.fastRunKernel K b v n u) ≤
      (1 - α / ℓ) ^ n * ‖u - S.sliceMin v‖ ^ 2 + σ ^ 2 / (α * ℓ * b) := by
  have hℓ := S.toNCObjective.L_pos
  have ha := S.α_pos
  have hr : 0 ≤ 1 - α / ℓ := sub_nonneg.mpr ((div_le_one hℓ).mpr hα)
  have hr1 : 1 - α / ℓ < 1 := by have := div_pos ha hℓ; linarith
  have hs : (∑ j ∈ Finset.range n, (1 - α / ℓ) ^ j) ≤ 1 / (α / ℓ) := by
    simpa only [Nat.Ico_zero_eq_range, pow_zero, sub_sub_cancel] using
      (geom_sum_Ico_le_of_lt_one hr hr1 (m := 0) (n := n))
  have hcoeff : 0 ≤ σ ^ 2 / (ℓ ^ 2 * b) := by positivity
  have hs' := mul_le_mul_of_nonneg_left hs hcoeff
  have he : (σ ^ 2 / (ℓ ^ 2 * b)) * (1 / (α / ℓ)) = σ ^ 2 / (α * ℓ * b) := by
    field_simp
    ring
  rw [he] at hs'
  exact (S.fastRunKernel_error K hb hα v n u).trans (add_le_add_left hs' _)

end SCObjective
end FreshGradientMinimax
