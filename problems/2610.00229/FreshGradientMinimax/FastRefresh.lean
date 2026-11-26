import FreshGradientMinimax.RefreshParameters
import FreshGradientMinimax.SolverEnergy

/-! The actual batched fast-variable refresh and its two error bounds. -/

set_option autoImplicit false
set_option maxHeartbeats 2200000
noncomputable section
namespace FreshGradientMinimax
open MeasureTheory ProbabilityTheory
namespace SCObjective
variable {dx dy : ℕ} {ℓ μ α σ : ℝ} (S : SCObjective dx dy ℓ μ α)

theorem jointFastRunKernel_apply (O : FreshOracle S.toNCObjective σ) (b n : ℕ)
    (u : Euclid dx) (x : Euclid dy) :
    S.jointFastRunKernel O b n (u, x) = (S.fastRunKernel O b x n u).map (fun w => (w, x)) := by
  have h := congrArg (fun K : Kernel (Euclid dx) (Joint dx dy) => K u)
    (S.jointFastRunKernel_fixed O b n x)
  simpa only [Kernel.comap_apply, Kernel.map_apply (f := fun w : Euclid dx => (w, x)) _
    (measurable_id.prodMk measurable_const)] using h

def refreshKernel (O : FreshOracle S.toNCObjective σ) (m E : ℝ) : Kernel (Joint dx dy) (Joint dx dy) :=
  S.jointFastRunKernel O (refreshBatch ℓ α σ m E) (refreshSteps ℓ α)

instance refreshKernel_markov (O : FreshOracle S.toNCObjective σ) (m E : ℝ) :
    IsMarkovKernel (S.refreshKernel O m E) := by unfold refreshKernel; infer_instance

theorem refreshKernel_apply (O : FreshOracle S.toNCObjective σ) (m E : ℝ)
    (u : Euclid dx) (x : Euclid dy) :
    S.refreshKernel O m E (u, x) =
      (S.fastRunKernel O (refreshBatch ℓ α σ m E) x (refreshSteps ℓ α) u).map (fun w => (w, x)) :=
  S.jointFastRunKernel_apply O _ _ u x

theorem refreshKernel_fast_integrable (O : FreshOracle S.toNCObjective σ) (m E : ℝ) (z : Joint dx dy) :
    Integrable (S.fastError m) (S.refreshKernel O m E z) := by
  rcases z with ⟨u, x⟩
  rw [S.refreshKernel_apply]
  apply (integrable_map_measure (g := S.fastError m) (S.fastError_continuous m).aestronglyMeasurable
    (measurable_id.prodMk measurable_const).aemeasurable).mpr
  exact (S.fastRunKernel_square_integrable O (refreshBatch_pos ℓ α σ m E) x (refreshSteps ℓ α) u).const_mul m

theorem refreshKernel_fast_bound (O : FreshOracle S.toNCObjective σ) (hαℓ : α ≤ ℓ)
    {m E : ℝ} (hm : 0 < m) (hE : 0 < E) (z : Joint dx dy) :
    (∫ w, S.fastError m w ∂S.refreshKernel O m E z) ≤ S.fastError m z / 1000000 + E / 1000000 := by
  rcases z with ⟨u, x⟩
  rw [S.refreshKernel_apply, integral_map (f := S.fastError m) (φ := fun w : Euclid dx => (w, x))
    (measurable_id.prodMk measurable_const).aemeasurable (S.fastError_continuous m).aestronglyMeasurable]
  dsimp [fastError]
  rw [integral_const_mul]
  have h := mul_le_mul_of_nonneg_left
    (S.fastRunKernel_error_floor O (refreshBatch_pos ℓ α σ m E) hαℓ x (refreshSteps ℓ α) u) hm.le
  have hc := mul_le_mul_of_nonneg_right
    (refreshSteps_contraction S.toNCObjective.L_pos S.α_pos hαℓ) (sq_nonneg ‖u - S.sliceMin x‖)
  have hcm := mul_le_mul_of_nonneg_left hc hm.le
  have hn := refreshBatch_noise (σ := σ) (m := m) S.toNCObjective.L_pos S.α_pos hE
  nlinarith only [h, hcm, hn]

theorem refreshKernel_energy_integrable (O : FreshOracle S.toNCObjective σ) (m E : ℝ)
    {Q : Euclid dy → ℝ} (hQ : Continuous Q) (v : Euclid dy) (z : Joint dx dy) :
    Integrable (S.solverEnergy Q m v) (S.refreshKernel O m E z) := by
  rcases z with ⟨u, x⟩
  rw [S.refreshKernel_apply]
  apply (integrable_map_measure (g := S.solverEnergy Q m v)
    (S.solverEnergy_continuous hQ m v).aestronglyMeasurable
    (measurable_id.prodMk measurable_const).aemeasurable).mpr
  have hc := S.fastRunKernel_square_integrable O (refreshBatch_pos ℓ α σ m E) x (refreshSteps ℓ α) u
  have hi := integrable_of_centered_square (f := id) measurable_id.aestronglyMeasurable (S.sliceMin x) hc
  have hs := square_integrable_of_centered hi (S.sliceMin x) hc
  exact (integrable_const (Q x - Q v)).add ((integrable_square_sub_const hi hs (S.sliceMin v)).const_mul m)

theorem refreshKernel_energy_bound (O : FreshOracle S.toNCObjective σ) (hαℓ : α ≤ ℓ)
    (hfast : ℓ / 4 ≤ α) {m E : ℝ} (hm : 0 < m) (hE : 0 < E)
    {Q : Euclid dy → ℝ} (hQ : Continuous Q) (v : Euclid dy) (z : Joint dx dy) :
    (∫ w, S.solverEnergy Q m v w ∂S.refreshKernel O m E z) ≤
      Q z.2 - Q v + 2 * S.fastError m z / 1000000 + 2 * E / 1000000 + 32 * m * ‖z.2 - v‖ ^ 2 := by
  rcases z with ⟨u, x⟩
  have hb := S.refreshKernel_fast_bound O hαℓ hm hE (u, x)
  rw [S.refreshKernel_apply, integral_map (f := S.fastError m) (φ := fun w : Euclid dx => (w, x))
    (measurable_id.prodMk measurable_const).aemeasurable (S.fastError_continuous m).aestronglyMeasurable] at hb
  rw [S.refreshKernel_apply, integral_map (f := S.solverEnergy Q m v) (φ := fun w : Euclid dx => (w, x))
    (measurable_id.prodMk measurable_const).aemeasurable (S.solverEnergy_continuous hQ m v).aestronglyMeasurable]
  have hi := S.refreshKernel_energy_integrable O m E hQ v (u, x)
  rw [S.refreshKernel_apply] at hi
  have hi' := (integrable_map_measure (g := S.solverEnergy Q m v)
    (S.solverEnergy_continuous hQ m v).aestronglyMeasurable
    (measurable_id.prodMk measurable_const).aemeasurable).mp hi
  have hf := (S.fastRunKernel_square_integrable O (refreshBatch_pos ℓ α σ m E) x (refreshSteps ℓ α) u).const_mul m
  have hW := ((integrable_const (Q x - Q v)).add (hf.const_mul 2)).add
    (integrable_const (32 * m * ‖x - v‖ ^ 2))
  have ht := integral_mono hi' hW (fun w => S.solverEnergy_triangle (Q := Q) hm.le hfast v (w, x))
  simp only [Function.comp_def, Pi.add_apply] at ht
  have hsum : Integrable (fun w => Q x - Q v + 2 * (m * ‖w - S.sliceMin x‖ ^ 2))
      (S.fastRunKernel O (refreshBatch ℓ α σ m E) x (refreshSteps ℓ α) u) :=
    (integrable_const _).add (hf.const_mul 2)
  rw [integral_add hsum (integrable_const _),
    integral_add (integrable_const _) (hf.const_mul 2), integral_const_mul,
    integral_const, integral_const, measureReal_univ_eq_one, one_smul, one_smul] at ht
  change (∫ w, S.solverEnergy Q m v (w, x) ∂_) ≤ _
  change (∫ w, m * ‖w - S.sliceMin x‖ ^ 2 ∂_) ≤ _ at hb
  change (∫ w, S.solverEnergy Q m v (w, x) ∂_) ≤ _ at ht
  dsimp only [Prod.fst, Prod.snd, fastError] at hb ⊢
  linarith only [ht, hb]

end SCObjective
end FreshGradientMinimax
