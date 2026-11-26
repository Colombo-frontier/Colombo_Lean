import FreshGradientMinimax.AccelerationKernel

/-! The accelerated phase of F.3, using the actual fresh multilevel batches.
The reference point is frozen for the phase. Bounds retain its energy as
a separate term, so later integration needs no almost-sure radius. -/

set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section
namespace FreshGradientMinimax
open MeasureTheory ProbabilityTheory
open scoped BigOperators

theorem relative_acceleration_recurrence {a m H ρ e V P R D b : ℝ}
    (hm : 0 < m) (hH : 0 < H) (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (hscale : a ^ 2 / m = H⁻¹) (hρ : 0 ≤ ρ) (hρsmall : ρ ≤ 1 / 1152)
    (hP : 0 ≤ P) (hD : 0 ≤ D) (hb : 1 ≤ b)
    (hquery : m * D ≤ 2 * R + 64 * P) :
    (1 - a / 2) * P + (V + ρ * m ^ 2 * D) / b / H +
      (2 * a / m) * (ρ * m * e + ρ * m ^ 2 * D) ≤
      (1 - a / 3) * P + 6 * ρ * a * R + 2 * ρ * a * e + V / (H * b) := by
  have hbpos : 0 < b := by linarith
  have hratio : m / H ≤ a := by
    have heq : a ^ 2 = m / H := by
      have hs := (div_eq_iff hm.ne').mp hscale
      simpa only [div_eq_mul_inv, mul_comm] using hs
    rw [← heq]
    nlinarith
  have hratio' : m / (H * b) ≤ a := by
    apply (div_le_iff₀ (mul_pos hH hbpos)).mpr
    have hmh := (div_le_iff₀ hH).mp hratio
    have hab := mul_le_mul_of_nonneg_left hb (mul_nonneg ha hH.le)
    nlinarith only [hmh, hab]
  have hnoise1 := mul_le_mul_of_nonneg_left hratio' (by positivity : 0 ≤ ρ * (m * D))
  have hnoise2 := mul_le_mul_of_nonneg_left hquery (mul_nonneg hρ ha)
  have hnoise : ρ * m ^ 2 * D / (H * b) ≤ ρ * a * (2 * R + 64 * P) := by
    have heq : ρ * m ^ 2 * D / (H * b) = ρ * (m * D) * (m / (H * b)) := by ring
    rw [heq]
    nlinarith only [hnoise1, hnoise2]
  have hbias := mul_le_mul_of_nonneg_left hquery (by positivity : 0 ≤ 2 * ρ * a)
  have heq : (1 - a / 2) * P + (V + ρ * m ^ 2 * D) / b / H +
      (2 * a / m) * (ρ * m * e + ρ * m ^ 2 * D) =
      (1 - a / 2) * P + V / (H * b) + ρ * m ^ 2 * D / (H * b) +
      2 * ρ * a * e + 2 * ρ * a * (m * D) := by
    field_simp
    ring
  rw [heq]
  have hsmall := mul_le_mul_of_nonneg_right hρsmall (by positivity : 0 ≤ 192 * a * P)
  nlinarith only [hnoise, hbias, hsmall]

namespace SCObjective
variable {dx dy : ℕ} {ℓ μ α σ : ℝ} (S : SCObjective dx dy ℓ μ α)

def epochOracleKernel (O : FreshOracle S.toNCObjective σ) (ρ m e : ℝ)
    (r : Euclid dy → Euclid dy) (hr : Measurable r) (b : ℕ) (u : Euclid dx) :
    Kernel (Euclid dy) (Euclid dy) :=
  (S.jointBatchedEstimatorKernel O ρ m e r hr b).comap (fun v => (u, v))
    (measurable_const.prodMk measurable_id)

instance epochOracleKernel_markov (O : FreshOracle S.toNCObjective σ) (ρ m e : ℝ)
    (r : Euclid dy → Euclid dy) (hr : Measurable r) (b : ℕ) (u : Euclid dx) :
    IsMarkovKernel (S.epochOracleKernel O ρ m e r hr b u) := by unfold epochOracleKernel; infer_instance

def epochStepKernel (O : FreshOracle S.toNCObjective σ) (ρ m H e : ℝ)
    (r : Euclid dy → Euclid dy) (hr : Measurable r) (b : ℕ) (u : Euclid dx) :
    Kernel (Joint dy dy) (Joint dy dy) :=
  accelerationStepKernel (S.epochOracleKernel O ρ m e r hr b u) (Real.sqrt (m / H)) m H

instance epochStepKernel_markov (O : FreshOracle S.toNCObjective σ) (ρ m H e : ℝ)
    (r : Euclid dy → Euclid dy) (hr : Measurable r) (b : ℕ) (u : Euclid dx) :
    IsMarkovKernel (S.epochStepKernel O ρ m H e r hr b u) := by unfold epochStepKernel; infer_instance

theorem epochStepKernel_potential_integrable (O : FreshOracle S.toNCObjective σ)
    (hαℓ : α ≤ ℓ) (hfast : ℓ / 4 ≤ α) {ρ m H e : ℝ} (hρ : 0 < ρ) (hm : 0 < m) (he : 0 < e)
    (r : Euclid dy → Euclid dy) (hr : Measurable r) {Q : Euclid dy → ℝ}
    (model : SmoothStrongModel Q (fun v => gradient S.effectiveValue v + r v) m H)
    (v : Euclid dy) (hmin : ∀ t, Q v ≤ Q t) {b : ℕ} (hb : 0 < b) (u : Euclid dx) (s : Joint dy dy) :
    Integrable (statePotential Q m v) (S.epochStepKernel O ρ m H e r hr b u s) := by
  obtain ⟨hi, hs, _, _⟩ := S.jointBatchedEstimator_contract O hαℓ hfast hρ hm he r hr hb
    (u, accelerationQuery (Real.sqrt (m / H)) s)
  exact accelerationStepKernel_potential_integrable model hm.le v hmin _ s hi hs

/-- The F.3 conditional recurrence with the frozen reference energy retained. -/
theorem epochStepKernel_potential_bound (O : FreshOracle S.toNCObjective σ)
    (hαℓ : α ≤ ℓ) (hfast : ℓ / 4 ≤ α) {ρ m H e : ℝ}
    (hρ : 0 < ρ) (hρsmall : ρ ≤ 1 / 1152) (hm : 0 < m) (hmH : m ≤ H) (he : 0 < e)
    (r : Euclid dy → Euclid dy) (hr : Measurable r) {Q : Euclid dy → ℝ}
    (model : SmoothStrongModel Q (fun v => gradient S.effectiveValue v + r v) m H)
    (v : Euclid dy) (hmin : ∀ t, Q v ≤ Q t) {b : ℕ} (hb : 0 < b) (u : Euclid dx) (s : Joint dy dy) :
    (∫ t, statePotential Q m v t ∂S.epochStepKernel O ρ m H e r hr b u s) ≤
      (1 - Real.sqrt (m / H) / 3) * statePotential Q m v s +
      6 * ρ * Real.sqrt (m / H) * (m * ‖u - S.sliceMin v‖ ^ 2) +
      2 * ρ * Real.sqrt (m / H) * e +
      (140 * (estimatorCutoff ρ m e σ + 1 : ℝ) * σ ^ 2) / (H * b) := by
  let a := Real.sqrt (m / H)
  let y := accelerationQuery a s
  have hH : 0 < H := hm.trans_le hmH
  obtain ⟨ha, ha1, hscale⟩ := acceleration_parameter hm hmH
  obtain ⟨hi, hs, hbi, hva⟩ := S.jointBatchedEstimator_contract O hαℓ hfast hρ hm he r hr hb (u, y)
  have hstep := accelerationStepKernel_potential_bound model hm hH ha ha1 hscale v hmin
    (S.epochOracleKernel O ρ m e r hr b u) s hi hs
  have hvardiv := div_le_div_of_nonneg_right hva hH.le
  have hbiasmul := mul_le_mul_of_nonneg_left hbi (by positivity : 0 ≤ 2 * a / m)
  have hLratio : ℓ / α ≤ 4 := (div_le_iff₀ S.α_pos).mpr (by linarith)
  have hLip (x z : Euclid dy) : ‖S.sliceMin x - S.sliceMin z‖ ≤ 4 * ‖x - z‖ :=
    (S.sliceMin_lip x z).trans (mul_le_mul_of_nonneg_right hLratio (norm_nonneg _))
  have hquery := model.reference_query_distance hm ha (by norm_num : (0 : ℝ) ≤ 4) v hmin
    S.sliceMin hLip u s.1 s.2
  norm_num only [show (4 : ℝ) ^ 2 = 16 by norm_num, show (4 : ℝ) * 16 = 64 by norm_num] at hquery
  rw [mul_assoc 2 m] at hquery
  have hbR : (1 : ℝ) ≤ b := by exact_mod_cast hb
  have hP : 0 ≤ statePotential Q m v s := SmoothStrongModel.potential_nonneg hm.le v hmin _ _
  have halg := relative_acceleration_recurrence hm hH ha ha1 hscale hρ.le hρsmall hP
    (sq_nonneg ‖u - S.sliceMin y‖) hbR hquery
    (e := e) (V := 140 * (estimatorCutoff ρ m e σ + 1 : ℝ) * σ ^ 2)
  change (∫ t, statePotential Q m v t ∂S.epochStepKernel O ρ m H e r hr b u s) ≤ _ at hstep
  change (∫ w, ‖w - ∫ z, z ∂S.epochOracleKernel O ρ m e r hr b u y‖ ^ 2
    ∂S.epochOracleKernel O ρ m e r hr b u y) / H ≤ _ at hvardiv
  change (2 * a / m) * ‖(∫ w, w ∂S.epochOracleKernel O ρ m e r hr b u y) -
    (gradient S.effectiveValue y + r y)‖ ^ 2 ≤ _ at hbiasmul
  exact (hstep.trans (add_le_add (add_le_add_left hvardiv _) hbiasmul)).trans halg

end SCObjective
end FreshGradientMinimax
