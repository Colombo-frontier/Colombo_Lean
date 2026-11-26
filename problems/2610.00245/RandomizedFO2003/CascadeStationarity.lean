import RandomizedFO2003.CascadeProjection
import RandomizedFO2003.SaturationActivation

namespace RandomizedFO2003.Cascade

open Primitives Calculus

variable {N : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

noncomputable def Data.momentS (d : Data N E) (L : Fin (N + 1) → E →L[ℝ] E) (i : Fin (N + 1)) : ℝ :=
  inner (𝕜 := ℝ) (d.a i) (L i (d.b i)) / d.α

noncomputable def Data.momentK (d : Data N E) (L : Fin (N + 1) → E →L[ℝ] E) (i : Fin (N + 1)) : ℝ :=
  d.D * inner (𝕜 := ℝ) (d.a i) (L i (d.a i)) / d.α ^ 2

noncomputable def Data.momentR (d : Data N E) (L : Fin (N + 1) → E →L[ℝ] E) (i : Fin (N + 1)) : ℝ :=
  inner (𝕜 := ℝ) (d.b i) (L i (d.b i)) / d.D

/-- Explicit deterministic hypotheses on the data and parameter choices.
They contain no stationarity, gate-activation, or query-dependent premise.
The random spectral construction must still be shown to supply these bounds. -/
structure Data.StationarityBounds (d : Data N E) (L : Fin (N + 1) → E →L[ℝ] E) (h γ ε : ℝ) : Prop where
  selfAdjoint : ∀ i, IsSelfAdjoint (d.A i)
  inverse_selfAdjoint : ∀ i, IsSelfAdjoint (L i)
  inverse_left : ∀ i x, L i (d.A i x) = x
  positive_D : 0 < d.D
  positive_α : 0 < d.α
  positive_B : 0 < d.B
  positive_γ : 0 < γ
  saturation_large : 12416 ≤ d.K
  offset_large : d.K + 2 ≤ d.C₀
  coercive : ∀ i x, γ * ‖x‖ ≤ ‖d.A i x‖
  rhs_norm : ∀ i, ‖d.b i‖ ≤ h
  direction_norm : ∀ i, ‖d.a i‖ ≤ 1
  radius_large : ε + h + d.D * (d.C₀ + d.K + 1) * (gateGradientConstant / d.α) ≤ γ * d.B
  s_bounds : ∀ i, 1 ≤ d.momentS L i ∧ d.momentS L i ≤ 64
  k_bounds : ∀ i, 1 ≤ d.momentK L i ∧ d.momentK L i ≤ 4096
  r_bounds : ∀ i, 0 ≤ d.momentR L i ∧ d.momentR L i ≤ 1
  a_error : ∀ i, (‖d.a i‖ * ‖L i‖ * ε) / d.α ≤ 1 / 8
  b_error : ∀ i, (‖d.b i‖ * ‖L i‖ * ε) / d.D ≤ 1

/-- Near-stationarity of the actual smooth cascade forces linear saturation,
complete gate activation, and a small final linear-system residual.
All normalized projection equations are derived from its actual gradient. -/
theorem Data.stationarity_from_bounds (d : Data N E) (L : Fin (N + 1) → E →L[ℝ] E)
    {h γ ε : ℝ} (p : d.StationarityBounds L h γ ε) (z : BlockProduct (N + 1) E)
    (hz : ‖gradient d.energy z‖ ≤ ε) :
    (∀ i, ‖z i‖ ≤ d.B) ∧
    (∀ i, |forcingReadout (d.b i) d.D (z i)| ≤ d.K) ∧
    (∀ i, d.gate i (z i) = 1) ∧
    ‖d.A (Fin.last N) (z (Fin.last N)) - d.b (Fin.last N)‖ ≤ ε := by
  have hK0 : 0 ≤ d.K := by linarith [p.saturation_large]
  have hball := d.stationary_blocks_in_ball p.selfAdjoint p.positive_D hK0 p.offset_large
    p.positive_B p.positive_α p.positive_γ p.coercive p.rhs_norm p.direction_norm p.radius_large z hz
  have hprojection (i : Fin (N + 1)) :
      |forcingReadout (d.b i) d.D (z i)| ≤ d.K ∧
      saturationSlope d.K (forcingReadout (d.b i) d.D (z i)) = 1 ∧
      d.incoming z i * d.momentS L i - 1 / 8 ≤ inner (𝕜 := ℝ) (d.a i) (z i) / d.α := by
    have heq := d.projected_gradient_equations p.selfAdjoint p.positive_D.ne' p.positive_α.ne'
      p.positive_B L p.inverse_selfAdjoint p.inverse_left z i (hball i)
    have herr (a : E) (α : ℝ) (hα : 0 < α) :
        |inner (𝕜 := ℝ) a (L i (gradient d.energy z i)) / α| ≤ (‖a‖ * ‖L i‖ * ε) / α := by
      apply (d.gradient_projection_norm_bound z i a (L i) hα).trans
      apply div_le_div_of_nonneg_right _ hα.le
      exact mul_le_mul_of_nonneg_left hz (mul_nonneg (norm_nonneg a) (norm_nonneg _))
    have hda := (herr (d.a i) d.α p.positive_α).trans (p.a_error i)
    have hdb := (herr (d.b i) d.D p.positive_D).trans (p.b_error i)
    have hc := d.incoming_mem z i
    have hout := d.outgoing_bounds p.positive_D.le hK0 p.offset_large z i
    exact projected_activation_bound (forcingReadout (d.b i) d.D (z i))
      (inner (𝕜 := ℝ) (d.a i) (z i) / d.α) (d.incoming z i)
      (d.momentS L i) (d.momentK L i) (d.momentR L i) (d.outgoing z i / d.D)
      (inner (𝕜 := ℝ) (d.a i) (L i (gradient d.energy z i)) / d.α)
      (inner (𝕜 := ℝ) (d.b i) (L i (gradient d.energy z i)) / d.D) d.K
      p.saturation_large hc.1 hc.2 (p.s_bounds i).1 (p.s_bounds i).2
      (p.k_bounds i).1 (p.k_bounds i).2 (p.r_bounds i).1 (p.r_bounds i).2
      (div_nonneg hout.1 p.positive_D.le) hda hdb heq.1 heq.2
  have hactivate (i : Fin (N + 1)) (hc : d.incoming z i = 1) : d.gate i (z i) = 1 := by
    have hv := (hprojection i).2.2
    rw [hc, one_mul] at hv
    change Primitives.gate (radialReadout (d.a i) d.B d.α (z i)) = 1
    rw [radialReadout, radialSquash_eq_self p.positive_B (hball i)]
    apply gate_one_of_le
    linarith [(p.s_bounds i).1]
  have hgate : ∀ i, d.gate i (z i) = 1 := by
    intro i
    refine Fin.induction (hactivate 0 (d.incoming_zero z)) (fun j ih => ?_) i
    apply hactivate j.succ
    rw [d.incoming_succ]
    exact ih
  refine ⟨hball, fun i => (hprojection i).1, hgate, ?_⟩
  exact (d.last_residual_norm_le p.selfAdjoint p.positive_D.ne' z
    (fun j => hgate j.castSucc) (hprojection (Fin.last N)).1).trans hz

end RandomizedFO2003.Cascade
