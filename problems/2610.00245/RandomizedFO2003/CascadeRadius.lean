import RandomizedFO2003.CascadeGradient

namespace RandomizedFO2003.Cascade

open Primitives Calculus

noncomputable def gateSlopeConstant : ℝ := (gate_derivative_bound 1 (by norm_num)).choose

theorem gateSlopeConstant_pos : 0 < gateSlopeConstant :=
  (gate_derivative_bound 1 (by norm_num)).choose_spec.1

theorem gateSlopeConstant_bound (x : ℝ) : |deriv Primitives.gate x| ≤ gateSlopeConstant := by
  simpa only [iteratedDeriv_one, gateSlopeConstant] using (gate_derivative_bound 1 (by norm_num)).choose_spec.2 x

noncomputable def gateGradientConstant : ℝ := gateSlopeConstant * radialDerivativeConstant 1

theorem gateGradientConstant_pos : 0 < gateGradientConstant :=
  mul_pos gateSlopeConstant_pos (radialDerivativeConstant_pos 1)

variable {N : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem radialGate_gradient_norm_le (a : E) {B α : ℝ} (hB : 0 < B) (hα : 0 < α) (x : E) :
    ‖gradient (radialGate a B α) x‖ ≤ gateGradientConstant * ‖a‖ / α := by
  have hR : ‖fderiv ℝ (radialSquash B : E → E) x‖ ≤ radialDerivativeConstant 1 := by
    have h := radialSquash_derivative_bound 1 hB x
    rw [← norm_iteratedFDeriv_fderiv (n := 0), norm_iteratedFDeriv_zero] at h
    simpa using h
  have hadj : ‖(fderiv ℝ (radialSquash B : E → E) x).adjoint a‖ ≤ radialDerivativeConstant 1 * ‖a‖ := by
    apply ((fderiv ℝ (radialSquash B : E → E) x).adjoint.le_opNorm a).trans
    rw [ContinuousLinearMap.adjoint.norm_map]
    exact mul_le_mul_of_nonneg_right hR (norm_nonneg a)
  rw [radialGate_gradient, norm_smul, Real.norm_eq_abs, abs_div, abs_of_pos hα]
  calc
    _ ≤ (gateSlopeConstant / α) * (radialDerivativeConstant 1 * ‖a‖) :=
      mul_le_mul (div_le_div_of_nonneg_right (gateSlopeConstant_bound _) hα.le) hadj
        (norm_nonneg _) (div_nonneg gateSlopeConstant_pos.le hα.le)
    _ = gateGradientConstant * ‖a‖ / α := by unfold gateGradientConstant; ring

theorem Data.forceGradient_norm_le (d : Data N E) (hD : d.D ≠ 0) (hK : 0 ≤ d.K)
    (i : Fin (N + 1)) (x : E) : ‖d.forceGradient i x‖ ≤ ‖d.b i‖ := by
  rw [← (d.force_hasGradientAt hD i x).gradient]
  exact forcing_gradient_norm_le _ hD hK _ _

theorem Data.gateGradient_norm_le (d : Data N E) (hB : 0 < d.B) (hα : 0 < d.α)
    (i : Fin (N + 1)) (x : E) : ‖d.gateGradient i x‖ ≤ gateGradientConstant * ‖d.a i‖ / d.α := by
  rw [← (d.gate_hasGradientAt i x).gradient]
  exact radialGate_gradient_norm_le _ hB hα _

omit [CompleteSpace E] in
theorem Data.outgoing_bounds (d : Data N E) (hD : 0 ≤ d.D) (hK : 0 ≤ d.K) (hC : d.K + 2 ≤ d.C₀)
    (z : BlockProduct (N + 1) E) (i : Fin (N + 1)) :
    0 ≤ d.outgoing z i ∧ d.outgoing z i ≤ d.D * (d.C₀ + d.K + 1) := by
  refine Fin.lastCases ?_ (fun j => ?_) i
  · have hC0 : 0 ≤ d.C₀ := by linarith
    simp only [d.outgoing_last, le_refl, true_and]
    positivity
  · have h := d.force_bounds hD hK hC j.succ (z j.succ)
    rw [d.outgoing_castSucc]
    exact ⟨hD.trans h.1, h.2⟩

/-- The block norm estimate uses the actual full gradient and the global
radial derivative bound, before assuming that any block is in the identity
region. Thus it does not assume its own conclusion. -/
theorem Data.matrix_image_norm_le (d : Data N E)
    (hA : ∀ i, IsSelfAdjoint (d.A i)) (hD : 0 < d.D) (hK : 0 ≤ d.K) (hC : d.K + 2 ≤ d.C₀)
    (hB : 0 < d.B) (hα : 0 < d.α) {h : ℝ}
    (hb : ∀ i, ‖d.b i‖ ≤ h) (ha : ∀ i, ‖d.a i‖ ≤ 1)
    (z : BlockProduct (N + 1) E) (i : Fin (N + 1)) :
    ‖d.A i (z i)‖ ≤ ‖gradient d.energy z‖ + h +
      d.D * (d.C₀ + d.K + 1) * (gateGradientConstant / d.α) := by
  have hc := d.incoming_mem z i
  have hout := d.outgoing_bounds hD.le hK hC z i
  have hforce : ‖d.incoming z i • d.forceGradient i (z i)‖ ≤ h := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hc.1]
    exact ((mul_le_of_le_one_left (norm_nonneg _) hc.2).trans
      (d.forceGradient_norm_le hD.ne' hK i (z i))).trans (hb i)
  have hgate : ‖d.gateGradient i (z i)‖ ≤ gateGradientConstant / d.α := by
    apply (d.gateGradient_norm_le hB hα i (z i)).trans
    apply div_le_div_of_nonneg_right _ hα.le
    exact mul_le_of_le_one_right gateGradientConstant_pos.le (ha i)
  have houtnorm : ‖d.outgoing z i • d.gateGradient i (z i)‖ ≤
      d.D * (d.C₀ + d.K + 1) * (gateGradientConstant / d.α) := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hout.1]
    exact mul_le_mul hout.2 hgate (norm_nonneg _) (hout.1.trans hout.2)
  have heq : d.A i (z i) = gradient d.energy z i +
      d.incoming z i • d.forceGradient i (z i) + d.outgoing z i • d.gateGradient i (z i) := by
    rw [d.energy_gradient_apply hA hD.ne']
    abel
  rw [heq]
  calc
    _ ≤ ‖gradient d.energy z i + d.incoming z i • d.forceGradient i (z i)‖ +
        ‖d.outgoing z i • d.gateGradient i (z i)‖ := norm_add_le _ _
    _ ≤ (‖gradient d.energy z i‖ + ‖d.incoming z i • d.forceGradient i (z i)‖) +
        ‖d.outgoing z i • d.gateGradient i (z i)‖ := add_le_add_right (norm_add_le _ _) _
    _ ≤ _ := add_le_add (add_le_add (block_norm_le _ _) hforce) houtnorm

theorem Data.stationary_blocks_in_ball (d : Data N E)
    (hA : ∀ i, IsSelfAdjoint (d.A i)) (hD : 0 < d.D) (hK : 0 ≤ d.K) (hC : d.K + 2 ≤ d.C₀)
    (hB : 0 < d.B) (hα : 0 < d.α) {h γ ε : ℝ} (hγ : 0 < γ)
    (hcoercive : ∀ i x, γ * ‖x‖ ≤ ‖d.A i x‖)
    (hb : ∀ i, ‖d.b i‖ ≤ h) (ha : ∀ i, ‖d.a i‖ ≤ 1)
    (hradius : ε + h + d.D * (d.C₀ + d.K + 1) * (gateGradientConstant / d.α) ≤ γ * d.B)
    (z : BlockProduct (N + 1) E) (hz : ‖gradient d.energy z‖ ≤ ε) :
    ∀ i : Fin (N + 1), ‖z i‖ ≤ d.B := by
  intro i
  have himage := d.matrix_image_norm_le hA hD hK hC hB hα hb ha z i
  have hlower := hcoercive i (z i)
  nlinarith

end RandomizedFO2003.Cascade
