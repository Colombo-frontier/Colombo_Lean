import MinimaxAudit.Gate

/-!
Dimension-independent high-order derivative bounds for the concrete double
primitive and scalar gate. Constants depend on the fixed cutoff and the two
fixed linear forms, never on the number of chain modules.
-/
open Set Filter
open scoped Topology ContDiff
namespace MinimaxAudit

noncomputable def gateDerivativeConstant (p : ℕ) (profile : GateProfile) (tau : ℝ) : ℝ :=
  gateBp p profile * tau ^ (1 - (p : ℤ))

theorem gateDerivativeConstant_nonneg (p : ℕ) (profile : GateProfile)
    {tau : ℝ} (htau : 0 < tau) : 0 ≤ gateDerivativeConstant p profile tau := by
  unfold gateDerivativeConstant gateBp
  exact mul_nonneg (le_trans (by norm_num) (le_max_left _ _)) (zpow_nonneg htau.le _)

/-- The p+1 derivative of H is controlled by the verified Lipschitz bound
for the p-1 derivative of h. -/
theorem doubleGate_high_derivative_bound (profile : GateProfile) {p : ℕ}
    (hp : 2 ≤ p) {tau : ℝ} (htau : 0 < tau) (s : ℝ) :
    |iteratedDeriv (p + 1) (doubleGate profile tau) s| ≤
      gateDerivativeConstant p profile tau := by
  have hder : deriv (doubleGate profile tau) = gate profile tau := by
    funext x
    exact doubleGate_deriv profile htau.ne' x
  have hn : p = p - 1 + 1 := by omega
  have heq : iteratedDeriv (p + 1) (doubleGate profile tau) s =
      deriv (iteratedDeriv (p - 1) (gate profile tau)) s := by
    rw [iteratedDeriv_succ', hder]
    conv_lhs => rw [hn]
    rw [iteratedDeriv_succ]
  rw [heq, ← Real.norm_eq_abs]
  apply norm_deriv_le_of_lip' (gateDerivativeConstant_nonneg p profile htau)
  exact Filter.Eventually.of_forall (fun x => by
    simpa [Real.norm_eq_abs, gateDerivativeConstant] using
      gate_high_derivative_lipschitz p profile hp htau x s)

/-- Pulling a one-dimensional double primitive back by a linear form has
the expected tensor bound, with the precise power of that form's norm. -/
theorem doubleGate_pullback_high_derivative_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (profile : GateProfile) {p : ℕ} (hp : 2 ≤ p) {tau : ℝ}
    (htau : 0 < tau) (A : E →L[ℝ] ℝ) (z : E) :
    ‖iteratedFDeriv ℝ (p + 1) (doubleGate profile tau ∘ A) z‖ ≤
      gateDerivativeConstant p profile tau * ‖A‖ ^ (p + 1) := by
  rw [A.iteratedFDeriv_comp_right
    (contDiff_infty.mp (doubleGate_contDiff profile htau.ne') (p + 1)) z le_rfl]
  calc
    _ ≤ ‖iteratedFDeriv ℝ (p + 1) (doubleGate profile tau) (A z)‖ *
        ∏ _ : Fin (p + 1), ‖A‖ :=
      ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
    _ ≤ gateDerivativeConstant p profile tau * ‖A‖ ^ (p + 1) := by
      rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
      simpa [Real.norm_eq_abs] using
        mul_le_mul_of_nonneg_right (doubleGate_high_derivative_bound profile hp htau (A z))
          (show 0 ≤ ‖A‖ ^ (p + 1) by positivity)

/-- The actual multi-variable scalar gate, pulled back by any two linear
forms, satisfies the claimed tau^(1-p) derivative scaling. -/
theorem scalarGate_pullback_high_derivative_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (profile : GateProfile) {p : ℕ} (hp : 2 ≤ p) {tau : ℝ}
    (htau : 0 < tau) (A B : E →L[ℝ] ℝ) (z : E) :
    ‖iteratedFDeriv ℝ (p + 1) (fun w => scalarGate profile tau (A w) (B w)) z‖ ≤
      gateDerivativeConstant p profile tau *
        (‖A + B‖ ^ (p + 1) + ‖A - B‖ ^ (p + 1)) / 2 := by
  let hpull : E → ℝ := doubleGate profile tau ∘ (A + B)
  let hminus : E → ℝ := doubleGate profile tau ∘ (A - B)
  have hc1 : ContDiff ℝ (p + 1) hpull :=
    (contDiff_infty.mp (doubleGate_contDiff profile htau.ne') (p + 1)).comp (A + B).contDiff
  have hc2 : ContDiff ℝ (p + 1) hminus :=
    (contDiff_infty.mp (doubleGate_contDiff profile htau.ne') (p + 1)).comp (A - B).contDiff
  have heq : (fun w => scalarGate profile tau (A w) (B w)) =
      fun w => (1 / 2 : ℝ) • (hpull w - hminus w) := by
    funext w
    simp [scalarGate, hpull, hminus, div_eq_mul_inv, mul_comm]
  rw [heq, iteratedFDeriv_const_smul_apply' (hc1.sub hc2).contDiffAt]
  change ‖(1 / 2 : ℝ) • iteratedFDeriv ℝ (p + 1) (hpull - hminus) z‖ ≤ _
  rw [iteratedFDeriv_sub_apply hc1.contDiffAt hc2.contDiffAt, norm_smul]
  have hb1 := doubleGate_pullback_high_derivative_bound profile hp htau (A + B) z
  have hb2 := doubleGate_pullback_high_derivative_bound profile hp htau (A - B) z
  have htri := norm_sub_le (iteratedFDeriv ℝ (p + 1) hpull z)
    (iteratedFDeriv ℝ (p + 1) hminus z)
  change ‖(1 / 2 : ℝ)‖ * _ ≤ _
  change ‖iteratedFDeriv ℝ (p + 1) hpull z‖ ≤ _ at hb1
  change ‖iteratedFDeriv ℝ (p + 1) hminus z‖ ≤ _ at hb2
  norm_num at ⊢
  nlinarith

end MinimaxAudit
