import MinimaxAudit.GateHighOrder
import MinimaxAudit.GateHessian
import MinimaxAudit.ScalarJet

open scoped ContDiff Topology

/-! Source-facing gate lemma, assembled from the concrete integral proofs. -/
namespace MinimaxAudit

theorem gateHessian_eigenvalues_iff (a b t : ℝ) :
    (∃ v : GatePlane, v ≠ 0 ∧ gateHessianAction a b v = t • v) ↔ t = a ∨ t = -b := by
  constructor
  · rintro ⟨v, hv, he⟩
    have h0 := congrArg (fun w : GatePlane => w 0) he
    have h1 := congrArg (fun w : GatePlane => w 1) he
    simp [gateHessianAction] at h0 h1
    have hp : (a - t) * (v 0 + v 1) = 0 := by nlinarith
    have hm : (-b - t) * (v 0 - v 1) = 0 := by nlinarith
    by_cases hs : v 0 + v 1 = 0
    · have hd : v 0 - v 1 ≠ 0 := by
        intro hd
        apply hv
        ext i
        fin_cases i <;> simp <;> linarith
      have := (mul_eq_zero.mp hm).resolve_right hd
      right
      linarith
    · have := (mul_eq_zero.mp hp).resolve_right hs
      left
      linarith
  · intro ht
    rcases ht with ht | ht
    · subst t
      refine ⟨WithLp.toLp 2 ![1, 1], ?_, gateHessian_eigen_plus a b⟩
      intro h
      have := congrArg (fun w : GatePlane => w 0) h
      norm_num at this
    · subst t
      refine ⟨WithLp.toLp 2 ![1, -1], ?_, gateHessian_eigen_minus a b⟩
      intro h
      have := congrArg (fun w : GatePlane => w 0) h
      norm_num at this

theorem doubleGate_second_deriv (profile : GateProfile) {tau : ℝ}
    (htau : tau ≠ 0) (s : ℝ) :
    deriv (deriv (doubleGate profile tau)) s = profile.rho (s / tau) := by
  have hfun : deriv (doubleGate profile tau) = gate profile tau :=
    funext (doubleGate_deriv profile htau)
  rw [hfun, gate_deriv profile htau]

noncomputable def scalarGateSmoothnessConstant (profile : GateProfile) (p : ℕ) : ℝ :=
  gateBp p profile *
    ((‖(EuclideanSpace.proj 0 + EuclideanSpace.proj 1 : GatePlane →L[ℝ] ℝ)‖ ^ (p + 1) +
      ‖(EuclideanSpace.proj 0 - EuclideanSpace.proj 1 : GatePlane →L[ℝ] ℝ)‖ ^ (p + 1)) / 2 + 1)

theorem scalarGateSmoothnessConstant_pos (profile : GateProfile) (p : ℕ) :
    0 < scalarGateSmoothnessConstant profile p := by
  have hb : (0 : ℝ) < gateBp p profile := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  unfold scalarGateSmoothnessConstant
  positivity

/-- Exact uniform `(p+1)`-tensor bound in the Euclidean gate plane, including
H's derivative and with a constant depending only on p and the fixed cutoff. -/
theorem gate_high_order_source (profile : GateProfile) {p : ℕ} (hp : 2 ≤ p)
    {tau : ℝ} (htau : 0 < tau) (v : GatePlane) :
    ‖iteratedFDeriv ℝ (p + 1) (fun w : GatePlane => scalarGate profile tau (w 0) (w 1)) v‖ +
      |iteratedDeriv (p + 1) (doubleGate profile tau) (v 0)| ≤
      scalarGateSmoothnessConstant profile p * tau ^ (1 - (p : ℤ)) := by
  have htheta := scalarGate_pullback_high_derivative_bound profile hp htau
    (EuclideanSpace.proj 0 : GatePlane →L[ℝ] ℝ) (EuclideanSpace.proj 1) v
  have hH := doubleGate_high_derivative_bound profile hp htau (v 0)
  change ‖iteratedFDeriv ℝ (p + 1) (fun w : GatePlane => scalarGate profile tau (w 0) (w 1)) v‖ ≤ _ at htheta
  unfold gateDerivativeConstant at htheta hH
  unfold scalarGateSmoothnessConstant
  nlinarith

/-- The original gate lemma's complete clauses, with derivative-zero statements
encoded as full Frechet tensors rather than selected directional derivatives. -/
def ScalarGateProperties (profile : GateProfile) (p : ℕ) (tau K : ℝ) : Prop :=
  Function.Odd (gate profile tau) ∧ Function.Even (doubleGate profile tau) ∧
  ContDiff ℝ ∞ (gate profile tau) ∧ ContDiff ℝ ∞ (doubleGate profile tau) ∧
  (∀ s, |s| ≤ tau / 2 → gate profile tau s = 0 ∧ doubleGate profile tau s = 0) ∧
  (∀ s, 0 ≤ deriv (gate profile tau) s ∧ deriv (gate profile tau) s ≤ 1 ∧
    |gate profile tau s - s| ≤ tau) ∧
  (∀ k (z : ℝ × ℝ), |z.1| + |z.2| ≤ tau / 2 →
    iteratedFDeriv ℝ k (fun w : ℝ × ℝ => scalarGate profile tau w.1 w.2) z = 0) ∧
  (∀ z : ℝ × ℝ, |z.1| + |z.2| < tau / 2 →
    (fun w : ℝ × ℝ => scalarGate profile tau w.1 w.2) =ᶠ[𝓝 z] (fun _ => 0)) ∧
  (∀ a b, deriv (fun x => scalarGate profile tau x b) a =
      (gate profile tau (a + b) - gate profile tau (a - b)) / 2 ∧
    deriv (fun y => scalarGate profile tau a y) b =
      (gate profile tau (a + b) + gate profile tau (a - b)) / 2 ∧
    |deriv (fun x => scalarGate profile tau x b) a - b| ≤ tau ∧
    |deriv (fun y => scalarGate profile tau a y) b - a| ≤ tau ∧
    |scalarGate profile tau a b - a * b| ≤ tau * |b| ∧
    |doubleGate profile tau a - a ^ 2 / 2| ≤ tau * |a|) ∧
  (∀ v : GatePlane,
    fderiv ℝ (scalarGateGradient profile tau) v =
      gateHessianCLM (profile.rho ((v 0 + v 1) / tau)) (profile.rho ((v 0 - v 1) / tau)) ∧
    ‖fderiv ℝ (fderiv ℝ (fun w : GatePlane => scalarGate profile tau (w 0) (w 1))) v‖ ≤ 1) ∧
  (∀ v : GatePlane, ∀ t : ℝ,
    (∃ w : GatePlane, w ≠ 0 ∧ fderiv ℝ (scalarGateGradient profile tau) v w = t • w) ↔
      t = profile.rho ((v 0 + v 1) / tau) ∨ t = -profile.rho ((v 0 - v 1) / tau)) ∧
  (∀ s, 0 ≤ deriv (deriv (doubleGate profile tau)) s ∧
    deriv (deriv (doubleGate profile tau)) s ≤ 1) ∧
  (∀ v : GatePlane,
    ‖iteratedFDeriv ℝ (p + 1) (fun w : GatePlane => scalarGate profile tau (w 0) (w 1)) v‖ +
      |iteratedDeriv (p + 1) (doubleGate profile tau) (v 0)| ≤ K * tau ^ (1 - (p : ℤ)))

theorem gate_properties_source (profile : GateProfile) {p : ℕ} (hp : 2 ≤ p) :
    ∃ K : ℝ, 0 < K ∧ ∀ tau : ℝ, 0 < tau → ScalarGateProperties profile p tau K := by
  refine ⟨scalarGateSmoothnessConstant profile p, scalarGateSmoothnessConstant_pos profile p, ?_⟩
  intro tau htau
  refine ⟨gate_odd profile tau, doubleGate_even profile tau, gate_contDiff profile htau.ne',
    doubleGate_contDiff profile htau.ne', ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro s hs
    exact ⟨gate_zero_core profile htau hs, doubleGate_zero_core profile htau hs⟩
  · intro s
    have h := gate_basic_bounds profile htau s
    exact ⟨h.1, h.2.1, by simpa [abs_sub_comm] using h.2.2.2.1⟩
  · intro k z hz
    exact scalarGate_all_fderivatives_zero_core profile htau k hz
  · intro z hz
    exact scalarGate_module_eventually_zero profile htau
      (ContinuousLinearMap.fst ℝ ℝ ℝ) (ContinuousLinearMap.snd ℝ ℝ ℝ) hz
  · intro a b
    exact ⟨(scalarGate_partial_a profile htau.ne' a b).deriv,
      (scalarGate_partial_b profile htau.ne' a b).deriv,
      scalarGate_partial_a_error profile htau a b, scalarGate_partial_b_error profile htau a b,
      scalarGate_bilinear_error profile htau a b, doubleGate_quadratic_error profile htau a⟩
  · intro v
    exact ⟨(scalarGateGradient_hasFDerivAt profile htau.ne' v).fderiv,
      scalarGate_second_fderiv_norm_le profile htau.ne' v⟩
  · intro v t
    rw [(scalarGateGradient_hasFDerivAt profile htau.ne' v).fderiv]
    exact gateHessian_eigenvalues_iff _ _ _
  · intro s
    rw [doubleGate_second_deriv profile htau.ne']
    exact profile.range _
  · exact gate_high_order_source profile hp htau

end MinimaxAudit
