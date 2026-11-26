import ExactValue.SCCounts
import ExactValue.RestartAlgorithm

open scoped ENNReal
set_option autoImplicit false
set_option maxHeartbeats 800000
namespace ExactValue
noncomputable section

def scSteps (d : ℕ) (μ β R : ℝ) : ℕ → ℝ
  | 0 => phaseStep d β (burninAccuracy μ R (scPhaseLength μ β))
  | s + 1 => phaseStep d β (restartAccuracy (scCertifiedGap μ R s) R (scPhaseLength μ β))

theorem scSteps_bounds {d : ℕ} (hd : 0 < d) {μ β R : ℝ}
    (hμ : 0 < μ) (hμβ : μ ≤ β) (hR : 0 < R) (s : ℕ) :
    0 ≤ scSteps d μ β R s ∧ scSteps d μ β R s ≤ R / 2 := by
  have hβ := hμ.trans_le hμβ
  cases s with
  | zero =>
    obtain ⟨hδ, hδmax⟩ := burninAccuracy_bounds hμ hμβ hR (scPhaseLength μ β)
    obtain ⟨hp, hb, _⟩ := phaseStep_bounds hd hβ hR hδ hδmax
    exact ⟨hp.le, hb⟩
  | succ s =>
    obtain ⟨hδ, hδmax⟩ := restartAccuracy_bounds hμ hμβ hR (scCertifiedGap_pos hμ hR s)
      (scCertifiedGap_le_initial hμ hR s) (scPhaseLength μ β)
    obtain ⟨hp, hb, _⟩ := phaseStep_bounds hd hβ hR hδ hδmax
    exact ⟨hp.le, hb⟩

theorem sc_restart_origin_error {d : ℕ} (hd : 0 < d) {μ β R : ℝ} {f : Euclid d → ℝ}
    (hf : SCObjective d μ β R f) (hμ : 0 < μ) (hμβ : μ ≤ β) (hR : 0 < R)
    (v : ℕ → ℝ)
    (hv : ∀ t, v t = f (restartPoint (ballDomain (R / 2) (by positivity)) (2 * β)
      (scSteps d μ β R) (scPhaseLength μ β) v t))
    {xstar : Euclid d} (hx : ‖xstar‖ ≤ R / 2) (hmin : ∀ y, f xstar ≤ f y) (s : ℕ) :
    f (restartOrigin (ballDomain (R / 2) (by positivity)) (2 * β)
      (scSteps d μ β R) (scPhaseLength μ β) v (s + 1)) - f xstar ≤ scCertifiedGap μ R s := by
  let K := ballDomain (d := d) (R / 2) (by positivity)
  have hβ := hμ.trans_le hμβ
  induction s with
  | zero =>
    rw [restartOrigin_oracle_step K (2 * β) (scSteps d μ β R) (scPhaseLength μ β) v f hv 0]
    simpa only [restartOrigin, scSteps, scCertifiedGap, pow_zero, div_one] using
      sc_burnin hd hf hμ hμβ hR hx
  | succ s ih =>
    rw [restartOrigin_oracle_step K (2 * β) (scSteps d μ β R) (scPhaseLength μ β) v f hv (s + 1)]
    have hz : (0 : Euclid d) ∈ K.carrier := by simp [K, ballDomain]; positivity
    have hc : ‖restartOrigin K (2 * β) (scSteps d μ β R) (scPhaseLength μ β) v (s + 1)‖ ≤ R / 2 := by
      simpa [K, ballDomain] using restartOrigin_mem K hz (show 0 < 2 * β by positivity)
        (scSteps d μ β R) (scPhaseLength μ β) v (s + 1)
    rw [scCertifiedGap_succ]
    exact sc_restart_half hd hf hμ hμβ hR (scCertifiedGap_pos hμ hR s)
      (scCertifiedGap_le_initial hμ hR s) hc hx hmin ih

def scRestartedAlgorithm {d : ℕ} (hd : 0 < d) {μ β R : ℝ}
    (hμ : 0 < μ) (hμβ : μ ≤ β) (hR : 0 < R) (ε : ℝ) :
    ValueAlgorithm d R ((d + 1) * scPhaseLength μ β * (scRestartCount μ R ε + 1)) :=
  restartedValueAlgorithm hR.le (show 0 < 2 * β by have := hμ.trans_le hμβ; positivity)
    (scSteps d μ β R) (scSteps_bounds hd hμ hμβ hR) (scPhaseLength μ β) (scRestartCount μ R ε + 1)

theorem scRestartedAlgorithm_guarantees {d : ℕ} (hd : 0 < d) {μ β R ε : ℝ}
    (hμ : 0 < μ) (hμβ : μ ≤ β) (hR : 0 < R) (hε : 0 < ε) :
    (scRestartedAlgorithm hd hμ hμβ hR ε).SCGuarantees (μ := μ) (β := β) (ε := ε) := by
  intro f hf
  obtain ⟨xstar, hx, hmin, _⟩ := hf.minimizer
  let A := scRestartedAlgorithm hd hμ hμβ hR ε
  let v := policyValue A.query f
  have hβ := hμ.trans_le hμβ
  have hv (t : ℕ) : v t = f (restartPoint (ballDomain (R / 2) (by positivity)) (2 * β)
      (scSteps d μ β R) (scPhaseLength μ β) v t) := by
    exact congrArg f (restarted_algorithm_query hR.le (show 0 < 2 * β by positivity)
      (scSteps d μ β R) (scSteps_bounds hd hμ hμβ hR) (scPhaseLength μ β)
      (scRestartCount μ R ε + 1) f t)
  have herr := sc_restart_origin_error hd hf hμ hμβ hR v hv hx hmin (scRestartCount μ R ε)
  refine ⟨xstar, hmin, ?_⟩
  unfold scRestartedAlgorithm
  rw [restarted_algorithm_result]
  exact herr.trans (scRestartCount_accuracy hμ hR hε)

theorem sc_restarted_upper_calls {d : ℕ} (hd : 0 < d) {μ β R ε : ℝ}
    (hμ : 0 < μ) (hμβ : μ ≤ β) (hR : 0 < R) (hε : 0 < ε) :
    scValueComplexity d R μ β ε ≤
      ((d + 1) * scPhaseLength μ β * (scRestartCount μ R ε + 1) : ℕ) :=
  scValueComplexity_le (scRestartedAlgorithm hd hμ hμβ hR ε)
    (scRestartedAlgorithm_guarantees hd hμ hμβ hR hε)

theorem scRestartedAlgorithm_output_inner {d : ℕ} (hd : 0 < d) {μ β R ε : ℝ}
    (hμ : 0 < μ) (hμβ : μ ≤ β) (hR : 0 < R)
    (hist : QueryHistory d R ((d + 1) * scPhaseLength μ β * (scRestartCount μ R ε + 1))) :
    ‖((scRestartedAlgorithm hd hμ hμβ hR ε).output hist : Euclid d)‖ ≤ R / 2 := by
  have hβ := hμ.trans_le hμβ
  let K := ballDomain (d := d) (R / 2) (by positivity)
  have hz : (0 : Euclid d) ∈ K.carrier := by simp [K, ballDomain]; positivity
  have hm := restartOrigin_mem K hz (show 0 < 2 * β by positivity) (scSteps d μ β R)
    (scPhaseLength μ β) (historyValues hist) (scRestartCount μ R ε + 1)
  simpa only [K, ballDomain, Metric.mem_closedBall, dist_zero_right] using hm

theorem sc_restarted_upper {d : ℕ} (hd : 0 < d) {μ β R ε : ℝ}
    (hμ : 0 < μ) (hμβ : μ ≤ β) (hR : 0 < R) (hε : 0 < ε) :
    scValueComplexity d R μ β ε ≤
      ENNReal.ofReal (36 * d * Real.sqrt (β / μ) * (1 + logPlus (μ * R ^ 2 / ε))) := by
  apply (sc_restarted_upper_calls hd hμ hμβ hR hε).trans
  rw [← ENNReal.ofReal_natCast]
  exact ENNReal.ofReal_le_ofReal (sc_restarted_call_count hd hμ hμβ hR hε)

theorem sc_combined_upper {d : ℕ} (hd : 0 < d) {μ β R ε : ℝ}
    (hμ : 0 < μ) (hμβ : μ ≤ β) (hR : 0 < R) (hε : 0 < ε) (hεmax : ε ≤ β * R ^ 2) :
    scValueComplexity d R μ β ε ≤ ENNReal.ofReal (36 * d *
      min (Real.sqrt (β * R ^ 2 / ε)) (Real.sqrt (β / μ) * (1 + logPlus (μ * R ^ 2 / ε)))) := by
  rcases le_total (Real.sqrt (β * R ^ 2 / ε)) (Real.sqrt (β / μ) * (1 + logPlus (μ * R ^ 2 / ε))) with h | h
  · rw [min_eq_left h]
    apply (sc_direct_upper hd (hμ.trans_le hμβ) hR hε hεmax).trans
    apply ENNReal.ofReal_le_ofReal
    have : 0 ≤ (d : ℝ) * Real.sqrt (β * R ^ 2 / ε) := by positivity
    nlinarith
  · rw [min_eq_right h, ← mul_assoc]
    exact sc_restarted_upper hd hμ hμβ hR hε

end
end ExactValue
