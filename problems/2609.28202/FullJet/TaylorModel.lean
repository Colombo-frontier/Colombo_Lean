import FullJet.FirstHitCoupling
import Mathlib.Analysis.Calculus.ContDiff.CPolynomial
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.InnerProductSpace.NormPow
import Mathlib.Topology.Order.Compact

open scoped BigOperators Topology ContDiff

namespace FullJet

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {p : ℕ}

/-- The positive-order Taylor polynomial computed from one derivative packet. -/
noncomputable def jetTaylor (J : JetPacket p E) (h : E) : ℝ :=
  ∑ j : Fin p, ((j.val + 1).factorial : ℝ)⁻¹ * J j.succ (fun _ => h)

/-- The trust-region model used by the higher-order upper-bound algorithm. -/
noncomputable def regularizedJetModel (J : JetPacket p E) (M : ℝ) (h : E) : ℝ :=
  jetTaylor J h + M / ((p + 1).factorial : ℝ) * ‖h‖ ^ (p + 1)

theorem jetTaylor_contDiff (J : JetPacket p E) : ContDiff ℝ ∞ (jetTaylor J) := by
  unfold jetTaylor
  apply ContDiff.sum
  intro j _
  exact contDiff_const.mul ((J j.succ).contDiff.comp (contDiff_pi.mpr fun _ => contDiff_id))

theorem jetTaylor_zero (J : JetPacket p E) : jetTaylor J 0 = 0 := by
  apply Finset.sum_eq_zero
  intro j _
  have hz : J j.succ (fun _ => (0 : E)) = 0 := by
    letI : Nonempty (Fin j.succ.val) := ⟨⟨0, Nat.succ_pos _⟩⟩
    exact (J j.succ).map_zero
  rw [hz, mul_zero]

theorem regularizedJetModel_continuous (J : JetPacket p E) (M : ℝ) :
    Continuous (regularizedJetModel J M) :=
  (jetTaylor_contDiff J).continuous.add (continuous_const.mul (continuous_norm.pow _))

theorem regularizedJetModel_zero (J : JetPacket p E) (M : ℝ) :
    regularizedJetModel J M 0 = 0 := by
  simp [regularizedJetModel, jetTaylor_zero]

theorem normPower_contDiff (hp : 0 < p) :
    ContDiff ℝ 1 (fun h : E => ‖h‖ ^ (p + 1)) := by
  have h := contDiff_norm_rpow (E := E) (p := ((p + 1 : ℕ) : ℝ)) (by exact_mod_cast Nat.succ_lt_succ hp)
  simpa only [Real.rpow_natCast] using h

theorem normPower_fderiv_norm (hp : 0 < p) (h : E) :
    ‖fderiv ℝ (fun y : E => ‖y‖ ^ (p + 1)) h‖ = (p + 1 : ℝ) * ‖h‖ ^ p := by
  have hb : (1 : ℝ) < ((p + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_lt_succ hp
  have hd := norm_fderiv_norm_id_rpow (E := E) h hb
  simp only [Real.rpow_natCast] at hd
  simpa only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right, Real.rpow_natCast] using hd

theorem regularizedJetModel_differentiable (hp : 0 < p) (J : JetPacket p E) (M : ℝ) :
    Differentiable ℝ (regularizedJetModel J M) := by
  have ht : Differentiable ℝ (jetTaylor J) := (jetTaylor_contDiff J).differentiable (by simp)
  exact ht.add ((normPower_contDiff hp).differentiable le_rfl |>.const_mul _)

theorem regularizedJetModel_fderiv (hp : 0 < p) (J : JetPacket p E) (M : ℝ) (h : E) :
    fderiv ℝ (regularizedJetModel J M) h = fderiv ℝ (jetTaylor J) h +
      (M / ((p + 1).factorial : ℝ)) • fderiv ℝ (fun y : E => ‖y‖ ^ (p + 1)) h := by
  unfold regularizedJetModel
  rw [fderiv_add ((jetTaylor_contDiff J).differentiable (by simp) h)
    (((normPower_contDiff hp).differentiable le_rfl h).const_mul _)]
  rw [fderiv_const_mul ((normPower_contDiff hp).differentiable le_rfl h)]

theorem regularizedJetModel_exists_min [FiniteDimensional ℝ E]
    (J : JetPacket p E) (M r : ℝ) (hr : 0 ≤ r) :
    ∃ h ∈ Metric.closedBall (0 : E) r,
      IsMinOn (regularizedJetModel J M) (Metric.closedBall 0 r) h := by
  exact (isCompact_closedBall (0 : E) r).exists_isMinOn
    ⟨0, Metric.mem_closedBall_self hr⟩ (regularizedJetModel_continuous J M).continuousOn

/-- A global minimizer is free internal computation in the component-oracle model. -/
noncomputable def regularizedJetStep [FiniteDimensional ℝ E]
    (J : JetPacket p E) (M r : ℝ) (hr : 0 ≤ r) : E :=
  Classical.choose (regularizedJetModel_exists_min J M r hr)

theorem regularizedJetStep_spec [FiniteDimensional ℝ E]
    (J : JetPacket p E) (M r : ℝ) (hr : 0 ≤ r) :
    ‖regularizedJetStep J M r hr‖ ≤ r ∧
      ∀ h, ‖h‖ ≤ r → regularizedJetModel J M (regularizedJetStep J M r hr) ≤
        regularizedJetModel J M h := by
  have h := Classical.choose_spec (regularizedJetModel_exists_min J M r hr)
  refine ⟨by simpa only [regularizedJetStep, Metric.mem_closedBall, dist_zero_right] using h.1, ?_⟩
  intro y hy
  exact h.2 (by simpa only [Metric.mem_closedBall, dist_zero_right] using hy)

theorem regularizedJetStep_value_nonpos [FiniteDimensional ℝ E]
    (J : JetPacket p E) (M r : ℝ) (hr : 0 ≤ r) :
    regularizedJetModel J M (regularizedJetStep J M r hr) ≤ 0 := by
  have h := (regularizedJetStep_spec J M r hr).2 0 (by simpa using hr)
  simpa only [regularizedJetModel_zero] using h

theorem regularizedJetStep_fderiv_zero [FiniteDimensional ℝ E]
    (J : JetPacket p E) (M r : ℝ) (hr : 0 ≤ r)
    (hinterior : ‖regularizedJetStep J M r hr‖ < r) :
    fderiv ℝ (regularizedJetModel J M) (regularizedJetStep J M r hr) = 0 := by
  have hmin := (Classical.choose_spec (regularizedJetModel_exists_min J M r hr)).2
  apply (hmin.isLocalMin ?_).fderiv_eq_zero
  exact Metric.closedBall_mem_nhds_of_mem (by simpa only [Metric.mem_ball, dist_zero_right] using hinterior)

end FullJet
