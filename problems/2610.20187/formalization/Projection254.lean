import Problem254
import Audit254
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal

noncomputable section
open scoped RealInnerProductSpace
namespace Paper254

/-- A positive-definite metric is represented by an invertible continuous
linear factor Q: its squared norm is ||Q(x)||^2. -/
theorem exists_metric_projection {d : ℕ} {D : ℝ} (W : Domain d D)
    (Q : Space d ≃L[ℝ] Space d) (a : Space d) :
    ∃ m : W.carrier, ∀ u : W.carrier, ⟪Q (a-m.val), Q (u.val-m.val)⟫ ≤ 0 := by
  have hn : (Q '' W.carrier).Nonempty := W.nonempty.image Q
  have hk : IsCompact (Q '' W.carrier) := W.compact.image Q.continuous
  have hc : Convex ℝ (Q '' W.carrier) := W.convex.linear_image Q.toLinearEquiv.toLinearMap
  obtain ⟨p, hp, hmin⟩ := exists_norm_eq_iInf_of_complete_convex hn hk.isComplete hc (Q a)
  have hv := (norm_eq_iInf_iff_real_inner_le_zero hc hp).mp hmin
  obtain ⟨m, hm, rfl⟩ := hp
  refine ⟨⟨m, hm⟩, ?_⟩
  intro u
  simpa only [map_sub] using hv (Q u.val) ⟨u.val, u.property, rfl⟩

def metricProject {d : ℕ} {D : ℝ} (W : Domain d D)
    (Q : Space d ≃L[ℝ] Space d) (a : Space d) : W.carrier :=
  (exists_metric_projection W Q a).choose

theorem metricProject_variational {d : ℕ} {D : ℝ} (W : Domain d D)
    (Q : Space d ≃L[ℝ] Space d) (a : Space d) (u : W.carrier) :
    ⟪Q (a-(metricProject W Q a).val), Q (u.val-(metricProject W Q a).val)⟫ ≤ 0 :=
  (exists_metric_projection W Q a).choose_spec u

theorem metricProject_pythagorean {d : ℕ} {D : ℝ} (W : Domain d D)
    (Q : Space d ≃L[ℝ] Space d) (a : Space d) (u : W.carrier) :
    ‖Q (u.val-(metricProject W Q a).val)‖^2 +
      ‖Q (a-(metricProject W Q a).val)‖^2 ≤ ‖Q (u.val-a)‖^2 := by
  let m := (metricProject W Q a).val
  have hv := metricProject_variational W Q a u
  change ⟪Q (a-m), Q (u.val-m)⟫ ≤ 0 at hv
  have he := norm_sub_sq_real (Q (u.val-m)) (Q (a-m))
  have heq : Q (u.val-m)-Q (a-m) = Q (u.val-a) := by
    rw [← map_sub]
    congr 1
    abel
  rw [heq] at he
  have hvi : ⟪Q (u.val-m), Q (a-m)⟫ ≤ 0 := by
    calc
      _ = ⟪Q (a-m), Q (u.val-m)⟫ := real_inner_comm _ _
      _ ≤ 0 := hv
  change ‖Q (u.val-m)‖^2 + ‖Q (a-m)‖^2 ≤ ‖Q (u.val-a)‖^2
  linarith

theorem metricProject_minimizes {d : ℕ} {D : ℝ} (W : Domain d D)
    (Q : Space d ≃L[ℝ] Space d) (a : Space d) (u : W.carrier) :
    ‖Q ((metricProject W Q a).val-a)‖^2 ≤ ‖Q (u.val-a)‖^2 := by
  have hp := metricProject_pythagorean W Q a u
  have he : ‖Q (a-(metricProject W Q a).val)‖ =
      ‖Q ((metricProject W Q a).val-a)‖ := by rw [map_sub, map_sub, norm_sub_rev]
  rw [he] at hp
  nlinarith [sq_nonneg ‖Q (u.val-(metricProject W Q a).val)‖]

/-- Exact mean projection decreases the full quadratic potential for every
feasible comparator. The covariance term c is unchanged. -/
theorem metricProject_potential_decreases {d : ℕ} {D : ℝ} (W : Domain d D)
    (Q : Space d ≃L[ℝ] Space d) (a : Space d) (u : W.carrier) (c : ℝ) :
    c+‖Q (u.val-(metricProject W Q a).val)‖^2/2 ≤ c+‖Q (u.val-a)‖^2/2 := by
  have hp := metricProject_pythagorean W Q a u
  nlinarith [sq_nonneg ‖Q (a-(metricProject W Q a).val)‖]

/-- The numerical objective-gap implication is also derived, not assumed. -/
theorem metricProject_objective_gap {d : ℕ} {D : ℝ} (W : Domain d D)
    (Q : Space d ≃L[ℝ] Space d) (a : Space d) (u : W.carrier) (ξ : ℝ)
    (hgap : ‖Q (u.val-a)‖^2 ≤ ‖Q ((metricProject W Q a).val-a)‖^2+ξ) :
    ‖Q (u.val-(metricProject W Q a).val)‖^2 ≤ ξ := by
  have hp := metricProject_pythagorean W Q a u
  have he : ‖Q (a-(metricProject W Q a).val)‖ =
      ‖Q ((metricProject W Q a).val-a)‖ := by rw [map_sub, map_sub, norm_sub_rev]
  rw [he] at hp
  linarith

end Paper254
#print axioms Paper254.exists_metric_projection
#print axioms Paper254.metricProject_potential_decreases
#print axioms Paper254.metricProject_objective_gap
