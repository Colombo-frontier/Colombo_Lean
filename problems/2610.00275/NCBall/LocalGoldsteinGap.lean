import NCBall.RandomSegment
import NCBall.UpperProjection

/-! # A large Goldstein radius admits the starting point as output

For a C¹ function, a gap bound on a ball controls the Goldstein residual at
its center. Projection onto the closed convex hull supplies a common descent
direction whenever the least-norm vector is nonzero.
-/

noncomputable section
open MeasureTheory Set Metric
open scoped InnerProductSpace
namespace NCBall

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem smoothGoldsteinResidual_le_gap_div_radius {f : E → ℝ} (hf : ContDiff ℝ 1 f)
    (x₀ : E) {ρ Δ : ℝ} (hρ : 0 < ρ)
    (hgap : ∀ x ∈ closedBall x₀ ρ, f x₀ - f x ≤ Δ) :
    smoothGoldsteinResidual (gradient f) ρ x₀ ≤ Δ / ρ := by
  let C := smoothGoldsteinSet (gradient f) ρ x₀
  have hC : C.Nonempty := smoothGoldsteinSet_nonempty (gradient f) hρ.le x₀
  have hclosed : IsClosed C := isClosed_closedConvexHull
  have hconv : Convex ℝ C := convex_closedConvexHull
  obtain ⟨p, hp, hmin⟩ := exists_norm_eq_iInf_of_complete_convex hC hclosed.isComplete hconv (0 : E)
  have hres : smoothGoldsteinResidual (gradient f) ρ x₀ ≤ ‖p‖ := by
    simpa only [dist_zero_left] using infDist_le_dist_of_mem hp (x := (0 : E))
  have hΔ : 0 ≤ Δ := by simpa only [sub_self] using hgap x₀ (mem_closedBall_self hρ.le)
  by_cases hp0 : p = 0
  · simpa only [hp0, norm_zero] using hres.trans (by simpa only [hp0, norm_zero] using div_nonneg hΔ hρ.le)
  have hpn : 0 < ‖p‖ := norm_pos_iff.mpr hp0
  have hdir : ∀ y ∈ closedBall x₀ ρ, ‖p‖ ^ 2 ≤ ⟪p, gradient f y⟫_ℝ := by
    intro y hy
    have hyC : gradient f y ∈ C := subset_closedConvexHull (mem_image_of_mem (gradient f) hy)
    have hh := (norm_eq_iInf_iff_real_inner_le_zero hconv hp).mp hmin (gradient f y) hyC
    simp only [zero_sub, inner_neg_left, inner_sub_right, real_inner_self_eq_norm_sq] at hh
    linarith
  let v : E := -(ρ / ‖p‖) • p
  have hv : ‖v‖ = ρ := by
    simp only [v, norm_smul, Real.norm_eq_abs, abs_neg, abs_div, abs_of_pos hρ, abs_of_pos hpn]
    field_simp
  have hpoint (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : x₀ + t • v ∈ closedBall x₀ ρ := by
    rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1, hv]
    nlinarith [ht.2]
  have hderiv (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      ⟪gradient f (x₀ + t • v), v⟫_ℝ ≤ -ρ * ‖p‖ := by
    calc
      _ = -(ρ / ‖p‖) * ⟪p, gradient f (x₀ + t • v)⟫_ℝ := by
        rw [show v = -(ρ / ‖p‖) • p from rfl, inner_smul_right, real_inner_comm p]
      _ ≤ -(ρ / ‖p‖) * ‖p‖ ^ 2 :=
        mul_le_mul_of_nonpos_left (hdir _ (hpoint t ht)) (neg_nonpos.mpr (div_nonneg hρ.le hpn.le))
      _ = _ := by field_simp; ring
  have hc : Continuous (fun t : ℝ => ⟪gradient f (x₀ + t • v), v⟫_ℝ) :=
    ((gradient_continuous_of_C1 hf).comp (continuous_const.add (continuous_id.smul continuous_const))).inner
      continuous_const
  have hdrop : f (x₀ + v) - f x₀ ≤ -ρ * ‖p‖ := by
    calc
      _ = ∫ t in (0 : ℝ)..1, ⟪gradient f (x₀ + t • v), v⟫_ℝ :=
        (interval_segment_gradient_integral hf x₀ v).symm
      _ ≤ ∫ _t in (0 : ℝ)..1, -ρ * ‖p‖ :=
        intervalIntegral.integral_mono_on (by norm_num) (hc.intervalIntegrable 0 1) intervalIntegrable_const hderiv
      _ = _ := by simp
  have hx : x₀ + v ∈ closedBall x₀ ρ := by simpa only [one_smul] using hpoint 1 ⟨by norm_num, le_rfl⟩
  have hb : ‖p‖ ≤ Δ / ρ := (le_div_iff₀ hρ).2 (by nlinarith [hgap (x₀ + v) hx])
  exact hres.trans hb

omit [CompleteSpace E] in
theorem smoothGoldsteinResidual_radius_antitone (g : E → E) (x : E) {ρ ν : ℝ}
    (hρ : 0 ≤ ρ) (hρν : ρ ≤ ν) :
    smoothGoldsteinResidual g ν x ≤ smoothGoldsteinResidual g ρ x :=
  infDist_le_infDist_of_subset
    ((closedConvexHull ℝ).monotone (image_mono (closedBall_subset_closedBall hρν)))
    (smoothGoldsteinSet_nonempty g hρ x)

theorem clarkeGoldsteinResidual_le_local_gap {f : E → ℝ} (hf : ContDiff ℝ 1 f)
    (x₀ : E) {ρ ν R Δ : ℝ} (hρ : 0 < ρ) (hρν : ρ ≤ ν) (hρR : ρ ≤ R)
    (hgap : ∀ x ∈ closedBall x₀ R, f x₀ - f x ≤ Δ) :
    clarkeGoldsteinResidual f ν x₀ ≤ Δ / ρ := by
  rw [clarkeGoldsteinResidual_eq_of_C1 hf]
  exact (smoothGoldsteinResidual_radius_antitone (gradient f) x₀ hρ.le hρν).trans
    (smoothGoldsteinResidual_le_gap_div_radius hf x₀ hρ
      (fun x hx => hgap x ((closedBall_subset_closedBall hρR) hx)))

theorem large_radius_start_stationary {f : E → ℝ} (hf : ContDiff ℝ 1 f)
    (x₀ : E) {ν R Δ ε : ℝ} (hΔ : 0 < Δ) (hε : 0 < ε)
    (hν : Δ / ε ≤ ν) (hR : Δ / ε ≤ R)
    (hgap : ∀ x ∈ closedBall x₀ R, f x₀ - f x ≤ Δ) :
    clarkeGoldsteinResidual f ν x₀ ≤ ε := by
  have hb := clarkeGoldsteinResidual_le_local_gap hf x₀ (div_pos hΔ hε) hν hR hgap
  have he : Δ / (Δ / ε) = ε := by field_simp
  rwa [he] at hb

theorem zero_gap_start_stationary {f : E → ℝ} (hf : ContDiff ℝ 1 f)
    (x₀ : E) {ν R : ℝ} (hν : 0 < ν) (hR : 0 < R)
    (hgap : ∀ x ∈ closedBall x₀ R, f x₀ - f x ≤ 0) :
    clarkeGoldsteinResidual f ν x₀ ≤ 0 := by
  have hb := clarkeGoldsteinResidual_le_local_gap hf x₀ (lt_min hν hR)
    (min_le_left ν R) (min_le_right ν R) hgap
  simpa only [zero_div] using hb

end NCBall
