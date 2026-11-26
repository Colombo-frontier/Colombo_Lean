import Smoothness2601.Cutoffs
import Bilevel.JointDerivative
import Mathlib.Analysis.Normed.Group.Bounded

/-! Bounds for the actual smooth cutoffs, including the self-bounding
gate inequality needed for dimension-free prefix-product estimates. -/
noncomputable section
open Filter Set
open scoped Topology RealInnerProductSpace ContDiff
namespace Smoothness2601.Cutoffs

theorem compact_abs_bound {f : ℝ → ℝ} (hc : HasCompactSupport f)
    (hf : Continuous f) : ∃ C : ℝ, 0 < C ∧ ∀ t, |f t| ≤ C := by
  obtain ⟨C,hC⟩ := (hc.isCompact_range hf).exists_bound_of_continuousOn
    (continuous_id.continuousOn : ContinuousOn (fun t : ℝ => t) (range f))
  refine ⟨max C 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro t
  exact (hC (f t) ⟨t,rfl⟩).trans (le_max_left _ _)

theorem bump_compact : HasCompactSupport bump := by
  apply HasCompactSupport.intro (isCompact_Icc : IsCompact (Icc (-1:ℝ) 1))
  intro t ht
  apply bump_zero
  by_contra h
  have ha : |t| < 1/4 := lt_of_not_ge h
  have hb := abs_lt.mp ha
  exact ht ⟨by linarith,by linarith⟩

theorem zeta_compact : HasCompactSupport zeta := by
  apply HasCompactSupport.intro (isCompact_Icc : IsCompact (Icc (-2:ℝ) 2))
  intro t ht
  apply zeta_zero_far
  by_contra h
  have ha := abs_lt.mp (lt_of_not_ge h)
  exact ht ⟨ha.1.le,ha.2.le⟩

theorem gate_deriv_compact : HasCompactSupport (deriv gate) := by
  apply HasCompactSupport.intro (isCompact_Icc : IsCompact (Icc (-2:ℝ) 2))
  intro t ht
  have ha : 1 < |t| := by
    by_contra h
    have hb := abs_le.mp (le_of_not_gt h)
    exact ht ⟨by linarith,by linarith⟩
  have he : gate =ᶠ[𝓝 t] (fun _ => 1) := by
    have hn : ∀ᶠ u in 𝓝 t, 1 < |u| :=
      continuous_abs.continuousAt.eventually (lt_mem_nhds ha)
    exact hn.mono fun _ hu => gate_one hu.le
  simpa using he.deriv_eq

theorem bump_deriv_contDiff : ContDiff ℝ ∞ (deriv bump) :=
  (contDiff_infty_iff_deriv.mp (bump_contDiff ⊤)).2

theorem gate_deriv_contDiff : ContDiff ℝ ∞ (deriv gate) :=
  (contDiff_infty_iff_deriv.mp (gate_contDiff ⊤)).2

theorem zeta_deriv_contDiff : ContDiff ℝ ∞ (deriv zeta) :=
  (contDiff_infty_iff_deriv.mp (zeta_contDiff ⊤)).2

theorem bump_derivative_bounds : ∃ L K : ℝ, 0 < L ∧ 0 < K ∧
    (∀ t, |deriv bump t| ≤ L) ∧ (∀ t, |deriv (deriv bump) t| ≤ K) := by
  obtain ⟨L,hL,hLb⟩ := compact_abs_bound bump_compact.deriv bump_deriv_contDiff.continuous
  obtain ⟨K,hK,hKb⟩ := compact_abs_bound bump_compact.deriv.deriv
    (bump_deriv_contDiff.continuous_deriv (by norm_num))
  exact ⟨L,K,hL,hK,hLb,hKb⟩

theorem gate_curvature_bound : ∃ M : ℝ, 0 < M ∧ ∀ t, |deriv (deriv gate) t| ≤ M :=
  compact_abs_bound gate_deriv_compact.deriv
    (gate_deriv_contDiff.continuous_deriv (by norm_num))

theorem zeta_derivative_bound : ∃ M : ℝ, 0 < M ∧ ∀ t, |deriv zeta t| ≤ M :=
  compact_abs_bound zeta_compact.deriv zeta_deriv_contDiff.continuous

/-- A nonnegative function with M-Lipschitz derivative has squared slope
at most twice M times its value. No compactness assumption is needed. -/
theorem nonneg_slope_square {f g : ℝ → ℝ} {M : ℝ} (hM : 0 < M)
    (hf : ∀ t, HasDerivAt f (g t) t)
    (hg : ∀ x y, ‖g x-g y‖ ≤ M*‖x-y‖) (hn : ∀ t, 0 ≤ f t) (x : ℝ) :
    (g x)^2 ≤ 2*M*f x := by
  let d := -g x/M
  have ht := Bilevel.JointDerivative.gradient_taylor f g M
    (fun t => (hf t).hasGradientAt') hg x d
  simp only [Real.norm_eq_abs,RCLike.inner_apply,conj_trivial,sq_abs] at ht
  have he : g x*d+M/2*d^2 = -((g x)^2/(2*M)) := by
    dsimp [d]
    field_simp
    ring
  have hb : (g x)^2/(2*M) ≤ f x := by
    have hu := (abs_le.mp ht).2
    have hz := hn (x+d)
    have hu' : f (x+d) ≤ f x + (g x*d+M/2*d^2) := by nlinarith only [hu]
    rw [he] at hu'
    linarith only [hu',hz]
  exact (div_le_iff₀ (by positivity : 0 < 2*M)).mp hb |>.trans_eq (by ring)

theorem gate_slope_bound {M : ℝ} (hM : 0 < M)
    (hb : ∀ t, |deriv (deriv gate) t| ≤ M) (t : ℝ) :
    (deriv gate t)^2 ≤ (4*M)*gate t*(1-gate t) := by
  have hd : ∀ t, HasDerivAt gate (deriv gate t) t :=
    fun t => ((gate_contDiff 1).differentiable (by norm_num) t).hasDerivAt
  have hl : ∀ x y, ‖deriv gate x-deriv gate y‖ ≤ M*‖x-y‖ := by
    intro x y
    exact Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun z _ => (gate_deriv_contDiff.differentiable (by norm_num) z).hasDerivAt.hasDerivWithinAt)
      (fun z _ => hb z) convex_univ (mem_univ y) (mem_univ x)
  have h1 := nonneg_slope_square hM hd hl gate_nonneg t
  have h2 := nonneg_slope_square hM (fun z => (hd z).const_sub 1)
    (fun x y => by simpa only [neg_sub_neg,norm_sub_rev] using hl x y)
    (fun z => sub_nonneg.mpr (gate_le_one z)) t
  have ha := gate_nonneg t
  have hc := gate_le_one t
  have hs := sq_nonneg (deriv gate t)
  by_cases hm : gate t ≤ 1/2
  · nlinarith [mul_nonneg (sub_nonneg.mpr h1) (show 0 ≤ 1-gate t by linarith)]
  · nlinarith [mul_nonneg (sub_nonneg.mpr h2) ha]

theorem actual_gate_bounds : ∃ C M : ℝ, 0 < C ∧ 0 < M ∧
    (∀ t, (deriv gate t)^2 ≤ C*gate t*(1-gate t)) ∧
    (∀ t, |deriv (deriv gate) t| ≤ M) := by
  obtain ⟨M,hM,hb⟩ := gate_curvature_bound
  exact ⟨4*M,M,by positivity,hM,gate_slope_bound hM hb,hb⟩

end Smoothness2601.Cutoffs
