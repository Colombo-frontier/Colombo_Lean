import Nonsmooth.NormalizedBodyCutPolicy
import Nonsmooth.ConvexCapVolume

open MeasureTheory MeasureTheory.Measure Set
open scoped InnerProductSpace ENNReal
set_option autoImplicit false
namespace Nonsmooth
noncomputable section
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem convex_inner_sublevel (e : E) (τ : ℝ) : Convex ℝ {z : E | ⟪z, e⟫_ℝ ≤ τ} := by
  intro x hx y hy a b ha hb hab
  simp only [Set.mem_setOf_eq, inner_add_left, real_inner_smul_left]
  have h1 := mul_le_mul_of_nonneg_left hx ha
  have h2 := mul_le_mul_of_nonneg_left hy hb
  have heq : a * τ + b * τ = τ := by rw [← add_mul, hab, one_mul]
  linarith

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

/-- Under an explicit central halfspace-volume condition, the actual cut removes a fixed volume fraction. -/
theorem actual_normalized_body_volume_cut (μ : Measure E) [IsAddHaarMeasure μ]
    (r : ℝ) (hr : 0 < r) (G : Set E) (hG : Convex ℝ G) (hGm : MeasurableSet G)
    (hinner : Metric.closedBall (0 : E) r ⊆ G)
    (houter : G ⊆ Metric.closedBall (0 : E) ((Module.finrank ℝ E : ℝ) * r))
    (hd : 2 ≤ Module.finrank ℝ E) (κ : ℝ≥0∞)
    (hdepth : ∀ e : E, ‖e‖ = 1 → κ * μ G ≤ μ {z | z ∈ G ∧ 0 ≤ ⟪z, e⟫_ℝ}) :
    ∃ T : ℕ, ∃ p : Policy Unit (CircularHistory × CyclicPeakState) (Feasible E r),
      ∃ axis : CircularHistory × CyclicPeakState → E,
      p.IsMeasurable ∧ Measurable axis ∧
      (T : ℝ) ≤ 248 * (Module.finrank ℝ E : ℝ) * Real.log ((Module.finrank ℝ E : ℝ) + 1) ∧
      ∀ f : E → ℝ, ConvexOn ℝ G f → ∃ e : E,
        e = axis (p.run (fun z => f z.val) () T) ∧ ‖e‖ = 1 ∧
        let x := (p.result (fun z => f z.val) () T).val
        let K := {z | z ∈ G ∧ ⟪z, e⟫_ℝ ≤ r / (4 * (Module.finrank ℝ E : ℝ))}
        Convex ℝ K ∧ (∀ z ∈ G, f z < f x → z ∈ K) ∧
          μ K + (ENNReal.ofReal (1 / 2 : ℝ) * κ) * μ G ≤ μ G := by
  obtain ⟨T, p, axis, hp, haxis, hcount, hcert⟩ := actual_normalized_body_cut_policy_with_direction r hr G hinner houter hd
  refine ⟨T, p, axis, hp, haxis, hcount, ?_⟩
  intro f hf
  obtain ⟨e, hcomputed, he, _, _, hcut⟩ := hcert f hf
  refine ⟨e, hcomputed, he, ?_⟩
  dsimp only
  have hdp : 0 < Module.finrank ℝ E := by omega
  have hdpR : (0 : ℝ) < Module.finrank ℝ E := by exact_mod_cast hdp
  have hre : r • e ∈ G := by
    apply hinner
    simpa only [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg hr.le, he, mul_one] using (le_rfl : r ≤ r)
  have hcap := addHaar_cap_fraction_of_halfspace_fraction μ hG he hre hdp (hdepth e he)
  have ht : r / (4 * (Module.finrank ℝ E : ℝ)) < r / (2 * (Module.finrank ℝ E : ℝ)) := by
    apply (div_lt_div_iff₀ (by positivity : (0 : ℝ) < 4 * (Module.finrank ℝ E : ℝ))
      (by positivity : (0 : ℝ) < 2 * (Module.finrank ℝ E : ℝ))).mpr
    nlinarith [mul_pos hr hdpR]
  have hpartition := separated_cap_retained_volume_add_le μ hGm e ht
  refine ⟨hG.inter (convex_inner_sublevel e _), ?_, ?_⟩
  · intro z hz hbetter
    refine ⟨hz, ?_⟩
    by_contra hn
    exact (not_lt_of_ge (hcut z hz (lt_of_not_ge hn).le)) hbetter
  · exact (add_le_add le_rfl hcap).trans hpartition

end
end Nonsmooth
