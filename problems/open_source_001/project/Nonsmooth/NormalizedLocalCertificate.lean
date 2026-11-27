import Nonsmooth.DiscreteBodyVolumeCut
import Nonsmooth.GuardedHalfspaceCut
import Nonsmooth.PolynomialAspectBudget

open MeasureTheory MeasureTheory.Measure Set
open scoped ENNReal InnerProductSpace
set_option autoImplicit false
namespace Nonsmooth
noncomputable section
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E] in
theorem positive_inner_ball_interior {G : Set E} {r : ℝ} (hr : 0 < r)
    (hinner : Metric.closedBall (0 : E) r ⊆ G) : (0 : E) ∈ interior G :=
  mem_interior_iff_mem_nhds.mpr (Filter.mem_of_superset (Metric.closedBall_mem_nhds 0 hr) hinner)

theorem actual_normalized_local_certificate {G : Set E} (hconv : Convex ℝ G)
    (hcompact : IsCompact G) (hd : 2 ≤ Module.finrank ℝ E)
    (hinner : Metric.closedBall (0 : E) (1 / (Module.finrank ℝ E : ℝ)) ⊆ G)
    (houter : G ⊆ Metric.closedBall (0 : E) (4 * (Module.finrank ℝ E : ℝ) ^ 2))
    (hdepth : ∀ ℓ : E →L[ℝ] ℝ, ℓ ≠ 0 →
      ENNReal.ofReal (1 / 4 : ℝ) * volume G ≤ volume (G ∩ {z | 0 ≤ ℓ z})) :
    ∃ T : ℕ, ∃ p : Policy Unit (CircularHistory × CyclicPeakState)
      (Feasible E (1 / (Module.finrank ℝ E : ℝ))),
      ∃ out : CircularHistory → Feasible E (1 / (Module.finrank ℝ E : ℝ)),
      ∃ cut : CircularHistory → Set E,
      p.IsMeasurable ∧ (∀ st, p.output () st = out st.1) ∧ Measurable out ∧
      (T : ℝ) ≤ 434 * (Module.finrank ℝ E : ℝ) * Real.log ((Module.finrank ℝ E : ℝ) + 1) ∧
      (∀ h, cut h ⊆ G ∧ Convex ℝ (cut h) ∧ IsCompact (cut h) ∧ (0 : E) ∈ interior (cut h)) ∧
      ∀ f : E → ℝ, ConvexOn ℝ G f →
        let st := p.run (fun z => f z.val) () T
        (∀ z ∈ G, f z < f (p.result (fun z => f z.val) () T).val → z ∈ cut st.1) ∧
        volume (cut st.1) + ENNReal.ofReal (1 / 8 : ℝ) * volume G ≤ volume G := by
  have hdp : 0 < Module.finrank ℝ E := by omega
  have hdr : (0 : ℝ) < Module.finrank ℝ E := by exact_mod_cast hdp
  let r : ℝ := 1 / (Module.finrank ℝ E : ℝ)
  have hr : 0 < r := by positivity
  have houter' : G ⊆ Metric.closedBall (0 : E) (((4 * Module.finrank ℝ E ^ 3 : ℕ) : ℝ) * r) := by
    simpa only [r, polynomial_aspect_radius _ hdp] using houter
  have hdep : ∀ e : E, ‖e‖ = 1 → ENNReal.ofReal (1 / 4 : ℝ) * volume G ≤
      volume {z | z ∈ G ∧ 0 ≤ ⟪z, e⟫_ℝ} := by
    intro e he
    have hne : innerSL ℝ e ≠ 0 := by
      intro hz
      have h := congrArg (fun q : E →L[ℝ] ℝ => q e) hz
      change ⟪e, e⟫_ℝ = 0 at h
      simp [real_inner_self_eq_norm_sq, he] at h
    have h := hdepth (innerSL ℝ e) hne
    change ENNReal.ofReal (1 / 4 : ℝ) * volume G ≤ volume {z | z ∈ G ∧ 0 ≤ ⟪e, z⟫_ℝ} at h
    simpa only [real_inner_comm e] using h
  obtain ⟨T, p, out, axis, hp, hout, houtm, _haxis, hT, hcert⟩ :=
    actual_aspect_body_volume_cut_discrete_readout volume r hr (4 * Module.finrank ℝ E ^ 3)
      (polynomial_aspect_positive _ hdp) G hconv hcompact.measurableSet hinner houter' hd
      (ENNReal.ofReal (1 / 4 : ℝ)) hdep
  let τ := r / (4 * (Module.finrank ℝ E : ℝ))
  have hτ : 0 < τ := by positivity
  have hτr : τ ≤ r := by
    dsimp only [τ]
    apply div_le_self hr.le
    have hd1 : (1 : ℝ) ≤ Module.finrank ℝ E := by exact_mod_cast hdp
    linarith
  let cut := fun h => guardedHalfspaceCut G (axis h) τ
  refine ⟨T, p, out, cut, hp, hout, houtm, hT.trans (polynomial_aspect_local_budget_bound _ hdp), ?_, ?_⟩
  · intro h
    exact ⟨guardedHalfspaceCut_subset G _ _, guardedHalfspaceCut_convex hconv _ _,
      guardedHalfspaceCut_compact hcompact _ _, positive_inner_ball_interior hτ
        (guardedHalfspaceCut_contains_ball hinner hτr _)⟩
  · intro f hf
    obtain ⟨e, hcomputed, he, _, hkeep, hvol⟩ := hcert f hf
    dsimp only
    have hcut : cut (p.run (fun z => f z.val) () T).1 = halfspaceCutBody G e τ := by
      dsimp only [cut]
      rw [← hcomputed, guardedHalfspaceCut_of_unit G he]
    rw [hcut]
    constructor
    · exact hkeep
    · have hfactor : ENNReal.ofReal (1 / 2 : ℝ) * ENNReal.ofReal (1 / 4 : ℝ) =
          ENNReal.ofReal (1 / 8 : ℝ) := by rw [← ENNReal.ofReal_mul (by norm_num)]; norm_num
      rw [hfactor] at hvol
      exact hvol

end
end Nonsmooth
