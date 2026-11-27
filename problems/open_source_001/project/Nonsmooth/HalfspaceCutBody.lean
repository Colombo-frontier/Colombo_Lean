import Nonsmooth.NormalizedBodyVolumeCut
import Nonsmooth.ProtasovVolumeCertificate

open MeasureTheory MeasureTheory.Measure Set Metric
open scoped InnerProductSpace ENNReal
set_option autoImplicit false
namespace Nonsmooth
noncomputable section
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def halfspaceCutBody (G : Set E) (e : E) (τ : ℝ) : Set E :=
  {z | z ∈ G ∧ ⟪z, e⟫_ℝ ≤ τ}

theorem halfspaceCutBody_subset (G : Set E) (e : E) (τ : ℝ) :
    halfspaceCutBody G e τ ⊆ G := fun _ hz => hz.1

theorem halfspaceCutBody_convex {G : Set E} (hG : Convex ℝ G) (e : E) (τ : ℝ) :
    Convex ℝ (halfspaceCutBody G e τ) := hG.inter (convex_inner_sublevel e τ)

theorem halfspaceCutBody_compact {G : Set E} (hG : IsCompact G) (e : E) (τ : ℝ) :
    IsCompact (halfspaceCutBody G e τ) := by
  have hc : Continuous (fun z : E => ⟪z, e⟫_ℝ) := continuous_id.inner continuous_const
  exact hG.inter_right (isClosed_le hc (continuous_const : Continuous (fun _ : E => τ)))

theorem halfspaceCutBody_contains_ball {G : Set E} {r τ : ℝ} {e : E}
    (hinner : Metric.closedBall (0 : E) r ⊆ G) (hτr : τ ≤ r) (he : ‖e‖ = 1) :
    Metric.closedBall (0 : E) τ ⊆ halfspaceCutBody G e τ := by
  intro z hz
  have hnorm : ‖z‖ ≤ τ := by simpa using hz
  refine ⟨hinner (by simpa using hnorm.trans hτr), ?_⟩
  have hi := real_inner_le_norm z e
  simpa only [he, mul_one] using hi.trans (by simpa only [he, mul_one] using hnorm)

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [FiniteDimensional ℝ E] [BorelSpace E] in
theorem halfspaceCutBody_positive_finite_volume (μ : Measure E) [IsAddHaarMeasure μ]
    {G : Set E} (hG : IsCompact G) {r τ : ℝ} {e : E}
    (hinner : Metric.closedBall (0 : E) r ⊆ G) (hτ : 0 < τ) (hτr : τ ≤ r) (he : ‖e‖ = 1) :
    0 < μ (halfspaceCutBody G e τ) ∧ μ (halfspaceCutBody G e τ) < ⊤ := by
  refine ⟨(measure_closedBall_pos μ 0 hτ).trans_le
    (measure_mono (halfspaceCutBody_contains_ball hinner hτr he)), ?_⟩
  exact (halfspaceCutBody_compact hG e τ).measure_lt_top

end
end Nonsmooth
