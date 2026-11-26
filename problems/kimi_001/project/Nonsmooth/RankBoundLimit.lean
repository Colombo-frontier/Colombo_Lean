import Nonsmooth.AtomlessCDFEntropy

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
set_option autoImplicit false
namespace Nonsmooth
noncomputable section
variable {E : Type} [NormedAddCommGroup E]

theorem norm_rank_bound_of_tendsto (m : ℕ → E) (p : ℕ → ℝ) (M : E) (q K : ℝ)
    (hq0 : 0 < q) (hq1 : q < 1) (hm : Tendsto m atTop (𝓝 M))
    (hp : Tendsto p atTop (𝓝 q))
    (hb : ∀ n, ‖m n‖ ^ 2 ≤ K * (1 + rankQuantileLog (p n))) :
    ‖M‖ ^ 2 ≤ K * (1 + rankQuantileLog q) := by
  have hmin : 0 < min q (1 - q) := lt_min hq0 (by linarith)
  have htail : Tendsto (fun n => min (p n) (1 - p n)) atTop (𝓝 (min q (1 - q))) :=
    hp.min (tendsto_const_nhds.sub hp)
  have hinv : Tendsto (fun n => 1 / min (p n) (1 - p n)) atTop (𝓝 (1 / min q (1 - q))) :=
    tendsto_const_nhds.div htail hmin.ne'
  have hlog : Tendsto (fun n => rankQuantileLog (p n)) atTop (𝓝 (rankQuantileLog q)) :=
    hinv.log (one_div_ne_zero hmin.ne')
  have hr : Tendsto (fun n => K * (1 + rankQuantileLog (p n))) atTop
      (𝓝 (K * (1 + rankQuantileLog q))) :=
    tendsto_const_nhds.mul (tendsto_const_nhds.add hlog)
  exact le_of_tendsto_of_tendsto (hm.norm.pow 2) hr (Eventually.of_forall hb)

/-- Rank bounds persist under posterior-mean and CDF convergence. Absolute
continuity transfers every approximating null exception to the target law. -/
theorem ae_rank_bound_of_approximation (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (Q : ℕ → Measure ℝ) [∀ n, IsProbabilityMeasure (Q n)]
    (hatom : ∀ y : ℝ, ν {y} = 0) (hAC : ∀ n, ν ≪ Q n)
    (m : ℕ → ℝ → E) (M : ℝ → E) (K : ℝ)
    (hb : ∀ n, ∀ᵐ y ∂Q n, ‖m n y‖ ^ 2 ≤ K * (1 + rankQuantileLog (cdf (Q n) y)))
    (hm : ∀ᵐ y ∂ν, Tendsto (fun n => m n y) atTop (𝓝 (M y)))
    (hcdf : ∀ᵐ y ∂ν, Tendsto (fun n => cdf (Q n) y) atTop (𝓝 (cdf ν y))) :
    ∀ᵐ y ∂ν, ‖M y‖ ^ 2 ≤ K * (1 + rankQuantileLog (cdf ν y)) := by
  have hall : ∀ᵐ y ∂ν, ∀ n, ‖m n y‖ ^ 2 ≤ K * (1 + rankQuantileLog (cdf (Q n) y)) :=
    ae_all_iff.mpr (fun n => (hAC n).ae_le (hb n))
  filter_upwards [hall, hm, hcdf, atomless_cdf_interior_ae ν hatom] with y hy hmy hcy hqy
  exact norm_rank_bound_of_tendsto _ _ _ _ K hqy.1 hqy.2 hmy hcy hy

end
end Nonsmooth
