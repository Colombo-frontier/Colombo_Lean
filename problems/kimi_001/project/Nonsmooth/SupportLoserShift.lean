import Nonsmooth.HalfspacePosteriorShift
import Nonsmooth.GaussianSelectionRank

open MeasureTheory ProbabilityTheory Set Filter
open scoped InnerProductSpace
set_option autoImplicit false
namespace Nonsmooth
noncomputable section
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]

theorem supportSelection_loser_halfspace_kernel {k : ℕ}
    (μ : Fin k → Measure E) [∀ i, IsProbabilityMeasure (μ i)] (u : E)
    (hzero : ∀ i y, μ i {z : E | ⟪z, u⟫_ℝ = y} = 0)
    (w i : Fin k) (hni : i ≠ w) (y : ℝ) :
    supportSelectionRowKernel μ u i (w, y) = halfspacePosteriorKernel (μ i) u y := by
  classical
  have hs := supportLoserRegion_ae_halfspace (μ i) (hzero i) w i y
  rw [supportSelectionRowKernel, Kernel.piecewise_apply]
  simp only [mem_preimage, mem_singleton_iff, Ne.symm hni, if_false]
  change (if μ i (Prod.mk (w, y) ⁻¹' supportLoserRegion u i) = 0
      then μ i else (μ i)[|Prod.mk (w, y) ⁻¹' supportLoserRegion u i]) =
    (if μ i {z : E | ⟪z, u⟫_ℝ ≤ y} = 0
      then μ i else (μ i)[|{z : E | ⟪z, u⟫_ℝ ≤ y}])
  simp only [measure_congr hs, ProbabilityTheory.cond, Measure.restrict_congr_set hs]

def supportPosteriorShift {k : ℕ} [Nonempty (Fin k)]
    (μ : Fin k → Measure E) [∀ i, IsProbabilityMeasure (μ i)] (u : E)
    (i : Fin k) (h : Fin k × ℝ) : E :=
  ∫ a : Fin k → E, (a i - ∫ z : E, z ∂μ i)
    ∂condDistrib id (supportSingleObservation u) (Measure.pi μ) h

theorem supportPosteriorShift_measurable {k : ℕ} [Nonempty (Fin k)]
    (μ : Fin k → Measure E) [∀ i, IsProbabilityMeasure (μ i)] (u : E) (i : Fin k) :
    Measurable (supportPosteriorShift μ u i) := by
  have hf : StronglyMeasurable (fun a : Fin k → E => a i - ∫ z : E, z ∂μ i) :=
    (measurable_pi_apply i).stronglyMeasurable.sub stronglyMeasurable_const
  exact hf.integral_kernel.measurable

theorem supportPosteriorShift_loser_ae {n : ℕ}
    (μ : Fin (n + 1) → Measure E) [∀ i, IsProbabilityMeasure (μ i)] (u : E)
    (hzero : ∀ i y, μ i {z : E | ⟪z, u⟫_ℝ = y} = 0) :
    ∀ᵐ h ∂(Measure.pi μ).map (supportSingleObservation u), ∀ i, i ≠ h.1 →
      supportPosteriorShift μ u i h = halfspacePosteriorShift (μ i) u h.2 := by
  filter_upwards [supportSelectionKernel_ae_eq_condDistrib μ u] with h hh
  intro i hni
  unfold supportPosteriorShift
  rw [← hh]
  have he := integral_map_of_stronglyMeasurable (μ := supportSelectionKernel μ u h)
    (measurable_pi_apply i)
    (stronglyMeasurable_id.sub (stronglyMeasurable_const (b := ∫ z : E, z ∂μ i)))
  rw [supportSelectionKernel_coordinate, supportSelection_loser_halfspace_kernel μ u hzero h.1 i hni h.2] at he
  exact he.symm

def supportLoserShiftEnergy {k : ℕ} [Nonempty (Fin k)]
    (μ : Fin k → Measure E) [∀ i, IsProbabilityMeasure (μ i)] (u : E) (h : Fin k × ℝ) : ℝ :=
  ∑ i, if i = h.1 then 0 else ‖supportPosteriorShift μ u i h‖ ^ 2

theorem supportLoserShiftEnergy_measurable {k : ℕ} [Nonempty (Fin k)]
    (μ : Fin k → Measure E) [∀ i, IsProbabilityMeasure (μ i)] (u : E) :
    Measurable (supportLoserShiftEnergy μ u) := by
  have hs (i : Fin k) := supportPosteriorShift_measurable μ u i
  have hm (i : Fin k) : Measurable (fun h : Fin k × ℝ =>
      if i = h.1 then 0 else ‖supportPosteriorShift μ u i h‖ ^ 2) := by
    have hiSet : MeasurableSet {h : Fin k × ℝ | i = h.1} := by
      have heq : {h : Fin k × ℝ | i = h.1} = Prod.fst ⁻¹' {i} := by
        ext h
        simp only [mem_setOf_eq, mem_preimage, mem_singleton_iff, eq_comm]
      rw [heq]
      exact measurable_fst (measurableSet_singleton i)
    exact Measurable.ite hiSet measurable_const ((hs i).norm.pow_const 2)
  unfold supportLoserShiftEnergy
  fun_prop

/-- Actual posterior mean shifts of every unselected row have total expected
squared norm at most 2c under the uniform centered MGF hypothesis. -/
theorem support_loser_posterior_shift_bound {n : ℕ}
    (μ : Fin (n + 1) → Measure E) [∀ i, IsProbabilityMeasure (μ i)] (u : E)
    (hzero : ∀ i y, μ i {z : E | ⟪z, u⟫_ℝ = y} = 0)
    (hi : ∀ i, Integrable (fun z : E => z) (μ i)) {c : ℝ} (hc : 0 < c)
    (he : ∀ i (v : E), Integrable (fun z => Real.exp ⟪v, z - ∫ a : E, a ∂μ i⟫_ℝ) (μ i))
    (hb : ∀ i (v : E), (∫ z, Real.exp ⟪v, z - ∫ a : E, a ∂μ i⟫_ℝ ∂μ i) ≤ Real.exp (c * ‖v‖ ^ 2 / 2)) :
    Integrable (supportLoserShiftEnergy μ u) ((Measure.pi μ).map (supportSingleObservation u)) ∧
      (∫ h, supportLoserShiftEnergy μ u h ∂(Measure.pi μ).map (supportSingleObservation u)) ≤ 2 * c := by
  let ρ := (Measure.pi μ).map (supportSingleObservation u)
  let F : ℝ → ℝ := fun y => ∑ i, ‖halfspacePosteriorShift (μ i) u y‖ ^ 2
  have hFm : Measurable F := by
    have hm (i : Fin (n + 1)) := halfspacePosteriorShift_measurable (μ i) u
    dsimp only [F]
    fun_prop
  have hmap : ρ.map Prod.snd = supportResponseLaw μ u := by
    rw [Measure.map_map measurable_snd (supportSingleObservation_measurable u)]
    rfl
  have hcost := maximum_total_halfspace_shift μ u hzero hi hc he hb
  change Integrable F (supportResponseLaw μ u) ∧ (∫ y, F y ∂supportResponseLaw μ u) ≤ 2 * c at hcost
  rw [← hmap] at hcost
  have hright : Integrable (fun h : Fin (n + 1) × ℝ => F h.2) ρ :=
    (integrable_map_measure hFm.aestronglyMeasurable measurable_snd.aemeasurable).mp hcost.1
  have hbound : supportLoserShiftEnergy μ u ≤ᵐ[ρ] (fun h => F h.2) := by
    filter_upwards [supportPosteriorShift_loser_ae μ u hzero] with h hh
    apply Finset.sum_le_sum
    intro i _
    by_cases hni : i = h.1
    · simp only [hni, if_pos rfl]
      exact sq_nonneg _
    · simp only [if_neg hni, hh i hni]
      exact le_rfl
  have hnonneg (h : Fin (n + 1) × ℝ) : 0 ≤ supportLoserShiftEnergy μ u h := by
    apply Finset.sum_nonneg
    intro i _
    split_ifs <;> positivity
  have hleft : Integrable (supportLoserShiftEnergy μ u) ρ := by
    apply hright.mono' (supportLoserShiftEnergy_measurable μ u).aestronglyMeasurable
    filter_upwards [hbound] with h hh
    simpa only [Real.norm_of_nonneg (hnonneg h)] using hh
  refine ⟨hleft, (integral_mono_ae hleft hright hbound).trans ?_⟩
  simpa only [integral_map_of_stronglyMeasurable measurable_snd hFm.stronglyMeasurable] using hcost.2

end
end Nonsmooth
