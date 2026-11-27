import Nonsmooth.IndependentCovariance

open MeasureTheory ProbabilityTheory Filter Set
open scoped InnerProductSpace ENNReal
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace Nonsmooth
noncomputable section

theorem condDistrib_ae_support {α β Ω : Type} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace Ω] [StandardBorelSpace β] [Nonempty β]
    (μ : Measure Ω) [IsFiniteMeasure μ] (X : Ω → α) (hX : Measurable X)
    (Y : Ω → β) (hY : Measurable Y) {B : Set β} (hB : MeasurableSet B)
    (h : ∀ᵐ a ∂μ, Y a ∈ B) :
    ∀ᵐ x ∂μ.map X, ∀ᵐ b ∂condDistrib Y X μ x, b ∈ B := by
  have hpair : Measurable (fun a : Ω => (X a, Y a)) := hX.prodMk hY
  have hs : MeasurableSet {p : α × β | p.2 ∈ B} := measurable_snd hB
  have hj : ∀ᵐ p ∂μ.map (fun a => (X a, Y a)), p.2 ∈ B :=
    (ae_map_iff hpair.aemeasurable hs).mpr h
  rw [← compProd_map_condDistrib hY.aemeasurable] at hj
  exact Measure.ae_ae_of_ae_compProd hj

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] {k : ℕ}

theorem bounded_row_directional_variance (ν : Measure (Fin k → E)) [IsProbabilityMeasure ν]
    (i : Fin k) (b : ℝ) (hb : ∀ᵐ a ∂ν, ‖a i‖ ≤ b) (u : E) :
    variance (fun a : Fin k → E => ⟪u, a i⟫_ℝ) ν ≤ (‖u‖ * b) ^ 2 := by
  have hLp : MemLp (fun a : Fin k → E => a i) 2 ν :=
    MemLp.of_bound (measurable_pi_apply i).aestronglyMeasurable b hb
  have hv : MemLp (fun a : Fin k → E => ⟪u, a i⟫_ℝ) 2 ν := hLp.const_inner u
  have hsecond : (∫ a : Fin k → E, ⟪u, a i⟫_ℝ ^ 2 ∂ν) ≤ (‖u‖ * b) ^ 2 := by
    calc
      _ ≤ ∫ _ : Fin k → E, (‖u‖ * b) ^ 2 ∂ν := by
        apply integral_mono_ae hv.integrable_sq (integrable_const _)
        filter_upwards [hb] with a ha
        have hbound := (abs_real_inner_le_norm u (a i)).trans
          (mul_le_mul_of_nonneg_left ha (norm_nonneg u))
        nlinarith [abs_nonneg ⟪u, a i⟫_ℝ, sq_abs ⟪u, a i⟫_ℝ]
      _ = _ := by simp
  rw [variance_eq_sub hv]
  dsimp only [Pi.pow_apply]
  exact (sub_le_self _ (sq_nonneg _)).trans hsecond

variable [Nontrivial E] [Nonempty (Fin k)] {Ω S : Type} [MeasurableSpace Ω] [MeasurableSpace S]

theorem gaussianSupportPosterior_row_norm_le (p : Policy Ω S E) (hp : p.IsMeasurable) (ω : Ω) (n : ℕ) :
    let Q := Measure.pi (fun _ : Fin k => gaussianAmbientRowLaw E)
    ∀ᵐ h ∂Q.map (fun a => supportAugmentedTranscript p a ω n),
      ∀ i, ∀ᵐ a ∂supportPosteriorKernel Q p ω n h, ‖a i‖ ≤ 2 := by
  dsimp only
  let Q := Measure.pi (fun _ : Fin k => gaussianAmbientRowLaw E)
  have hT : Measurable (fun a : Fin k → E => supportAugmentedTranscript p a ω n) :=
    (supportAugmentedTranscript_measurable p hp n).comp
      (measurable_id.prodMk (measurable_const (a := ω)))
  apply ae_all_iff.mpr
  intro i
  have hco : ∀ᵐ a ∂Q, ‖a i‖ ≤ 2 := by
    have h := gaussianAmbientRowLaw_norm_le_two (E := E)
    rw [← (finite_product_coordinate (gaussianAmbientRowLaw E) i).map_eq] at h
    exact ae_of_ae_map (measurable_pi_apply i).aemeasurable h
  exact condDistrib_ae_support Q _ hT id measurable_id
    (measurableSet_le ((continuous_apply i).norm.measurable) measurable_const) hco

theorem gaussianSupportPosterior_rows_memLp (p : Policy Ω S E) (hp : p.IsMeasurable) (ω : Ω) (n : ℕ) :
    let Q := Measure.pi (fun _ : Fin k => gaussianAmbientRowLaw E)
    ∀ᵐ h ∂Q.map (fun a => supportAugmentedTranscript p a ω n),
      ∀ i, MemLp (fun a : Fin k → E => a i) 2 (supportPosteriorKernel Q p ω n h) := by
  dsimp only
  filter_upwards [gaussianSupportPosterior_row_norm_le (k := k) p hp ω n] with h hh i
  exact MemLp.of_bound (measurable_pi_apply i).aestronglyMeasurable 2 (hh i)

theorem gaussianSupportPosterior_centered_second (p : Policy Ω S E) (hp : p.IsMeasurable) (ω : Ω) (n : ℕ) :
    let Q := Measure.pi (fun _ : Fin k => gaussianAmbientRowLaw E)
    ∀ᵐ h ∂Q.map (fun a => supportAugmentedTranscript p a ω n), ∀ u : E,
      (∫ a : Fin k → E, ⟪u, (∑ i, a i) - ∫ b : Fin k → E, ∑ i, b i
        ∂supportPosteriorKernel Q p ω n h⟫_ℝ ^ 2 ∂supportPosteriorKernel Q p ω n h) =
      ∑ i, variance (fun a : Fin k → E => ⟪u, a i⟫_ℝ) (supportPosteriorKernel Q p ω n h) := by
  dsimp only
  filter_upwards [gaussianSupportPosterior_rows_memLp (k := k) p hp ω n,
    supportPosteriorKernel_independent (fun _ : Fin k => gaussianAmbientRowLaw E) p hp ω n] with h hm hi u
  exact independent_rows_centered_second _ hi hm u

theorem gaussianSupportPosterior_centered_second_le_coarse
    (p : Policy Ω S E) (hp : p.IsMeasurable) (ω : Ω) (n : ℕ) :
    let Q := Measure.pi (fun _ : Fin k => gaussianAmbientRowLaw E)
    ∀ᵐ h ∂Q.map (fun a => supportAugmentedTranscript p a ω n), ∀ u : E,
      (∫ a : Fin k → E, ⟪u, (∑ i, a i) - ∫ b : Fin k → E, ∑ i, b i
        ∂supportPosteriorKernel Q p ω n h⟫_ℝ ^ 2 ∂supportPosteriorKernel Q p ω n h) ≤
      4 * (k : ℝ) * ‖u‖ ^ 2 := by
  dsimp only
  filter_upwards [gaussianSupportPosterior_centered_second (k := k) p hp ω n,
    gaussianSupportPosterior_row_norm_le (k := k) p hp ω n] with h he hb u
  rw [he u]
  calc
    _ ≤ ∑ i : Fin k, (‖u‖ * 2) ^ 2 := Finset.sum_le_sum
      (fun i _ => bounded_row_directional_variance _ i 2 (hb i) u)
    _ = _ := by simp; ring

end
end Nonsmooth
