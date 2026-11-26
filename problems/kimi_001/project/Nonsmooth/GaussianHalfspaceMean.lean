import Nonsmooth.RankTailEntropy
import Nonsmooth.GaussianSharpMGF

open MeasureTheory ProbabilityTheory Filter Set
open scoped InnerProductSpace ENNReal
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace Nonsmooth
noncomputable section

theorem parametricEventKernel_absolutelyContinuous {α β : Type}
    [MeasurableSpace α] [MeasurableSpace β] (μ : Measure β) [IsProbabilityMeasure μ]
    (B : Set (α × β)) (hB : MeasurableSet B) (x : α) :
    parametricEventKernel μ B hB x ≪ μ := by
  by_cases hx : μ (Prod.mk x ⁻¹' B) = 0
  · change (if μ (Prod.mk x ⁻¹' B) = 0 then μ else μ[|Prod.mk x ⁻¹' B]) ≪ μ
    rw [if_pos hx]
  · rw [parametricEventKernel_apply μ B hB x hx, ProbabilityTheory.cond]
    exact (Measure.absolutelyContinuous_of_le Measure.restrict_le_self).smul_left _

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]

def gaussianHalfspaceKernel (u : E) : Kernel ℝ E :=
  parametricEventKernel (gaussianAmbientRowLaw E) {p : ℝ × E | ⟪p.2, u⟫_ℝ ≤ p.1}
    (measurableSet_le (continuous_snd.inner continuous_const).measurable measurable_fst)

instance gaussianHalfspaceKernel_markov (u : E) : IsMarkovKernel (gaussianHalfspaceKernel u) := by
  unfold gaussianHalfspaceKernel
  infer_instance

def gaussianHalfspaceMean (u : E) (y : ℝ) : E := ∫ z, z ∂gaussianHalfspaceKernel u y

theorem gaussianHalfspaceMean_stronglyMeasurable (u : E) : StronglyMeasurable (gaussianHalfspaceMean u) :=
  stronglyMeasurable_id.integral_kernel

theorem gaussianHalfspaceMean_norm_le (u : E) (y : ℝ) : ‖gaussianHalfspaceMean u y‖ ≤ 2 := by
  have hac : gaussianHalfspaceKernel u y ≪ gaussianAmbientRowLaw E :=
    parametricEventKernel_absolutelyContinuous _ _ _ _
  have hbound : ∀ᵐ z ∂gaussianHalfspaceKernel u y, ‖z‖ ≤ 2 := hac.ae_le gaussianAmbientRowLaw_norm_le_two
  simpa only [gaussianHalfspaceMean, measureReal_def, measure_univ, ENNReal.toReal_one, mul_one] using
    norm_integral_le_of_norm_le_const hbound

theorem gaussianHalfspaceMean_memLp (u : E) (ν : Measure ℝ) [IsFiniteMeasure ν] :
    MemLp (gaussianHalfspaceMean u) 2 ν :=
  MemLp.of_bound (gaussianHalfspaceMean_stronglyMeasurable u).aestronglyMeasurable 2
    (Eventually.of_forall (gaussianHalfspaceMean_norm_le u))

theorem gaussianHalfspaceMean_eq_cond (u : E) (y : ℝ)
    (hpos : gaussianAmbientRowLaw E {z : E | ⟪z, u⟫_ℝ ≤ y} ≠ 0) :
    gaussianHalfspaceMean u y = ∫ z, z ∂(gaussianAmbientRowLaw E)[|{z : E | ⟪z, u⟫_ℝ ≤ y}] := by
  rw [gaussianHalfspaceMean, gaussianHalfspaceKernel, parametricEventKernel_apply _ _ _ _ hpos]
  rfl

theorem gaussianSelection_loser_kernel {u : E} (hu : u ≠ 0) {k : ℕ}
    (w i : Fin k) (hi : i ≠ w) (y : ℝ) :
    supportSelectionRowKernel (fun _ : Fin k => gaussianAmbientRowLaw E) u i (w, y) =
      gaussianHalfspaceKernel u y := by
  classical
  have hzero (t : ℝ) : gaussianAmbientRowLaw E {z : E | ⟪z, u⟫_ℝ = t} = 0 := by
    simpa only [real_inner_comm u] using gaussianAmbientRow_hyperplane_zero hu t
  have hs := supportLoserRegion_ae_halfspace (gaussianAmbientRowLaw E) hzero w i y
  rw [supportSelectionRowKernel, Kernel.piecewise_apply]
  simp only [mem_preimage, mem_singleton_iff, Ne.symm hi, if_false]
  change (if gaussianAmbientRowLaw E (Prod.mk (w, y) ⁻¹' supportLoserRegion u i) = 0
      then gaussianAmbientRowLaw E else (gaussianAmbientRowLaw E)[|Prod.mk (w, y) ⁻¹' supportLoserRegion u i]) =
    (if gaussianAmbientRowLaw E {z : E | ⟪z, u⟫_ℝ ≤ y} = 0
      then gaussianAmbientRowLaw E else (gaussianAmbientRowLaw E)[|{z : E | ⟪z, u⟫_ℝ ≤ y}])
  simp only [measure_congr hs, ProbabilityTheory.cond, Measure.restrict_congr_set hs]

theorem gaussianHalfspaceMean_entropy_bound (u : E) (y : ℝ)
    (hp : cdf ((gaussianAmbientRowLaw E).map (fun z : E => ⟪z, u⟫_ℝ)) y ∈ Ioo (0 : ℝ) 1) :
    ‖gaussianHalfspaceMean u y‖ ^ 2 ≤ (2 / (Module.finrank ℝ E : ℝ)) *
      ((1 - cdf ((gaussianAmbientRowLaw E).map (fun z : E => ⟪z, u⟫_ℝ)) y) /
        cdf ((gaussianAmbientRowLaw E).map (fun z : E => ⟪z, u⟫_ℝ)) y) ^ 2 *
      Real.log (1 / (1 - cdf ((gaussianAmbientRowLaw E).map (fun z : E => ⟪z, u⟫_ℝ)) y)) := by
  let A : Set E := {z : E | ⟪z, u⟫_ℝ ≤ y}
  let p := cdf ((gaussianAmbientRowLaw E).map (fun z : E => ⟪z, u⟫_ℝ)) y
  have hr : Measurable (fun z : E => ⟪z, u⟫_ℝ) := (continuous_id.inner continuous_const).measurable
  have hAm : MeasurableSet A := measurableSet_le hr measurable_const
  have hpm : (gaussianAmbientRowLaw E).real A = p := by
    dsimp only [p]
    rw [cdf_eq_real]
    simp only [measureReal_def]
    rw [Measure.map_apply hr measurableSet_Iic]
    rfl
  have hqm : (gaussianAmbientRowLaw E).real Aᶜ = 1 - p := by
    rw [measureReal_compl hAm, hpm]
    simp [measureReal_def]
  have hA : gaussianAmbientRowLaw E A ≠ 0 := by
    intro hz
    have hp0 : (gaussianAmbientRowLaw E).real A = 0 := by simp [measureReal_def, hz]
    rw [hpm] at hp0
    exact (ne_of_gt hp.1) hp0
  have hAc : gaussianAmbientRowLaw E Aᶜ ≠ 0 := by
    intro hz
    have hq0 : (gaussianAmbientRowLaw E).real Aᶜ = 0 := by simp [measureReal_def, hz]
    rw [hqm] at hq0
    exact (ne_of_gt (sub_pos.mpr hp.2)) hq0
  have hb := (gaussianAmbientRow_event_mean_two_sided hAm hA hAc).trans (min_le_right _ _)
  rw [hpm, hqm] at hb
  rw [gaussianHalfspaceMean_eq_cond u y hA]
  convert! hb using 1 <;> ring

end
end Nonsmooth
