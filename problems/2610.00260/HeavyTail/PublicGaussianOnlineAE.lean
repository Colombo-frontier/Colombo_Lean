import HeavyTail.PublicGaussianOnline
import HeavyTail.ChangingHistoryAE

/-! The conditional online theorem with moment assumptions only almost
everywhere under the actual law of the preceding history. The observable
learner is unchanged. Exceptional-history kernels are modified only for
the proof, and equality of all execution laws and regret sums is derived. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical InnerProductSpace

namespace HeavyTail.GaussianEntropy
open GaussianEstimates AdaptiveKernel
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]

theorem conditional_mixed_moment_online_rate_ae {Seed : Type u} [MeasurableSpace Seed] {n : ℕ}
    (κ : (t : ℕ) → Kernel (History Seed E t) E) [∀ t, IsMarkovKernel (κ t)]
    (P : Measure Seed) [IsProbabilityMeasure P]
    (b : (t : ℕ) → History Seed E t → E) {p s V M R α : ℝ}
    (hbm : ∀ t, Measurable (b t))
    (hbb : ∀ t, ∀ᵐ h ∂changingHistoryLaw P κ t, ‖b t h‖ ≤ M)
    (h2 : ∀ t, ∀ᵐ h ∂changingHistoryLaw P κ t,
      Integrable (fun r => ‖r - b t h‖ ^ 2) (κ t h))
    (hzero : ∀ t, ∀ᵐ h ∂changingHistoryLaw P κ t, (∫ r, r - b t h ∂κ t h) = 0)
    (hsecond : ∀ t, ∀ᵐ h ∂changingHistoryLaw P κ t,
      (∫ r, ‖r - b t h‖ ^ 2 ∂κ t h) ≤ V)
    (hweak : ∀ t, ∀ᵐ h ∂changingHistoryLaw P κ t,
      ∀ v, ‖v‖ = 1 → (∫ r, |⟪v, r - b t h⟫_ℝ| ^ p ∂κ t h) ≤ s ^ p)
    (hp : 1 < p) (hp2 : p ≤ 2) (hM : 0 < M) (hV : 0 ≤ V) (hs : 0 < s)
    (c : E) (hR : 0 < R) (hα : 0 < α) (hα1 : α < 1 / 10) (hn : 0 < n)
    (u : E) (hu : ‖u - c‖ ≤ R) :
    let N := publicOnlineNet c hR hn
    (changingHistoryLaw P κ n).real {h |
      (96 + 16 * mixedConstant p) * R * ((M + Real.sqrt V) / Real.sqrt n +
        M * confidenceLog α / n + s * (confidenceLog α / n) ^ (1 - 1 / p)) <
      historySum (predictableGaussianRegret N.centers
        (tunedGaussianWeights c (p := p) hM hV hs hR hα hα1 hn N.centers N.centerIndex) b u) n h / n} ≤ α := by
  have hgood (t : ℕ) : ∀ᵐ h ∂changingHistoryLaw P κ t,
      ‖b t h‖ ≤ M ∧ Integrable (fun r => ‖r - b t h‖ ^ 2) (κ t h) ∧
      (∫ r, r - b t h ∂κ t h) = 0 ∧
      (∫ r, ‖r - b t h‖ ^ 2 ∂κ t h) ≤ V ∧
      ∀ v, ‖v‖ = 1 → (∫ r, |⟪v, r - b t h⟫_ℝ| ^ p ∂κ t h) ≤ s ^ p := by
    filter_upwards [hbb t, h2 t, hzero t, hsecond t, hweak t] with h hb hi hz hsq hw
    exact ⟨hb, hi, hz, hsq, hw⟩
  choose S hSm hSae hS using fun t ↦ exists_measurable_full_set (hgood t)
  let κ' : (t : ℕ) → Kernel (History Seed E t) E :=
    fun t ↦ Kernel.piecewise (hSm t) (κ t) (Kernel.const _ (Measure.dirac (0 : E)))
  let b' : (t : ℕ) → History Seed E t → E := fun t ↦ (S t).piecewise (b t) (fun _ ↦ 0)
  letI : ∀ t, IsMarkovKernel (κ' t) := fun t ↦ by dsimp only [κ']; infer_instance
  have hbm' (t : ℕ) : Measurable (b' t) := (hbm t).piecewise (hSm t) measurable_const
  have hκeq (t : ℕ) : κ t =ᵐ[changingHistoryLaw P κ t] κ' t := by
    filter_upwards [hSae t] with h hh
    simp only [κ', Kernel.piecewise_apply, if_pos hh]
  have hbeq (t : ℕ) : b t =ᵐ[changingHistoryLaw P κ t] b' t := by
    filter_upwards [hSae t] with h hh
    simp only [b', Set.piecewise, if_pos hh]
  have hprop (t : ℕ) (h : History Seed E t) :
      ‖b' t h‖ ≤ M ∧ Integrable (fun r => ‖r - b' t h‖ ^ 2) (κ' t h) ∧
      (∫ r, r - b' t h ∂κ' t h) = 0 ∧
      (∫ r, ‖r - b' t h‖ ^ 2 ∂κ' t h) ≤ V ∧
      ∀ v, ‖v‖ = 1 → (∫ r, |⟪v, r - b' t h⟫_ℝ| ^ p ∂κ' t h) ≤ s ^ p := by
    by_cases hh : h ∈ S t
    · simpa only [κ', Kernel.piecewise_apply, b', Set.piecewise, if_pos hh] using hS t h hh
    · simp only [κ', Kernel.piecewise_apply, b', Set.piecewise, if_neg hh, Kernel.const_apply]
      refine ⟨by simpa using hM.le, integrable_dirac, ?_, ?_, ?_⟩
      · simp
      · simpa using hV
      · intro v hv
        simpa [Real.zero_rpow (show p ≠ 0 by linarith)] using Real.rpow_nonneg hs.le p
  have hlaw := changingHistoryLaw_congr_ae P κ κ' hκeq n
  have hrate := conditional_mixed_moment_online_rate κ' P b' hbm'
    (fun t h ↦ (hprop t h).1) (fun t h ↦ (hprop t h).2.1)
    (fun t h ↦ (hprop t h).2.2.1) (fun t h ↦ (hprop t h).2.2.2.1)
    (fun t h ↦ (hprop t h).2.2.2.2) hp hp2 hM hV hs c hR hα hα1 hn u hu
  rw [← hlaw] at hrate
  let N := publicOnlineNet c hR hn
  let weights : (t : ℕ) → History Seed E t → SimplexPoint N.Index :=
    tunedGaussianWeights c (p := p) hM hV hs hR hα hα1 hn N.centers N.centerIndex
  have hw (t : ℕ) : Measurable (weights t) := by
    dsimp only [weights, tunedGaussianWeights]
    exact onlineHistoryWeights_measurable _ _ _ _ _ _ _ t
  have hreg (b₀ : (t : ℕ) → History Seed E t → E) (hb₀ : ∀ t, Measurable (b₀ t))
      (t : ℕ) : Measurable (predictableGaussianRegret N.centers weights b₀ u t) := by
    have hm : Measurable (fun h : History Seed E t ↦ finiteMixtureMean N.centers (weights t h).val) :=
      (finiteMixtureMean N.centers).continuous.measurable.comp (measurable_subtype_coe.comp (hw t))
    exact ((hb₀ t).comp measurable_fst).inner ((hm.comp measurable_fst).sub_const u)
  have hsum := changingHistorySum_congr_ae P κ
    (predictableGaussianRegret N.centers weights b u)
    (predictableGaussianRegret N.centers weights b' u) (hreg b hbm) (hreg b' hbm')
    (fun t ↦ (hbeq t).mono fun h hh r ↦ by simp only [predictableGaussianRegret, hh]) n
  have hevent := hsum.mono fun h hh ↦ show
      ((96 + 16 * mixedConstant p) * R * ((M + Real.sqrt V) / Real.sqrt n +
        M * confidenceLog α / n + s * (confidenceLog α / n) ^ (1 - 1 / p)) <
        historySum (predictableGaussianRegret N.centers weights b u) n h / n) ↔
      ((96 + 16 * mixedConstant p) * R * ((M + Real.sqrt V) / Real.sqrt n +
        M * confidenceLog α / n + s * (confidenceLog α / n) ^ (1 - 1 / p)) <
        historySum (predictableGaussianRegret N.centers weights b' u) n h / n) from by rw [hh]
  exact (measureReal_congr (hevent.mono fun _ hh ↦ propext hh)).le.trans hrate

end HeavyTail.GaussianEntropy
