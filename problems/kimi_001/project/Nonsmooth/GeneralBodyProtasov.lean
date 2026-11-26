import Nonsmooth.GeneralEvaluatedLocalization
import Nonsmooth.EvaluatedLocalizationLegality
import Nonsmooth.BodyFallbackMap
import Nonsmooth.BodyTreeInitialSubset
import Nonsmooth.UniformBodyLocalCertificate
import Nonsmooth.CountableBodyTree
import Nonsmooth.EvaluatedLocalizationBudget

open MeasureTheory MeasureTheory.Measure Set
open scoped ENNReal
set_option autoImplicit false
namespace Nonsmooth
noncomputable section
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

/-- The full known-convex-body value-query theorem in dimensions at least two. -/
theorem general_body_protasov (G : Set E) (hG : Convex ℝ G) (hGc : IsCompact G)
    (hGi : (interior G).Nonempty) (hd : 2 ≤ Module.finrank ℝ E)
    (η : ℝ) (hη : 0 < η) (hηhalf : η < 1 / 2) :
    ∃ (T : ℕ) (S : Type) (mS : MeasurableSpace S),
      letI := mS
      StandardBorelSpace S ∧ ∃ p : Policy Unit S G, p.IsMeasurable ∧
      (T : ℝ) ≤ 10488 * (Module.finrank ℝ E : ℝ) ^ 2 *
        Real.log ((Module.finrank ℝ E : ℝ) + 1) * Real.log (1 / η) ∧
      ∀ f : E → ℝ, ContinuousOn f G → ConvexOn ℝ G f →
        f (p.result (fun z => f z.val) () T).val - bodyMinimum G f ≤
          η * (bodyMaximum G f - bodyMinimum G f) := by
  classical
  have hne : G.Nonempty := hGi.mono interior_subset
  obtain ⟨xmax, _hxmax, hmax⟩ := hGc.exists_isMaxOn hne continuous_norm.continuousOn
  let R := ‖xmax‖ + 1
  have hGR : G ⊆ Metric.closedBall (0 : E) R := by
    intro z hz
    have h := hmax hz
    change ‖z‖ ≤ ‖xmax‖ at h
    simpa only [Metric.mem_closedBall, dist_zero_right] using h.trans (by dsimp [R]; linarith)
  let B0 : LocalizationBody E R := ⟨G, hG, hGc, hGi, hGR⟩
  let x0 : G := ⟨hne.choose, hne.choose_spec⟩
  choose p step hp hsub hcert using (fun B : LocalizationBody E R => uniform_body_local_certificate B hd)
  let body := fun h : LocalizationHistory => localizationBodyTree step B0 h.entries
  let family := fun h : LocalizationHistory => p (body h)
  let K := fun h : LocalizationHistory => (body h).carrier
  have hKG : ∀ h, K h ⊆ G := fun h => localizationBodyTree_subset_initial step hsub B0 h.entries
  let c0 : LocalizationHistory := ⟨[]⟩
  let T := localizationLocalBudget (Module.finrank ℝ E)
  let N := volumeLocalizationRounds (Module.finrank ℝ E) (1 / 8) η
  let raw := evaluatedLocalizationPolicy family T localizationHistoryNext c0 (localizationBodyPoint B0)
  have hrawm : raw.IsMeasurable := evaluatedLocalizationPolicy_measurable family (fun h => hp (body h))
    T localizationHistoryNext localizationHistoryNext_measurable c0 (localizationBodyPoint B0)
  have hraw : ∀ F : E → ℝ, ContinuousOn F G → ConvexOn ℝ G F →
      F (raw.result (fun z => F z.val) () (N * (T + 1))).val - bodyMinimum G F ≤
        η * (bodyMaximum G F - bodyMinimum G F) := by
    intro F hcont hf
    apply evaluatedLocalizationPolicy_body_relative_error hG hGc hGi hGR family T
      localizationHistoryNext c0 (localizationBodyPoint B0) K rfl (1 / 8) η
      (by norm_num) (by norm_num) hη (by linarith) F hcont hf
    · intro h z hz hbetter
      exact (hcert (body h) F (hf.subset (hKG h) (body h).convex)).1 z hz hbetter
    · intro h
      exact (hcert (body h) F (hf.subset (hKG h) (body h).convex)).2
  let q : Feasible E R → G := fun z => bodyFallbackMap G x0 z.val
  have hqm : Measurable q := (bodyFallbackMap_measurable hGc.measurableSet x0).comp measurable_subtype_coe
  let S := (LocalizationHistory × BestValueRecord (Feasible E R)) × ((CircularHistory × CyclicPeakState) × ℝ)
  letI : StandardBorelSpace (Feasible E R) :=
    (isClosed_le continuous_norm continuous_const).measurableSet.standardBorel
  letI : StandardBorelSpace S := by dsimp only [S]; infer_instance
  let alg : Policy Unit S G := raw.simulate q (fun _ y => y)
  refine ⟨N * (T + 1), S, inferInstance, inferInstance, alg,
    simulation_measurable hrawm hqm measurable_snd, ?_, ?_⟩
  · have h := total_evaluated_localization_query_bound (Module.finrank ℝ E) hd
      (by norm_num : (0 : ℝ) ≤ 435) (by norm_num : (0 : ℝ) < 1 / 8)
      (by norm_num : (1 / 8 : ℝ) ≤ 1) hη hηhalf.le T (localizationLocalBudget_bound _ hd)
    convert h using 1
    norm_num
  · intro f hcont hf
    let F : E → ℝ := fun z => f (bodyFallbackMap G x0 z).val
    have hEq : EqOn F f G := fun z hz => by dsimp only [F]; rw [bodyFallbackMap_of_mem x0 hz]
    have h := hraw F (hcont.congr hEq) (hf.congr hEq.symm)
    have hext := body_extrema_fallback G x0 f
    change bodyMinimum G F = bodyMinimum G f ∧ bodyMaximum G F = bodyMaximum G f at hext
    rw [hext.1, hext.2] at h
    have hres := simulation_output_exact raw q (fun _ y => y) (fun z => f z.val)
      (fun z => F z.val) (fun _ => rfl) () (N * (T + 1))
    change alg.result (fun z => f z.val) () (N * (T + 1)) = _ at hres
    rw [hres]
    exact h

end
end Nonsmooth
