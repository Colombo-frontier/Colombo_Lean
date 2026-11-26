import NCBall.StochasticClass
import NCBall.HandleSampleLaw
import NCBall.AbsoluteParameters
import NCBall.SmoothLower

/-! # A common family certificate and the bounded-domain smooth lower bound -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace NCBall

def goodHiddenFamily (n : ℕ) (η H Δ : ℝ) : Set (HiddenTable n (calibratedDepth (4 * η) H Δ)) :=
  fixedGoodEvent (Real.sqrt (n : ℝ))⁻¹

def familyPopulation {n : ℕ} (η H Δ : ℝ)
    (u : HiddenTable n (calibratedDepth (4 * η) H Δ)) : Space n → ℝ :=
  calibratedPopulation η H Δ (fixedDirections (Real.sqrt (n : ℝ))⁻¹ u)

def familySample {n : ℕ} (η H Δ L : ℝ)
    (u : HiddenTable n (calibratedDepth (4 * η) H Δ)) :
    (Fin (calibratedDepth (4 * η) H Δ) → Fin n → ℝ) → Space n → ℝ :=
  calibratedSample η H Δ L (fixedDirections (Real.sqrt (n : ℝ))⁻¹ u)

theorem real_reply_eq_family_sample {Seed : Type*} [MeasurableSpace Seed] {n K : ℕ}
    (p : RoomQueryPolicy Seed n K) (η H Δ L : ℝ)
    (u : HiddenTable n (calibratedDepth (4 * η) H Δ))
    (z : SampleTable n K (calibratedDepth (4 * η) H Δ))
    (t : ℕ) (h : LinearHistory Seed t) :
    fullRealReply p (calibratedRho (4 * η) H) (4 * η) (calibratedLam (4 * η))
      (L / (4 * η)) (Real.sqrt (n : ℝ))⁻¹ t h
      ((splitRoomEquiv n K (calibratedDepth (4 * η) H Δ)).symm (u, z)) =
      familySample η H Δ L u (fixedSampleCoordinates (p.handle t h) z) (p.point t h) := by
  unfold fullRealReply realRoomReply fullRoomCenters
  rw [combined_latentDirections, combined_latentSamples]
  rfl

theorem family_class_of_absolute {n : ℕ} {η H Δ L : ℝ}
    (hη : 0 < η) (hH : 0 < H) (hΔ : 0 ≤ Δ) (hL : 0 < L)
    (hsmall : η ≤ lowerConstant * L)
    (hlarge : regimeConstant * η ^ 2 ≤ H * Δ)
    (hd : regimeConstant * Real.log (2 + H * Δ * L ^ 2 / η ^ 4) ≤ (n : ℝ) + 1)
    (u : HiddenTable n (calibratedDepth (4 * η) H Δ)) (hu : u ∈ goodHiddenFamily n η H Δ) :
    SmoothStochasticClass (gaussianRooms n (calibratedDepth (4 * η) H Δ))
      (familyPopulation η H Δ u) (familySample η H Δ L u)
      (sampleLipschitzModulus (4 * η) L) (calibratedRadius η H Δ) H L Δ := by
  have hdim := transverse_dimension_of_absolute (show 0 ≤ H * Δ * L ^ 2 / η ^ 4 by positivity) hd
  have hscale := accuracy_scale_of_absolute hη hsmall
  have hregime := depth_regime_of_absolute hlarge
  have hq := calibratedCharges_pos hdim.1 (by positivity : 0 < 4 * η) hscale
  have hlog := calibrated_dimension_condition hη hH hΔ hdim.2
  exact calibrated_class_verified hdim.1 hη hH hΔ hL.le hregime hscale
    (dimension_good_log hq hlog) _ (fixedDirections_clock _ u) hu

universe u

/-- The radius and family are chosen before the randomized strategy. All sample
functions are smooth on the whole ambient space, with the certified ball gap.
The strategy may query anywhere, so restricting its queries to the ball only
narrows the class of strategies covered by this lower bound. -/
theorem bounded_smooth_lower_bound {n : ℕ} {η H Δ L : ℝ}
    (hη : 0 < η) (hH : 0 < H) (hΔ : 0 ≤ Δ) (hL : 0 < L)
    (hsmall : η ≤ lowerConstant * L)
    (hlarge : regimeConstant * η ^ 2 ≤ H * Δ)
    (hd : regimeConstant * Real.log (2 + H * Δ * L ^ 2 / η ^ 4) ≤ (n : ℝ) + 1) :
    ∃ radius : ℝ, 0 < radius ∧
      (37 / 400) * (Δ / η) ≤ radius ∧ radius ≤ (37 / 200) * (Δ / η) ∧
      (∀ u ∈ goodHiddenFamily n η H Δ,
        SmoothStochasticClass (gaussianRooms n (calibratedDepth (4 * η) H Δ))
          (familyPopulation η H Δ u) (familySample η H Δ L u)
          (sampleLipschitzModulus (4 * η) L) radius H L Δ) ∧
      (∀ (K : ℕ), MeasurePreserving
        (fun z : SampleTable n K (calibratedDepth (4 * η) H Δ) => fun h => fixedSampleCoordinates h z)
        (sampleTableLaw n K (calibratedDepth (4 * η) H Δ))
        (Measure.pi (fun _ : Fin K => gaussianRooms n (calibratedDepth (4 * η) H Δ)))) ∧
      (∀ (Seed : Type u) [MeasurableSpace Seed] (ν : Measure Seed) [IsProbabilityMeasure ν]
        (K N : ℕ) (p : RoomQueryPolicy Seed n K)
        (out : LinearHistory Seed N → Space n), Measurable out →
        (∀ u ∈ goodHiddenFamily n η H Δ,
          (1 / 2 : ℝ≥0∞) ≤ (ν.prod (sampleTableLaw n K (calibratedDepth (4 * η) H Δ)))
            {rz | experimentFromSplit (u, rz) ∈ fullGradientSuccess p (calibratedRho (4 * η) H)
              η (L / (4 * η)) (Real.sqrt (n : ℝ))⁻¹ N out}) →
        lowerConstant * (((n : ℝ) + 1) * L ^ 2 * H * Δ / η ^ 4) ≤ N) := by
  have hdim := transverse_dimension_of_absolute (show 0 ≤ H * Δ * L ^ 2 / η ^ 4 by positivity) hd
  have hscale := accuracy_scale_of_absolute hη hsmall
  have hregime := depth_regime_of_absolute hlarge
  have hγ : 0 < 4 * η := by positivity
  have hρ := calibratedRho_pos hγ hH
  have hM := calibratedDepth_ge_two hγ hregime
  have hr := calibrated_radius_bounds hγ hH hΔ hregime
  refine ⟨calibratedRadius η H Δ, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold calibratedRadius
    have : (0 : ℝ) < calibratedDepth (4 * η) H Δ := by exact_mod_cast (show 0 < calibratedDepth (4 * η) H Δ by omega)
    positivity
  · convert hr.1 using 1; ring
  · convert hr.2 using 1; ring
  · exact fun u hu => family_class_of_absolute hη hH hΔ hL hsmall hlarge hd u hu
  · exact fun K => fixed_sample_table_law n K _
  · intro Seed _ ν _ K N p out hout hsuccess
    have hb := smooth_scalar_evaluation_lower_bound ν p hdim.1 hη hH hΔ hL
      hregime hscale hdim.2 out hout hsuccess
    exact (smooth_coefficient_of_absolute hη hH hΔ).trans hb

end NCBall
