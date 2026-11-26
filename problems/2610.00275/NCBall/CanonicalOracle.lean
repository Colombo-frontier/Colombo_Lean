import NCBall.CountablePolicy
import NCBall.HandleSampleLaw

/-! # The Gaussian-latent oracle is exactly evaluation of the verified samples -/

noncomputable section
open MeasureTheory Set Metric
open scoped ENNReal
namespace NCBall

abbrev SampleNoise (n M : ℕ) := Fin M → Fin n → ℝ

def fixedSampleValue {n M : ℕ} (ρ γ lam σ : ℝ) (u : HiddenTable n M)
    (z : SampleNoise n M) (x : Space n) : ℝ :=
  let U := fixedDirections (Real.sqrt (n : ℝ))⁻¹ u
  chainValue M ρ γ lam (roomCenter ρ U) (fun j => U j + σ • roomNoise z j) x

theorem fixedDirections_measurable {n M : ℕ} (scale : ℝ) (j : ℕ) :
    Measurable (fun u : HiddenTable n M => fixedDirections scale u j) :=
  finiteRoomExtension_measurable _ ((transverseEmbed n).continuous.measurable.comp
    (measurable_id.const_smul scale)) j

theorem fixedSampleValue_measurable {n M : ℕ} (ρ γ lam σ : ℝ) :
    Measurable (fun w : HiddenTable n M × (SampleNoise n M × Space n) =>
      fixedSampleValue ρ γ lam σ w.1 w.2.1 w.2.2) := by
  have hU (j : ℕ) : Measurable (fun w : HiddenTable n M × (SampleNoise n M × Space n) =>
      fixedDirections (Real.sqrt (n : ℝ))⁻¹ w.1 j) :=
    (fixedDirections_measurable _ j).comp measurable_fst
  have hc (j : ℕ) := roomCenter_measurable_data ρ _ hU j
  have hv (j : ℕ) : Measurable (fun w : HiddenTable n M × (SampleNoise n M × Space n) =>
      fixedDirections (Real.sqrt (n : ℝ))⁻¹ w.1 j + σ • roomNoise w.2.1 j) :=
    (hU j).add (((roomNoise_continuous n M j).measurable.comp
      (measurable_fst.comp measurable_snd)).const_smul σ)
  have hm := shadowValue_measurable_data M ρ γ lam
    (fun _ : HiddenTable n M × (SampleNoise n M × Space n) => M)
    _ _ _ measurable_const hc hv (measurable_snd.comp measurable_snd)
  simpa only [shadowValue_all_unlocked M M le_rfl] using hm

def fixedTerminalTarget {n M : ℕ} (ρ : ℝ) : Set (HiddenTable n M × Space n) :=
  {ux | ux.2 ∈ closedBall (roomCenter ρ (fixedDirections (Real.sqrt (n : ℝ))⁻¹ ux.1) M) ρ}

theorem fixedTerminalTarget_measurable {n M : ℕ} (ρ : ℝ) :
    MeasurableSet (fixedTerminalTarget (n := n) (M := M) ρ) := by
  have hc := (roomCenter_measurable_data ρ _
    (fixedDirections_measurable (M := M) (Real.sqrt (n : ℝ))⁻¹) M).comp
    (measurable_fst : Measurable (Prod.fst : HiddenTable n M × Space n → _))
  exact measurableSet_le (measurable_snd.dist hc) measurable_const

theorem real_reply_eq_fixedSampleValue {S : Type*} [MeasurableSpace S] {n K M : ℕ}
    (p : RoomQueryPolicy S n K) (ρ γ lam σ : ℝ)
    (u : HiddenTable n M) (z : SampleTable n K M) (t : ℕ) (h : LinearHistory S t) :
    fullRealReply p ρ γ lam σ (Real.sqrt (n : ℝ))⁻¹ t h
      ((splitRoomEquiv n K M).symm (u, z)) =
      fixedSampleValue ρ γ lam σ u (fixedSampleCoordinates (p.handle t h) z) (p.point t h) := by
  unfold fullRealReply realRoomReply fullRoomCenters
  rw [combined_latentDirections, combined_latentSamples]
  rfl

theorem real_transcript_eq_sampleTranscript {S : Type*} [MeasurableSpace S] {n K M : ℕ}
    (p : RoomQueryPolicy S n K) (ρ γ lam σ : ℝ)
    (u : HiddenTable n M) (rz : S × SampleTable n K M) (N : ℕ) :
    oracleTranscript (fullRealReply p ρ γ lam σ (Real.sqrt (n : ℝ))⁻¹) N
      (experimentFromSplit (u, rz)) =
      sampleTranscript p.point p.handle (fixedSampleValue ρ γ lam σ) N
        (u, (rz.1, fun h => fixedSampleCoordinates h rz.2)) := by
  induction N with
  | zero => rfl
  | succ N ih =>
    rw [sampleTranscript_succ]
    simp only [oracleTranscript, experimentFromSplit] at *
    rw [real_reply_eq_fixedSampleValue, ih]

theorem finite_sample_terminal_quarter {S : Type*} [MeasurableSpace S]
    {n K M q₀ N : ℕ} (ν : Measure S) [IsProbabilityMeasure ν]
    (p : RoomQueryPolicy S n K) (hq : 0 < q₀) (hN : N < M * q₀) (hn : 0 < n)
    {ρ σ : ℝ} (hρ : 0 < ρ) (hσ : 0 < σ) (γ lam : ℝ)
    (hqcap : (q₀ : ℝ) ≤ n * σ ^ 2 / 16)
    (hlog : 40 * Real.log (2 + (M * q₀ : ℕ)) ≤ n)
    (out : LinearHistory S N → Space n) (hout : Measurable out) :
    ((hiddenTableLaw n M).prod (ν.prod (Measure.pi (fun _ : Fin K => gaussianRooms n M))))
      {w | (w.1, out (sampleTranscript p.point p.handle (fixedSampleValue ρ γ lam σ) N w))
        ∈ fixedTerminalTarget ρ} ≤ 1 / 4 := by
  let B : Set (HiddenTable n M × (S × (Fin K → SampleNoise n M))) :=
    {w | (w.1, out (sampleTranscript p.point p.handle (fixedSampleValue ρ γ lam σ) N w))
      ∈ fixedTerminalTarget ρ}
  have hB : MeasurableSet B :=
    (measurable_fst.prodMk (hout.comp (sampleTranscript_measurable _ _ _
      p.measurable_point p.measurable_handle (fixedSampleValue_measurable ρ γ lam σ) N)))
      (fixedTerminalTarget_measurable ρ)
  let a : HiddenTable n M × (S × SampleTable n K M) →
      HiddenTable n M × (S × (Fin K → SampleNoise n M)) :=
    fun w => (w.1, (w.2.1, fun h => fixedSampleCoordinates h w.2.2))
  have ha : MeasurePreserving a
      ((hiddenTableLaw n M).prod (ν.prod (sampleTableLaw n K M)))
      ((hiddenTableLaw n M).prod (ν.prod (Measure.pi (fun _ : Fin K => gaussianRooms n M)))) :=
    (MeasurePreserving.id _).prod ((MeasurePreserving.id ν).prod (fixed_sample_table_law n K M))
  let A := fullRealTerminalEvent (M := M) p ρ γ lam σ (Real.sqrt (n : ℝ))⁻¹ N out
  have hA : MeasurableSet A := fullRealTerminalEvent_measurable p ρ γ lam σ _ N out hout
  have hset : a ⁻¹' B = experimentFromSplit ⁻¹' A := by
    ext w
    change out (sampleTranscript p.point p.handle (fixedSampleValue ρ γ lam σ) N (a w)) ∈
      closedBall (roomCenter ρ (fixedDirections (Real.sqrt (n : ℝ))⁻¹ w.1) M) ρ ↔
      out (oracleTranscript (fullRealReply p ρ γ lam σ (Real.sqrt (n : ℝ))⁻¹) N
        (experimentFromSplit w)) ∈
        closedBall (fullRoomCenters ρ (Real.sqrt (n : ℝ))⁻¹ (experimentFromSplit w).2 M) ρ
    rw [real_transcript_eq_sampleTranscript]
    simp only [fullRoomCenters, experimentFromSplit, combined_latentDirections]
    rfl
  have he := experimentFromSplit_law ν n K M
  change ((hiddenTableLaw n M).prod (ν.prod (Measure.pi (fun _ : Fin K => gaussianRooms n M)))) B ≤ _
  rw [← ha.map_eq, Measure.map_apply ha.measurable hB, hset,
    ← Measure.map_apply he.measurable hA, he.map_eq]
  exact full_chain_terminal_quarter ν p hq hN hn hρ hσ γ lam hqcap hlog out hout

end NCBall
