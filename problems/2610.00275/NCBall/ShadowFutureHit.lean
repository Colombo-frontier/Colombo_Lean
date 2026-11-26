import NCBall.ShadowEstimation

/-! # A concrete future-room hit forces a forbidden hidden-vector estimate -/

noncomputable section
open MeasureTheory Set Metric
open scoped InnerProductSpace ENNReal
namespace NCBall

theorem roomCenter_update_decompose {n : ℕ} (ρ : ℝ) (U : ℕ → Space n)
    {j k : ℕ} (hjk : j < k) (u : Space n) :
    roomCenter ρ (Function.update U j u) k =
      roomCenter ρ (Function.update U j 0) k + (16 * ρ) • u := by
  have hj : j ∈ Finset.range k := Finset.mem_range.mpr hjk
  simp only [roomCenter, Finset.sum_update_of_mem hj]
  module

def roomPrediction {n : ℕ} (ρ : ℝ) (U : ℕ → Space n) (j k : ℕ) (x : Space n) : Transverse n :=
  transverseProjection n ((16 * ρ)⁻¹ • (x - roomCenter ρ (Function.update U j 0) k))

theorem spliced_room_hit_predicts {n : ℕ} {ρ : ℝ} (hρ : 0 < ρ)
    (U : ℕ → Space n) {j k : ℕ} (hjk : j < k) (u : Transverse n) (x : Space n)
    (hx : x ∈ closedBall (roomCenter ρ (Function.update U j (transverseEmbed n u)) k) ρ) :
    ‖u - roomPrediction ρ U j k x‖ ≤ 1 / 16 := by
  have hd : ‖x - (roomCenter ρ (Function.update U j 0) k + (16 * ρ) • transverseEmbed n u)‖ ≤ ρ := by
    rw [mem_closedBall, dist_eq_norm, roomCenter_update_decompose ρ U hjk] at hx
    exact hx
  have hb := next_room_hit_predicts hρ x (roomCenter ρ (Function.update U j 0) k)
    (transverseEmbed n u) hd
  have hp := (transverseProjection_norm_le
    ((16 * ρ)⁻¹ • (x - roomCenter ρ (Function.update U j 0) k) - transverseEmbed n u)).trans hb
  rw [map_sub, transverseProjection_embed] at hp
  simpa only [roomPrediction, norm_sub_rev] using hp

theorem roomPrediction_measurable {A : Type*} [MeasurableSpace A] {n : ℕ}
    (ρ : ℝ) (U : A → ℕ → Space n) (hU : ∀ k, Measurable (fun a => U a k))
    (j k : ℕ) (x : A → Space n) (hx : Measurable x) :
    Measurable (fun a => roomPrediction ρ (U a) j k (x a)) := by
  have hu (i : ℕ) : Measurable (fun a => Function.update (U a) j 0 i) := by
    by_cases hi : i = j
    · subst i
      simpa only [Function.update_self] using (measurable_const : Measurable (fun _ : A => (0 : Space n)))
    · simpa only [Function.update_of_ne hi] using hU i
  have hc := roomCenter_measurable_data ρ (fun a => Function.update (U a) j 0) hu k
  exact (transverseProjection n).measurable.comp ((hx.sub hc).const_smul ((16 * ρ)⁻¹))

theorem spliced_shadow_future_hit_bound {S : Type*} [MeasurableSpace S] {n H : ℕ}
    (ν : Measure S) [IsProbabilityMeasure ν]
    (d : RoomBackground S n H) (p : RoomQueryPolicy S n H)
    (hdclock : ∀ s i, d.directions s i 0 = 0)
    {M j k q₀ : ℕ} (hj : j < M) (hjk : j < k) (hq : 0 < q₀) (hn : 0 < n)
    {ρ σ : ℝ} (hρ : 0 < ρ) (hσ : 0 < σ) (γ lam : ℝ)
    (hqcap : (q₀ : ℝ) ≤ n * σ ^ 2 / 16) (t : ℕ)
    (x : LinearHistory S t → Space n) (hx : Measurable x) :
    (ν.prod (euclideanGaussianLaw (HandleLatent (Transverse n) H)))
      {w | let h := oracleTranscript (splicedShadowReply d p M q₀ j ρ γ lam σ (Real.sqrt (n : ℝ))⁻¹) t w
        shadowStage p ρ q₀ t h = j ∧
        x h ∈ closedBall (roomCenter ρ (Function.update (d.directions w.1) j
          (transverseEmbed n ((Real.sqrt (n : ℝ))⁻¹ • w.2 0))) k) ρ} ≤
      ENNReal.ofReal (Real.exp (-(n : ℝ) / 8)) := by
  let u := fun h : LinearHistory S t => roomPrediction ρ (d.directions (historySeed t h)) j k (x h)
  have hu : Measurable u := roomPrediction_measurable ρ _
    (fun i => (d.measurable_directions i).comp (historySeed_measurable t)) j k x hx
  apply le_trans (measure_mono ?_) (spliced_shadow_estimation_bound ν d p hdclock hj hq hn
    hρ hσ γ lam hqcap t u hu)
  intro w hw
  dsimp only at hw ⊢
  refine ⟨hw.1, ?_⟩
  have he := spliced_room_hit_predicts hρ (d.directions w.1) hjk
    ((Real.sqrt (n : ℝ))⁻¹ • w.2 0) _ hw.2
  simpa only [u, oracleTranscript_seed, hiddenBlock, PiLp.proj_apply] using he

end NCBall
