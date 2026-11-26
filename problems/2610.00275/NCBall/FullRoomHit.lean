import NCBall.FullRoomOracle

/-! # Future-room hit probability in the common complete experiment -/

noncomputable section
open MeasureTheory Set Metric
namespace NCBall

variable {R : Type*} [MeasurableSpace R] {n H M : ℕ}

theorem full_shadow_future_hit_bound (ν : Measure R) [IsProbabilityMeasure ν]
    (p : RoomQueryPolicy R n H) {q₀ : ℕ} (j : Fin M) {k : ℕ}
    (hjk : j.val < k) (hq : 0 < q₀) (hn : 0 < n)
    {ρ σ : ℝ} (hρ : 0 < ρ) (hσ : 0 < σ) (γ lam : ℝ)
    (hqcap : (q₀ : ℝ) ≤ n * σ ^ 2 / 16) (t : ℕ)
    (x : LinearHistory R t → Space n) (hx : Measurable x) :
    (ν.prod (roomLatentLaw n H M))
      (fullShadowHit p q₀ ρ γ lam σ (Real.sqrt (n : ℝ))⁻¹ t j.val k x) ≤
      ENNReal.ofReal (Real.exp (-(n : ℝ) / 8)) := by
  let scale := (Real.sqrt (n : ℝ))⁻¹
  let d : RoomBackground (R × RoomLatents n H M) n H := latentBackground n H M σ scale
  let p' : RoomQueryPolicy (R × RoomLatents n H M) n H :=
    liftRoomPolicy p Prod.fst measurable_fst
  let f := fun w : (R × RoomLatents n H M) × HandleLatent (Transverse n) H =>
    (w.1.1, Function.update w.1.2 j w.2)
  have hf : Measurable f :=
    (measurable_fst.comp measurable_fst).prodMk
      ((independent_replacement_measurable j).comp
        ((measurable_snd.comp measurable_fst).prodMk measurable_snd))
  have hlaw : ((ν.prod (roomLatentLaw n H M)).prod
      (euclideanGaussianLaw (HandleLatent (Transverse n) H))).map f =
        ν.prod (roomLatentLaw n H M) :=
    independent_replacement_with_seed ν _ j
  rw [← hlaw, Measure.map_apply hf (fullShadowHit_measurable p q₀ ρ γ lam σ scale t j.val k x hx)]
  have hb := spliced_shadow_future_hit_bound (ν.prod (roomLatentLaw n H M)) d p'
    (fun s i => latentDirections_clock scale s.2 i) j.isLt hjk hq hn hρ hσ γ lam hqcap t
    (fun h => x (mapHistorySeed Prod.fst t h))
    (hx.comp (mapHistorySeed_measurable Prod.fst measurable_fst t))
  apply le_trans (measure_mono ?_) hb
  intro w hw
  change shadowStage p ρ q₀ t
      (oracleTranscript (fullShadowReply p q₀ ρ γ lam σ scale) t (f w)) = j.val ∧
    x (oracleTranscript (fullShadowReply p q₀ ρ γ lam σ scale) t (f w)) ∈
      closedBall (fullRoomCenters ρ scale (f w).2 k) ρ at hw
  dsimp only
  change shadowStage p' ρ q₀ t
      (oracleTranscript (splicedShadowReply d p' M q₀ j.val ρ γ lam σ scale) t w) = j.val ∧ _
  rw [shadowStage_lift, spliced_full_history_map]
  refine ⟨hw.1, ?_⟩
  simpa only [fullRoomCenters, f, latentDirections_update, d, latentBackground] using hw.2

end NCBall
