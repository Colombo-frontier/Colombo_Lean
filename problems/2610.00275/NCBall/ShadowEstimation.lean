import NCBall.ShadowReplay

/-! # An actual shadow-history estimation bound before the current room unlocks -/

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace NCBall

variable {S : Type*} [MeasurableSpace S] {n H : ℕ}

theorem spliced_shadow_estimation_bound (ν : Measure S) [IsProbabilityMeasure ν]
    (d : RoomBackground S n H) (p : RoomQueryPolicy S n H)
    (hdclock : ∀ s k, d.directions s k 0 = 0)
    {M j q₀ : ℕ} (hj : j < M) (hq : 0 < q₀) (hn : 0 < n)
    {ρ σ : ℝ} (hρ : 0 < ρ) (hσ : 0 < σ) (γ lam : ℝ)
    (hqcap : (q₀ : ℝ) ≤ n * σ ^ 2 / 16) (t : ℕ)
    (u : LinearHistory S t → Transverse n) (hu : Measurable u) :
    (ν.prod (euclideanGaussianLaw (HandleLatent (Transverse n) H)))
      {w | let h := oracleTranscript (splicedShadowReply d p M q₀ j ρ γ lam σ (Real.sqrt (n : ℝ))⁻¹) t w
        shadowStage p ρ q₀ t h = j ∧
        ‖(Real.sqrt (n : ℝ))⁻¹ • hiddenBlock (Transverse n) H w.2 - u h‖ ≤ 1 / 16} ≤
      ENNReal.ofReal (Real.exp (-(n : ℝ) / 8)) := by
  let scale := (Real.sqrt (n : ℝ))⁻¹
  let q := truncatedShadowPolicy d p q₀ j ρ lam scale
  let offset := truncatedShadowOffset d p M q₀ j ρ γ lam
  let affine := affineReusableReply q σ offset
  have hoff : ∀ k, Measurable (offset k) := truncatedShadowOffset_measurable d p M q₀ j ρ γ lam
  have hfin : Module.finrank ℝ (Transverse n) = n := finrank_euclideanSpace_fin
  have hb := affine_reusable_estimation_bound ν q σ hσ offset hoff t (by simpa [hfin] using hn) u hu
  rw [hfin] at hb
  apply le_trans (measure_mono ?_) hb
  intro w hw
  dsimp only at hw
  have he := spliced_shadow_history_replay d p hj q₀ ρ γ lam σ scale t w hw.1.le
  change oracleTranscript (splicedShadowReply d p M q₀ j ρ γ lam σ scale) t w =
    oracleTranscript affine t w at he
  change shadowStage p ρ q₀ t
    (oracleTranscript (splicedShadowReply d p M q₀ j ρ γ lam σ scale) t w) = j ∧ _ at hw
  rw [he] at hw
  have hcount := truncated_queryCount_lt_threshold d p hdclock hq j hρ lam scale t
    (oracleTranscript affine t w) hw.1
  have hcount' : (reusableQueryCount q t (oracleTranscript affine t w) : ℝ) < q₀ :=
    Nat.cast_lt.mpr hcount
  exact ⟨hcount'.trans_le hqcap, hw.2⟩

end NCBall
