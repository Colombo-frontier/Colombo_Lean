import NCBall.TruncatedReply
import NCBall.TruncatedCharges

/-! # Replaying the concrete shadow history up to the room's unlock -/

noncomputable section
namespace NCBall

variable {S Ω : Type*} [MeasurableSpace S] {n H : ℕ}

theorem shadowCounter_path_mono (p : RoomQueryPolicy S n H) (ρ : ℝ) (q₀ : ℕ)
    (reply : (t : ℕ) → LinearHistory S t → Ω → ℝ) (w : S × Ω) :
    Monotone (fun t => shadowCounter p ρ q₀ t (oracleTranscript reply t w)) := by
  apply monotone_nat_of_le_succ
  intro t
  exact (shadowCounter_step p ρ q₀ t (oracleTranscript reply (t + 1) w)).1

theorem shadowStage_path_mono (p : RoomQueryPolicy S n H) (ρ : ℝ) (q₀ : ℕ)
    (reply : (t : ℕ) → LinearHistory S t → Ω → ℝ) (w : S × Ω) :
    Monotone (fun t => shadowStage p ρ q₀ t (oracleTranscript reply t w)) := by
  intro t k htk
  exact Nat.div_le_div_right (shadowCounter_path_mono p ρ q₀ reply w htk)

theorem spliced_shadow_history_replay (d : RoomBackground S n H) (p : RoomQueryPolicy S n H)
    {M j : ℕ} (hj : j < M) (q₀ : ℕ) (ρ γ lam σ scale : ℝ) (N : ℕ)
    (w : S × HandleLatent (Transverse n) H)
    (hr : shadowStage p ρ q₀ N
      (oracleTranscript (splicedShadowReply d p M q₀ j ρ γ lam σ scale) N w) ≤ j) :
    oracleTranscript (splicedShadowReply d p M q₀ j ρ γ lam σ scale) N w =
      oracleTranscript (affineReusableReply (truncatedShadowPolicy d p q₀ j ρ lam scale) σ
        (truncatedShadowOffset d p M q₀ j ρ γ lam)) N w := by
  have hagree (t : ℕ) (h : LinearHistory S t) (z : HandleLatent (Transverse n) H)
      (hsafe : ¬ j < shadowStage p ρ q₀ t h) :
      affineReusableReply (truncatedShadowPolicy d p q₀ j ρ lam scale) σ
          (truncatedShadowOffset d p M q₀ j ρ γ lam) t h z =
        splicedShadowReply d p M q₀ j ρ γ lam σ scale t h z :=
    (spliced_shadow_reply_affine d p hj q₀ ρ γ lam σ scale t h z (Nat.le_of_not_gt hsafe)).symm
  have hs (t : ℕ) (ht : t < N) : ¬j < shadowStage p ρ q₀ t
      (oracleTranscript (splicedShadowReply d p M q₀ j ρ γ lam σ scale) t w) := by
    have hm := shadowStage_path_mono p ρ q₀
      (splicedShadowReply d p M q₀ j ρ γ lam σ scale) w (Nat.le_of_lt ht)
    exact Nat.not_lt_of_ge (hm.trans hr)
  exact (oracleTranscript_eq_of_no_bad _ _ _ hagree N w hs N le_rfl).symm

end NCBall
