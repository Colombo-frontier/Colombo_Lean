import NCBall.TruncatedShadow

/-! # The concrete spliced shadow oracle has the proved affine scalar form -/

noncomputable section
open scoped InnerProductSpace
namespace NCBall

variable {S : Type*} [MeasurableSpace S] {n H : ℕ}

theorem noisy_transverse_scalar (σ scale : ℝ) (h : Fin H)
    (w : HandleLatent (Transverse n) H) (y : Space n) :
    ⟪transverseEmbed n (scale • w 0) + σ • transverseEmbed n (scale • w h.succ), y⟫_ℝ =
      ⟪noisyHandleDirection (Transverse n) σ h (scale • transverseProjection n y), w⟫_ℝ := by
  rw [noisy_handle_reply]
  simp only [inner_add_left, inner_add_right, real_inner_smul_left,
    real_inner_smul_right, transverse_inner]
  rw [real_inner_comm (w 0) (transverseProjection n y),
    real_inner_comm (w h.succ) (transverseProjection n y)]

def splicedShadowReply (d : RoomBackground S n H) (p : RoomQueryPolicy S n H)
    (M q₀ j : ℕ) (ρ γ lam σ scale : ℝ)
    (t : ℕ) (h : LinearHistory S t) (w : HandleLatent (Transverse n) H) : ℝ :=
  shadowValue M (shadowStage p ρ q₀ t h) ρ γ lam
    (roomCenter ρ (Function.update (d.directions (historySeed t h)) j
      (transverseEmbed n (scale • w 0))))
    (Function.update (backgroundSamples d p t h) j
      (transverseEmbed n (scale • w 0) + σ • transverseEmbed n (scale • w (p.handle t h).succ)))
    (p.point t h)

theorem spliced_shadow_reply_affine (d : RoomBackground S n H) (p : RoomQueryPolicy S n H)
    {M j : ℕ} (hj : j < M) (q₀ : ℕ) (ρ γ lam σ scale : ℝ)
    (t : ℕ) (h : LinearHistory S t) (w : HandleLatent (Transverse n) H)
    (hr : shadowStage p ρ q₀ t h ≤ j) :
    splicedShadowReply d p M q₀ j ρ γ lam σ scale t h w =
      affineReusableReply (truncatedShadowPolicy d p q₀ j ρ lam scale) σ
        (truncatedShadowOffset d p M q₀ j ρ γ lam) t h w := by
  by_cases hlt : shadowStage p ρ q₀ t h < j
  · unfold splicedShadowReply
    rw [shadow_before_spliced_room (hlt.trans hj) hlt]
    simp only [affineReusableReply, truncatedShadowPolicy, truncatedShadowDirection,
      if_neg (Nat.ne_of_lt hlt), map_zero, inner_zero_left, add_zero,
      truncatedShadowOffset, if_pos hlt, backgroundCenters]
  · have he : shadowStage p ρ q₀ t h = j := by omega
    unfold splicedShadowReply
    rw [he, shadow_at_spliced_room hj]
    simp only [affineReusableReply, truncatedShadowPolicy, truncatedShadowDirection,
      he, if_true, truncatedShadowOffset, lt_self_iff_false, if_false]
    change shadowPastValue j ρ γ lam (backgroundCenters d ρ t h) (backgroundSamples d p t h)
      (p.point t h) + _ = _
    rw [noisy_transverse_scalar]
    rfl

end NCBall
