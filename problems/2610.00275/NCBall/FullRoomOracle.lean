import NCBall.RoomLatents
import NCBall.ShadowFutureHit

/-! # The single common random experiment for the complete room chain -/

noncomputable section
open MeasureTheory Set Metric
namespace NCBall

variable {R : Type*} [MeasurableSpace R] {n H M : ℕ}

attribute [local irreducible] latentDirections latentSamples

def fullRoomCenters (ρ scale : ℝ) (w : RoomLatents n H M) : ℕ → Space n :=
  roomCenter ρ (latentDirections scale w)

def fullShadowReply (p : RoomQueryPolicy R n H) (q₀ : ℕ) (ρ γ lam σ scale : ℝ) :
    (t : ℕ) → LinearHistory R t → RoomLatents n H M → ℝ :=
  shadowRoomReply p M q₀ ρ γ lam (fullRoomCenters ρ scale) (latentSamples σ scale)

def fullRealReply (p : RoomQueryPolicy R n H) (ρ γ lam σ scale : ℝ) :
    (t : ℕ) → LinearHistory R t → RoomLatents n H M → ℝ :=
  realRoomReply p M ρ γ lam (fullRoomCenters ρ scale) (latentSamples σ scale)

theorem fullRoomCenters_measurable (ρ scale : ℝ) (k : ℕ) :
    Measurable (fun w : RoomLatents n H M => fullRoomCenters ρ scale w k) :=
  roomCenter_measurable_data ρ (latentDirections scale) (latentDirections_measurable scale) k

theorem fullShadowReply_measurable (p : RoomQueryPolicy R n H)
    (q₀ : ℕ) (ρ γ lam σ scale : ℝ) (t : ℕ) :
    Measurable (fun hw : LinearHistory R t × RoomLatents n H M =>
      fullShadowReply p q₀ ρ γ lam σ scale t hw.1 hw.2) := by
  have hr := (shadowStage_measurable p ρ q₀ t).comp
    (measurable_fst : Measurable (Prod.fst : LinearHistory R t × RoomLatents n H M → _))
  have hx : Measurable (fun hw : LinearHistory R t × RoomLatents n H M => p.point t hw.1) :=
    (p.measurable_point t).comp measurable_fst
  have hc (k : ℕ) : Measurable (fun hw : LinearHistory R t × RoomLatents n H M =>
      fullRoomCenters ρ scale hw.2 k) := (fullRoomCenters_measurable ρ scale k).comp measurable_snd
  have hv (k : ℕ) : Measurable (fun hw : LinearHistory R t × RoomLatents n H M =>
      latentSamples σ scale hw.2 (p.handle t hw.1) k) :=
    (latentSamples_measurable σ scale k).comp (measurable_snd.prodMk
      ((p.measurable_handle t).comp measurable_fst))
  exact shadowValue_measurable_data M ρ γ lam _ _ _ _ hr hc hv hx

theorem fullShadowTranscript_measurable (p : RoomQueryPolicy R n H)
    (q₀ : ℕ) (ρ γ lam σ scale : ℝ) (t : ℕ) :
    Measurable (oracleTranscript (fullShadowReply (M := M) p q₀ ρ γ lam σ scale) t) :=
  oracleTranscript_measurable _ (fullShadowReply_measurable p q₀ ρ γ lam σ scale) t

theorem spliced_full_reply_map (p : RoomQueryPolicy R n H) (q₀ : ℕ) (j : Fin M)
    (ρ γ lam σ scale : ℝ) (t : ℕ)
    (h : LinearHistory (R × RoomLatents n H M) t) (z : HandleLatent (Transverse n) H) :
    splicedShadowReply (latentBackground n H M σ scale)
        (liftRoomPolicy p Prod.fst measurable_fst) M q₀ j.val ρ γ lam σ scale t h z =
      fullShadowReply p q₀ ρ γ lam σ scale t (mapHistorySeed Prod.fst t h)
        (Function.update (historySeed t h).2 j z) := by
  unfold fullShadowReply shadowRoomReply fullRoomCenters
  rw [latentDirections_update, latentSamples_update]
  unfold splicedShadowReply
  rw [shadowStage_lift]
  rfl

theorem spliced_full_history_map (p : RoomQueryPolicy R n H) (q₀ : ℕ) (j : Fin M)
    (ρ γ lam σ scale : ℝ) (t : ℕ)
    (w : (R × RoomLatents n H M) × HandleLatent (Transverse n) H) :
    mapHistorySeed Prod.fst t
      (oracleTranscript (splicedShadowReply (latentBackground n H M σ scale)
        (liftRoomPolicy p Prod.fst measurable_fst) M q₀ j.val ρ γ lam σ scale) t w) =
      oracleTranscript (fullShadowReply p q₀ ρ γ lam σ scale) t
        (w.1.1, Function.update w.1.2 j w.2) :=
  oracleTranscript_map_seed Prod.fst (fun s z => Function.update s.2 j z) _ _
    (spliced_full_reply_map p q₀ j ρ γ lam σ scale) t w

def fullShadowHit (p : RoomQueryPolicy R n H) (q₀ : ℕ) (ρ γ lam σ scale : ℝ)
    (t j k : ℕ) (x : LinearHistory R t → Space n) : Set (R × RoomLatents n H M) :=
  {w | let h := oracleTranscript (fullShadowReply p q₀ ρ γ lam σ scale) t w
    shadowStage p ρ q₀ t h = j ∧ x h ∈ closedBall (fullRoomCenters ρ scale w.2 k) ρ}

theorem fullShadowHit_measurable (p : RoomQueryPolicy R n H) (q₀ : ℕ) (ρ γ lam σ scale : ℝ)
    (t j k : ℕ) (x : LinearHistory R t → Space n) (hx : Measurable x) :
    MeasurableSet (fullShadowHit (M := M) p q₀ ρ γ lam σ scale t j k x) := by
  have hh := fullShadowTranscript_measurable (M := M) p q₀ ρ γ lam σ scale t
  have hs := (shadowStage_measurable p ρ q₀ t).comp hh
  have hc : Measurable (fun w : R × RoomLatents n H M => fullRoomCenters ρ scale w.2 k) :=
    (fullRoomCenters_measurable ρ scale k).comp measurable_snd
  exact (hs (measurableSet_singleton j)).inter
    (measurableSet_le ((hx.comp hh).dist hc) measurable_const)

end NCBall
