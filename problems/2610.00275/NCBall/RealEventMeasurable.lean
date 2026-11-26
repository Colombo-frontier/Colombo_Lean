import NCBall.FullSuccess

/-! # Measurable real-oracle histories and terminal events -/

noncomputable section
open MeasureTheory Set Metric
namespace NCBall

variable {R : Type*} [MeasurableSpace R] {n H M : ℕ}
attribute [local irreducible] latentDirections latentSamples

theorem fullRealReply_measurable (p : RoomQueryPolicy R n H)
    (ρ γ lam σ scale : ℝ) (t : ℕ) :
    Measurable (fun hw : LinearHistory R t × RoomLatents n H M =>
      fullRealReply p ρ γ lam σ scale t hw.1 hw.2) := by
  have hx : Measurable (fun hw : LinearHistory R t × RoomLatents n H M => p.point t hw.1) :=
    (p.measurable_point t).comp measurable_fst
  have hc (k : ℕ) : Measurable (fun hw : LinearHistory R t × RoomLatents n H M =>
      fullRoomCenters ρ scale hw.2 k) := (fullRoomCenters_measurable ρ scale k).comp measurable_snd
  have hv (k : ℕ) : Measurable (fun hw : LinearHistory R t × RoomLatents n H M =>
      latentSamples σ scale hw.2 (p.handle t hw.1) k) :=
    (latentSamples_measurable σ scale k).comp (measurable_snd.prodMk
      ((p.measurable_handle t).comp measurable_fst))
  have hm := shadowValue_measurable_data M ρ γ lam (fun _ : LinearHistory R t × RoomLatents n H M => M)
    _ _ _ measurable_const hc hv hx
  simpa only [shadowValue_all_unlocked M M le_rfl] using hm

theorem fullRealTranscript_measurable (p : RoomQueryPolicy R n H)
    (ρ γ lam σ scale : ℝ) (t : ℕ) :
    Measurable (oracleTranscript (fullRealReply (M := M) p ρ γ lam σ scale) t) :=
  oracleTranscript_measurable _ (fullRealReply_measurable p ρ γ lam σ scale) t

theorem fullRealTerminalEvent_measurable (p : RoomQueryPolicy R n H)
    (ρ γ lam σ scale : ℝ) (N : ℕ) (out : LinearHistory R N → Space n) (hout : Measurable out) :
    MeasurableSet (fullRealTerminalEvent (M := M) p ρ γ lam σ scale N out) := by
  have hh := fullRealTranscript_measurable (M := M) p ρ γ lam σ scale N
  have hc : Measurable (fun w : R × RoomLatents n H M => fullRoomCenters ρ scale w.2 M) :=
    (fullRoomCenters_measurable ρ scale M).comp measurable_snd
  exact measurableSet_le ((hout.comp hh).dist hc) measurable_const

theorem latentGoodEvent_measurable (scale : ℝ) :
    MeasurableSet (latentGoodEvent (n := n) (H := H) (M := M) scale) := by
  unfold latentGoodEvent
  simp only [setOf_forall]
  exact MeasurableSet.iInter (fun j => MeasurableSet.iInter (fun _ =>
    measurableSet_le (latentDirections_measurable scale j).norm measurable_const))

end NCBall
