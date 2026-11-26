import SecondOrder.PostMoveConfidence

open scoped Classical BigOperators

namespace SecondOrder
noncomputable section

def postChordNodes {d L : ℕ} (Lip s τ : ℝ) (z : TrackedState d L)
    (r : CurvatureReply d) (b : Bool) : Finset (BinaryNode L) :=
  if (trackedNext Lip s τ z r b).running then createdNodes L z.memory.length else ∅

abbrev PostChordSlot {d L : ℕ} (P : Parameters) (Lip s τ ρ δ : ℝ)
    (z : TrackedState d L) (r : CurvatureReply d) (b : Bool) :=
  (i : {i // i ∈ postChordNodes Lip s τ z r b}) ×
    AdaptiveChordSlot P (fun _ : Unit => trackerPushPoints z.memory (trackedNext Lip s τ z r b).point (nodeLeft i.val))
      (fun _ : Unit => trackerPushPoints z.memory (trackedNext Lip s τ z r b).point (nodeRight i.val)) ρ δ ()

/-- The oracle query belonging to an actual requested chord slot. It is
one HVP at one point, with a fresh loss sample from that chord's batch. -/
def postChordCall {Ω : Type*} {d L : ℕ} (P : Parameters) (Lip s τ ρ δ : ℝ)
    (z : TrackedState d L) (r : CurvatureReply d) (b : Bool) (w : ChordPacketTape Ω L δ)
    (slot : PostChordSlot P Lip s τ ρ δ z r b) : Ω × HvpQuery d :=
  adaptiveChordCall P Prod.fst Prod.snd ρ δ
    ((trackerPushPoints z.memory (trackedNext Lip s τ z r b).point (nodeLeft slot.1.val),
      trackerPushPoints z.memory (trackedNext Lip s τ z r b).point (nodeRight slot.1.val)),w slot.1.val) slot.2

theorem postChordCall_count {d L : ℕ} (P : Parameters) (q : ℕ) (Lip s τ ρ δ : ℝ)
    (z : TrackedState d L) (r : CurvatureReply d) (b : Bool) :
    Fintype.card (PostChordSlot P Lip s τ ρ δ z r b) =
      requestCharge (requestChordCost P ρ δ) (trackedStepRequests q Lip s τ z r b) := by
  let c := fun i : BinaryNode L => localQueryCount (chordVariance P
    (trackerPushPoints z.memory (trackedNext Lip s τ z r b).point (nodeLeft i))
    (trackerPushPoints z.memory (trackedNext Lip s τ z r b).point (nodeRight i))) ρ δ
  calc
    _ = ∑ i : {i // i ∈ postChordNodes Lip s τ z r b}, c i.val := by
      simp only [PostChordSlot,Fintype.card_sigma,adaptiveChordCall_count,adaptiveChordCost]
      rfl
    _ = ∑ i ∈ postChordNodes Lip s τ z r b, c i :=
      (Finset.sum_subtype _ (fun _ => Iff.rfl) c).symm
    _ = _ := by
      change _ = requestCharge (chordRequestCharge (fun x y => localQueryCount (chordVariance P x y) ρ δ)) _
      rw [trackedStepRequests_chordCharge]
      dsimp only [postChordNodes]
      split_ifs <;> rfl

/-- Every stored active chord is exactly the robust average of its
counted oracle replies. The last chords of a restarting epoch are included. -/
theorem sampledChordPacket_eq_query_average {Ω : Type*} [MeasurableSpace Ω] {d L : ℕ}
    (P : Parameters) (f : Ω → Point d → ℝ) (Lip s τ ρ δ : ℝ) (z : TrackedState d L)
    (r : CurvatureReply d) (b : Bool) (w : ChordPacketTape Ω L δ)
    (i : {i // i ∈ postChordNodes Lip s τ z r b}) :
    sampledChordPacket P f Lip s τ ρ δ z r b w i.val =
      robustCenter (confidenceRepeats_pos δ)
        (fun j => ((localBatchSize (chordVariance P
          (trackerPushPoints z.memory (trackedNext Lip s τ z r b).point (nodeLeft i.val))
          (trackerPushPoints z.memory (trackedNext Lip s τ z r b).point (nodeRight i.val))) ρ : ℕ) : ℝ)⁻¹ •
          ∑ k : Fin (localBatchSize (chordVariance P
            (trackerPushPoints z.memory (trackedNext Lip s τ z r b).point (nodeLeft i.val))
            (trackerPushPoints z.memory (trackedNext Lip s τ z r b).point (nodeRight i.val))) ρ),
            hvpReply f (postChordCall P Lip s τ ρ δ z r b w ⟨i,(j,k)⟩).1
              (postChordCall P Lip s τ ρ δ z r b w ⟨i,(j,k)⟩).2) (ρ/3) := by
  have hi := i.property
  dsimp only [postChordNodes] at hi
  split_ifs at hi with hr
  · rw [sampledChordPacket_active P f Lip s τ ρ δ z r b w i.val hr hi]
    exact adaptiveChord_eq_query_average P f Prod.fst Prod.snd ρ δ _
  · simp at hi

abbrev PostRefreshSlot {d L : ℕ} (P : Parameters) (q : ℕ) (Lip s τ δ : ℝ)
    (z : TrackedState d L) (r : CurvatureReply d) (b : Bool) :=
  Fin (if (trackedNext Lip s τ z r b).running = true ∧ trackedRestart q τ z r then 1 else 0) ×
    AnchorSlot P (τ/4) δ

def postRefreshCall {Ω : Type*} {d L : ℕ} (P : Parameters) (q : ℕ) (Lip s τ δ : ℝ)
    (z : TrackedState d L) (r : CurvatureReply d) (b : Bool)
    (w : LocalDraws Ω (P.gradientNoise^2) (τ/4) δ) (slot : PostRefreshSlot P q Lip s τ δ z r b) :
    Ω × HvpQuery d :=
  anchorSampleCall P (trackedNext Lip s τ z r b).point (τ/4) δ w slot.2

theorem sampledRefreshAnchor_eq_query_average {Ω : Type*} {d L : ℕ} (P : Parameters)
    (f : Ω → Point d → ℝ) (q : ℕ) (Lip s τ δ : ℝ) (z : TrackedState d L)
    (r : CurvatureReply d) (b : Bool) (w : LocalDraws Ω (P.gradientNoise^2) (τ/4) δ)
    (gate : Fin (if (trackedNext Lip s τ z r b).running = true ∧ trackedRestart q τ z r then 1 else 0)) :
    sampledRefreshAnchor P f q Lip s τ δ z r b w =
      robustCenter (confidenceRepeats_pos δ)
        (fun j => ((localBatchSize (P.gradientNoise^2) (τ/4) : ℕ) : ℝ)⁻¹ •
          ∑ k : Fin (localBatchSize (P.gradientNoise^2) (τ/4)),
            hvpReply f (postRefreshCall P q Lip s τ δ z r b w (gate,(j,k))).1
              (postRefreshCall P q Lip s τ δ z r b w (gate,(j,k))).2) ((τ/4)/3) := by
  have ha : (trackedNext Lip s τ z r b).running = true ∧ trackedRestart q τ z r := by
    by_contra hh
    have hg := gate.isLt
    simp [hh] at hg
  rw [sampledRefreshAnchor_active P f q Lip s τ δ z r b w ha.1 ha.2]
  exact gradientAnchor_eq_query_average P f _ (τ/4) δ w

theorem postRefreshCall_count {d L : ℕ} (P : Parameters) (q : ℕ) (Lip s τ δ : ℝ)
    (z : TrackedState d L) (r : CurvatureReply d) (b : Bool) :
    Fintype.card (PostRefreshSlot P q Lip s τ δ z r b) =
      requestCharge isAnchorRequest (trackedStepRequests q Lip s τ z r b)*
        localQueryCount (P.gradientNoise^2) (τ/4) δ := by
  simp [PostRefreshSlot,AnchorSlot,localQueryCount,trackedStepRequests_anchor,Nat.mul_comm]

/-- The price assigned to the post-move request list equals the number of
actual permitted gradient/HVP slots used by the fresh sampled estimators. -/
theorem postMove_oracle_slot_count {d L : ℕ} (P : Parameters) (q : ℕ) (Lip s τ ρ δ : ℝ)
    (z : TrackedState d L) (r : CurvatureReply d) (b : Bool) :
    Fintype.card (PostChordSlot P Lip s τ ρ δ z r b)+
      Fintype.card (PostRefreshSlot P q Lip s τ δ z r b) =
        requestCharge (requestOracleCost P τ ρ δ (fun _ => 0)) (trackedStepRequests q Lip s τ z r b) := by
  rw [postChordCall_count P q,postRefreshCall_count,requestOracleCost_decomposition]
  omega

end
end SecondOrder
