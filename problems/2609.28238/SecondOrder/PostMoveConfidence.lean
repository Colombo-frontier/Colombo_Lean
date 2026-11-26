import SecondOrder.PostMoveMeasurability

open MeasureTheory
open scoped Classical ENNReal BigOperators

namespace SecondOrder
noncomputable section

def postCallCount {d L : ℕ} (q : ℕ) (Lip s τ : ℝ) (z : TrackedState d L)
    (r : CurvatureReply d) (b : Bool) : ℕ :=
  if (trackedNext Lip s τ z r b).running then
    (createdNodes L z.memory.length).card+(if trackedRestart q τ z r then 1 else 0) else 0

theorem postCallCount_eq_requests {d L : ℕ} (q : ℕ) (Lip s τ : ℝ)
    (z : TrackedState d L) (r : CurvatureReply d) (b : Bool) :
    postCallCount q Lip s τ z r b =
      requestCharge isChordRequest (trackedStepRequests q Lip s τ z r b)+
        requestCharge isAnchorRequest (trackedStepRequests q Lip s τ z r b) := by
  rw [trackedStepRequests_chords,trackedStepRequests_anchor]
  unfold postCallCount
  split_ifs <;> simp_all

theorem postCallCount_measurable {A : Type*} [MeasurableSpace A] {d L : ℕ}
    (q : ℕ) (Lip s τ : ℝ) {z : A → TrackedState d L} {r : A → CurvatureReply d} {b : A → Bool}
    (hz : Measurable z) (hr : Measurable r) (hb : Measurable b) :
    Measurable (fun a => postCallCount q Lip s τ (z a) (r a) (b a)) := by
  have hn := state_measurable_fields.mp (trackedNext_measurable Lip s τ hz hr hb)
  have hl := (trackerMemory_measurable_fields.mp (tracked_measurable_fields.mp hz).2.2).1
  exact Measurable.ite (hn.2.1 (measurableSet_singleton true))
    (((measurable_of_countable (fun n => (createdNodes L n).card)).comp hl).add
      (Measurable.ite (trackedRestart_measurableSet q τ hz hr) measurable_const measurable_const)) measurable_const

/-- A history-dependent fresh slice bound, with the actual predictable
charge inside the integral. This permits summing actual call counts across
epochs instead of paying a worst-case packet size at every move. -/
theorem fresh_event_past_variable_bound {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    {η : Measure A} {μ : Measure B} [SFinite μ] {event : Set (A × B)} {c : A → ℝ≥0∞}
    (he : MeasurableSet event) (hb : ∀ a, μ {b | (a,b) ∈ event} ≤ c a)
    {past : Set A} (hp : MeasurableSet past) :
    (η.prod μ) {w | w.1 ∈ past ∧ w ∈ event} ≤ ∫⁻ a in past, c a ∂η := by
  change (η.prod μ) ((Prod.fst ⁻¹' past) ∩ event) ≤ _
  rw [Measure.prod_apply ((hp.preimage measurable_fst).inter he)]
  calc
    _ ≤ ∫⁻ a, past.indicator c a ∂η := by
      apply lintegral_mono
      intro a
      change μ {b | a ∈ past ∧ (a,b) ∈ event} ≤ past.indicator c a
      by_cases ha : a ∈ past
      · simpa [ha] using hb a
      · simp [ha]
    _ = _ := lintegral_indicator hp _

variable {Ω A : Type*} [MeasurableSpace Ω] [MeasurableSpace A] {d L : ℕ}
  {μ : Measure Ω} [IsProbabilityMeasure μ] {P : Parameters} {ν : ℝ}
  {F : Point d → ℝ} {f : Ω → Point d → ℝ}

theorem CommonLoss.sampleChordAt_confidence (h : CommonLoss μ P ν F f)
    (x y : Point d) {ρ δ : ℝ} (hρ : 0 < ρ) (hδ : 0 < δ) :
    batchTapeLaw (unitLine.prod μ) (confidenceRepeats δ)
      {w | ρ < ‖sampleChordAt P f x y ρ δ w-(gradient F y-gradient F x)‖} ≤ ENNReal.ofReal δ := by
  exact variableFreshEstimate_slice_confidence (μ := unitLine.prod μ)
    (target := fun a : Point d × Point d => gradient F a.2-gradient F a.1)
    (h.randomLine_adaptive_measurable measurable_fst measurable_snd) ρ δ
    (fun a => h.chord_confidence a.1 a.2 hρ hδ) (x,y)

theorem CommonLoss.postMove_chord_confidence (h : CommonLoss μ P ν F f)
    (Lip s τ : ℝ) {ρ δ : ℝ} (hρ : 0 < ρ) (hδ : 0 < δ)
    (z : TrackedState d L) (r : CurvatureReply d) (b : Bool) (i : BinaryNode L)
    (hr : (trackedNext Lip s τ z r b).running = true) (hi : i ∈ createdNodes L z.memory.length) :
    postMoveLaw μ P L τ δ {w | ρ < ‖sampledChordPacket P f Lip s τ ρ δ z r b w.1 i-
      (gradient F (trackerPushPoints z.memory (trackedNext Lip s τ z r b).point (nodeRight i))-
        gradient F (trackerPushPoints z.memory (trackedNext Lip s τ z r b).point (nodeLeft i)))‖} ≤ ENNReal.ofReal δ := by
  simp_rw [sampledChordPacket_active P f Lip s τ ρ δ z r b _ i hr hi]
  let x := trackerPushPoints z.memory (trackedNext Lip s τ z r b).point (nodeLeft i)
  let y := trackerPushPoints z.memory (trackedNext Lip s τ z r b).point (nodeRight i)
  have hm : Measurable (sampleChordAt P f x y ρ δ) :=
    h.sampleChordAt_measurable measurable_const measurable_const ρ δ measurable_id
  have hs := measurableSet_lt (measurable_const (a := ρ)) (hm.sub_const (gradient F y-gradient F x)).norm
  exact (postMoveLaw_chord_eval μ P L τ δ i hs).le.trans
    (h.sampleChordAt_confidence x y hρ hδ)

theorem CommonLoss.postMove_anchor_confidence (h : CommonLoss μ P ν F f)
    (q : ℕ) (Lip s : ℝ) {τ δ : ℝ} (hτ : 0 < τ) (hδ : 0 < δ)
    (z : TrackedState d L) (r : CurvatureReply d) (b : Bool)
    (hr : (trackedNext Lip s τ z r b).running = true) :
    postMoveLaw μ P L τ δ {w | trackedRestart q τ z r ∧
      τ/4 < ‖sampledRefreshAnchor P f q Lip s τ δ z r b w.2-gradient F (trackedNext Lip s τ z r b).point‖} ≤
        ENNReal.ofReal (((if trackedRestart q τ z r then 1 else 0 : ℕ) : ℝ)*δ) := by
  by_cases he : trackedRestart q τ z r
  · simp only [he,true_and,if_pos,Nat.cast_one,one_mul]
    simp_rw [sampledRefreshAnchor_active P f q Lip s τ δ z r b _ hr he]
    exact (postMoveLaw_anchor_eval μ P L τ δ
      {w | τ/4 < ‖gradientAnchor P f (trackedNext Lip s τ z r b).point (τ/4) δ w-
        gradient F (trackedNext Lip s τ z r b).point‖}).le.trans
      (h.anchor_confidence _ (by positivity) hδ)
  · simp [he]

/-- Conditional on the entire state, curvature reply and new sign, all
post-move samples are fresh and their failure probability is bounded by
δ times the number of genuinely requested local routines. -/
theorem CommonLoss.sampledPostFailure_confidence (h : CommonLoss μ P ν F f)
    (q : ℕ) (Lip s : ℝ) {τ ρ δ : ℝ} (hτ : 0 < τ) (hρ : 0 < ρ) (hδ : 0 < δ)
    (z : TrackedState d L) (r : CurvatureReply d) (b : Bool) :
    postMoveLaw μ P L τ δ {w | sampledPostFailure F P f q Lip s τ ρ δ z r b w} ≤
      ENNReal.ofReal ((postCallCount q Lip s τ z r b : ℝ)*δ) := by
  by_cases hr : (trackedNext Lip s τ z r b).running = true
  · let C := fun i : BinaryNode L => {w : PostMoveTape Ω P L τ δ |
      ρ < ‖sampledChordPacket P f Lip s τ ρ δ z r b w.1 i-
        (gradient F (trackerPushPoints z.memory (trackedNext Lip s τ z r b).point (nodeRight i))-
          gradient F (trackerPushPoints z.memory (trackedNext Lip s τ z r b).point (nodeLeft i)))‖}
    let B := {w : PostMoveTape Ω P L τ δ | trackedRestart q τ z r ∧
      τ/4 < ‖sampledRefreshAnchor P f q Lip s τ δ z r b w.2-gradient F (trackedNext Lip s τ z r b).point‖}
    have hs : {w | sampledPostFailure F P f q Lip s τ ρ δ z r b w} ⊆
        (⋃ i ∈ createdNodes L z.memory.length, C i) ∪ B := by
      intro w hw
      rcases hw.2 with ⟨i,hi,hc⟩ | ha
      · exact Or.inl (Set.mem_iUnion.mpr ⟨i,Set.mem_iUnion.mpr ⟨hi,hc⟩⟩)
      · exact Or.inr ha
    have hmul (n : ℕ) : (n : ℝ≥0∞)*ENNReal.ofReal δ=ENNReal.ofReal ((n : ℝ)*δ) := by
      rw [ENNReal.ofReal_mul (Nat.cast_nonneg n),ENNReal.ofReal_natCast]
    calc
      _ ≤ postMoveLaw μ P L τ δ ((⋃ i ∈ createdNodes L z.memory.length, C i) ∪ B) := measure_mono hs
      _ ≤ postMoveLaw μ P L τ δ (⋃ i ∈ createdNodes L z.memory.length, C i)+postMoveLaw μ P L τ δ B := measure_union_le _ _
      _ ≤ (∑ i ∈ createdNodes L z.memory.length, ENNReal.ofReal δ)+
          ENNReal.ofReal (((if trackedRestart q τ z r then 1 else 0 : ℕ) : ℝ)*δ) :=
        add_le_add ((measure_biUnion_finset_le _ _).trans
          (Finset.sum_le_sum (fun i hi => h.postMove_chord_confidence Lip s τ hρ hδ z r b i hr hi)))
          (h.postMove_anchor_confidence q Lip s hτ hδ z r b hr)
      _ = _ := by
        rw [Finset.sum_const,nsmul_eq_mul,hmul,← ENNReal.ofReal_add
          (mul_nonneg (Nat.cast_nonneg _) hδ.le) (mul_nonneg (Nat.cast_nonneg _) hδ.le)]
        congr 1
        simp only [postCallCount,hr,↓reduceIte,Nat.cast_add]
        ring
  · simp [sampledPostFailure,postCallCount,hr]

/-- The same bound holds on every measurable past event, with the actual
history-dependent request count kept inside the integral. -/
theorem CommonLoss.sampledPostFailure_past_confidence (h : CommonLoss μ P ν F f)
    {η : Measure A} (q : ℕ) (Lip s : ℝ) {τ ρ δ : ℝ} (hτ : 0 < τ) (hρ : 0 < ρ) (hδ : 0 < δ)
    {z : A → TrackedState d L} {r : A → CurvatureReply d} {b : A → Bool}
    (hz : Measurable z) (hr : Measurable r) (hb : Measurable b)
    {past : Set A} (hp : MeasurableSet past) :
    (η.prod (postMoveLaw μ P L τ δ))
      {w | w.1 ∈ past ∧ sampledPostFailure F P f q Lip s τ ρ δ (z w.1) (r w.1) (b w.1) w.2} ≤
        ∫⁻ a in past, ENNReal.ofReal ((postCallCount q Lip s τ (z a) (r a) (b a) : ℝ)*δ) ∂η := by
  apply fresh_event_past_variable_bound
    (h.sampledPostFailure_measurableSet q Lip s τ ρ δ
      (hz.comp measurable_fst) (hr.comp measurable_fst) (hb.comp measurable_fst) measurable_snd)
    (fun a => h.sampledPostFailure_confidence q Lip s hτ hρ hδ (z a) (r a) (b a)) hp

theorem CommonLoss.sampledInitial_confidence (h : CommonLoss μ P ν F f)
    {τ δ : ℝ} (hτ : 0 < τ) (hδ : 0 < δ) (ρ : ℝ) :
    localLaw μ (P.gradientNoise^2) (τ/4) δ
      {w | ¬TrackedConsistent F τ ρ (sampledInitial (L := L) P f τ δ w)} ≤ ENNReal.ofReal δ := by
  apply le_trans (measure_mono ?_) (h.anchor_confidence 0 (by positivity) hδ)
  intro w hw
  change τ/4 < ‖gradientAnchor P f 0 (τ/4) δ w-gradient F 0‖
  by_contra hh
  exact hw (trackedInitial_consistent _ (le_of_not_gt hh))

end
end SecondOrder
