import SecondOrder.PostMoveSampling

open MeasureTheory
open scoped Classical

namespace SecondOrder
noncomputable section

def sampledPostFailure {Ω : Type*} {d L : ℕ} (F : Point d → ℝ) (P : Parameters) (f : Ω → Point d → ℝ)
    (q : ℕ) (Lip s τ ρ δ : ℝ) (z : TrackedState d L) (r : CurvatureReply d) (b : Bool)
    (w : PostMoveTape Ω P L τ δ) : Prop :=
  (trackedNext Lip s τ z r b).running = true ∧
    ((∃ i ∈ createdNodes L z.memory.length,
      ρ < ‖sampledChordPacket P f Lip s τ ρ δ z r b w.1 i-
        (gradient F (trackerPushPoints z.memory (trackedNext Lip s τ z r b).point (nodeRight i))-
          gradient F (trackerPushPoints z.memory (trackedNext Lip s τ z r b).point (nodeLeft i)))‖) ∨
    (trackedRestart q τ z r ∧ τ/4 < ‖sampledRefreshAnchor P f q Lip s τ δ z r b w.2-
      gradient F (trackedNext Lip s τ z r b).point‖))

variable {Ω A : Type*} [MeasurableSpace Ω] [MeasurableSpace A] {d L : ℕ}
  {μ : Measure Ω} [IsProbabilityMeasure μ] {P : Parameters} {ν : ℝ}
  {F : Point d → ℝ} {f : Ω → Point d → ℝ}

theorem CommonLoss.sampleChordAt_measurable (h : CommonLoss μ P ν F f)
    {x y : A → Point d} (hx : Measurable x) (hy : Measurable y) (ρ δ : ℝ)
    {tape : A → BatchTape (ℝ × Ω) (confidenceRepeats δ)} (hw : Measurable tape) :
    Measurable (fun a => sampleChordAt P f (x a) (y a) ρ δ (tape a)) :=
  (h.adaptiveChord_measurable (A := Point d × Point d)
    (x := Prod.fst) (y := Prod.snd) measurable_fst measurable_snd ρ δ).comp
      ((hx.prodMk hy).prodMk hw)

theorem CommonLoss.sampledChordPacket_measurable (h : CommonLoss μ P ν F f)
    (Lip s τ ρ δ : ℝ) {z : A → TrackedState d L} {r : A → CurvatureReply d} {b : A → Bool}
    {tape : A → ChordPacketTape Ω L δ} (hz : Measurable z) (hr : Measurable r)
    (hb : Measurable b) (hw : Measurable tape) :
    Measurable (fun a => sampledChordPacket P f Lip s τ ρ δ (z a) (r a) (b a) (tape a)) := by
  have hn := state_measurable_fields.mp (trackedNext_measurable Lip s τ hz hr hb)
  have hm := (tracked_measurable_fields.mp hz).2.2
  have hl := (trackerMemory_measurable_fields.mp hm).1
  have hp := trackerPushPoints_measurable hm hn.1
  apply measurable_pi_lambda
  intro i
  have hi : MeasurableSet {a | i ∈ createdNodes L (z a).memory.length} := by
    simp only [mem_createdNodes]
    exact measurableSet_eq_fun_of_countable measurable_const (hl.add_const 1)
  exact Measurable.ite ((hn.2.1 (measurableSet_singleton true)).inter hi)
    (h.sampleChordAt_measurable (hp.eval (a := nodeLeft i)) (hp.eval (a := nodeRight i)) ρ δ (hw.eval (a := i)))
    measurable_const

theorem CommonLoss.sampledRefreshAnchor_measurable (h : CommonLoss μ P ν F f)
    (q : ℕ) (Lip s τ δ : ℝ) {z : A → TrackedState d L} {r : A → CurvatureReply d} {b : A → Bool}
    {tape : A → LocalDraws Ω (P.gradientNoise^2) (τ/4) δ} (hz : Measurable z) (hr : Measurable r)
    (hb : Measurable b) (hw : Measurable tape) :
    Measurable (fun a => sampledRefreshAnchor P f q Lip s τ δ (z a) (r a) (b a) (tape a)) := by
  have hn := state_measurable_fields.mp (trackedNext_measurable Lip s τ hz hr hb)
  have hbase : Measurable (fun w : Point d × LocalDraws Ω (P.gradientNoise^2) (τ/4) δ =>
      gradientAnchor P f w.1 (τ/4) δ w.2) := h.anchor_joint_measurable (τ/4) δ
  have ha : Measurable (fun a => gradientAnchor P f (trackedNext Lip s τ (z a) (r a) (b a)).point
      (τ/4) δ (tape a)) :=
    hbase.comp (f := fun a : A => ((trackedNext Lip s τ (z a) (r a) (b a)).point,tape a))
      (hn.1.prodMk hw)
  dsimp only [sampledRefreshAnchor]
  exact Measurable.ite ((hn.2.1 (measurableSet_singleton true)).inter (trackedRestart_measurableSet q τ hz hr))
    ha measurable_const

theorem CommonLoss.sampledPostStep_measurable (h : CommonLoss μ P ν F f)
    (q : ℕ) (Lip s τ ρ δ : ℝ) {z : A → TrackedState d L} {r : A → CurvatureReply d} {b : A → Bool}
    {tape : A → PostMoveTape Ω P L τ δ} (hz : Measurable z) (hr : Measurable r)
    (hb : Measurable b) (hw : Measurable tape) :
    Measurable (fun a => sampledPostStep P f q Lip s τ ρ δ (z a) (r a) (b a) (tape a)) :=
  trackedStep_measurable q Lip s τ hz hr hb
    (h.sampledChordPacket_measurable Lip s τ ρ δ hz hr hb hw.fst)
    (h.sampledRefreshAnchor_measurable q Lip s τ δ hz hr hb hw.snd)

theorem CommonLoss.sampledInitial_measurable (h : CommonLoss μ P ν F f) (τ δ : ℝ) :
    Measurable (sampledInitial (L := L) P f τ δ) :=
  trackedInitial_measurable (h.anchor_measurable 0 (τ/4) δ)

theorem CommonLoss.sampledPostFailure_measurableSet (h : CommonLoss μ P ν F f)
    (q : ℕ) (Lip s τ ρ δ : ℝ) {z : A → TrackedState d L} {r : A → CurvatureReply d} {b : A → Bool}
    {tape : A → PostMoveTape Ω P L τ δ} (hz : Measurable z) (hr : Measurable r)
    (hb : Measurable b) (hw : Measurable tape) :
    MeasurableSet {a | sampledPostFailure F P f q Lip s τ ρ δ (z a) (r a) (b a) (tape a)} := by
  have hn := state_measurable_fields.mp (trackedNext_measurable Lip s τ hz hr hb)
  have hm := (tracked_measurable_fields.mp hz).2.2
  have hl := (trackerMemory_measurable_fields.mp hm).1
  have hp := trackerPushPoints_measurable hm hn.1
  have hc := h.sampledChordPacket_measurable Lip s τ ρ δ hz hr hb hw.fst
  have ha := h.sampledRefreshAnchor_measurable q Lip s τ δ hz hr hb hw.snd
  have hg := (contDiff_gradient_one h.population_smooth).continuous.measurable
  simp only [sampledPostFailure,Set.setOf_and,Set.setOf_or,Set.setOf_exists]
  apply (hn.2.1 (measurableSet_singleton true)).inter
  apply MeasurableSet.union
  · apply MeasurableSet.iUnion
    intro i
    have hi : MeasurableSet {a | i ∈ createdNodes L (z a).memory.length} := by
      simp only [mem_createdNodes]
      exact measurableSet_eq_fun_of_countable measurable_const (hl.add_const 1)
    exact hi.inter (measurableSet_lt measurable_const
      ((hc.eval (a := i)).sub ((hg.comp (hp.eval (a := nodeRight i))).sub
        (hg.comp (hp.eval (a := nodeLeft i))))).norm)
  · exact (trackedRestart_measurableSet q τ hz hr).inter
      (measurableSet_lt measurable_const (ha.sub (hg.comp hn.1)).norm)

/-- The actual sampled update preserves the stored tracker invariant when
the requested estimates succeed. No accuracy is demanded of unused tapes. -/
theorem sampledPostStep_consistent (q : ℕ) (Lip s τ ρ δ γ : ℝ) (P : Parameters)
    (f : Ω → Point d → ℝ) (F : Point d → ℝ) (z : TrackedState d L) (r : CurvatureReply d) (b : Bool)
    (w : PostMoveTape Ω P L τ δ) (hz : TrackedConsistent F τ ρ z)
    (hr : z.physical.running = true → ‖trackerRead z.memory‖ ≤ 4*τ → ValidCurvatureReply F γ z.physical.point r)
    (hg : ¬sampledPostFailure F P f q Lip s τ ρ δ z r b w) :
    TrackedConsistent F τ ρ (sampledPostStep P f q Lip s τ ρ δ z r b w) := by
  apply trackedStep_consistent q Lip s z hz
  refine ⟨hr,?_⟩
  intro hrun
  constructor
  · intro i hi
    apply le_of_not_gt
    intro hh
    exact hg ⟨hrun,Or.inl ⟨i,hi,hh⟩⟩
  · intro he
    apply le_of_not_gt
    intro hh
    exact hg ⟨hrun,Or.inr ⟨he,hh⟩⟩

end
end SecondOrder
