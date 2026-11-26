import SecondOrder.LocalPrivateSeeds

open MeasureTheory

namespace SecondOrder
noncomputable section

def freshChordProgram {d : ℕ} (P : Parameters) (x y : Point d) (ρ δ : ℝ)
    (us : LocalReplySlot (chordVariance P x y) ρ δ → ℝ) :
    OracleProgram (HvpQuery d) (Point d) (Point d) :=
  localReplyProgram (chordVariance P x y) ρ δ (fun i => .hvp (x+us i•(y-x)) (y-x))

theorem freshChordQueries_measurable {d : ℕ} (P : Parameters) (x y : Point d) (ρ δ : ℝ)
    (i : LocalReplySlot (chordVariance P x y) ρ δ) :
    Measurable (fun us : LocalReplySlot (chordVariance P x y) ρ δ → ℝ =>
      (HvpQuery.hvp (x+us i•(y-x)) (y-x))) := by
  have hx : Measurable (fun us : LocalReplySlot (chordVariance P x y) ρ δ → ℝ => x+us i•(y-x)) :=
    measurable_const.add ((measurable_pi_apply i).smul_const (y-x))
  exact (hvpQueryMeasurableEquiv d).symm.measurable.comp
    (measurable_inr.comp (hx.prodMk measurable_const))

theorem freshChordProgram_measurable {d : ℕ} (P : Parameters) (x y : Point d) (ρ δ : ℝ) :
    OracleProgram.MeasurableFamily (.grad 0) 0 (freshChordProgram P x y ρ δ) :=
  localReplyProgram_measurable _ ρ δ _ (freshChordQueries_measurable P x y ρ δ)

theorem freshChordProgram_usesExactly {d : ℕ} (P : Parameters) (x y : Point d) (ρ δ : ℝ)
    (us : LocalReplySlot (chordVariance P x y) ρ δ → ℝ) :
    OracleProgram.UsesExactly (localQueryCount (chordVariance P x y) ρ δ)
      (freshChordProgram P x y ρ δ us) :=
  localReplyProgram_usesExactly _ ρ δ _

variable {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {P : Parameters} {d : ℕ} {ν : ℝ} {F : Point d → ℝ} {f : Ω → Point d → ℝ}

theorem CommonLoss.freshChordProgram_outputLaw (h : CommonLoss μ P ν F f)
    (a₀ : Ω) (x y : Point d) (ρ δ : ℝ) :
    OracleProgram.seededOutputLaw μ
      (Measure.pi (fun _ : LocalReplySlot (chordVariance P x y) ρ δ => unitLine))
      (.grad 0) 0 (fun q z => hvpReply f z q) (freshChordProgram P x y ρ δ)
      (localQueryCount (chordVariance P x y) ρ δ)=
      Measure.map (freshChord P f x y ρ δ) (localLaw (unitLine.prod μ) (chordVariance P x y) ρ δ) := by
  have hh := localReplyProgram_private_outputLaw unitLine μ (chordVariance P x y) ρ δ
    (fun us i => HvpQuery.hvp (x+us i•(y-x)) (y-x)) (freshChordQueries_measurable P x y ρ δ)
    (fun q z => hvpReply f z q) h.hvpReply_joint_measurable a₀
  unfold freshChordProgram
  rw [hh]
  apply congrArg (fun g : LocalDraws (ℝ × Ω) (chordVariance P x y) ρ δ → Point d =>
    Measure.map g (localLaw (unitLine.prod μ) (chordVariance P x y) ρ δ))
  funext w
  exact (freshEstimate_eq_localReplyCenter (randomLineHvp f x y) (chordVariance P x y) ρ δ w).symm

theorem CommonLoss.freshChordProgram_confidence (h : CommonLoss μ P ν F f)
    (a₀ : Ω) (x y : Point d) {ρ δ : ℝ} (hρ : 0<ρ) (hδ : 0<δ) :
    (OracleProgram.seededOutputLaw μ
      (Measure.pi (fun _ : LocalReplySlot (chordVariance P x y) ρ δ => unitLine))
      (.grad 0) 0 (fun q z => hvpReply f z q) (freshChordProgram P x y ρ δ)
      (localQueryCount (chordVariance P x y) ρ δ))
      {g | ρ<‖g-(gradient F y-gradient F x)‖}≤ENNReal.ofReal δ := by
  have hs : MeasurableSet {g : Point d | ρ<‖g-(gradient F y-gradient F x)‖} :=
    measurableSet_lt measurable_const (measurable_id.sub_const _).norm
  rw [h.freshChordProgram_outputLaw a₀ x y ρ δ,
    Measure.map_apply (h.chord_measurable x y ρ δ) hs]
  exact h.chord_confidence x y hρ hδ

theorem CommonLoss.gradientAnchorProgram_confidence (h : CommonLoss μ P ν F f)
    (a₀ : Ω) (x : Point d) {ρ δ : ℝ} (hρ : 0<ρ) (hδ : 0<δ) :
    (OracleProgram.outputLaw μ (.grad 0) 0 (fun q z => hvpReply f z q)
      (gradientAnchorProgram P x ρ δ) (localQueryCount (P.gradientNoise^2) ρ δ))
      {g | ρ<‖g-gradient F x‖}≤ENNReal.ofReal δ := by
  have hs : MeasurableSet {g : Point d | ρ<‖g-gradient F x‖} :=
    measurableSet_lt measurable_const (measurable_id.sub_const _).norm
  rw [h.gradientAnchorProgram_outputLaw a₀ x ρ δ,Measure.map_apply (h.anchor_measurable x ρ δ) hs]
  exact h.anchor_confidence x hρ hδ

end
end SecondOrder
