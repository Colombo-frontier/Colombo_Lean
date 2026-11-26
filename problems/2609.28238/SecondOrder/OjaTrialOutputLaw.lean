import SecondOrder.LocalSampleEnumeration
import SecondOrder.OjaSeedIndependence
import SecondOrder.OracleProgramLawComposition
import SecondOrder.OracleSuccessProbability
import SecondOrder.DrawsAppendCoordinates

open MeasureTheory

namespace SecondOrder
noncomputable section

def ojaTrialSampleBlock {Ω : Type} {d : ℕ} (P : Parameters) (γ δ : ℝ)
    (w : OjaTrialSamples Ω d P γ δ) : Draws Ω (ojaTrialCallCount P d γ δ) :=
  drawsAppend _ _ w.1 (localEnumeratedDraws (P.hessianBound^2) (γ/8) δ w.2)

theorem ojaTrialSampleBlock_measurePreserving {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (P : Parameters) (d : ℕ) (γ δ : ℝ) :
    MeasurePreserving (ojaTrialSampleBlock (d := d) P γ δ) (ojaTrialSamplesLaw μ P d γ δ)
      (drawsLaw μ (ojaTrialCallCount P d γ δ)) :=
  (drawsAppend_measurePreserving μ _ _).comp
    ((MeasurePreserving.id _).prod (localEnumeratedDraws_measurePreserving μ (P.hessianBound^2) (γ/8) δ))

def ojaTrialPacked {Ω : Type} {d : ℕ} (P : Parameters) (γ δ : ℝ)
    (w : OjaTrialDraws Ω d P γ δ) : OjaTrialSeed d P γ × Draws Ω (ojaTrialCallCount P d γ δ) :=
  ((w.1.1.2,w.1.2),drawsAppend (ojaIterationCount d (ojaCurvatureTolerance P γ))
    (localQueryCount (P.hessianBound^2) (γ/8) δ) w.1.1.1
      (localEnumeratedDraws (P.hessianBound^2) (γ/8) δ w.2))

theorem ojaTrialPacked_seed {Ω : Type} {d : ℕ} (P : Parameters) (γ δ : ℝ)
    (w : OjaTrialDraws Ω d P γ δ) : (ojaTrialPacked P γ δ w).1=(w.1.1.2,w.1.2) := rfl

theorem ojaTrialPacked_samples {Ω : Type} {d : ℕ} (P : Parameters) (γ δ : ℝ)
    (w : OjaTrialDraws Ω d P γ δ) :
    (ojaTrialPacked P γ δ w).2=drawsAppend (ojaIterationCount d (ojaCurvatureTolerance P γ))
      (localQueryCount (P.hessianBound^2) (γ/8) δ) w.1.1.1
        (localEnumeratedDraws (P.hessianBound^2) (γ/8) δ w.2) := rfl

theorem ojaTrialPacked_measurePreserving {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (P : Parameters) {d : ℕ} (hd : 0<d)
    {γ : ℝ} (hγ : 0<γ) (δ : ℝ) :
    MeasurePreserving (ojaTrialPacked P γ δ) (ojaTrialLaw μ P hd hγ δ)
      ((ojaTrialSeedLaw P hd hγ).prod (drawsLaw μ (ojaTrialCallCount P d γ δ))) :=
  ((MeasurePreserving.id _).prod (ojaTrialSampleBlock_measurePreserving μ P d γ δ)).comp
    (ojaTrialSplit_measurePreserving μ P hd hγ δ)

theorem ojaCandidateProgram_runDraws {Ω : Type} {d : ℕ} (P : Parameters)
    (f : Ω → Point d → ℝ) (a₀ : Ω) (η : ℝ) (x : Point d) (N : ℕ)
    (w : (Draws Ω N × (Fin d → Bool)) × Fin N) :
    OracleProgram.runDraws (.grad 0) (fun q z => hvpReply f z q)
      (ojaCandidateProgram P η x N w.1.2 w.2) N w.1.1=.done (ojaCandidate P f η x N w) := by
  have he := OracleProgram.run_eq_runDraws (HvpQuery.grad (0 : Point d))
    (fun q z => hvpReply f z q) (drawsTape a₀ N w.1.1)
    (ojaCandidateProgram P η x N w.1.2 w.2) N w.1.1 (drawsTape_apply a₀ N w.1.1)
  exact he.symm.trans (ojaCandidateProgram_run P f η x N w _ (drawsTape_apply a₀ N w.1.1))

theorem rayleighValidationProgram_runDraws {Ω : Type} {d : ℕ} (P : Parameters)
    (f : Ω → Point d → ℝ) (a₀ : Ω) (x v : Point d) (γ δ : ℝ)
    (w : LocalDraws Ω (P.hessianBound^2) (γ/8) δ) :
    OracleProgram.runDraws (.grad 0) (fun q z => hvpReply f z q)
      (rayleighValidationProgram P x v γ δ) (localQueryCount (P.hessianBound^2) (γ/8) δ)
      (localEnumeratedDraws (P.hessianBound^2) (γ/8) δ w)=.done (rayleighValidatedReply P f x v γ δ w) := by
  have he := OracleProgram.run_eq_runDraws (HvpQuery.grad (0 : Point d))
    (fun q z => hvpReply f z q) (drawsTape a₀ _ (localEnumeratedDraws _ _ _ w))
    (rayleighValidationProgram P x v γ δ) _ (localEnumeratedDraws _ _ _ w) (drawsTape_apply a₀ _ _)
  exact he.symm.trans (rayleighValidationProgram_run P f x v γ δ w _ (localEnumeratedDraws_tape a₀ _ _ _ w))

/-- The packed sample block is consumed in chronological order: candidate
generation first, independent Rayleigh validation next. -/
theorem ojaTrialProgram_runDraws {Ω : Type} {d : ℕ} (P : Parameters)
    (f : Ω → Point d → ℝ) (a₀ : Ω) (x : Point d) (γ δ : ℝ) (w : OjaTrialDraws Ω d P γ δ) :
    OracleProgram.runDraws (.grad 0) (fun q z => hvpReply f z q)
      (ojaTrialProgram P x γ δ (ojaTrialPacked P γ δ w).1) (ojaTrialCallCount P d γ δ)
        (ojaTrialPacked P γ δ w).2=.done (ojaTrialReply P f x γ δ w) := by
  rw [ojaTrialPacked_seed,ojaTrialPacked_samples]
  let block := drawsAppend (ojaIterationCount d (ojaCurvatureTolerance P γ))
    (localQueryCount (P.hessianBound^2) (γ/8) δ) w.1.1.1 (localEnumeratedDraws _ _ _ w.2)
  let zs := drawsTape a₀ _ block
  have he := OracleProgram.run_eq_runDraws (HvpQuery.grad (0 : Point d))
    (fun q z => hvpReply f z q) zs (ojaTrialProgram P x γ δ (w.1.1.2,w.1.2))
    (ojaTrialCallCount P d γ δ) block (drawsTape_apply a₀ _ _)
  apply he.symm.trans
  apply ojaTrialProgram_run P f x γ δ w zs
  · intro i
    exact drawsTape_append_left a₀ _ _ w.1.1.1 (localEnumeratedDraws _ _ _ w.2) i
  · intro i
    exact (drawsTape_append_right a₀ _ _ w.1.1.1 (localEnumeratedDraws _ _ _ w.2)
      (localReplyEnumeration _ _ _ i)).trans (localEnumeratedDraws_sample _ _ _ w.2 i)

theorem CommonLoss.ojaTrialProgram_outputLaw {Ω : Type} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {P : Parameters} {d : ℕ} {ν : ℝ}
    {F : Point d → ℝ} {f : Ω → Point d → ℝ} (h : CommonLoss μ P ν F f)
    (a₀ : Ω) (hd : 0<d) {γ : ℝ} (hγ : 0<γ) (δ : ℝ) (x : Point d) :
    OracleProgram.seededOutputLaw μ (ojaTrialSeedLaw P hd hγ) (.grad 0) .certificate
      (fun q z => hvpReply f z q) (ojaTrialProgram P x γ δ) (ojaTrialCallCount P d γ δ)=
      Measure.map (ojaTrialReply P f x γ δ) (ojaTrialLaw μ P hd hγ δ) := by
  have hp := (ojaTrialProgram_measurable (d := d) P γ δ).comp
    (fun s : OjaTrialSeed d P γ => (x,s)) (measurable_const.prodMk measurable_id)
  have hm := hp.runDrawsOutput 0 a₀ (fun q z => hvpReply f z q) h.hvpReply_joint_measurable
    (ojaTrialCallCount P d γ δ)
  have ht := ojaTrialPacked_measurePreserving μ P hd hγ δ
  unfold OracleProgram.seededOutputLaw
  rw [←ht.map_eq,Measure.map_map hm ht.measurable]
  congr 1
  funext w
  simp only [Function.comp_apply,ojaTrialProgram_runDraws P f a₀,OracleProgram.output]

end
end SecondOrder
