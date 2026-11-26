import SecondOrder.OjaTrialOutputLaw
import SecondOrder.ConcatenatedDraws

open MeasureTheory

namespace SecondOrder
noncomputable section

def ojaRepeatedPack {Ω : Type} {d : ℕ} (P : Parameters) (γ δ : ℝ) (n : ℕ)
    (w : Draws (OjaTrialDraws Ω d P γ δ) n) :
    (Fin n → OjaTrialSeed d P γ) × Draws Ω (ojaTrialCallCount P d γ δ*n) :=
  repeatedSamplePack (ojaTrialCallCount P d γ δ) (ojaTrialPacked P γ δ) n w

theorem ojaRepeatedPack_measurePreserving {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (P : Parameters) {d : ℕ} (hd : 0<d)
    {γ : ℝ} (hγ : 0<γ) (δ : ℝ) (n : ℕ) :
    MeasurePreserving (ojaRepeatedPack P γ δ n) (drawsLaw (ojaTrialLaw μ P hd hγ δ) n)
      ((Measure.map (drawsVector id n) (drawsLaw (ojaTrialSeedLaw P hd hγ) n)).prod
        (drawsLaw μ (ojaTrialCallCount P d γ δ*n))) :=
  repeatedSamplePack_measurePreserving _ _ μ _ _ (ojaTrialPacked_measurePreserving μ P hd hγ δ) n

theorem ojaRepeatedProgram_runDraws {Ω : Type} {d : ℕ} (P : Parameters)
    (f : Ω → Point d → ℝ) (a₀ : Ω) (x : Point d) (γ δ : ℝ) (n : ℕ)
    (w : Draws (OjaTrialDraws Ω d P γ δ) n) :
    OracleProgram.runDraws (.grad 0) (fun q z => hvpReply f z q)
      (ojaRepeatedProgram P x γ δ n (ojaRepeatedPack P γ δ n w).1)
      (ojaTrialCallCount P d γ δ*n) (ojaRepeatedPack P γ δ n w).2=
        .done (firstNegative (ojaTrialReply P f x γ δ) n w) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hN : OracleProgram.UsesExactly (ojaTrialCallCount P d γ δ*n)
        (ojaRepeatedProgram P x γ δ n (ojaRepeatedPack P γ δ n w.1).1) := by
      simpa only [Nat.mul_comm] using ojaRepeatedProgram_usesExactly P x γ δ n (ojaRepeatedPack P γ δ n w.1).1
    have hp := OracleProgram.runDraws_bind_of_exact (HvpQuery.grad (0 : Point d))
      (fun q z => hvpReply f z q) a₀ hN
      (fun old => (ojaTrialProgram P x γ δ (ojaTrialPacked P γ δ w.2).1).bind
        (fun new => .done (preferNegative old new))) (ojaRepeatedPack P γ δ n w.1).2 (ih w.1)
      (ojaTrialCallCount P d γ δ) (ojaTrialPacked P γ δ w.2).2
    have hl := OracleProgram.runDraws_bind_of_exact (HvpQuery.grad (0 : Point d))
      (fun q z => hvpReply f z q) a₀ (ojaTrialProgram_usesExactly P x γ δ (ojaTrialPacked P γ δ w.2).1)
      (fun new => .done (preferNegative (firstNegative (ojaTrialReply P f x γ δ) n w.1) new))
      (ojaTrialPacked P γ δ w.2).2 (ojaTrialProgram_runDraws P f a₀ x γ δ w.2) 0 PUnit.unit
    simpa only [ojaRepeatedPack,repeatedSamplePack_succ,ojaRepeatedProgram,
      Fin.snoc_castSucc,Fin.snoc_last] using hp.trans hl

theorem CommonLoss.ojaRepeatedProgram_outputLaw {Ω : Type} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {P : Parameters} {d : ℕ} {ν : ℝ}
    {F : Point d → ℝ} {f : Ω → Point d → ℝ} (h : CommonLoss μ P ν F f)
    (a₀ : Ω) (hd : 0<d) {γ : ℝ} (hγ : 0<γ) (δ : ℝ) (n : ℕ) (x : Point d) :
    OracleProgram.seededOutputLaw μ
      (Measure.map (drawsVector id n) (drawsLaw (ojaTrialSeedLaw P hd hγ) n)) (.grad 0) .certificate
      (fun q z => hvpReply f z q) (ojaRepeatedProgram P x γ δ n) (ojaTrialCallCount P d γ δ*n)=
      Measure.map (firstNegative (ojaTrialReply P f x γ δ) n) (drawsLaw (ojaTrialLaw μ P hd hγ δ) n) := by
  have hp := (ojaRepeatedProgram_measurable (d := d) P γ δ n).comp
    (fun s : Fin n → OjaTrialSeed d P γ => (x,s)) (measurable_const.prodMk measurable_id)
  have hm := hp.runDrawsOutput 0 a₀ (fun q z => hvpReply f z q) h.hvpReply_joint_measurable
    (ojaTrialCallCount P d γ δ*n)
  have ht := ojaRepeatedPack_measurePreserving μ P hd hγ δ n
  unfold OracleProgram.seededOutputLaw
  rw [←ht.map_eq,Measure.map_map hm ht.measurable]
  congr 1
  funext w
  simp only [Function.comp_apply,ojaRepeatedProgram_runDraws P f a₀,OracleProgram.output]

/-- The complete amplified reply program has exactly the output law used
in the original Oja confidence proof, with an instance-independent seed. -/
theorem CommonLoss.ojaAmplifiedProgram_outputLaw {Ω : Type} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {P : Parameters} {d : ℕ} {ν : ℝ}
    {F : Point d → ℝ} {f : Ω → Point d → ℝ} (h : CommonLoss μ P ν F f)
    (a₀ : Ω) (hd : 0<d) {γ : ℝ} (hγ : 0<γ) (δ : ℝ) (x : Point d) :
    OracleProgram.seededOutputLaw μ (ojaAmplifiedSeedLaw P hd hγ δ) (.grad 0) .certificate
      (fun q z => hvpReply f z q) (ojaAmplifiedProgram P x γ δ) (ojaAmplifiedQueryCount P d γ δ)=
      Measure.map (ojaAmplifiedReply P f x γ δ) (ojaAmplifiedLaw μ P hd hγ δ) := by
  simpa only [ojaAmplifiedSeedLaw,ojaAmplifiedLaw,ojaAmplifiedProgram,ojaAmplifiedReply,
    ojaAmplifiedQueryCount,ojaTrialCallCount,Nat.mul_comm] using
    h.ojaRepeatedProgram_outputLaw a₀ hd hγ (ojaValidationFailure δ) (ojaRepeats δ) x

end
end SecondOrder
