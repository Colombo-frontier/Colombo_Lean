import SecondOrder.RayleighReplyProgram

open MeasureTheory
open scoped Classical

namespace SecondOrder
noncomputable section

abbrev OjaTrialSeed (d : ℕ) (P : Parameters) (γ : ℝ) :=
  (Fin d → Bool) × Fin (ojaIterationCount d (ojaCurvatureTolerance P γ))

def ojaTrialSeedLaw (P : Parameters) {d : ℕ} (hd : 0<d) {γ : ℝ} (hγ : 0<γ) :
    Measure (OjaTrialSeed d P γ) := by
  letI : NeZero (ojaIterationCount d (ojaCurvatureTolerance P γ)) :=
    ⟨(ojaIterationCount_pos hd (ojaCurvatureTolerance_pos P hγ)).ne'⟩
  exact (signLaw d).prod (PMF.uniformOfFintype _).toMeasure

instance ojaTrialSeedLaw_probability (P : Parameters) {d : ℕ} (hd : 0<d) {γ : ℝ} (hγ : 0<γ) :
    IsProbabilityMeasure (ojaTrialSeedLaw P hd hγ) := by
  unfold ojaTrialSeedLaw
  infer_instance

def ojaTrialCallCount (P : Parameters) (d : ℕ) (γ δ : ℝ) : ℕ :=
  ojaIterationCount d (ojaCurvatureTolerance P γ)+localQueryCount (P.hessianBound^2) (γ/8) δ

/-- The random seed contains only signs and the independently chosen
candidate index; all sample information arrives through HVP replies. -/
def ojaTrialProgram {d : ℕ} (P : Parameters) (x : Point d) (γ δ : ℝ) (s : OjaTrialSeed d P γ) :
    OracleProgram (HvpQuery d) (Point d) (CurvatureReply d) :=
  (ojaCandidateProgram P (ojaLearningRate d (ojaCurvatureTolerance P γ)) x
    (ojaIterationCount d (ojaCurvatureTolerance P γ)) s.1 s.2).bind
      (fun v => rayleighValidationProgram P x v γ δ)

theorem ojaTrialProgram_usesExactly {d : ℕ} (P : Parameters) (x : Point d) (γ δ : ℝ)
    (s : OjaTrialSeed d P γ) : OracleProgram.UsesExactly (ojaTrialCallCount P d γ δ)
      (ojaTrialProgram P x γ δ s) :=
  (ojaCandidateProgram_usesExactly P _ x _ s.1 s.2).bind _
    (fun v => rayleighValidationProgram_usesExactly P x v γ δ)

theorem ojaTrialProgram_measurable {d : ℕ} (P : Parameters) (γ δ : ℝ) :
    OracleProgram.MeasurableFamily (.grad 0) .certificate
      (fun w : Point d × OjaTrialSeed d P γ => ojaTrialProgram P w.1 γ δ w.2) := by
  apply (ojaCandidateProgram_measurable (d := d) P _ _).bind
  exact (rayleighValidationProgram_measurable (d := d) P γ δ).comp
    (fun w : (Point d × OjaTrialSeed d P γ) × Point d => (w.1.1,w.2))
    (measurable_fst.fst.prodMk measurable_snd)

theorem ojaTrialProgram_run {Ω : Type} {d : ℕ} (P : Parameters)
    (f : Ω → Point d → ℝ) (x : Point d) (γ δ : ℝ)
    (w : OjaTrialDraws Ω d P γ δ) (zs : ℕ → Ω)
    (hgen : ∀ i : Fin (ojaIterationCount d (ojaCurvatureTolerance P γ)),
      zs i=drawsVector id _ w.1.1.1 i)
    (hval : ∀ i : RayleighSlot P (γ/8) δ,
      zs (ojaIterationCount d (ojaCurvatureTolerance P γ)+(Fintype.equivFin _ i:ℕ))=
        (rayleighSampleCall P x (ojaTrialCandidate P f x γ w.1) (γ/8) δ w.2 i).1) :
    OracleProgram.run (.grad 0) (fun q z => hvpReply f z q) zs
      (ojaTrialProgram P x γ δ (w.1.1.2,w.1.2)) (ojaTrialCallCount P d γ δ)=
        .done (ojaTrialReply P f x γ δ w) := by
  have hfirst := ojaCandidateProgram_run P f (ojaLearningRate d (ojaCurvatureTolerance P γ)) x
    (ojaIterationCount d (ojaCurvatureTolerance P γ)) w.1 zs hgen
  rw [ojaTrialProgram,ojaTrialCallCount,OracleProgram.run_bind_of_exact (.grad 0) _ zs
    (ojaCandidateProgram_usesExactly P _ x _ w.1.1.2 w.1.2) _ hfirst]
  exact rayleighValidationProgram_run P f x (ojaTrialCandidate P f x γ w.1) γ δ w.2
    (fun i => zs (ojaIterationCount d (ojaCurvatureTolerance P γ)+i)) hval

end
end SecondOrder
