import SecondOrder.PostReservationOutputLaw

open MeasureTheory ProbabilityTheory

namespace SecondOrder
noncomputable section

variable {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {P : Parameters} {d L : ℕ} {ν : ℝ} {F : Point d → ℝ} {f : Ω → Point d → ℝ}

theorem CommonLoss.signedPostReservation_outputLaw (h : CommonLoss μ P ν F f)
    (a₀ : Ω) (q Q : ℕ) (Lip s τ ρ γ δ : ℝ) (z : BudgetTracker d L)
    (r : CurvatureReply d) (os : BranchedOjaSeed d P γ δ) :
    OracleProgram.seededOutputLaw μ
      ((PMF.uniformOfFintype Bool).toMeasure.prod (postChordSeedLaw L δ))
      (.grad 0) (trackedInitial 0,0,true) (fun q a => hvpReply f a q)
      (fun w : Bool × PostChordSeed L δ => postReservationProgram P q Q Lip s τ ρ γ δ (z,os,w.1,w.2) r) Q=
      Measure.map (fun w : Bool × PostMoveTape Ω P L τ δ =>
        sampledPostReservation P f q Q (branchedOjaQueryCount P d γ δ) Lip s τ ρ δ z r w.1 w.2)
        ((PMF.uniformOfFintype Bool).toMeasure.prod (postMoveLaw μ P L τ δ)) := by
  let pf := fun w : Bool × PostChordSeed L δ =>
    postReservationProgram P q Q Lip s τ ρ γ δ (z,os,w.1,w.2) r
  have hpf : OracleProgram.MeasurableFamily (.grad 0) (trackedInitial 0,0,true) pf :=
    (postReservationProgram_measurable P q Q Lip s τ ρ γ δ).comp
      (fun w : Bool × PostChordSeed L δ => ((z,os,w.1,w.2),r))
      ((measurable_const.prodMk (measurable_const.prodMk (measurable_fst.prodMk measurable_snd))).prodMk
        measurable_const)
  let step := fun (b : Bool) (w : PostMoveTape Ω P L τ δ) =>
    sampledPostReservation P f q Q (branchedOjaQueryCount P d γ δ) Lip s τ ρ δ z r b w
  have hs : Measurable (fun w : Bool × PostMoveTape Ω P L τ δ => step w.1 w.2) :=
    h.sampledPostReservation_measurable q Q _ Lip s τ ρ δ
      measurable_const measurable_const measurable_fst measurable_snd
  let K := sampledResponseKernel (postMoveLaw μ P L τ δ) step hs
  have hk : (OracleProgram.seededOutputKernel μ (postChordSeedLaw L δ) (.grad 0) 0
      ((trackedInitial 0,0,true) : BudgetTracker d L) a₀ (fun q a => hvpReply f a q)
      h.hvpReply_joint_measurable pf hpf Q : Bool → Measure (BudgetTracker d L))=K := by
    funext b
    exact h.postReservationProgram_slice_outputLaw a₀ q Q Lip s τ ρ γ δ z r b os
  have hh := OracleProgram.seededOutputLaw_prod_eq_bind μ (PMF.uniformOfFintype Bool).toMeasure
    (postChordSeedLaw L δ) (.grad 0) 0 ((trackedInitial 0,0,true) : BudgetTracker d L) a₀
    (fun q a => hvpReply f a q) h.hvpReply_joint_measurable pf hpf Q
  rw [hk] at hh
  have hm := map_bind_sampledResponse (PMF.uniformOfFintype Bool).toMeasure
    (postMoveLaw μ P L τ δ) id measurable_id step hs
  rw [Measure.map_id] at hm
  exact hh.trans hm

end
end SecondOrder
