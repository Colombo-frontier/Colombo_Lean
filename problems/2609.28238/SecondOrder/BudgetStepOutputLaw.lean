import SecondOrder.SignedReservationLaw

open MeasureTheory ProbabilityTheory
open scoped Classical

namespace SecondOrder
noncomputable section

abbrev OrderedStepTape (Ω : Type) (d L : ℕ) (P : Parameters) (γ τ δ : ℝ) :=
  Prod (BranchedOjaDraws Ω d P γ δ : Type) (Prod Bool (PostMoveTape Ω P L τ δ))

def orderedStepLaw {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (P : Parameters) (d L : ℕ) {γ : ℝ} (hγ : 0<γ) (τ δ : ℝ) :
    Measure (OrderedStepTape Ω d L P γ τ δ) :=
  (branchedOjaLaw μ P d hγ δ).prod
    ((PMF.uniformOfFintype Bool).toMeasure.prod (postMoveLaw μ P L τ δ))

instance orderedStepLaw_probability {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (P : Parameters) (d L : ℕ) {γ : ℝ} (hγ : 0<γ) (τ δ : ℝ) :
    IsProbabilityMeasure (orderedStepLaw μ P d L hγ τ δ) := by
  unfold orderedStepLaw
  infer_instance

variable {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {P : Parameters} {d L : ℕ} {ν : ℝ} {F : Point d → ℝ} {f : Ω → Point d → ℝ}

theorem CommonLoss.budgetStepProgram_outputLaw (h : CommonLoss μ P ν F f)
    (a₀ : Ω) (q Q : ℕ) (Lip s τ ρ : ℝ) {γ : ℝ} (hγ : 0<γ) (δ : ℝ) (z : BudgetTracker d L) :
    OracleProgram.seededOutputLaw μ (trackingProgramSeedLaw P d L hγ δ) (.grad 0)
      (trackedInitial 0,0,true) (fun q a => hvpReply f a q)
      (fun seeds => budgetStepProgram P q Q Lip s τ ρ γ δ (z,seeds)) Q=
      Measure.map (fun w : OrderedStepTape Ω d L P γ τ δ =>
        budgetedTrackedStep P f q Q (branchedOjaQueryCount P d γ δ) Lip s τ ρ δ
          (fun x a => branchedOjaReply P f x γ δ a) z w.2.1 (w.1,w.2.2))
        (orderedStepLaw μ P d L hγ τ δ) := by
  let c := curvatureRequestPrice τ (branchedOjaQueryCount P d γ δ) z.1
  let η := (PMF.uniformOfFintype Bool).toMeasure.prod (postChordSeedLaw L δ)
  let θ := (PMF.uniformOfFintype Bool).toMeasure.prod (postMoveLaw μ P L τ δ)
  by_cases hz : z.2.2=true
  · have he : (fun seeds => budgetStepProgram P q Q Lip s τ ρ γ δ (z,seeds))=
        (fun _ : TrackingProgramSeed d L P γ δ => .done z) := by
      funext seeds
      exact if_pos hz
    rw [he,OracleProgram.seededOutputLaw_done]
    have ht : (fun w : OrderedStepTape Ω d L P γ τ δ =>
        budgetedTrackedStep P f q Q (branchedOjaQueryCount P d γ δ) Lip s τ ρ δ
          (fun x a => branchedOjaReply P f x γ δ a) z w.2.1 (w.1,w.2.2))=(fun _ => z) := by
      funext w
      exact if_pos hz
    rw [ht]
    simp
  · by_cases hc : z.2.1+c≤Q
    · let p := fun os => requestedOjaProgram P τ γ δ (z.1,os)
      let pf := fun w : CurvatureReply d × (Bool × PostChordSeed L δ) =>
        postReservationProgram P q Q Lip s τ ρ γ δ (z,Sum.inl PUnit.unit,w.2.1,w.2.2) w.1
      have hp : OracleProgram.MeasurableFamily (.grad 0) .certificate p :=
        (requestedOjaProgram_measurable P τ γ δ).comp _ (measurable_const.prodMk measurable_id)
      have hpf : OracleProgram.MeasurableFamily (.grad 0) (trackedInitial 0,0,true) pf :=
        (postReservationProgram_measurable P q Q Lip s τ ρ γ δ).comp
          (fun w : CurvatureReply d × (Bool × PostChordSeed L δ) =>
            ((z,Sum.inl PUnit.unit,w.2.1,w.2.2),w.1))
          ((measurable_const.prodMk (measurable_const.prodMk
            (measurable_snd.fst.prodMk measurable_snd.snd))).prodMk measurable_fst)
      have hN : ∀ os, OracleProgram.UsesAtMost c (p os) := by
        intro os
        exact requestedOjaProgram_usesAtMost P τ γ δ (z.1,os)
      have hM : ∀ w, OracleProgram.UsesAtMost Q (pf w) := by
        intro w
        exact OracleProgram.usesAtMost_mono
          (postReservationProgram_credit P q Q Lip s τ ρ γ δ
            (z,Sum.inl PUnit.unit,w.2.1,w.2.2) w.1).usesAtMost (by omega)
      have hcomp := OracleProgram.seededOutputLaw_bind_of_usesAtMost μ
        (branchedOjaSeedLaw P d hγ δ) η (.grad 0) 0 .certificate
        ((trackedInitial 0,0,true) : BudgetTracker d L) a₀ (fun q a => hvpReply f a q)
        h.hvpReply_joint_measurable p hp c hN pf hpf Q hM
      let step := fun (r : CurvatureReply d) (w : Bool × PostMoveTape Ω P L τ δ) =>
        sampledPostReservation P f q Q (branchedOjaQueryCount P d γ δ) Lip s τ ρ δ z r w.1 w.2
      have hs : Measurable (fun w : CurvatureReply d × (Bool × PostMoveTape Ω P L τ δ) =>
          step w.1 w.2) := h.sampledPostReservation_measurable q Q _ Lip s τ ρ δ
        measurable_const measurable_fst measurable_snd.fst measurable_snd.snd
      let K := sampledResponseKernel θ step hs
      have hk : (OracleProgram.seededOutputKernel μ η (.grad 0) 0
          ((trackedInitial 0,0,true) : BudgetTracker d L) a₀ (fun q a => hvpReply f a q)
          h.hvpReply_joint_measurable pf hpf Q : CurvatureReply d → Measure (BudgetTracker d L))=K := by
        funext r
        exact h.signedPostReservation_outputLaw a₀ q Q Lip s τ ρ γ δ z r (Sum.inl PUnit.unit)
      rw [hk] at hcomp
      have ho := h.requestedOjaProgram_outputLaw a₀ τ hγ δ z.1
      change OracleProgram.seededOutputLaw μ (branchedOjaSeedLaw P d hγ δ) (.grad 0) .certificate
        (fun q a => hvpReply f a q) p c=_ at ho
      rw [ho] at hcomp
      have hm : Measurable (fun a : (BranchedOjaDraws Ω d P γ δ : Type) =>
          sampledCurvature τ (fun x a => branchedOjaReply P f x γ δ a) z.1 a) :=
        sampledCurvature_measurable τ (h.branchedOjaReply_measurable γ δ)
          measurable_const measurable_id
      have hmap := map_bind_sampledResponse (branchedOjaLaw μ P d hγ δ) θ
        (fun a : (BranchedOjaDraws Ω d P γ δ : Type) =>
          sampledCurvature τ (fun x a => branchedOjaReply P f x γ δ a) z.1 a) hm step hs
      have he : (fun seeds => budgetStepProgram P q Q Lip s τ ρ γ δ (z,seeds))=
          (fun seeds : TrackingProgramSeed d L P γ δ =>
            OracleProgram.bind (p seeds.1) (fun r => pf (r,seeds.2))) := by
        funext seeds
        simp only [budgetStepProgram,hz,Bool.false_eq_true,↓reduceIte,show z.2.1+
          curvatureRequestPrice τ (branchedOjaQueryCount P d γ δ) z.1≤Q from hc]
        rfl
      have hfull := (budgetStepProgram_measurable (d := d) (L := L) P q Q Lip s τ ρ γ δ).comp
        (fun seeds => (z,seeds)) (measurable_const.prodMk measurable_id)
      have hQ : ∀ seeds, OracleProgram.UsesAtMost Q (budgetStepProgram P q Q Lip s τ ρ γ δ (z,seeds)) := by
        intro seeds
        exact OracleProgram.usesAtMost_mono
          (budgetStepProgram_credit P q Q Lip s τ ρ γ δ (z,seeds)).usesAtMost (Nat.sub_le _ _)
      have hpad := OracleProgram.seededOutputLaw_of_budget_le μ (trackingProgramSeedLaw P d L hγ δ)
        (.grad 0) 0 ((trackedInitial 0,0,true) : BudgetTracker d L) a₀ (fun q a => hvpReply f a q)
        h.hvpReply_joint_measurable _ hfull Q hQ (c+Q) (by omega)
      rw [he] at hpad ⊢
      refine hpad.symm.trans (hcomp.trans (hmap.trans ?_))
      apply congrArg (fun k : OrderedStepTape Ω d L P γ τ δ → BudgetTracker d L =>
        Measure.map k (orderedStepLaw μ P d L hγ τ δ))
      funext w
      simp only [budgetedTrackedStep,hz,Bool.false_eq_true,↓reduceIte,show z.2.1+
        curvatureRequestPrice τ (branchedOjaQueryCount P d γ δ) z.1≤Q from hc]
      rfl
    · have he : (fun seeds => budgetStepProgram P q Q Lip s τ ρ γ δ (z,seeds))=
          (fun _ : TrackingProgramSeed d L P γ δ => .done ((z.1,z.2.1,true) : BudgetTracker d L)) := by
        funext seeds
        simp only [budgetStepProgram,hz,Bool.false_eq_true,↓reduceIte,show ¬z.2.1+
          curvatureRequestPrice τ (branchedOjaQueryCount P d γ δ) z.1≤Q from hc]
      have ht : (fun w : OrderedStepTape Ω d L P γ τ δ =>
          budgetedTrackedStep P f q Q (branchedOjaQueryCount P d γ δ) Lip s τ ρ δ
            (fun x a => branchedOjaReply P f x γ δ a) z w.2.1 (w.1,w.2.2))=
          (fun _ => ((z.1,z.2.1,true) : BudgetTracker d L)) := by
        funext w
        simp only [budgetedTrackedStep,hz,Bool.false_eq_true,↓reduceIte,show ¬z.2.1+
          curvatureRequestPrice τ (branchedOjaQueryCount P d γ δ) z.1≤Q from hc]
      rw [he,ht,OracleProgram.seededOutputLaw_done]
      simp

end
end SecondOrder
