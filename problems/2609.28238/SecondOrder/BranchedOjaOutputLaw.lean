import SecondOrder.OjaRepeatedOutputLaw
import SecondOrder.OracleSeedTransport

open MeasureTheory
open scoped Classical

namespace SecondOrder
noncomputable section

variable {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {P : Parameters} {d : ℕ} {ν : ℝ} {F : Point d → ℝ} {f : Ω → Point d → ℝ}

theorem CommonLoss.branchedOjaProgram_outputLaw (h : CommonLoss μ P ν F f)
    (a₀ : Ω) {γ : ℝ} (hγ : 0<γ) (δ : ℝ) (x : Point d) :
    OracleProgram.seededOutputLaw μ (branchedOjaSeedLaw P d hγ δ) (.grad 0) .certificate
      (fun q z => hvpReply f z q) (branchedOjaProgram P x γ δ) (branchedOjaQueryCount P d γ δ)=
      Measure.map (fun w : (BranchedOjaDraws Ω d P γ δ : Type) => branchedOjaReply P f x γ δ w)
        (branchedOjaLaw μ P d hγ δ) := by
  by_cases hc : zeroQueryCurvatureCase P d γ
  · have hp : branchedOjaProgram P x γ δ=(fun _ => .done .certificate) := by
      funext s
      exact if_pos hc
    rw [branchedOjaSeedLaw,dif_pos hc,branchedOjaLaw,dif_pos hc,hp,
      OracleProgram.seededOutputLaw_done,Measure.map_dirac (h.branchedOjaReply_fixed_measurable x γ δ)]
    simp only [branchedOjaReply,if_pos hc]
  · have hp := (branchedOjaProgram_measurable (d := d) P γ δ).comp
      (fun s : BranchedOjaSeed d P γ δ => (x,s)) (measurable_const.prodMk measurable_id)
    have ht := OracleProgram.seededOutputLaw_mapSeed μ
      (ojaAmplifiedSeedLaw P (not_zeroQueryCurvatureCase_dimension hc) hγ δ)
      (HvpQuery.grad (0 : Point d)) (0 : Point d) (CurvatureReply.certificate : CurvatureReply d) a₀
      (fun q z => hvpReply f z q) h.hvpReply_joint_measurable (branchedOjaProgram P x γ δ) hp
      Sum.inr measurable_inr (branchedOjaQueryCount P d γ δ)
    rw [branchedOjaSeedLaw,dif_neg hc,ht]
    rw [branchedOjaLaw,dif_neg hc,
      Measure.map_map (h.branchedOjaReply_fixed_measurable x γ δ) measurable_inr]
    have hprog : (fun s => branchedOjaProgram P x γ δ (Sum.inr s))=
        ojaAmplifiedProgram P x γ δ := by
      funext s
      unfold branchedOjaProgram
      rw [if_neg hc]
      exact Sum.elim_inr _ _ _
    have hreply : (fun w : (BranchedOjaDraws Ω d P γ δ : Type) =>
        branchedOjaReply P f x γ δ w) ∘ Sum.inr=ojaAmplifiedReply P f x γ δ := by
      funext w
      change branchedOjaReply P f x γ δ (Sum.inr w)=_
      unfold branchedOjaReply
      rw [if_neg hc]
      exact Sum.elim_inr _ _ _
    rw [hprog,hreply,branchedOjaQueryCount,if_neg hc]
    exact h.ojaAmplifiedProgram_outputLaw a₀ (not_zeroQueryCurvatureCase_dimension hc) hγ δ x

/-- The permitted, reply-only curvature algorithm inherits the original
confidence guarantee under independent private seeds and fresh samples. -/
theorem CommonLoss.branchedOjaProgram_confidence (h : CommonLoss μ P ν F f)
    (a₀ : Ω) {γ δ : ℝ} (hγ : 0<γ) (hδ : 0<δ) (hδ1 : δ≤1) (x : Point d) :
    (OracleProgram.seededOutputLaw μ (branchedOjaSeedLaw P d hγ δ) (.grad 0) .certificate
      (fun q z => hvpReply f z q) (branchedOjaProgram P x γ δ) (branchedOjaQueryCount P d γ δ))
      {r | ¬ RayleighReplyValid γ (hessian F x) r}≤ENNReal.ofReal δ := by
  have he : MeasurableSet {r : CurvatureReply d | ¬ RayleighReplyValid γ (hessian F x) r} :=
    (rayleighReplyValid_measurableSet γ measurable_const measurable_id).compl
  rw [h.branchedOjaProgram_outputLaw a₀ hγ δ x,
    Measure.map_apply (h.branchedOjaReply_fixed_measurable x γ δ) he]
  exact h.branchedOjaReply_confidence hγ hδ hδ1 x

theorem CommonLoss.branchedOjaProgramAlgorithm_confidence (h : CommonLoss μ P ν F f)
    (a₀ : Ω) {γ δ : ℝ} (hγ : 0<γ) (hδ : 0<δ) (hδ1 : δ≤1) (x : Point d) :
    ((branchedOjaSeedLaw P d hγ δ).prod (oracleHistoryLaw μ (branchedOjaQueryCount P d γ δ)))
      {w | ¬ RayleighReplyValid γ (hessian F x)
        (oracleHistoryOutput (branchedOjaProgramAlgorithm P x γ δ w.1)
          (fun q z => hvpReply f z q) (branchedOjaQueryCount P d γ δ) w.2)}≤ENNReal.ofReal δ := by
  have hp := (branchedOjaProgram_measurable (d := d) P γ δ).comp
    (fun s : BranchedOjaSeed d P γ δ => (x,s)) (measurable_const.prodMk measurable_id)
  have he := OracleProgram.algorithm_seeded_history_outputLaw μ (branchedOjaSeedLaw P d hγ δ)
    (.grad 0) 0 .certificate a₀ (fun q z => hvpReply f z q) h.hvpReply_joint_measurable
    (branchedOjaProgram P x γ δ) hp (branchedOjaQueryCount P d γ δ)
  have hm := oracleHistoryOutput_measurable
    (branchedOjaProgramAlgorithm P x γ δ) (OracleProgram.algorithm_measurable 0 hp)
    (fun q z => hvpReply f z q) h.hvpReply_joint_measurable (branchedOjaQueryCount P d γ δ)
  have hs : MeasurableSet {r : CurvatureReply d | ¬ RayleighReplyValid γ (hessian F x) r} :=
    (rayleighReplyValid_measurableSet γ measurable_const measurable_id).compl
  have hh := h.branchedOjaProgram_confidence a₀ hγ hδ hδ1 x
  unfold branchedOjaProgramAlgorithm at hm
  rw [←he,Measure.map_apply hm hs] at hh
  exact hh

end
end SecondOrder
