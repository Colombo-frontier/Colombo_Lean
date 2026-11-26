import SecondOrder.OracleHistory

open MeasureTheory

namespace SecondOrder
noncomputable section

def oracleAlgorithmSuccessProbability {Ω : Type} {Ξ Q Y O S : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (seedLaw : Measure Ξ) (sampleLaw : Measure Ω) (P : Ξ → OracleAlgorithm Q Y O S)
    (reply : Q → Ω → Y) (N : ℕ) (success : O → Prop) : ℝ :=
  (seedLaw.prod (oracleHistoryLaw sampleLaw N)).real
    {w : Ξ × FiniteHistory Unit Ω N | success (oracleHistoryOutput (P w.1) reply N w.2)}

def richAlgorithmSospProbability {Ω : Type} {Ξ S : Type*} {d : ℕ}
    [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (seedLaw : Measure Ξ) (sampleLaw : Measure Ω) (P : Ξ → RichAlgorithm d S)
    (F : Point d → ℝ) (f : Ω → Point d → ℝ) (ε γ : ℝ) (N : ℕ) : ℝ :=
  oracleAlgorithmSuccessProbability seedLaw sampleLaw P (fun x a => richReply f a x) N (IsSOSP F ε γ)

def hvpAlgorithmSospProbability {Ω : Type} {Ξ S : Type*} {d : ℕ}
    [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (seedLaw : Measure Ξ) (sampleLaw : Measure Ω) (P : Ξ → HvpAlgorithm d S)
    (F : Point d → ℝ) (f : Ω → Point d → ℝ) (ε γ : ℝ) (N : ℕ) : ℝ :=
  oracleAlgorithmSuccessProbability seedLaw sampleLaw P (fun q a => hvpReply f a q) N (IsSOSP F ε γ)

theorem translateOracleAlgorithm_historyRun {Ω : Type} {Q Y Q' Y' O S : Type*}
    (P : OracleAlgorithm Q Y O S) (encode : Q → Q') (decode : Q → Y' → Y)
    (reply : Q → Ω → Y) (rich : Q' → Ω → Y')
    (hsim : ∀ q a, decode q (rich (encode q) a)=reply q a) (N : ℕ) (h : FiniteHistory Unit Ω N) :
    oracleHistoryRun (translateOracleAlgorithm P encode decode).toQueryPolicy rich N h=
      oracleHistoryRun P.toQueryPolicy reply N h := by
  induction N with
  | zero => rfl
  | succ N ih =>
    simp only [oracleHistoryRun]
    rw [ih h.1]
    simp only [translateOracleAlgorithm,hsim]

theorem translateOracleAlgorithm_historyOutput {Ω : Type} {Q Y Q' Y' O S : Type*}
    (P : OracleAlgorithm Q Y O S) (encode : Q → Q') (decode : Q → Y' → Y)
    (reply : Q → Ω → Y) (rich : Q' → Ω → Y')
    (hsim : ∀ q a, decode q (rich (encode q) a)=reply q a) (N : ℕ) (h : FiniteHistory Unit Ω N) :
    oracleHistoryOutput (translateOracleAlgorithm P encode decode) rich N h=
      oracleHistoryOutput P reply N h := by
  unfold oracleHistoryOutput
  rw [translateOracleAlgorithm_historyRun P encode decode reply rich hsim]
  rfl

theorem hvpAlgorithmSospProbability_simulation {Ω : Type} {Ξ S : Type*} {d : ℕ}
    [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (seedLaw : Measure Ξ) (sampleLaw : Measure Ω) (P : Ξ → HvpAlgorithm d S)
    (F : Point d → ℝ) (f : Ω → Point d → ℝ) (ε γ : ℝ) (N : ℕ) :
    richAlgorithmSospProbability seedLaw sampleLaw (fun ξ => hvpAlgorithmRich (P ξ)) F f ε γ N=
      hvpAlgorithmSospProbability seedLaw sampleLaw P F f ε γ N := by
  unfold richAlgorithmSospProbability hvpAlgorithmSospProbability oracleAlgorithmSuccessProbability
  congr 1
  ext w
  simp only [Set.mem_setOf_eq,hvpAlgorithmRich]
  rw [translateOracleAlgorithm_historyOutput (P w.1) queryPoint extractHvp
    (fun q a => hvpReply f a q) (fun x a => richReply f a x)
    (fun q a => one_rich_call_simulates_hvp f a q)]

/-- Connect a general measurable-sample algorithm to the concrete finite
coefficient law used by the lower bounds. The default tape value is unused. -/
theorem oracleAlgorithmSuccessProbability_finite_policy {Ω : Type} {Ξ Q Y S : Type*}
    [MeasurableSpace Ω] [MeasurableSingletonClass Ω] [Fintype Ω] [MeasurableSpace Ξ]
    (μ : Measure Ξ) (p : PMF Ω) (P : Ξ → OracleAlgorithm Q Y Q S)
    (reply : Q → Ω → Y) (a₀ : Ω) (N : ℕ) (success : Q → Prop) :
    oracleAlgorithmSuccessProbability μ p.toMeasure P reply N success=
      (μ.prod (finiteAdaptiveLaw (PMF.pure ()) (fun _ _ => p) N).toMeasure).real
        {w : Ξ × FiniteHistory Unit Ω N | success ((oracleAlgorithmPolicy (P w.1) N).query N
          (queryPolicyRun (oracleAlgorithmPolicy (P w.1) N) reply (finiteHistoryTape a₀ N w.2) N))} := by
  rw [finiteAdaptiveLaw_iid_toMeasure]
  unfold oracleAlgorithmSuccessProbability
  congr 1
  ext w
  simp only [Set.mem_setOf_eq,oracleAlgorithmPolicy_output,oracleHistoryOutput_tape _ _ a₀]

theorem CommonLoss.richReply_joint_measurable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {P : Parameters} {ν : ℝ}
    {F : Point d → ℝ} {f : Ω → Point d → ℝ} (h : CommonLoss μ P ν F f) :
    Measurable (fun w : Point d × Ω => richReply f w.2 w.1) :=
  (h.value_measurable.prodMk (h.gradient_measurable.prodMk h.hessian_measurable)).comp measurable_swap

theorem CommonLoss.hvpReply_joint_measurable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {P : Parameters} {ν : ℝ}
    {F : Point d → ℝ} {f : Ω → Point d → ℝ} (h : CommonLoss μ P ν F f) :
    Measurable (fun w : HvpQuery d × Ω => hvpReply f w.2 w.1) := by
  have hr := h.richReply_joint_measurable.comp
    (((queryPoint_measurable d).comp measurable_fst).prodMk measurable_snd)
  have hh := (extractHvp_measurable d).comp (measurable_fst.prodMk hr)
  simpa only [Function.comp_def,one_rich_call_simulates_hvp] using hh

end
end SecondOrder
