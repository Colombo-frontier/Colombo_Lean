import Bilevel.OracleSelectedLaw

/-! Expected loss and original-call accounting for a compiled causal program
with an independent private output index. The statements use the actual
stopped Borel program and its total calls, including its proved termination.
-/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace Bilevel.OracleCode
open Stateful BorelAdaptive
set_option autoImplicit false
variable {Q O I B C : Space} {Seed : Type} [MeasurableSpace Seed]
  (response : Q → Seed → O) (q₀ : Q) (o₀ : O)
  (c : Code Q O (of Unit) B) (f : prod I B → C) (hf : Measurable f)

theorem selected_result_measurable
    (hr : Measurable (Function.uncurry response)) :
    Measurable (fun z : I × IndependentStream.Stream Seed =>
      Machine.result (compile q₀ o₀ (selectedCode c f hf)) response z.1 z.2) := by
  have hm := compiled_result_measurable response q₀ o₀ c hr ()
  have hs := (selectedOutcome_measurable f hf).comp
    (measurable_id.prodMap hm)
  simpa only [Function.comp_def,Prod.map,selected_result response q₀ o₀ c f hf] using hs

variable (ξ : Measure I) [IsProbabilityMeasure ξ]
  (ν : Measure Seed) [IsProbabilityMeasure ν]
  (hr : Measurable (Function.uncurry response))
  (K : Kernel Q O) [IsMarkovKernel K] (hK : ∀ q,K q=ν.map (response q))

include hr hK in
theorem selected_lintegral (g : Outcome C Unit → ℝ≥0∞) (hg : Measurable g) :
    (∫⁻ z,g (Machine.result (compile q₀ o₀ (selectedCode c f hf)) response z.1 z.2)
      ∂ξ.prod (IndependentStream.law ν))=
    ∫⁻ z,g (selectedOutcome f z) ∂ξ.prod ((denote K c).law ((),())) := by
  have h := congrArg (fun m => ∫⁻ z,g z ∂m)
    (selected_law response q₀ o₀ c f hf ξ ν hr K hK)
  dsimp only at h
  rw [lintegral_map hg (selected_result_measurable response q₀ o₀ c f hf hr),
    lintegral_map hg (selectedOutcome_measurable f hf)] at h
  exact h

include hr hK in
theorem selected_stopped_lintegral (loss : C → ℝ≥0∞) (hloss : Measurable loss) :
    (∫⁻ z,loss (seededStopped (compile q₀ o₀ (selectedCode c f hf)).program
      (fun _ : Unit => response) (compile q₀ o₀ (selectedCode c f hf)).start ((),z)).2
      ∂ξ.prod (IndependentStream.law ν))=
    ∫⁻ z,loss (f (z.1,z.2.1)) ∂ξ.prod ((denote K c).law ((),())) := by
  exact selected_lintegral response q₀ o₀ c f hf ξ ν hr K hK
    (fun z => loss z.1) (hloss.comp measurable_fst)

omit [MeasurableSpace Seed] in
theorem selected_seededCalls (i : I) (s : IndependentStream.Stream Seed) :
    seededCalls (compile q₀ o₀ (selectedCode c f hf)).program
      (fun _ : Unit => response) (compile q₀ o₀ (selectedCode c f hf)).start ((),i,s)=
      ((Machine.result (compile q₀ o₀ c) response () s).2.2:ℝ≥0∞) := by
  change totalCalls (compile q₀ o₀ (selectedCode c f hf)).program
    (fun _ : Unit => response) ((),(compile q₀ o₀ (selectedCode c f hf)).start i,s)=_
  rw [Machine.totalCalls_eq _ _ (compile_correct q₀ o₀ _),
    Machine.result_eq _ _ (compile_correct q₀ o₀ c)]
  simp only [selectedCode,map,eval,Procedure.combine,Nat.add_zero]

include hr hK in
theorem selected_calls_lintegral :
    (∫⁻ z,seededCalls (compile q₀ o₀ (selectedCode c f hf)).program
      (fun _ : Unit => response) (compile q₀ o₀ (selectedCode c f hf)).start ((),z)
      ∂ξ.prod (IndependentStream.law ν))=
    ∫⁻ z,(z.2.2:ℝ≥0∞) ∂(denote K c).law ((),()) := by
  have hm : Measurable (fun z : Outcome B Unit => (z.2.2:ℝ≥0∞)) :=
    (measurable_of_countable (fun n : ℕ => (n:ℝ≥0∞))).comp
      (measurable_snd.comp measurable_snd)
  have he (z : I × IndependentStream.Stream Seed) :
      seededCalls (compile q₀ o₀ (selectedCode c f hf)).program
        (fun _ : Unit => response) (compile q₀ o₀ (selectedCode c f hf)).start ((),z)=
      ((Machine.result (compile q₀ o₀ (selectedCode c f hf)) response z.1 z.2).2.2:ℝ≥0∞) := by
    rw [selected_seededCalls response q₀ o₀ c f hf,selected_result response q₀ o₀ c f hf]
    rfl
  simp_rw [he]
  rw [selected_lintegral response q₀ o₀ c f hf ξ ν hr K hK
    (fun z => (z.2.2:ℝ≥0∞))
    ((measurable_of_countable (fun n : ℕ => (n:ℝ≥0∞))).comp
      (measurable_snd.comp measurable_snd))]
  change (∫⁻ z : I × Outcome B Unit,(z.2.2.2:ℝ≥0∞)
    ∂ξ.prod ((denote K c).law ((),())))=_
  have hp := lintegral_prod (fun z : I × Outcome B Unit => (z.2.2.2:ℝ≥0∞))
    (show AEMeasurable (fun z : I × Outcome B Unit => (z.2.2.2:ℝ≥0∞))
      (ξ.prod ((denote K c).law ((),()))) from (hm.comp measurable_snd).aemeasurable)
  simpa only [lintegral_const,measure_univ,mul_one] using hp

include hr hK in
theorem selected_risk_le (loss : C → ℝ) (hloss : Measurable loss)
    (hpos : ∀ x,0≤loss x) {ε : ℝ}
    (hi : Integrable (fun z : I × Outcome B Unit => loss (f (z.1,z.2.1)))
      (ξ.prod ((denote K c).law ((),()))))
    (hbound : (∫ z : I × Outcome B Unit,loss (f (z.1,z.2.1))
      ∂ξ.prod ((denote K c).law ((),())))≤ε) :
    (∫⁻ z,ENNReal.ofReal (loss (seededStopped (compile q₀ o₀ (selectedCode c f hf)).program
      (fun _ : Unit => response) (compile q₀ o₀ (selectedCode c f hf)).start ((),z)).2)
      ∂ξ.prod (IndependentStream.law ν))≤ENNReal.ofReal ε := by
  rw [selected_stopped_lintegral response q₀ o₀ c f hf ξ ν hr K hK
    (fun x => ENNReal.ofReal (loss x)) hloss.ennreal_ofReal,
    ← ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall (fun z => hpos _))]
  exact ENNReal.ofReal_le_ofReal hbound

include hr hK in
theorem selected_cost_le {R : ℝ}
    (hi : Integrable (fun z : Outcome B Unit => (z.2.2:ℝ)) ((denote K c).law ((),())))
    (hbound : (∫ z : Outcome B Unit,(z.2.2:ℝ) ∂(denote K c).law ((),()))≤R) :
    (∫⁻ z,seededCalls (compile q₀ o₀ (selectedCode c f hf)).program
      (fun _ : Unit => response) (compile q₀ o₀ (selectedCode c f hf)).start ((),z)
      ∂ξ.prod (IndependentStream.law ν))≤ENNReal.ofReal R := by
  rw [selected_calls_lintegral response q₀ o₀ c f hf ξ ν hr K hK]
  have he := ofReal_integral_eq_lintegral_ofReal hi
    (Filter.Eventually.of_forall (fun z : Outcome B Unit => Nat.cast_nonneg z.2.2))
  simp only [ENNReal.ofReal_natCast] at he
  rw [← he]
  exact ENNReal.ofReal_le_ofReal hbound

end Bilevel.OracleCode
