import Bilevel.PolishedHistoryConditionalRepresentation
import Bilevel.PolishedHistoryStationaryStopping

/-! A deterministic-query adaptive experiment with a public call clock is
realized by a single fixed-initial-history oracle. Per-call conditional laws
are combined by the actual call clock; halted states remain absorbing. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace Bilevel.PolishedHistory
set_option autoImplicit false
variable {S Q O Y Ω : Type*} [MeasurableSpace S] [MeasurableSpace Q]
  [MeasurableSpace O] [MeasurableSpace Y] [MeasurableSpace Ω]

/-- Selection among measurable conditional kernels by a measurable clock. -/
def clockKernel (K : ℕ → Kernel (Q × S) O) (clock : S → ℕ)
    (hc : Measurable clock) : Kernel (Q × S) O where
  toFun := fun z => K (clock z.2) z
  measurable' := by
    have hm : Measurable (fun z : (Q × S) × ℕ => K z.2 z.1) := by
      apply measurable_from_prod_countable
      intro n
      exact (K n).measurable
    exact hm.comp (measurable_id.prodMk (hc.comp measurable_snd))

instance clockKernel_markov (K : ℕ → Kernel (Q × S) O) [∀ n,IsMarkovKernel (K n)]
    (clock : S → ℕ) (hc : Measurable clock) : IsMarkovKernel (clockKernel K clock hc) :=
  ⟨fun z => show IsProbabilityMeasure (K (clock z.2) z) from inferInstance⟩

def deterministicHistoryOracle (A : BorelAdaptive.Program S Q O Y)
    (K : ℕ → Kernel (Q × S) O) [∀ n,IsMarkovKernel (K n)]
    (clock : S → ℕ) (hc : Measurable clock) : HistoryProgram.Oracle Q O S where
  law := clockKernel K clock hc
  markov := inferInstance
  update := fun z => A.update (z.1.2,z.2)
  update_measurable := A.update_measurable.comp
    ((measurable_snd.comp measurable_fst).prodMk measurable_snd)

variable (A : BorelAdaptive.Program S Q O Y)

def absorbingDiagonal (z : (Q × S) × O) : S × S :=
  let s := if A.halt z.1.2=true then z.1.2 else A.update (z.1.2,z.2)
  (s,s)

theorem absorbingDiagonal_measurable : Measurable (absorbingDiagonal A) := by
  classical
  have hs : Measurable (fun z : (Q × S) × O => z.1.2) :=
    measurable_snd.comp measurable_fst
  have hh : MeasurableSet {z : (Q × S) × O | A.halt z.1.2=true} :=
    (A.halt_measurable.comp hs) (measurableSet_singleton true)
  have hm : Measurable (fun z : (Q × S) × O =>
      if A.halt z.1.2=true then z.1.2 else A.update (z.1.2,z.2)) :=
    hs.ite hh (A.update_measurable.comp (hs.prodMk measurable_snd))
  exact hm.prodMk hm

theorem diagonal_step (K : ℕ → Kernel (Q × S) O) [∀ n,IsMarkovKernel (K n)]
    (clock : S → ℕ) (hc : Measurable clock) (n : ℕ) (s : S)
    (hclock : A.halt s=false → clock s=n) :
    HistoryProgram.step A (deterministicHistoryOracle A K clock hc) (s,s)=
      Stateful.KernelMap.dependent (K n) (absorbingDiagonal A) (A.query s,s) := by
  rw [Stateful.KernelMap.dependent_apply _ _ (absorbingDiagonal_measurable A)]
  cases hh : A.halt s with
  | true =>
      rw [HistoryProgram.step_halted _ _ _ hh]
      simp only [absorbingDiagonal,hh,if_true]
      rw [Measure.map_const,measure_univ,one_smul]
  | false =>
      rw [HistoryProgram.step_live _ _ _ hh]
      change (K (clock s) (A.query s,s)).map _=_
      rw [hclock hh]
      congr 1
      funext o
      simp [HistoryProgram.advance,HistoryProgram.request,deterministicHistoryOracle,
        absorbingDiagonal,hh]

/-- Kernel composition commutes with a measurable entering-state map. -/
theorem kernel_comp_entering {T U V : Type*} [MeasurableSpace T]
    [MeasurableSpace U] [MeasurableSpace V] (ν : Measure T)
    (K : Kernel U V) (f : T → U) (hf : Measurable f) :
    K ∘ₘ ν.map f=K.comap f hf ∘ₘ ν := by
  rw [← Measure.deterministic_comp_eq_map hf,Measure.comp_assoc,
    Kernel.comp_deterministic_eq_comap]

variable {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Equality of the actual next-state law, including absorbing halting. -/
theorem deterministic_experiment_step
    (state : ℕ → Ω → S) (obs : ℕ → Ω → O)
    (hs : ∀ n,Measurable (state n)) (ho : ∀ n,Measurable (obs n))
    (K : ℕ → Kernel (Q × S) O) [∀ n,IsMarkovKernel (K n)]
    (hK : ∀ n,(μ.map (fun ω => (A.query (state n ω),state n ω))) ⊗ₘ K n=
      μ.map (fun ω => ((A.query (state n ω),state n ω),obs n ω)))
    (clock : S → ℕ) (hc : Measurable clock)
    (hclock : ∀ n,∀ᵐ ω ∂μ,A.halt (state n ω)=false → clock (state n ω)=n)
    (hnext : ∀ n,∀ᵐ ω ∂μ,state (n+1) ω=
      if A.halt (state n ω)=true then state n ω else A.update (state n ω,obs n ω))
    (n : ℕ) :
    HistoryProgram.step A (deterministicHistoryOracle A K clock hc) ∘ₘ
      μ.map (fun ω => (state n ω,state n ω))=
      μ.map (fun ω => (state (n+1) ω,state (n+1) ω)) := by
  let enter : Ω → Q × S := fun ω => (A.query (state n ω),state n ω)
  have he : Measurable enter := (A.query_measurable.comp (hs n)).prodMk (hs n)
  have hdiag : Measurable (fun ω => (state n ω,state n ω)) := (hs n).prodMk (hs n)
  calc
    _ = Stateful.KernelMap.dependent (K n) (absorbingDiagonal A) ∘ₘ μ.map enter := by
      rw [kernel_comp_entering _ _ _ hdiag,kernel_comp_entering _ _ _ he]
      apply Measure.bind_congr_right
      filter_upwards [hclock n] with ω hω
      exact diagonal_step A K clock hc n (state n ω) hω
    _ = μ.map (fun ω => absorbingDiagonal A (enter ω,obs n ω)) :=
      disintegration_update_law enter (obs n) he (ho n) (K n) (hK n)
        (absorbingDiagonal A) (absorbingDiagonal_measurable A)
    _ = _ := by
      apply Measure.map_congr
      filter_upwards [hnext n] with ω hω
      simp only [absorbingDiagonal,enter]
      rw [← hω]

/-- The exact finite marginals of the abstract adaptive experiment equal the
actual Ionescu-Tulcea program run under one fixed-initial-history oracle. -/
theorem deterministic_experiment_run
    (state : ℕ → Ω → S) (obs : ℕ → Ω → O)
    (hs : ∀ n,Measurable (state n)) (ho : ∀ n,Measurable (obs n))
    (K : ℕ → Kernel (Q × S) O) [∀ n,IsMarkovKernel (K n)]
    (hK : ∀ n,(μ.map (fun ω => (A.query (state n ω),state n ω))) ⊗ₘ K n=
      μ.map (fun ω => ((A.query (state n ω),state n ω),obs n ω)))
    (clock : S → ℕ) (hc : Measurable clock)
    (hclock : ∀ n,∀ᵐ ω ∂μ,A.halt (state n ω)=false → clock (state n ω)=n)
    (hnext : ∀ n,∀ᵐ ω ∂μ,state (n+1) ω=
      if A.halt (state n ω)=true then state n ω else A.update (state n ω,obs n ω))
    (s₀ : S) (hinit : state 0 =ᵐ[μ] fun _ => s₀) (n : ℕ) :
    HistoryProgram.run A (deterministicHistoryOracle A K clock hc) n (s₀,s₀)=
      μ.map (fun ω => (state n ω,state n ω)) := by
  induction n with
  | zero =>
      rw [HistoryProgram.run_zero,Kernel.id_apply]
      symm
      calc
        _ = μ.map (fun _ => (s₀,s₀)) := Measure.map_congr (hinit.mono (fun _ h => by rw [h]))
        _ = _ := by rw [Measure.map_const,measure_univ,one_smul]
  | succ n ih =>
      rw [HistoryProgram.run_succ,Kernel.comp_apply,ih]
      exact deterministic_experiment_step A state obs hs ho K hK clock hc hclock hnext n

def experimentPath (state : ℕ → Ω → S) (ω : Ω) : HistoryProgram.Path S S :=
  fun n => (state n ω,state n ω)

theorem experimentPath_measurable (state : ℕ → Ω → S)
    (hs : ∀ n,Measurable (state n)) : Measurable (experimentPath state) :=
  measurable_pi_iff.mpr (fun n => (hs n).prodMk (hs n))

omit [IsProbabilityMeasure μ] in
/-- The original probability-space process retains all observables after
halt, because its actual program dynamics are absorbing. -/
theorem experimentPath_step_good (state : ℕ → Ω → S) (obs : ℕ → Ω → O)
    (hs : ∀ n,Measurable (state n))
    (hnext : ∀ n,∀ᵐ ω ∂μ,state (n+1) ω=
      if A.halt (state n ω)=true then state n ω else A.update (state n ω,obs n ω))
    (v : S → ℝ) (hv : Measurable v) :
    ∀ᵐ w ∂μ.map (experimentPath state),∀ n,pathStepGood A v n w := by
  apply ae_all_iff.mpr
  intro n
  apply (ae_map_iff (experimentPath_measurable state hs).aemeasurable
    (pathStepGood_measurable A v hv n)).mpr
  filter_upwards [hnext n] with ω hω
  intro hh
  change A.halt (state n ω)=true at hh
  have hn : state (n+1) ω=state n ω := by simpa only [hh,if_true] using hω
  change A.halt (state (n+1) ω)=true ∧ v (state (n+1) ω)=v (state n ω)
  rw [hn]
  exact ⟨hh,rfl⟩

section Stopping
variable (state : ℕ → Ω → S) (obs : ℕ → Ω → O)
    (hs : ∀ n,Measurable (state n)) (ho : ∀ n,Measurable (obs n))
    (K : ℕ → Kernel (Q × S) O) [∀ n,IsMarkovKernel (K n)]
    (hK : ∀ n,(μ.map (fun ω => (A.query (state n ω),state n ω))) ⊗ₘ K n=
      μ.map (fun ω => ((A.query (state n ω),state n ω),obs n ω)))
    (clock : S → ℕ) (hc : Measurable clock)
    (hclock : ∀ n,∀ᵐ ω ∂μ,A.halt (state n ω)=false → clock (state n ω)=n)
    (hnext : ∀ n,∀ᵐ ω ∂μ,state (n+1) ω=
      if A.halt (state n ω)=true then state n ω else A.update (state n ω,obs n ω))
    (s₀ : S) (hinit : state 0 =ᵐ[μ] fun _ => s₀)

include hs ho hK hclock hnext hinit in
/-- Exact finite marginals against the actual complete execution measure. -/
theorem deterministic_experiment_endpoint (n : ℕ) :
    (HistoryProgram.trajectoryLaw A (deterministicHistoryOracle A K clock hc)
      (Measure.dirac s₀) id s₀).map (fun w => w n)=
      (μ.map (experimentPath state)).map (fun w => w n) := by
  rw [HistoryProgram.trajectoryLaw_endpoint _ _ _ _ measurable_id,
    HistoryProgram.runLaw,Measure.map_dirac (measurable_id.prodMk measurable_const),
    Measure.dirac_bind (Kernel.measurable _),
    Measure.map_map (measurable_pi_apply n) (experimentPath_measurable state hs)]
  exact deterministic_experiment_run A state obs hs ho K hK clock hc hclock hnext s₀ hinit n

include hs ho hK hclock hnext hinit in
/-- The actual number of original calls is preserved, including infinite
cost. The statement derives stopping costs from the finite marginals. -/
theorem deterministic_experiment_stopped_cost :
    (∫⁻ w,HistoryProgram.totalCalls A w ∂HistoryProgram.trajectoryLaw A
      (deterministicHistoryOracle A K clock hc) (Measure.dirac s₀) id s₀)=
    ∫⁻ ω,HistoryProgram.totalCalls A (experimentPath state ω) ∂μ := by
  have hleft : ∀ᵐ w ∂HistoryProgram.trajectoryLaw A
      (deterministicHistoryOracle A K clock hc) (Measure.dirac s₀) id s₀,
      ∀ n,pathStepGood A (fun _ => (0:ℝ)) n w := by
    apply ae_all_iff.mpr
    intro n
    exact trajectoryLaw_step_good _ _ _ _ _ _ measurable_const n
  have hright := experimentPath_step_good A state obs hs hnext (fun _ => (0:ℝ)) measurable_const
  have he := totalCalls_integral_eq A _ _
    (deterministic_experiment_endpoint A state obs hs ho K hK clock hc hclock hnext s₀ hinit)
    (hleft.mono (fun _ hw n hn => (hw n hn).1))
    (hright.mono (fun _ hw n hn => (hw n hn).1))
  exact he.trans (lintegral_map (HistoryProgram.totalCalls_measurable A)
    (experimentPath_measurable state hs))

include hs ho hK hclock hnext hinit in
/-- A finite expected-call budget also preserves the actual first-halt
output risk. No accuracy inequality is an assumption of this bridge. -/
theorem deterministic_experiment_stopped_risk (loss : Y → ℝ) (hloss : Measurable loss)
    (hcost : (∫⁻ w,HistoryProgram.totalCalls A w ∂HistoryProgram.trajectoryLaw A
      (deterministicHistoryOracle A K clock hc) (Measure.dirac s₀) id s₀)≠⊤) :
    (∫⁻ w,ENNReal.ofReal (loss (HistoryProgram.stoppedOutput A w))
      ∂HistoryProgram.trajectoryLaw A (deterministicHistoryOracle A K clock hc)
        (Measure.dirac s₀) id s₀)=
    ∫⁻ ω,ENNReal.ofReal (loss (HistoryProgram.stoppedOutput A (experimentPath state ω))) ∂μ := by
  let v := loss ∘ A.output
  have hv : Measurable v := hloss.comp A.output_measurable
  have hleft : ∀ᵐ w ∂HistoryProgram.trajectoryLaw A
      (deterministicHistoryOracle A K clock hc) (Measure.dirac s₀) id s₀,
      ∀ n,pathStepGood A v n w := by
    apply ae_all_iff.mpr
    intro n
    exact trajectoryLaw_step_good _ _ _ _ _ _ hv n
  have hright := experimentPath_step_good A state obs hs hnext v hv
  have he := stoppedValue_integral_eq A _ _
    (deterministic_experiment_endpoint A state obs hs ho K hK clock hc hclock hnext s₀ hinit)
    v hv hleft hright hcost
  change (∫⁻ w : HistoryProgram.Path S S,ENNReal.ofReal (v (w (HistoryProgram.stopTime A w)).1)
    ∂HistoryProgram.trajectoryLaw A (deterministicHistoryOracle A K clock hc)
      (Measure.dirac s₀) id s₀)=_
  have hm : Measurable (fun w : HistoryProgram.Path S S =>
      ENNReal.ofReal (v (w (HistoryProgram.stopTime A w)).1)) :=
    (hloss.comp (HistoryProgram.stoppedOutput_measurable A)).ennreal_ofReal
  exact he.trans (lintegral_map hm (experimentPath_measurable state hs))

include hs ho hK hclock hnext hinit in
/-- The full first-halt output distribution agrees, rather than merely its
expected gradient norm. This supports a fresh terminal selection index. -/
theorem deterministic_experiment_stopped_output_law
    (hcost : (∫⁻ w,HistoryProgram.totalCalls A w ∂HistoryProgram.trajectoryLaw A
      (deterministicHistoryOracle A K clock hc) (Measure.dirac s₀) id s₀)≠⊤) :
    (HistoryProgram.trajectoryLaw A (deterministicHistoryOracle A K clock hc)
      (Measure.dirac s₀) id s₀).map (HistoryProgram.stoppedOutput A)=
      μ.map (fun ω => HistoryProgram.stoppedOutput A (experimentPath state ω)) := by
  apply Measure.ext
  intro t ht
  let loss : Y → ℝ := t.indicator (fun _ => 1)
  have hloss : Measurable loss := measurable_const.indicator ht
  have he := deterministic_experiment_stopped_risk A state obs hs ho K hK clock hc
    hclock hnext s₀ hinit loss hloss hcost
  have htest : ∀ y,ENNReal.ofReal (loss y)=t.indicator (fun _ => (1:ℝ≥0∞)) y := by
    intro y
    by_cases hy : y∈t <;> simp [loss,Set.indicator_of_mem,Set.indicator_of_not_mem,hy]
  simp_rw [htest] at he
  have hmap : Measurable (fun ω => HistoryProgram.stoppedOutput A (experimentPath state ω)) :=
    (HistoryProgram.stoppedOutput_measurable A).comp (experimentPath_measurable state hs)
  rw [← lintegral_map (measurable_const.indicator ht)
    (HistoryProgram.stoppedOutput_measurable A),
    ← lintegral_map (measurable_const.indicator ht) hmap] at he
  exact (lintegral_indicator_one ht).symm.trans (he.trans (lintegral_indicator_one ht))

end Stopping

end Bilevel.PolishedHistory
