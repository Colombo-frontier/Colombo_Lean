import Bilevel.OrdinaryFrameProtocol

/-! Measurability of the actual ordinary-frame execution, with the evolving
subspace represented by its finite projector matrix and the revealed set by
its finitely many membership events. -/
noncomputable section
open MeasureTheory
universe u v
namespace Bilevel.OrdinaryFrame
open EuclideanGaussian ProjectionPosterior TransportControllerMachine RawGenieBorel

variable {Ω : Type v} [MeasurableSpace Ω] {d T : ℕ} {H : Memory.{u}}

structure BorelState (s : Ω → State H d T) : Prop where
  memory : Measurable (fun ω => (s ω).1)
  projector : Measurable (fun ω => ProjectionStore.ofSubspace d (s ω).2.1)
  known : ∀ i,MeasurableSet {ω | i∈(s ω).2.2}

theorem BorelState.query {s : Ω → State H d T} (hs : BorelState s)
    (U : Ω → Frame d T) (hU : Measurable U) (q : H → Space d) (hq : Measurable q)
    (respond : H × Frame d T → H) (hr : Measurable respond) :
    BorelState (fun ω => queryStep q respond (s ω) (U ω)) := by
  have hv := RawGenieBorel.insert_measurable d _ hs.projector _ (hq.comp hs.memory)
  have hz := projections_measurable d T _ hv U hU
  exact ⟨hr.comp (hs.memory.prodMk hz),hv,hs.known⟩

theorem BorelState.reveal {s : Ω → State H d T} (hs : BorelState s)
    (U : Ω → Frame d T) (hU : Measurable U) (j : H → Fin T) (hj : Measurable j)
    (respond : H × (Space d × Frame d T) → H) (hr : Measurable respond) :
    BorelState (fun ω => revealStep j respond (s ω) (U ω)) := by
  have hjm := hj.comp hs.memory
  have hy := ProjectionObservation.selected_column_measurable d T U hU _ hjm
  have hv := RawGenieBorel.insert_measurable d _ hs.projector _ hy
  have hz := projections_measurable d T _ hv U hU
  refine ⟨hr.comp (hs.memory.prodMk (hy.prodMk hz)),hv,?_⟩
  intro i
  have he : MeasurableSet {ω | i=j (s ω).1} := by
    convert hjm (measurableSet_singleton i) using 1
    ext ω
    simp [eq_comm]
  exact he.union (hs.known i)

open Classical in
theorem BorelState.ite {s₁ s₂ : Ω → State H d T} (h₁ : BorelState s₁) (h₂ : BorelState s₂)
    (A : Set Ω) (hA : MeasurableSet A) :
    BorelState (fun ω => if ω∈A then s₁ ω else s₂ ω) := by
  classical
  refine ⟨?_,?_,?_⟩
  · change Measurable (fun ω => (if ω∈A then s₁ ω else s₂ ω).1)
    simp only [apply_ite]
    exact h₁.memory.ite hA h₂.memory
  · change Measurable (fun ω => ProjectionStore.ofSubspace d (if ω∈A then s₁ ω else s₂ ω).2.1)
    simp only [apply_ite]
    exact h₁.projector.ite hA h₂.projector
  · intro i
    convert (hA.inter (h₁.known i)).union (hA.compl.inter (h₂.known i)) using 1
    ext ω
    by_cases h : ω∈A <;> simp [h]

theorem precoin_borel (L : Rules H d T) (t : ℕ) {s : Ω → State H d T} (hs : BorelState s)
    (U : Ω → Frame d T) (hU : Measurable U) :
    BorelState (fun ω => precoin L t (s ω) (U ω)) :=
  (hs.query U hU (L.first t) (L.first_measurable t) (L.afterFirst t) (L.afterFirst_measurable t)).query
    U hU (L.second t) (L.second_measurable t) (L.afterSecond t) (L.afterSecond_measurable t)

theorem run_borel (L : Rules H d T) : ∀ Q R t (s : Ω → State H d T), BorelState s →
    ∀ (U : Ω → Frame d T),Measurable U → BorelState (fun ω => run L Q R t (s ω) (U ω)) := by
  classical
  intro Q
  induction Q with
  | zero =>
    intro R t s hs U hU
    exact hs.query U hU L.output L.output_measurable Prod.fst measurable_fst
  | succ Q ih =>
    intro R t s hs U hU
    have hp := precoin_borel L t hs U hU
    cases R with
    | zero => exact ih 0 (t+1) _ hp U hU
    | succ R =>
      have hr := hp.reveal U hU (L.column t) (L.column_measurable t)
        (L.afterReveal t) (L.afterReveal_measurable t)
      have hy := ih R (t+1) _ hr U hU
      have hn := ih (R+1) (t+1) _ hp U hU
      exact hy.ite hn _ (hp.memory (L.success_measurable t))

theorem initial_run_borel (L : Rules H d T) (Q R t : ℕ) :
    BorelState (fun p : H × Frame d T => run L Q R t (p.1,(⊥,∅)) p.2) := by
  apply run_borel (Ω := H × Frame d T) L Q R t (fun p => (p.1,(⊥,∅)))
  · refine ⟨measurable_fst,?_,fun _ => MeasurableSet.empty⟩
    change Measurable (fun _ : H × Frame d T => ProjectionStore.ofSubspace d (⊥ : Submodule ℝ (Space d)))
    exact measurable_const
  · exact measurable_snd

theorem output_measurable (L : Rules H d T) (Q R t : ℕ) :
    Measurable (fun p : H × Frame d T => L.output (run L Q R t (p.1,(⊥,∅)) p.2).1) :=
  L.output_measurable.comp (initial_run_borel L Q R t).memory

end Bilevel.OrdinaryFrame
