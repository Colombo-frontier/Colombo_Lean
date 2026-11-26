import Bilevel.RawGenieBorelPolicy

/-! Joint Borelness of the actual, unnormalized energy event, including
adaptive full-column insertions and their all-column projection updates. -/
noncomputable section
open MeasureTheory
universe u v
namespace Bilevel.RawGenieBorel
open EuclideanGaussian ProjectionPosterior ProjectionGeometry TransportControllerMachine

variable {Ω : Type v} [MeasurableSpace Ω]

theorem projection_measurable (d : ℕ) (V : Ω → Submodule ℝ (Space d))
    (hV : Measurable (fun ω => ProjectionStore.ofSubspace d (V ω)))
    (q : Ω → Space d) (hq : Measurable q) : Measurable (fun ω => project (V ω) (q ω)) := by
  simpa only [ProjectionStore.apply_subspace] using
    ProjectionStore.apply_measurable d _ hV q hq

theorem insert_measurable (d : ℕ) (V : Ω → Submodule ℝ (Space d))
    (hV : Measurable (fun ω => ProjectionStore.ofSubspace d (V ω)))
    (q : Ω → Space d) (hq : Measurable q) :
    Measurable (fun ω => ProjectionStore.ofSubspace d (V ω ⊔ Submodule.span ℝ {q ω})) := by
  simpa only [ProjectionStore.insert_subspace] using
    ProjectionStore.insert_measurable d _ hV q hq

theorem projections_measurable (d T : ℕ) (V : Ω → Submodule ℝ (Space d))
    (hV : Measurable (fun ω => ProjectionStore.ofSubspace d (V ω)))
    (U : Ω → Frame d T) (hU : Measurable U) :
    Measurable (fun ω => RawGenieProtocol.projections d T (V ω) (U ω)) := by
  apply measurable_pi_lambda
  intro i
  exact projection_measurable d V hV _ ((measurable_pi_apply i).comp hU)

theorem boundedEnergy_measurable (d T : ℕ) (cap : ℝ) (V : Ω → Submodule ℝ (Space d))
    (hV : Measurable (fun ω => ProjectionStore.ofSubspace d (V ω)))
    (S : Ω → Set (Fin T)) (hS : ∀ i,MeasurableSet {ω | i∈S ω})
    (U : Ω → Frame d T) (hU : Measurable U) :
    MeasurableSet {ω | GenieProtocol.BoundedEnergy (V ω) (S ω) (U ω) cap} := by
  have hi : ∀ i : Fin T,MeasurableSet {ω | i∈S ω ∨ energy (V ω) (U ω i)≤cap} := by
    intro i
    exact (hS i).union (measurableSet_le
      ((projection_measurable d V hV _ ((measurable_pi_apply i).comp hU)).norm.pow_const 2)
      measurable_const)
  convert MeasurableSet.iInter hi using 1
  ext ω
  simp only [Set.mem_setOf_eq,Set.mem_iInter,GenieProtocol.BoundedEnergy]
  exact forall_congr' (fun i => by tauto)

theorem safe_measurable {d T m r : ℕ} {H : Memory.{u}} (P : Policy d T H m r) (cap : ℝ) :
    ∀ (memory : Ω → H), Measurable memory →
    ∀ (V : Ω → Submodule ℝ (Space d)),
      Measurable (fun ω => ProjectionStore.ofSubspace d (V ω)) →
    ∀ (S : Ω → Set (Fin T)), (∀ i,MeasurableSet {ω | i∈S ω}) →
    ∀ (U : Ω → Frame d T), Measurable U →
    MeasurableSet {ω | RawGenieProtocol.Safe cap (compile P (memory ω)) (V ω) (S ω) (U ω)} := by
  induction P with
  | halt =>
    intro memory hm V hV S hS U hU
    exact boundedEnergy_measurable d T cap V hV S hS U hU
  | query q hq respond hr next ih =>
    intro memory hm V hV S hS U hU
    have hv := insert_measurable d V hV (fun ω => q (memory ω)) (hq.comp hm)
    have hz := projections_measurable d T _ hv U hU
    have hn := ih (fun ω => respond (memory ω,RawGenieProtocol.projections d T
      (V ω ⊔ Submodule.span ℝ {q (memory ω)}) (U ω))) (hr.comp (hm.prodMk hz))
      _ hv S hS U hU
    exact (boundedEnergy_measurable d T cap V hV S hS U hU).inter hn
  | reveal j hj respond hr next ih =>
    intro memory hm V hV S hS U hU
    have hjm := hj.comp hm
    have hy := ProjectionObservation.selected_column_measurable d T U hU (fun ω => j (memory ω)) hjm
    have hv := insert_measurable d V hV _ hy
    have hz := projections_measurable d T _ hv U hU
    have hs : ∀ i : Fin T,MeasurableSet {ω | i∈insert (j (memory ω)) (S ω)} := by
      intro i
      have he : MeasurableSet {ω | i=j (memory ω)} := by
        convert hjm (measurableSet_singleton i) using 1
        ext ω
        simp [eq_comm]
      exact he.union (hS i)
    have hn := ih (fun ω => respond (memory ω,(U ω (j (memory ω)),RawGenieProtocol.projections d T
      (V ω ⊔ Submodule.span ℝ {U ω (j (memory ω))}) (U ω))))
      (hr.comp (hm.prodMk (hy.prodMk hz))) _ hv _ hs U hU
    exact (boundedEnergy_measurable d T cap V hV S hS U hU).inter hn
  | adapt update hu next ih =>
    intro memory hm V hV S hS U hU
    exact ih _ (hu.comp hm) V hV S hS U hU
  | branch A hA yes no hy hn =>
    intro memory hm V hV S hS U hU
    have hyes := hy memory hm V hV S hS U hU
    have hno := hn memory hm V hV S hS U hU
    have ha := hm hA
    convert (ha.inter hyes).union (ha.compl.inter hno) using 1
    ext ω
    by_cases h : memory ω∈A <;> simp [compile,h]

theorem initial_unsafe_measurable {d T m r : ℕ} {H : Memory.{u}}
    (P : Policy d T H m r) (cap : ℝ) :
    MeasurableSet {p : H × Frame d T | ¬RawGenieProtocol.Safe cap (compile P p.1) ⊥ ∅ p.2} :=
  (safe_measurable P cap _ measurable_fst _ measurable_const _
    (fun _ => MeasurableSet.empty) _ measurable_snd).compl

end Bilevel.RawGenieBorel
