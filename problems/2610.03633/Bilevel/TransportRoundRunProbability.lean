import Bilevel.TransportRoundBatchProbability
import Bilevel.TransportControllerPriorProjection

/-! Actual finite-run failure and projection bounds. Query, forward, and
reverse events all refer to the same original instance and executed history.
Only public finite dimension inequalities and measurable algorithms remain
as premises; no angle-good event or local probability premise is supplied. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace Bilevel.TransportRound
open EuclideanGaussian TransportNetwork TransportNetworkAuxiliary TransportControllerMachine
set_option maxHeartbeats 800000

theorem runFailureEvent_split {H : Type*} {n D p T : ℕ} (hT : T≤D) (a : ℝ)
    (choose : ∀ t,H × Generators n D (size n p 1 1 t) → Queries n D p)
    (respond : ∀ t,StepData H n D (size n p 1 1 t) p T → H) (memory : H) (z : Latent n D) (M : ℕ) :
    (memory,z)∈runFailureEvent hT a choose respond M ↔
      runQueryBad hT a choose respond (prefixNames n T) (memory,seed T hT z) z M ∨
      ∃ t : Fin M,runBatchBad hT choose respond memory z t := by
  constructor
  · rintro ⟨t,ht,hb⟩
    rcases hb with hq|he
    · exact Or.inl ⟨t,ht,hq⟩
    · exact Or.inr ⟨⟨t,ht⟩,he⟩
  · rintro (⟨t,ht,hq⟩|⟨t,he⟩)
    · exact ⟨t,ht,Or.inl hq⟩
    · exact ⟨t,t.isLt,Or.inr he⟩

theorem measure_exists_fin_sum {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) {n : ℕ}
    (P : Fin n → Ω → Prop) (b : Fin n → ℝ≥0∞) (hb : ∀ i,μ {s | P i s}≤b i) :
    μ {s | ∃ i,P i s}≤∑ i,b i := by
  have he : {s | ∃ i,P i s}=⋃ i,{s | P i s} := by ext s; simp
  rw [he]
  calc
    _ ≤ ∑' i,μ {s | P i s} := measure_iUnion_le _
    _ ≤ ∑' i,b i := ENNReal.tsum_le_tsum hb
    _ = _ := tsum_fintype _

def runBudget (n p T M r : ℕ) (a : ℝ) : ℝ≥0∞ :=
  (M:ℝ≥0∞)*((n+1)*p:ℕ)*ENNReal.ofReal ((T:ℝ)/((r:ℝ)*a))+
    ∑ t : Fin M,batchBudget n p t r

theorem actual_run_failure_probability {n D T p k : ℕ} (H : Memory) (hT : T≤D) (hpos : 0<T)
    (choose : ∀ t,H × Generators n D (size n p 1 1 t) → Queries n D p) (hc : ∀ t,Measurable (choose t))
    (respond : ∀ t,StepData H n D (size n p 1 1 t) p T → H) (hr : ∀ t,Measurable (respond t))
    (ρ : Measure H) [IsProbabilityMeasure ρ] (M r : ℕ) (hrpos : 0<r) (a : ℝ) (ha : 0<a)
    (hquery : queryCap n p 1 1 M+r≤D)
    (hedge : ∀ t<M,T+(1+((size n p 1 1 t+p)+historyProbes n p 1 1 t))+r≤D) :
    (ρ.prod (TransportNetworkAuxiliary.law n D k))
      {s | (s.1,s.2.1)∈runFailureEvent hT a choose respond M}≤runBudget n p T M r a := by
  let Q := {s : H × Sample n D k | runQueryBad hT a choose respond (prefixNames n T) (s.1,seed T hT s.2.1) s.2.1 M}
  let B := fun t : Fin M => fun s : H × Sample n D k => runBatchBad hT choose respond s.1 s.2.1 t
  have he : {s : H × Sample n D k | (s.1,s.2.1)∈runFailureEvent hT a choose respond M}=Q∪{s | ∃ t,B t s} := by
    ext s
    exact runFailureEvent_split hT a choose respond s.1 s.2.1 M
  have hQ : (ρ.prod (TransportNetworkAuxiliary.law n D k)) Q≤
      (M:ℝ≥0∞)*((n+1)*p:ℕ)*ENNReal.ofReal ((T:ℝ)/((r:ℝ)*a)) :=
    augmented_run_query_failure hT hpos a ha r hrpos choose hc respond hr ρ M hquery
  have hB : ∀ t : Fin M,(ρ.prod (TransportNetworkAuxiliary.law n D k)) {s | B t s}≤batchBudget n p t r := by
    intro t
    exact actual_batch_failure_probability H hT choose hc respond hr ρ t r hrpos (hedge t t.isLt)
  rw [he,runBudget]
  exact (measure_union_le _ _).trans (add_le_add hQ (measure_exists_fin_sum _ B _ hB))

theorem actual_projection_failure_probability {n D T p k : ℕ} (H : Memory) (hT : T≤D) (hn : 0<n) (hpos : 0<T)
    (choose : ∀ t,H × Generators n D (size n p 1 1 t) → Queries n D p) (hc : ∀ t,Measurable (choose t))
    (respond : ∀ t,StepData H n D (size n p 1 1 t) p T → H) (hr : ∀ t,Measurable (respond t))
    (ρ : Measure H) [IsProbabilityMeasure ρ] (M r : ℕ) (hrpos : 0<r) {b : ℝ} (hb : 0<b)
    (hquery : queryCap n p 1 1 M+r≤D)
    (hedge : ∀ t<M,T+(1+((size n p 1 1 t+p)+historyProbes n p 1 1 t))+r≤D) :
    (ρ.prod (TransportNetworkAuxiliary.law n D k)) {s | ∃ t≤M,∃ v : Vertex n,∃ i : Fin T,
      ¬Protected t v i ∧ b<‖ProjectionGeometry.project
        (known (run T hT choose respond (prefixNames n T) (s.1,seed T hT s.2.1) s.2.1 t).2 v)
        (frame T hT s.2.1 v i)‖}≤runBudget n p T M r (queryTolerance n p M b) := by
  apply le_trans (measure_mono ?_)
    (actual_run_failure_probability H hT hpos choose hc respond hr ρ M r hrpos _ (queryTolerance_pos n p M hb) hquery hedge)
  rintro s ⟨t,ht,v,i,hi,hbad⟩
  by_contra hnone
  have hgood : ∀ j<M,¬runFailure hT (queryTolerance n p M b) choose respond s.1 s.2.1 j := by
    intro j hj hfail
    exact hnone ⟨j,hj,hfail⟩
  exact (not_lt_of_ge (run_projection_bound hT hn hpos choose respond s.1 s.2.1 M hb hgood t ht v i hi)) hbad

end Bilevel.TransportRound
