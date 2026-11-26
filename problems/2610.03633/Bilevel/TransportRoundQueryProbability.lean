import Bilevel.TransportRoundQueryPhase
import Bilevel.TransportRoundPosterior
import Bilevel.TransportNetworkProbability

/-! Finite conditional assembly of raw-query failures through actual frozen
round transcripts. The same latent network is retained across all rounds.
Regularity here is only Borel regularity of continuation events. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace Bilevel.TransportRound
open EuclideanGaussian TransportNetwork
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000

def requests {n D p : ℕ} (q : Queries n D p) : List (TransportRoundQuery.Request n D) :=
  List.ofFn (fun i : Fin ((n+1)*p) =>
    let vi : Vertex n × Fin p := finProdFinEquiv.symm i
    (vi.1,q vi.1 vi.2))

theorem requests_length {n D p : ℕ} (q : Queries n D p) : (requests q).length=(n+1)*p := List.length_ofFn

def queryCap (n p c : ℕ) : ℕ → ℕ → ℕ
  | m,0 => m
  | m,h+1 => max (m+(n+1)*p) (queryCap n p c (nextSize n p c m) h)

inductive Plan (n D p c T : ℕ) : ℕ → ℕ → Type
  | halt {m : ℕ} : Plan n D p c T m 0
  | step {m h : ℕ} (q : Queries n D p) (names : Vertex n → Fin c → Option (Fin T))
      (next : Observed n D m p c T → Plan n D p c T (nextSize n p c m) h) : Plan n D p c T m (h+1)

def planBad {n D p c T : ℕ} (hT : T≤D) (a : ℝ) :
    {m h : ℕ} → Plan n D p c T m h → Generators n D m → Latent n D → Prop
  | _,_,.halt,_,_ => False
  | _,_,.step q names next,g,z =>
    TransportRoundQuery.queryPhaseBad T hT a (requests q) (known g) z ∨
    let o := observe T hT g q names z
    planBad hT a (next o) (augment (outputs (augment g q) o.2.1) o.2.2) z

def Plan.Regular {n D p c T : ℕ} (hT : T≤D) (a : ℝ) :
    {m h : ℕ} → Plan n D p c T m h → Generators n D m → Prop
  | _,_,.halt,_ => True
  | m,_,.step q _ next,g =>
    MeasurableSet {z : Observed n D m p c T × Latent n D |
      planBad hT a (next z.1) (augment (outputs (augment g q) z.1.2.1) z.1.2.2) z.2} ∧
      ∀ o, Plan.Regular hT a (next o) (augment (outputs (augment g q) o.2.1) o.2.2)

theorem planBad_measurable {n D p c T m h : ℕ} (hT : T≤D) (a : ℝ)
    (P : Plan n D p c T m h) (g : Generators n D m) (hP : P.Regular hT a g) :
    MeasurableSet {z | planBad hT a P g z} := by
  cases P with
  | halt => exact MeasurableSet.empty
  | step q names next =>
    exact (TransportRoundQuery.queryPhaseBad_measurable T hT a (requests q) (known g)).union
      (((observe_measurable T hT g q names).prodMk measurable_id) hP.1)

theorem finite_round_query_failure {n D p c T m h : ℕ} (hT : T≤D) (a : ℝ) (ha : 0<a)
    (r : ℕ) (hr : 0<r) (P : Plan n D p c T m h) :
    ∀ (g : Generators n D m), P.Regular hT a g → queryCap n p c m h+r≤D →
      ∀ (μ : Measure (Latent n D)) [IsProbabilityMeasure μ], Invariant (known g) μ →
        μ {z | planBad hT a P g z} ≤
          (h:ℝ≥0∞)*((n+1)*p:ℕ)*ENNReal.ofReal ((T:ℝ)/((r:ℝ)*a)) := by
  induction P with
  | halt =>
    intro g hP hD μ _ hμ
    simp [planBad]
  | @step m h q names next ih =>
    intro g hP hD μ _ hμ
    have hhead := TransportRoundQuery.query_phase_failure T hT a ha r hr (requests q)
      (known g) m (fun v => TransportGeneratorStore.span_rank_le (g v))
      (by rw [requests_length]; exact (Nat.add_le_add_right (le_max_left _ _) r).trans hD) μ hμ
    rw [requests_length] at hhead
    have htail : μ {z | planBad hT a (next (observe T hT g q names z))
        (augment (outputs (augment g q) (observe T hT g q names z).2.1) (observe T hT g q names z).2.2) z} ≤
        (h:ℝ≥0∞)*((n+1)*p:ℕ)*ENNReal.ofReal ((T:ℝ)/((r:ℝ)*a)) := by
      apply observation_tail_bound μ (observe T hT g q names) (observe_measurable T hT g q names)
        (fun o z => planBad hT a (next o) (augment (outputs (augment g q) o.2.1) o.2.2) z) hP.1
      filter_upwards [actual_round_posterior T hT g q names μ hμ] with o ho
      exact ih o _ (hP.2 o) ((Nat.add_le_add_right (le_max_right _ _) r).trans hD) _ ho
    apply (measure_union_le _ _).trans
    convert add_le_add hhead htail using 1
    simp only [planBad,Nat.cast_add,Nat.cast_one,add_mul,one_mul,add_comm]

end Bilevel.TransportRound
