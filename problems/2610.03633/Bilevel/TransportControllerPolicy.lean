import Bilevel.TransportControllerRawMeasurable

/-! Borel adaptive policies executing the actual round function. Compilation
to the conditional-probability plan preserves execution and discharges its
continuation regularity from the policy's ordinary measurable request and
memory-update functions. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace Bilevel.TransportRound
open EuclideanGaussian TransportNetwork
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000

def afterObservation {H : Type*} {n D m p c T : ℕ}
    (choose : H × Generators n D m → Queries n D p) (respond : StepData H n D m p T → H)
    (s : H × Generators n D m) (o : Observed n D m p c T) : H × Generators n D (nextSize n p c m) :=
  (respond (s,o.1,o.2.1),augment (outputs (augment s.2 (choose s)) o.2.1) o.2.2)

theorem afterObservation_measurable {H : Type*} [MeasurableSpace H] {n D m p c T : ℕ}
    (choose : H × Generators n D m → Queries n D p) (hc : Measurable choose)
    (respond : StepData H n D m p T → H) (hr : Measurable respond) :
    Measurable (fun z : (H × Generators n D m) × Observed n D m p c T => afterObservation choose respond z.1 z.2) := by
  have hg : Measurable (fun z : (H × Generators n D m) × Observed n D m p c T => augment z.1.2 (choose z.1)) :=
    (augment_measurable n D m p).comp
      ((measurable_snd.comp measurable_fst).prodMk (hc.comp measurable_fst))
  have hy : Measurable (fun z : (H × Generators n D m) × Observed n D m p c T => z.2.2.1) :=
    measurable_fst.comp (measurable_snd.comp measurable_snd)
  have hnames : Measurable (fun z : (H × Generators n D m) × Observed n D m p c T => z.2.2.2) :=
    measurable_snd.comp (measurable_snd.comp measurable_snd)
  exact (hr.comp (measurable_fst.prodMk ((measurable_fst.comp measurable_snd).prodMk hy))).prodMk
    ((augment_measurable n D ((m+p)+(n*(m+p)+n*(m+p))) c).comp
      (((outputs_measurable n D (m+p)).comp (hg.prodMk hy)).prodMk hnames))

inductive Policy (H : Type*) [MeasurableSpace H] (n D p c T : ℕ) : ℕ → ℕ → Type _
  | halt {m : ℕ} : Policy H n D p c T m 0
  | step {m h : ℕ} (choose : H × Generators n D m → Queries n D p) (hc : Measurable choose)
      (respond : StepData H n D m p T → H) (hr : Measurable respond)
      (names : Vertex n → Fin c → Option (Fin T))
      (next : Policy H n D p c T (nextSize n p c m) h) : Policy H n D p c T m (h+1)

def compilePolicy {H : Type*} [MeasurableSpace H] {n D p c T : ℕ} :
    {m h : ℕ} → Policy H n D p c T m h → H × Generators n D m → Plan n D p c T m h
  | _,_,.halt,_ => .halt
  | _,_,.step choose _ respond _ names next,s => .step (choose s) names
      (fun o => compilePolicy next (afterObservation choose respond s o))

def policyBad {H : Type*} [MeasurableSpace H] {n D p c T : ℕ} (hT : T≤D) (a : ℝ) :
    {m h : ℕ} → Policy H n D p c T m h → H × Generators n D m → Latent n D → Prop
  | _,_,.halt,_,_ => False
  | _,_,.step choose _ respond _ names next,s,z =>
    TransportRoundQuery.queryPhaseBad T hT a (requests (choose s)) (known s.2) z ∨
    policyBad hT a next (round T hT choose respond names s z) z

theorem compilePolicy_bad {H : Type*} [MeasurableSpace H] {n D p c T m h : ℕ}
    (hT : T≤D) (a : ℝ) (P : Policy H n D p c T m h) (s : H × Generators n D m) (z : Latent n D) :
    planBad hT a (compilePolicy P s) s.2 z ↔ policyBad hT a P s z := by
  induction P with
  | halt => rfl
  | step choose hc respond hr names next ih =>
    simp only [compilePolicy,planBad,policyBad]
    exact or_congr_right (ih _)

theorem policyBad_measurable {H : Type*} [MeasurableSpace H] {n D p c T m h : ℕ}
    (hT : T≤D) (a : ℝ) (P : Policy H n D p c T m h) :
    MeasurableSet {z : (H × Generators n D m) × Latent n D | policyBad hT a P z.1 z.2} := by
  induction P with
  | halt => exact MeasurableSet.empty
  | step choose hc respond hr names next ih =>
    exact (requests_bad_joint_measurable hT a _ (measurable_snd.comp measurable_fst)
      _ (hc.comp measurable_fst) _ measurable_snd).union
        (((round_measurable T hT choose hc respond hr names).prodMk measurable_snd) ih)

theorem compilePolicy_regular {H : Type*} [MeasurableSpace H] {n D p c T m h : ℕ}
    (hT : T≤D) (a : ℝ) (P : Policy H n D p c T m h) (s : H × Generators n D m) :
    (compilePolicy P s).Regular hT a s.2 := by
  induction P with
  | halt => trivial
  | step choose hc respond hr names next ih =>
    constructor
    · have hm : Measurable (fun p : Observed n D _ p c T × Latent n D =>
          (afterObservation choose respond s p.1,p.2)) :=
        (((afterObservation_measurable choose hc respond hr).comp
          (measurable_const.prodMk measurable_fst)).prodMk measurable_snd)
      have hh := hm (policyBad_measurable hT a next)
      simpa only [Set.mem_preimage,Set.mem_setOf_eq,← compilePolicy_bad] using hh
    · intro o
      exact ih (afterObservation choose respond s o)

theorem policy_query_failure {H : Type*} [MeasurableSpace H] {n D p c T m h : ℕ}
    (hT : T≤D) (a : ℝ) (ha : 0<a) (r : ℕ) (hr : 0<r) (P : Policy H n D p c T m h)
    (s : H × Generators n D m) (hD : queryCap n p c m h+r≤D)
    (μ : Measure (Latent n D)) [IsProbabilityMeasure μ] (hμ : Invariant (known s.2) μ) :
    μ {z | policyBad hT a P s z} ≤
      (h:ℝ≥0∞)*((n+1)*p:ℕ)*ENNReal.ofReal ((T:ℝ)/((r:ℝ)*a)) := by
  have hh := finite_round_query_failure hT a ha r hr (compilePolicy P s) s.2
    (compilePolicy_regular hT a P s) hD μ hμ
  simpa only [compilePolicy_bad] using hh

end Bilevel.TransportRound
