import SecondOrder.HvpAlgorithmSimulation
import SecondOrder.FiniteSeedProbability

open MeasureTheory

namespace SecondOrder
noncomputable section

/-- The history law draws N fresh samples independently of past queries. -/
def oracleHistoryLaw {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) :
    (N : ℕ) → Measure (FiniteHistory Unit Ω N)
  | 0 => Measure.dirac ()
  | N+1 => (oracleHistoryLaw μ N).prod μ

instance oracleHistoryLaw_probability {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (N : ℕ) : IsProbabilityMeasure (oracleHistoryLaw μ N) := by
  induction N with
  | zero => exact inferInstanceAs (IsProbabilityMeasure (Measure.dirac ()))
  | succ N ih =>
    letI := ih
    exact inferInstanceAs (IsProbabilityMeasure ((oracleHistoryLaw μ N).prod μ))

def oracleHistoryRun {Ω : Type} {Q Y S : Type*} (P : QueryPolicy Q Y S) (reply : Q → Ω → Y) :
    (N : ℕ) → FiniteHistory Unit Ω N → S
  | 0, _ => P.initial
  | N+1, h => P.update N (oracleHistoryRun P reply N h.1)
      (reply (P.query N (oracleHistoryRun P reply N h.1)) h.2)

def oracleHistoryOutput {Ω : Type} {Q Y O S : Type*} (P : OracleAlgorithm Q Y O S)
    (reply : Q → Ω → Y) (N : ℕ) (h : FiniteHistory Unit Ω N) : O :=
  P.output N (oracleHistoryRun P.toQueryPolicy reply N h)

theorem queryPolicyRun_tape_congr {Q Y S Z : Type*} (P : QueryPolicy Q Y S)
    (reply : Q → Z → Y) (z z' : ℕ → Z) (N : ℕ) (hz : ∀ n, n<N → z n=z' n) :
    queryPolicyRun P reply z N=queryPolicyRun P reply z' N := by
  induction N with
  | zero => rfl
  | succ N ih =>
    simp only [queryPolicyRun]
    rw [ih (fun n hn => hz n (by omega)),hz N (by omega)]

theorem oracleHistoryRun_tape {Ω : Type} {Q Y S : Type*} (P : QueryPolicy Q Y S)
    (reply : Q → Ω → Y) (a₀ : Ω) (N : ℕ) (h : FiniteHistory Unit Ω N) :
    oracleHistoryRun P reply N h=queryPolicyRun P reply (finiteHistoryTape a₀ N h) N := by
  induction N with
  | zero => rfl
  | succ N ih =>
    have he := queryPolicyRun_tape_congr P reply (finiteHistoryTape a₀ (N+1) h)
      (finiteHistoryTape a₀ N h.1) N (fun n hn => finiteHistoryTape_succ_lt a₀ N h n hn)
    simp only [oracleHistoryRun,queryPolicyRun,he,finiteHistoryTape_succ_at,ih h.1]

theorem oracleHistoryOutput_tape {Ω : Type} {Q Y O S : Type*} (P : OracleAlgorithm Q Y O S)
    (reply : Q → Ω → Y) (a₀ : Ω) (N : ℕ) (h : FiniteHistory Unit Ω N) :
    oracleHistoryOutput P reply N h=oracleAlgorithmOutput P reply (finiteHistoryTape a₀ N h) N := by
  unfold oracleHistoryOutput oracleAlgorithmOutput
  rw [oracleHistoryRun_tape P.toQueryPolicy reply a₀]

theorem oracleHistoryRun_measurable {Ω : Type} {Ξ Q Y S : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ξ] [MeasurableSpace Q] [MeasurableSpace Y] [MeasurableSpace S]
    (P : Ξ → QueryPolicy Q Y S) (hP : MeasurableQueryPolicyFamily P)
    (reply : Q → Ω → Y) (hr : Measurable (fun w : Q × Ω => reply w.1 w.2)) (N : ℕ) :
    Measurable (fun w : Ξ × FiniteHistory Unit Ω N => oracleHistoryRun (P w.1) reply N w.2) := by
  induction N with
  | zero => exact hP.initial.comp measurable_fst
  | succ N ih =>
    have hs : Measurable (fun w : Ξ × FiniteHistory Unit Ω (N+1) =>
        oracleHistoryRun (P w.1) reply N w.2.1) := ih.comp (measurable_fst.prodMk measurable_snd.fst)
    have hq := (hP.query N).comp (measurable_fst.prodMk hs)
    have hy := hr.comp (hq.prodMk measurable_snd.snd)
    exact (hP.update N).comp (measurable_fst.prodMk (hs.prodMk hy))

theorem oracleHistoryOutput_measurable {Ω : Type} {Ξ Q Y O S : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ξ] [MeasurableSpace Q] [MeasurableSpace Y]
    [MeasurableSpace O] [MeasurableSpace S]
    (P : Ξ → OracleAlgorithm Q Y O S) (hP : MeasurableOracleAlgorithmFamily P)
    (reply : Q → Ω → Y) (hr : Measurable (fun w : Q × Ω => reply w.1 w.2)) (N : ℕ) :
    Measurable (fun w : Ξ × FiniteHistory Unit Ω N => oracleHistoryOutput (P w.1) reply N w.2) :=
  (hP.output N).comp (measurable_fst.prodMk
    (oracleHistoryRun_measurable (fun ξ => (P ξ).toQueryPolicy) hP.toMeasurableQueryPolicyFamily reply hr N))

theorem finiteAdaptiveLaw_iid_toMeasure {Ω : Type} [Fintype Ω] [MeasurableSpace Ω]
    [MeasurableSingletonClass Ω] (p : PMF Ω) (N : ℕ) :
    (finiteAdaptiveLaw (PMF.pure ()) (fun _ _ => p) N).toMeasure=oracleHistoryLaw p.toMeasure N := by
  induction N with
  | zero => exact PMF.toMeasure_pure ()
  | succ N ih =>
    have he : finiteConditionalPMF (finiteAdaptiveLaw (PMF.pure ()) (fun _ _ => p) N) (fun _ => p)=
        finiteProdPMF (finiteAdaptiveLaw (PMF.pure ()) (fun _ _ => p) N) p := by
      ext w
      rfl
    rw [finiteAdaptiveLaw_succ,he,finiteProdPMF_toMeasure,ih]
    rfl

end
end SecondOrder
