import SecondOrder.OracleAlgorithm
import SecondOrder.HvpQueryMeasurability

open MeasureTheory

namespace SecondOrder
noncomputable section

abbrev HvpAlgorithm (d : ℕ) (S : Type*) := OracleAlgorithm (HvpQuery d) (Point d) (Point d) S
abbrev RichAlgorithm (d : ℕ) (S : Type*) := OracleAlgorithm (Point d) (RichReply d) (Point d) S

def hvpAlgorithmRich {d : ℕ} {S : Type*} (P : HvpAlgorithm d S) : RichAlgorithm d S :=
  translateOracleAlgorithm P queryPoint extractHvp

theorem hvpAlgorithmRich_run {Ω S : Type*} {d : ℕ} (P : HvpAlgorithm d S)
    (f : Ω → Point d → ℝ) (z : ℕ → Ω) (n : ℕ) :
    queryPolicyRun (hvpAlgorithmRich P).toQueryPolicy (fun x a => richReply f a x) z n=
      queryPolicyRun P.toQueryPolicy (fun q a => hvpReply f a q) z n :=
  translateOracleAlgorithm_run P queryPoint extractHvp _ _ (fun q a => one_rich_call_simulates_hvp f a q) z n

theorem hvpAlgorithmRich_output {Ω S : Type*} {d : ℕ} (P : HvpAlgorithm d S)
    (f : Ω → Point d → ℝ) (z : ℕ → Ω) (n : ℕ) :
    oracleAlgorithmOutput (hvpAlgorithmRich P) (fun x a => richReply f a x) z n=
      oracleAlgorithmOutput P (fun q a => hvpReply f a q) z n :=
  translateOracleAlgorithm_output P queryPoint extractHvp _ _ (fun q a => one_rich_call_simulates_hvp f a q) z n

theorem hvpAlgorithmRich_measurable {Ξ S : Type*} [MeasurableSpace Ξ] [MeasurableSpace S] {d : ℕ}
    (P : Ξ → HvpAlgorithm d S) (hP : MeasurableOracleAlgorithmFamily P) :
    MeasurableOracleAlgorithmFamily (fun ξ => hvpAlgorithmRich (P ξ)) :=
  translateOracleAlgorithm_measurable P hP queryPoint extractHvp (queryPoint_measurable d) (extractHvp_measurable d)

def hvpAlgorithmRichPolicy {d : ℕ} {S : Type*} (P : HvpAlgorithm d S) (N : ℕ) :
    QueryPolicy (Point d) (RichReply d) S := oracleAlgorithmPolicy (hvpAlgorithmRich P) N

theorem hvpAlgorithmRichPolicy_output {Ω S : Type*} {d : ℕ} (P : HvpAlgorithm d S)
    (f : Ω → Point d → ℝ) (z : ℕ → Ω) (N : ℕ) :
    (hvpAlgorithmRichPolicy P N).query N
      (queryPolicyRun (hvpAlgorithmRichPolicy P N) (fun x a => richReply f a x) z N)=
      oracleAlgorithmOutput P (fun q a => hvpReply f a q) z N :=
  (oracleAlgorithmPolicy_output (hvpAlgorithmRich P) _ z N).trans (hvpAlgorithmRich_output P f z N)

theorem hvpAlgorithmRichPolicy_measurable {Ξ S : Type*} [MeasurableSpace Ξ] [MeasurableSpace S] {d : ℕ}
    (P : Ξ → HvpAlgorithm d S) (hP : MeasurableOracleAlgorithmFamily P) (N : ℕ) :
    MeasurableQueryPolicyFamily (fun ξ => hvpAlgorithmRichPolicy (P ξ) N) :=
  oracleAlgorithmPolicy_measurable _ (hvpAlgorithmRich_measurable P hP) N

/-- Simulation preserves every event of the output under any joint law of
private seeds and sample tapes. In particular it preserves the independent law. -/
theorem hvpAlgorithmRich_output_event {Ξ Ω S W : Type*} [MeasurableSpace W] {d : ℕ}
    (P : Ξ → HvpAlgorithm d S) (f : Ω → Point d → ℝ)
    (seed : W → Ξ) (tape : W → ℕ → Ω) (law : Measure W) (N : ℕ) (event : Point d → Prop) :
    law {w | event (oracleAlgorithmOutput (hvpAlgorithmRich (P (seed w)))
      (fun x a => richReply f a x) (tape w) N)}=
    law {w | event (oracleAlgorithmOutput (P (seed w)) (fun q a => hvpReply f a q) (tape w) N)} := by
  congr 1
  ext w
  simp only [Set.mem_setOf_eq,hvpAlgorithmRich_output]

end
end SecondOrder
