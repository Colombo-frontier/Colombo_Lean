import SecondOrder.SeededQueryPolicy

open MeasureTheory
open scoped Classical

namespace SecondOrder
noncomputable section

/-- An adaptive oracle algorithm with a separate, uncharged output map.
The algorithm's state contains only its private data and previous replies. -/
structure OracleAlgorithm (Q Y O S : Type*) extends QueryPolicy Q Y S where
  output : ℕ → S → O

def oracleAlgorithmOutput {Q Y O S Z : Type*} (P : OracleAlgorithm Q Y O S)
    (reply : Q → Z → Y) (z : ℕ → Z) (N : ℕ) : O :=
  P.output N (queryPolicyRun P.toQueryPolicy reply z N)

structure MeasurableOracleAlgorithmFamily {Ξ Q Y O S : Type*}
    [MeasurableSpace Ξ] [MeasurableSpace Q] [MeasurableSpace Y]
    [MeasurableSpace O] [MeasurableSpace S]
    (P : Ξ → OracleAlgorithm Q Y O S) : Prop extends
    MeasurableQueryPolicyFamily (fun ξ => (P ξ).toQueryPolicy) where
  output : ∀ n, Measurable (fun w : Ξ × S => (P w.1).output n w.2)

theorem oracleAlgorithmOutput_measurable_seed {Ξ Q Y O S Z : Type*}
    [MeasurableSpace Ξ] [MeasurableSpace Q] [MeasurableSpace Y]
    [MeasurableSpace O] [MeasurableSpace S]
    (P : Ξ → OracleAlgorithm Q Y O S) (hP : MeasurableOracleAlgorithmFamily P)
    (reply : Q → Z → Y) (hreply : ∀ z, Measurable (fun q => reply q z)) (z : ℕ → Z) (N : ℕ) :
    Measurable (fun ξ => oracleAlgorithmOutput (P ξ) reply z N) :=
  (hP.output N).comp (measurable_id.prodMk
    (queryPolicyRun_measurable_seed (fun ξ => (P ξ).toQueryPolicy) hP.toMeasurableQueryPolicyFamily reply hreply z N))

/-- Translate a whole adaptive program by converting each requested query
and extracting its answer from the richer reply. Output is unchanged. -/
def translateOracleAlgorithm {Q Y Q' Y' O S : Type*} (P : OracleAlgorithm Q Y O S)
    (encode : Q → Q') (decode : Q → Y' → Y) : OracleAlgorithm Q' Y' O S where
  initial := P.initial
  query n s := encode (P.query n s)
  update n s r := P.update n s (decode (P.query n s) r)
  output := P.output

theorem translateOracleAlgorithm_run {Q Y Q' Y' O S Z : Type*} (P : OracleAlgorithm Q Y O S)
    (encode : Q → Q') (decode : Q → Y' → Y)
    (reply : Q → Z → Y) (rich : Q' → Z → Y')
    (hsim : ∀ q z, decode q (rich (encode q) z)=reply q z) (z : ℕ → Z) (n : ℕ) :
    queryPolicyRun (translateOracleAlgorithm P encode decode).toQueryPolicy rich z n=
      queryPolicyRun P.toQueryPolicy reply z n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [queryPolicyRun]
    rw [ih]
    simp only [translateOracleAlgorithm,hsim]

theorem translateOracleAlgorithm_output {Q Y Q' Y' O S Z : Type*} (P : OracleAlgorithm Q Y O S)
    (encode : Q → Q') (decode : Q → Y' → Y)
    (reply : Q → Z → Y) (rich : Q' → Z → Y')
    (hsim : ∀ q z, decode q (rich (encode q) z)=reply q z) (z : ℕ → Z) (n : ℕ) :
    oracleAlgorithmOutput (translateOracleAlgorithm P encode decode) rich z n=
      oracleAlgorithmOutput P reply z n := by
  unfold oracleAlgorithmOutput
  rw [translateOracleAlgorithm_run P encode decode reply rich hsim]
  rfl

theorem translateOracleAlgorithm_measurable {Ξ Q Y Q' Y' O S : Type*}
    [MeasurableSpace Ξ] [MeasurableSpace Q] [MeasurableSpace Y] [MeasurableSpace Q']
    [MeasurableSpace Y'] [MeasurableSpace O] [MeasurableSpace S]
    (P : Ξ → OracleAlgorithm Q Y O S) (hP : MeasurableOracleAlgorithmFamily P)
    (encode : Q → Q') (decode : Q → Y' → Y) (he : Measurable encode)
    (hd : Measurable (fun w : Q × Y' => decode w.1 w.2)) :
    MeasurableOracleAlgorithmFamily (fun ξ => translateOracleAlgorithm (P ξ) encode decode) := by
  refine ⟨⟨hP.initial,fun n => he.comp (hP.query n),?_⟩,hP.output⟩
  intro n
  have hq : Measurable (fun w : Ξ × (S × Y') => (P w.1).query n w.2.1) :=
    (hP.query n).comp (measurable_fst.prodMk measurable_snd.fst)
  have hr := hd.comp (hq.prodMk measurable_snd.snd)
  exact (hP.update n).comp (measurable_fst.prodMk (measurable_snd.fst.prodMk hr))

/-- Use the final query-map slot only as an uncharged output slot, to match
the lower-bound policy interface. No reply at time N is read. -/
def oracleAlgorithmPolicy {Q Y S : Type*} (P : OracleAlgorithm Q Y Q S) (N : ℕ) : QueryPolicy Q Y S where
  initial := P.initial
  query n s := if n=N then P.output n s else P.query n s
  update := P.update

theorem oracleAlgorithmPolicy_run {Q Y S Z : Type*} (P : OracleAlgorithm Q Y Q S)
    (reply : Q → Z → Y) (z : ℕ → Z) (N n : ℕ) (hn : n≤N) :
    queryPolicyRun (oracleAlgorithmPolicy P N) reply z n=queryPolicyRun P.toQueryPolicy reply z n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hn' : n≠N := by omega
    simp only [queryPolicyRun]
    rw [ih (by omega)]
    simp only [oracleAlgorithmPolicy,if_neg hn']

theorem oracleAlgorithmPolicy_output {Q Y S Z : Type*} (P : OracleAlgorithm Q Y Q S)
    (reply : Q → Z → Y) (z : ℕ → Z) (N : ℕ) :
    (oracleAlgorithmPolicy P N).query N (queryPolicyRun (oracleAlgorithmPolicy P N) reply z N)=
      oracleAlgorithmOutput P reply z N := by
  rw [oracleAlgorithmPolicy_run P reply z N N le_rfl]
  simp [oracleAlgorithmPolicy,oracleAlgorithmOutput]

theorem oracleAlgorithmPolicy_measurable {Ξ Q Y S : Type*}
    [MeasurableSpace Ξ] [MeasurableSpace Q] [MeasurableSpace Y] [MeasurableSpace S]
    (P : Ξ → OracleAlgorithm Q Y Q S) (hP : MeasurableOracleAlgorithmFamily P) (N : ℕ) :
    MeasurableQueryPolicyFamily (fun ξ => oracleAlgorithmPolicy (P ξ) N) := by
  refine ⟨hP.initial,?_,hP.update⟩
  intro n
  by_cases hn : n=N
  · simpa only [oracleAlgorithmPolicy,if_pos hn] using hP.output n
  · simpa only [oracleAlgorithmPolicy,if_neg hn] using hP.query n

end
end SecondOrder
