import SecondOrder.OracleAlgorithm

open SecondOrder MeasureTheory
open scoped Classical

namespace SampleReuse
noncomputable section

/-- Preserve the first stopped output and perform only idle queries afterward.
The idle query can be a free Hessian query in a marginal gradient analysis. -/
def freezeOracle {Q Y O S : Type} (P : OracleAlgorithm Q Y O S)
    (stop : ℕ → S → Bool) (idle : Q) : OracleAlgorithm Q Y O (S × (Bool × O)) where
  initial := (P.initial,stop 0 P.initial,P.output 0 P.initial)
  query n s := if s.2.1 then idle else P.query n s.1
  update n s y := if s.2.1 then s else
    let next := P.update n s.1 y
    (next,stop (n+1) next,P.output (n+1) next)
  output _ s := s.2.2

theorem freezeOracle_measurable {Ξ Q Y O S : Type}
    [MeasurableSpace Ξ] [MeasurableSpace Q] [MeasurableSpace Y]
    [MeasurableSpace O] [MeasurableSpace S]
    (P : Ξ → OracleAlgorithm Q Y O S) (hP : MeasurableOracleAlgorithmFamily P)
    (stop : Ξ → ℕ → S → Bool) (hs : ∀ n, Measurable (fun w : Ξ × S => stop w.1 n w.2)) (idle : Q) :
    MeasurableOracleAlgorithmFamily (fun ξ => freezeOracle (P ξ) (stop ξ) idle) := by
  refine ⟨⟨?_,?_,?_⟩,?_⟩
  · exact hP.initial.prodMk (((hs 0).comp (measurable_id.prodMk hP.initial)).prodMk
      ((hP.output 0).comp (measurable_id.prodMk hP.initial)))
  · intro n
    exact Measurable.ite (measurable_snd.snd.fst (measurableSet_singleton true)) measurable_const
      ((hP.query n).comp (measurable_fst.prodMk measurable_snd.fst))
  · intro n
    have hn : Measurable (fun w : Ξ × ((S × (Bool × O)) × Y) => (P w.1).update n w.2.1.1 w.2.2) :=
      (hP.update n).comp (measurable_fst.prodMk (measurable_snd.fst.fst.prodMk measurable_snd.snd))
    exact Measurable.ite (measurable_snd.fst.snd.fst (measurableSet_singleton true)) measurable_snd.fst
      (hn.prodMk (((hs (n+1)).comp (measurable_fst.prodMk hn)).prodMk
        ((hP.output (n+1)).comp (measurable_fst.prodMk hn))))
  · intro n
    exact measurable_snd.snd.snd

theorem freezeOracle_run_before {Q Y O S Z : Type}
    (P : OracleAlgorithm Q Y O S) (stop : ℕ → S → Bool) (idle : Q)
    (reply : Q → Z → Y) (tape : ℕ → Z) : ∀ n,
    (∀ k < n, stop k (queryPolicyRun P.toQueryPolicy reply tape k) = false) →
    queryPolicyRun (freezeOracle P stop idle).toQueryPolicy reply tape n =
      (queryPolicyRun P.toQueryPolicy reply tape n,
        stop n (queryPolicyRun P.toQueryPolicy reply tape n),
        P.output n (queryPolicyRun P.toQueryPolicy reply tape n)) := by
  intro n
  induction n with
  | zero => intro hs; rfl
  | succ n ih =>
    intro hs
    have hh := ih (fun k hk => hs k (by omega))
    simp only [queryPolicyRun]
    rw [hh]
    simp only [freezeOracle,hs n (by omega),Bool.false_eq_true,if_false]

theorem freezeOracle_run_stable {Q Y O S Z : Type}
    (P : OracleAlgorithm Q Y O S) (stop : ℕ → S → Bool) (idle : Q)
    (reply : Q → Z → Y) (tape : ℕ → Z) {k : ℕ}
    (hk : (queryPolicyRun (freezeOracle P stop idle).toQueryPolicy reply tape k).2.1 = true) :
    ∀ n, k ≤ n → queryPolicyRun (freezeOracle P stop idle).toQueryPolicy reply tape n =
      queryPolicyRun (freezeOracle P stop idle).toQueryPolicy reply tape k := by
  intro n hn
  obtain ⟨r,rfl⟩ := Nat.exists_eq_add_of_le hn
  clear hn
  induction r with
  | zero => rfl
  | succ r ih =>
    change (freezeOracle P stop idle).update (k+r)
      (queryPolicyRun (freezeOracle P stop idle).toQueryPolicy reply tape (k+r))
      (reply ((freezeOracle P stop idle).query (k+r)
        (queryPolicyRun (freezeOracle P stop idle).toQueryPolicy reply tape (k+r))) (tape (k+r))) = _
    rw [ih]
    exact if_pos hk

/-- The frozen execution is the original execution through its first stop;
the output remains identical at every later horizon. -/
theorem freezeOracle_first_stop {Q Y O S Z : Type}
    (P : OracleAlgorithm Q Y O S) (stop : ℕ → S → Bool) (idle : Q)
    (reply : Q → Z → Y) (tape : ℕ → Z) {k n : ℕ} (hkn : k ≤ n)
    (hk : stop k (queryPolicyRun P.toQueryPolicy reply tape k)=true)
    (hbefore : ∀ j < k, stop j (queryPolicyRun P.toQueryPolicy reply tape j)=false) :
    queryPolicyRun (freezeOracle P stop idle).toQueryPolicy reply tape n =
      (queryPolicyRun P.toQueryPolicy reply tape k,true,
        P.output k (queryPolicyRun P.toQueryPolicy reply tape k)) := by
  have he := freezeOracle_run_before P stop idle reply tape k hbefore
  have hh : (queryPolicyRun (freezeOracle P stop idle).toQueryPolicy reply tape k).2.1=true := by
    rw [he]
    exact hk
  rw [freezeOracle_run_stable P stop idle reply tape hh n hkn,he,hk]

end
end SampleReuse
