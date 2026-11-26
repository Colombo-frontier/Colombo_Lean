import MinimaxAudit.BorelHistory
import MinimaxAudit.EvaluatedPolicy

open Set MeasureTheory
namespace MinimaxAudit.BorelEvaluatedPolicy
open VIReference.Pilot BorelHistory EvaluatedPolicy
noncomputable section
variable {p dx dy N : ℕ} {X : Set (Primal dx)} {Y : Set (Dual dy)}

private theorem history_ofFn_snoc {m : ℕ} (v : Fin m → Entry p dx dy) (e : Entry p dx dy) :
    List.ofFn (Fin.snoc v e) = List.ofFn v ++ [e] := by
  rw [List.ofFn_succ']
  simp

/-- The output-point query at an original stopping history is Borel. -/
theorem evaluated_nil_action_measurable
    (A : BorelDeterministicScalarPolicy p dx dy N X Y) (fill : productDomain X Y) :
    Measurable (fun h => evaluatedActionFrom A.policy h []) := by
  classical
  have he := (comap_measurable optionPointEncoding).comp A.measurable_query
  let pick : ScalarHistory p dx dy → SaddleSpace dx dy :=
    fun h => Sum.elim (fun _ : Unit => fill.1) id (optionPointEncoding (A.policy.query h))
  have hp : Measurable (Sum.elim (fun _ : Unit => fill.1) (id : SaddleSpace dx dy → SaddleSpace dx dy)) :=
    measurable_fun_sum measurable_const measurable_id
  have hpick : Measurable pick := hp.comp he
  have hnone := measurable_query_none A.measurable_query
  have hval : Measurable (fun h => if A.policy.query h = none then A.policy.output h else pick h) :=
    Measurable.ite hnone A.measurable_output hpick
  have hfeas : ∀ h, (if A.policy.query h = none then A.policy.output h else pick h) ∈ productDomain X Y := by
    intro h
    cases hq : A.policy.query h with
    | none => simp only [hq, ↓reduceIte]; exact A.policy.feasible_output h
    | some q => simpa [hq, pick, optionPointEncoding] using A.policy.feasible_query h q hq
  have hsub : Measurable (fun h => (⟨if A.policy.query h = none then A.policy.output h else pick h,
      hfeas h⟩ : productDomain X Y)) := hval.subtype_mk
  have hm : Measurable (fun h => (Sum.inr
      (⟨if A.policy.query h = none then A.policy.output h else pick h, hfeas h⟩ : productDomain X Y) :
      OracleAction (productDomain X Y))) := measurable_inr.comp hsub
  convert hm using 1
  funext h
  unfold evaluatedActionFrom
  split <;> rename_i hq <;> simp [hq, pick, optionPointEncoding]

/-- Fixed finite sequences allow a measurable replay of all original stops.
Both the original prefix and the remaining response sequence are variable. -/
theorem evaluated_action_ofFn_measurable
    (A : BorelDeterministicScalarPolicy p dx dy N X Y) (fill : productDomain X Y) :
    ∀ n m, Measurable (fun v : (Fin m → Entry p dx dy) × (Fin n → Entry p dx dy) =>
      evaluatedActionFrom A.policy (List.ofFn v.1) (List.ofFn v.2)) := by
  classical
  intro n
  induction n with
  | zero =>
    intro m
    simpa [Function.comp_def] using (evaluated_nil_action_measurable A fill).comp
      ((history_ofFn_measurable m).comp measurable_fst)
  | succ n ih =>
    intro m
    let input : (Fin m → Entry p dx dy) × (Fin (n + 1) → Entry p dx dy) →
        (Fin (m + 1) → Entry p dx dy) × (Fin n → Entry p dx dy) :=
      fun v => (Fin.snoc v.1 (v.2 0), Fin.tail v.2)
    have hi : Measurable input := by
      apply Measurable.prodMk
      · apply measurable_pi_lambda
        intro i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · simpa [input, Function.comp_def] using (measurable_pi_apply (0 : Fin (n + 1))).comp measurable_snd
        · simpa [input, Function.comp_def] using (measurable_pi_apply j).comp measurable_fst
      · apply measurable_pi_lambda
        intro i
        exact (measurable_pi_apply i.succ).comp measurable_snd
    have hrec := (ih (m + 1)).comp hi
    have hpref := (history_ofFn_measurable m).comp
      (measurable_fst : Measurable (Prod.fst : (Fin m → Entry p dx dy) × (Fin (n + 1) → Entry p dx dy) → _))
    have hstop := measurable_query_none (A.measurable_query.comp hpref)
    have hout : Measurable (fun v : (Fin m → Entry p dx dy) × (Fin (n + 1) → Entry p dx dy) =>
        (Sum.inl ⟨A.policy.output (List.ofFn v.1), A.policy.feasible_output _⟩ : OracleAction (productDomain X Y))) :=
      measurable_inl.comp ((A.measurable_output.comp hpref).subtype_mk)
    have hm : Measurable (fun v : (Fin m → Entry p dx dy) × (Fin (n + 1) → Entry p dx dy) =>
        if A.policy.query (List.ofFn v.1) = none then
          (Sum.inl ⟨A.policy.output (List.ofFn v.1), A.policy.feasible_output _⟩ : OracleAction (productDomain X Y))
        else evaluatedActionFrom A.policy (List.ofFn (input v).1) (List.ofFn (input v).2)) :=
      Measurable.ite hstop hout hrec
    convert hm using 1
    funext v
    rw [List.ofFn_succ]
    simp only [evaluatedActionFrom]
    split <;> rename_i hq
    · simp [hq]
    · simp only [hq, Option.some_ne_none, ↓reduceIte]
      change evaluatedActionFrom A.policy (List.ofFn v.1 ++ [v.2 0]) (List.ofFn (Fin.tail v.2)) =
        evaluatedActionFrom A.policy (List.ofFn (Fin.snoc v.1 (v.2 0))) (List.ofFn (Fin.tail v.2))
      rw [history_ofFn_snoc]

theorem evaluated_action_measurable
    (A : BorelDeterministicScalarPolicy p dx dy N X Y) (fill : productDomain X Y) :
    Measurable (fun h => evaluatedActionFrom A.policy [] h) := by
  apply (measurable_history_iff _).2
  intro n
  have hi : Measurable (fun v : Fin n → Entry p dx dy =>
      ((fun i : Fin 0 => (Fin.elim0 i : Entry p dx dy)), v)) := measurable_const.prodMk measurable_id
  have hm := (evaluated_action_ofFn_measurable A fill n 0).comp hi
  simpa [Function.comp_def] using hm

/-- The exact old endpoint-evaluation wrapper preserves canonical Borel
query/output rules, including its arbitrary off-path history behavior. -/
def evaluatedPolicy (A : BorelDeterministicScalarPolicy p dx dy N X Y)
    (fill : productDomain X Y) : BorelDeterministicScalarPolicy p dx dy (N + 1) X Y where
  policy := EvaluatedPolicy.evaluatedPolicy A.policy
  measurable_query := by
    have ha := evaluated_action_measurable A fill
    change Measurable[_, MeasurableSpace.comap optionPointEncoding inferInstance] _
    apply measurable_comap_iff.2
    have hm : Measurable (Sum.elim (fun _ : productDomain X Y => Sum.inl ())
        (fun q : productDomain X Y => (Sum.inr q.1 : Unit ⊕ SaddleSpace dx dy))) :=
      measurable_fun_sum measurable_const (measurable_inr.comp measurable_subtype_coe)
    convert hm.comp ha using 1
    funext h
    cases hh : evaluatedActionFrom A.policy [] h <;> simp [Function.comp_def, EvaluatedPolicy.evaluatedPolicy, optionPointEncoding, hh]
  measurable_output := by
    classical
    have ha := evaluated_action_measurable A fill
    let stop : Set (ScalarHistory p dx dy) := {h | evaluatedActionFrom A.policy [] h ∈
      Set.range (Sum.inl : productDomain X Y → OracleAction (productDomain X Y))}
    have hs : MeasurableSet stop := ha measurableSet_range_inl
    have hmval : Measurable (Sum.elim (fun out : productDomain X Y => out.1)
        (fun _ : productDomain X Y => fill.1)) :=
      measurable_fun_sum measurable_subtype_coe measurable_const
    have hv := hmval.comp ha
    have hm : Measurable (fun h : ScalarHistory p dx dy => if h ∈ stop then
        Sum.elim (fun out : productDomain X Y => out.1) (fun _ : productDomain X Y => fill.1)
          (evaluatedActionFrom A.policy [] h)
        else A.policy.output h) := Measurable.ite hs hv A.measurable_output
    convert hm using 1
    funext h
    have ho : (EvaluatedPolicy.evaluatedPolicy A.policy).output h =
        Sum.elim (fun out : productDomain X Y => out.1) (fun _ : productDomain X Y => A.policy.output h)
          (evaluatedActionFrom A.policy [] h) := by
      cases hh : evaluatedActionFrom A.policy [] h <;> simp [EvaluatedPolicy.evaluatedPolicy, hh]
    rw [ho]
    have hpoint : ∀ a : OracleAction (productDomain X Y),
        Sum.elim (fun out : productDomain X Y => out.1) (fun _ : productDomain X Y => A.policy.output h) a =
        if a ∈ Set.range (Sum.inl : productDomain X Y → OracleAction (productDomain X Y)) then
          Sum.elim (fun out : productDomain X Y => out.1) (fun _ : productDomain X Y => fill.1) a
        else A.policy.output h := by
      intro a
      cases a <;> simp
    have hpp := hpoint (evaluatedActionFrom A.policy [] h)
    by_cases hh : evaluatedActionFrom A.policy [] h ∈
        Set.range (Sum.inl : productDomain X Y → OracleAction (productDomain X Y))
    · simpa only [stop, Set.mem_setOf_eq, if_pos hh] using hpp
    · simpa only [stop, Set.mem_setOf_eq, if_neg hh] using hpp

end
end MinimaxAudit.BorelEvaluatedPolicy
