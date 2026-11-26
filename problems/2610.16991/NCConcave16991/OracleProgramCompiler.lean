import NCConcave16991.OracleProgram
import NCConcave16991.OracleMeasurability

/-!
# Compilation into the paper's measurable full-history oracle model

Only previous answers are replayed. The compiled policy is defined before the
unknown oracle is supplied. At its public fuel the output equals the independent
interactive interpreter and the transcript contains exactly that many queries.
-/

noncomputable section

open Set MeasureTheory

namespace NCConcave16991.OracleProgram

private theorem sigmaMk_measurableEmbedding {ι : Type*} {β : ι → Type*}
    [∀ i, MeasurableSpace (β i)] (i : ι) : MeasurableEmbedding (Sigma.mk i : β i → Sigma β) := by
  classical
  have hinj : Function.Injective (Sigma.mk i : β i → Sigma β) := by
    intro x y hxy
    simpa only [Sigma.mk.injEq, heq_eq_eq, true_and] using hxy
  refine ⟨hinj, ?_, ?_⟩
  · apply Measurable.of_le_map
    exact iInf_le (fun j => (inferInstance : MeasurableSpace (β j)).map (Sigma.mk j)) i
  · intro s hs
    change MeasurableSet[⨅ j, (inferInstance : MeasurableSpace (β j)).map (Sigma.mk j)] (Sigma.mk i '' s)
    rw [MeasurableSpace.measurableSet_iInf]
    intro j
    change MeasurableSet (Sigma.mk j ⁻¹' (Sigma.mk i '' s))
    by_cases hij : j = i
    · subst j
      simpa only [hinj.preimage_image] using hs
    · have he : Sigma.mk j ⁻¹' (Sigma.mk i '' s) = ∅ := by
        ext x
        constructor
        · rintro ⟨y, hy, hxy⟩
          exact (hij (congrArg Sigma.fst hxy).symm).elim
        · intro hx
          exact hx.elim
      rw [he]
      exact MeasurableSet.empty

private theorem measurable_prod_sigma {Ω ι γ : Type*} {β : ι → Type*}
    [MeasurableSpace Ω] [Countable ι] [∀ i, MeasurableSpace (β i)] [MeasurableSpace γ]
    {f : Ω × Sigma β → γ}
    (hf : ∀ i, Measurable (fun a : Ω × β i => f (a.1, ⟨i, a.2⟩))) : Measurable f := by
  intro s hs
  have he : f ⁻¹' s = ⋃ i,
      (fun a : Ω × β i => (a.1, Sigma.mk i a.2)) ''
        ((fun a : Ω × β i => f (a.1, Sigma.mk i a.2)) ⁻¹' s) := by
    ext a
    constructor
    · intro ha
      exact mem_iUnion.mpr ⟨a.2.1, ⟨(a.1, a.2.2), ha, rfl⟩⟩
    · intro ha
      rcases mem_iUnion.mp ha with ⟨i, a', ha', rfl⟩
      exact ha'
  rw [he]
  apply MeasurableSet.iUnion
  intro i
  exact ((MeasurableEmbedding.id (α := Ω)).prodMap (sigmaMk_measurableEmbedding i)).measurableSet_image'
    (hf i hs)

variable {n dx dy : ℕ} {D : ℝ} (K : KnownDualDomain dy D)
  {Ω : Type*} [MeasurableSpace Ω] {T : ℕ}

abbrev ProblemProgram (Ω : Type*) [MeasurableSpace Ω] (T : ℕ) :=
  Fixed (OracleQuery n dx K) (OracleAnswer dx dy) (PrimalSpace dx) Ω T

/-- Padding only defines forced outputs on prematurely exhausted or inconsistent histories. -/
def paddedReplies (h : OraclePolicy.History K (n := n) (dx := dx)) : Fin T → OracleAnswer dx dy :=
  fun i => if hi : i.val < h.1 then (h.2 ⟨i.val, hi⟩).2 else 0

def finalOutput (P : ProblemProgram K (n := n) (dx := dx) Ω T) (seed : Ω)
    (h : OraclePolicy.History K (n := n) (dx := dx)) : PrimalSpace dx :=
  P.finish seed (paddedReplies K h)

def nextAction (P : ProblemProgram K (n := n) (dx := dx) Ω T) (seed : Ω)
    (h : OraclePolicy.History K (n := n) (dx := dx)) : OraclePolicy.Action K (n := n) (dx := dx) :=
  if ht : h.1 < T then Sum.inr (P.ask ⟨h.1, ht⟩ seed (fun i => (h.2 i).2))
  else Sum.inl (finalOutput K P seed h)

theorem finalOutput_measurable (P : ProblemProgram K (n := n) (dx := dx) Ω T) :
    Measurable (Function.uncurry (finalOutput K P)) := by
  apply measurable_prod_sigma
  intro t
  change Measurable (Function.uncurry P.finish ∘
    (fun a : Ω × (Fin t → OraclePolicy.Observation K (n := n) (dx := dx)) => (a.1, paddedReplies K ⟨t, a.2⟩)))
  apply P.finish_measurable.comp
  apply Measurable.prodMk measurable_fst
  apply measurable_pi_iff.mpr
  intro i
  by_cases hi : i.val < t
  · simpa only [paddedReplies, hi, dite_true, Function.comp_def] using
      measurable_snd.comp ((measurable_pi_apply (⟨i.val, hi⟩ : Fin t)).comp measurable_snd)
  · simpa only [paddedReplies, hi, dite_false] using
      (measurable_const : Measurable (fun _ : Ω × (Fin t → OraclePolicy.Observation K (n := n) (dx := dx)) =>
        (0 : OracleAnswer dx dy)))

theorem nextAction_measurable (P : ProblemProgram K (n := n) (dx := dx) Ω T) :
    Measurable (Function.uncurry (nextAction K P)) := by
  apply measurable_prod_sigma
  intro t
  by_cases ht : t < T
  · change Measurable (fun a : Ω × (Fin t → OraclePolicy.Observation K (n := n) (dx := dx)) =>
      if h : t < T then Sum.inr (P.ask ⟨t, h⟩ a.1 (fun i => (a.2 i).2)) else _)
    simp only [ht, dite_true]
    apply measurable_inr.comp
    change Measurable (Function.uncurry (P.ask ⟨t, ht⟩) ∘
      (fun a : Ω × (Fin t → OraclePolicy.Observation K (n := n) (dx := dx)) =>
        (a.1, fun i => (a.2 i).2)))
    apply (P.ask_measurable ⟨t, ht⟩).comp
    apply Measurable.prodMk measurable_fst
    exact measurable_pi_iff.mpr fun i => by
      simpa only [Function.comp_def] using
        measurable_snd.comp ((measurable_pi_apply i).comp measurable_snd)
  · have hm := (finalOutput_measurable K P).comp
      (measurable_fst.prodMk ((sigmaMk_measurableEmbedding t).measurable.comp measurable_snd))
    simpa only [Function.uncurry, nextAction, ht, dite_false, Function.comp_def] using
      measurable_inl.comp hm

/-- Compilation needs only the public program; no unknown Problem occurs here. -/
def compile (P : ProblemProgram K (n := n) (dx := dx) Ω T) : OraclePolicy.AdaptivePolicy K (n := n) (dx := dx) Ω where
  next := nextAction K P
  final := finalOutput K P
  next_measurable := nextAction_measurable K P
  final_measurable := finalOutput_measurable K P

theorem answers_snoc (h : Fin t → OraclePolicy.Observation K (n := n) (dx := dx))
    (q : OracleQuery n dx K) (r : OracleAnswer dx dy) :
    (fun j : Fin (t + 1) =>
      (Fin.snoc (α := fun _ : Fin (t + 1) => OraclePolicy.Observation K (n := n) (dx := dx)) h (q, r) j).2) =
      Fin.snoc (α := fun _ : Fin (t + 1) => OracleAnswer dx dy) (fun j => (h j).2) r := by
  funext j
  refine Fin.lastCases ?_ (fun i => ?_) j
  · simp
  · simp

/-- Compiler correctness from every partial transcript with the matching remaining fuel. -/
theorem runAux_output_eq_evalFrom (P : ProblemProgram K (n := n) (dx := dx) Ω T)
    (oracle : OracleQuery n dx K → OracleAnswer dx dy) (seed : Ω)
    (k t : ℕ) (ht : t + k = T)
    (h : Fin t → OraclePolicy.Observation K (n := n) (dx := dx)) :
    (OraclePolicy.runAux K (compile K P) oracle seed k ⟨t, h⟩).1 =
      evalFrom P oracle seed k t ht (fun i => (h i).2) := by
  induction k generalizing t with
  | zero =>
    have he : t = T := by omega
    subst t
    change P.finish seed (paddedReplies K ⟨T, h⟩) = P.finish seed (fun i => (h i).2)
    congr 1
    funext i
    change (if hi : i.val < T then (h ⟨i.val, hi⟩).2 else 0) = (h i).2
    simp only [i.isLt, dite_true]
  | succ k ih =>
    have hlt : t < T := by omega
    let q := P.ask ⟨t, hlt⟩ seed (fun i => (h i).2)
    have hr := ih (t + 1) (by omega) (Fin.snoc h (q, oracle q))
    simpa only [OraclePolicy.runAux, compile, nextAction, hlt, dite_true,
      OraclePolicy.appendHistory, evalFrom, q, answers_snoc] using hr

theorem run_output_eq_eval (P : ProblemProgram K (n := n) (dx := dx) Ω T)
    (oracle : OracleQuery n dx K → OracleAnswer dx dy) (seed : Ω) :
    (OraclePolicy.run K (compile K P) oracle seed T).1 = eval P oracle seed := by
  have hr := runAux_output_eq_evalFrom K P oracle seed T 0 (by omega) Fin.elim0
  have he : (fun i : Fin 0 => (Fin.elim0 i : OraclePolicy.Observation K (n := n) (dx := dx)).2) =
      (Fin.elim0 : Fin 0 → OracleAnswer dx dy) := Subsingleton.elim _ _
  simpa only [he, OraclePolicy.run, OraclePolicy.emptyHistory, eval] using hr

/-- The declared fuel is consumed exactly, for every possible oracle and seed. -/
theorem runAux_exact_queries (P : ProblemProgram K (n := n) (dx := dx) Ω T)
    (oracle : OracleQuery n dx K → OracleAnswer dx dy) (seed : Ω)
    (k t : ℕ) (ht : t + k = T)
    (h : Fin t → OraclePolicy.Observation K (n := n) (dx := dx)) :
    (OraclePolicy.runAux K (compile K P) oracle seed k ⟨t, h⟩).2.1 = T := by
  induction k generalizing t with
  | zero => simpa [OraclePolicy.runAux] using ht
  | succ k ih =>
    have hlt : t < T := by omega
    let q := P.ask ⟨t, hlt⟩ seed (fun i => (h i).2)
    simpa only [OraclePolicy.runAux, compile, nextAction, hlt, dite_true,
      OraclePolicy.appendHistory, q] using ih (t + 1) (by omega) (Fin.snoc h (q, oracle q))

theorem run_exact_queries (P : ProblemProgram K (n := n) (dx := dx) Ω T)
    (oracle : OracleQuery n dx K → OracleAnswer dx dy) (seed : Ω) :
    (OraclePolicy.run K (compile K P) oracle seed T).2.1 = T :=
  runAux_exact_queries K P oracle seed T 0 (by omega) Fin.elim0

/-- The independent interpreter inherits actual measurability from the proved compiler. -/
theorem eval_measurable (P : ProblemProgram K (n := n) (dx := dx) Ω T)
    {oracle : OracleQuery n dx K → OracleAnswer dx dy} (ho : Measurable oracle) :
    Measurable (eval P oracle) := by
  have hm := OraclePolicy.output_measurable K (compile K P) ho T
  simpa only [run_output_eq_eval] using hm

end NCConcave16991.OracleProgram
