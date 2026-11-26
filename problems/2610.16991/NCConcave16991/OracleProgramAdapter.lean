import NCConcave16991.OracleProgram

/-! # Measurable adaptation of query and reply formats, with exact interpreter semantics -/

namespace NCConcave16991.OracleProgram

variable {Q R Q' R' X Ω : Type*} [MeasurableSpace Q] [MeasurableSpace R]
  [MeasurableSpace Q'] [MeasurableSpace R'] [MeasurableSpace X] [MeasurableSpace Ω]
  {T : ℕ}

/-- Adapt only the public query format and the supplied reply format. -/
def adapt (P : Fixed Q R X Ω T) (queryMap : Q → Q') (hq : Measurable queryMap)
    (replyMap : R' → R) (hr : Measurable replyMap) : Fixed Q' R' X Ω T where
  ask t seed replies := queryMap (P.ask t seed (fun i => replyMap (replies i)))
  finish seed replies := P.finish seed (fun i => replyMap (replies i))
  ask_measurable t := by
    apply hq.comp
    change Measurable (Function.uncurry (P.ask t) ∘
      (fun a : Ω × (Fin t.val → R') => (a.1, fun i => replyMap (a.2 i))))
    apply (P.ask_measurable t).comp
    exact measurable_fst.prodMk
      (measurable_pi_iff.mpr fun i => hr.comp ((measurable_pi_apply i).comp measurable_snd))
  finish_measurable := by
    change Measurable (Function.uncurry P.finish ∘
      (fun a : Ω × (Fin T → R') => (a.1, fun i => replyMap (a.2 i))))
    apply P.finish_measurable.comp
    exact measurable_fst.prodMk
      (measurable_pi_iff.mpr fun i => hr.comp ((measurable_pi_apply i).comp measurable_snd))

theorem map_snoc (f : R' → R) (replies : Fin t → R') (r : R') :
    (fun i : Fin (t + 1) => f (Fin.snoc (α := fun _ : Fin (t + 1) => R') replies r i)) =
      Fin.snoc (α := fun _ : Fin (t + 1) => R) (fun i => f (replies i)) (f r) := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i <;> simp

theorem evalFrom_adapt (P : Fixed Q R X Ω T) (queryMap : Q → Q') (hq : Measurable queryMap)
    (replyMap : R' → R) (hr : Measurable replyMap) (oracle : Q' → R') (seed : Ω)
    (k t : ℕ) (ht : t + k = T) (replies : Fin t → R') :
    evalFrom (adapt P queryMap hq replyMap hr) oracle seed k t ht replies =
      evalFrom P (replyMap ∘ oracle ∘ queryMap) seed k t ht (fun i => replyMap (replies i)) := by
  induction k generalizing t with
  | zero => rfl
  | succ k ih =>
    change evalFrom (adapt P queryMap hq replyMap hr) oracle seed k (t + 1) _
      (Fin.snoc replies (oracle (queryMap (P.ask ⟨t, by omega⟩ seed (fun i => replyMap (replies i)))))) =
      evalFrom P (replyMap ∘ oracle ∘ queryMap) seed k (t + 1) _
        (Fin.snoc (fun i => replyMap (replies i))
          (replyMap (oracle (queryMap (P.ask ⟨t, by omega⟩ seed (fun i => replyMap (replies i)))))))
    rw [ih, map_snoc]

/-- Query/reply adaptation preserves both the exact budget and actual output. -/
theorem eval_adapt (P : Fixed Q R X Ω T) (queryMap : Q → Q') (hq : Measurable queryMap)
    (replyMap : R' → R) (hr : Measurable replyMap) (oracle : Q' → R') (seed : Ω) :
    eval (adapt P queryMap hq replyMap hr) oracle seed =
      eval P (replyMap ∘ oracle ∘ queryMap) seed := by
  have he : (fun i : Fin 0 => replyMap (Fin.elim0 i)) = (Fin.elim0 : Fin 0 → R) :=
    Subsingleton.elim _ _
  simpa only [eval, he] using
    evalFrom_adapt P queryMap hq replyMap hr oracle seed T 0 (by omega) Fin.elim0

end NCConcave16991.OracleProgram
