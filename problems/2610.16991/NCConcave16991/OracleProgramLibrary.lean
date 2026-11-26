import NCConcave16991.OracleProgram

/-! # Full passes and fixed public query batches as genuine interactive programs -/

namespace NCConcave16991.OracleProgram

variable {Q R Ω : Type*} [MeasurableSpace Q] [MeasurableSpace R] [MeasurableSpace Ω]
  {T : ℕ}

/-- A full pass or a private-seed batch. Replies are returned as an indexed cache. -/
def fullPass (queries : Ω → Fin T → Q) (hq : ∀ i, Measurable (fun seed => queries seed i)) :
    Fixed Q R (Fin T → R) Ω T where
  ask t seed _ := queries seed t
  finish _ replies := replies
  ask_measurable t := (hq t).comp measurable_fst
  finish_measurable := measurable_snd

theorem evalFrom_fullPass (queries : Ω → Fin T → Q)
    (hq : ∀ i, Measurable (fun seed => queries seed i)) (oracle : Q → R) (seed : Ω)
    (k t : ℕ) (ht : t + k = T) (replies : Fin t → R)
    (hprev : ∀ i : Fin t, replies i = oracle (queries seed ⟨i.val, by omega⟩)) :
    evalFrom (fullPass (R := R) queries hq) oracle seed k t ht replies =
      (fun i => oracle (queries seed i)) := by
  induction k generalizing t with
  | zero =>
    have he : t = T := by omega
    subst t
    funext i
    exact hprev i
  | succ k ih =>
    apply ih (t + 1) (by omega)
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [Fin.snoc_last, fullPass, Fin.val_last]
    · simpa only [Fin.snoc_castSucc, Fin.val_castSucc] using hprev j

/-- Executing the full pass returns exactly the responses to its listed queries. -/
theorem eval_fullPass (queries : Ω → Fin T → Q)
    (hq : ∀ i, Measurable (fun seed => queries seed i)) (oracle : Q → R) (seed : Ω) :
    eval (fullPass (R := R) queries hq) oracle seed = (fun i => oracle (queries seed i)) :=
  evalFrom_fullPass queries hq oracle seed T 0 (by omega) Fin.elim0 (fun i => Fin.elim0 i)

/-- Two interactive queries; the second may depend on the first supplied reply. -/
def twoQueries (first : Ω → Q) (hf : Measurable first)
    (second : Ω → R → Q) (hs : Measurable (Function.uncurry second)) :
    Fixed Q R (R × R) Ω 2 where
  ask t seed replies := if ht : t.val = 0 then first seed
    else second seed (replies ⟨0, by omega⟩)
  finish _ replies := (replies 0, replies 1)
  ask_measurable t := by
    split_ifs with ht
    · exact hf.comp measurable_fst
    · change Measurable (Function.uncurry second ∘
        (fun a : Ω × (Fin t.val → R) => (a.1, a.2 ⟨0, by omega⟩)))
      exact hs.comp (measurable_fst.prodMk ((measurable_pi_apply _).comp measurable_snd))
  finish_measurable := ((measurable_pi_apply 0).comp measurable_snd).prodMk
    ((measurable_pi_apply 1).comp measurable_snd)

theorem eval_twoQueries (first : Ω → Q) (hf : Measurable first)
    (second : Ω → R → Q) (hs : Measurable (Function.uncurry second))
    (oracle : Q → R) (seed : Ω) :
    eval (twoQueries first hf second hs) oracle seed =
      (oracle (first seed), oracle (second seed (oracle (first seed)))) := by
  simp [eval, evalFrom, twoQueries, Fin.snoc]

end NCConcave16991.OracleProgram
