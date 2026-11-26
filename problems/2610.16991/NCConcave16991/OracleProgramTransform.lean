import NCConcave16991.OracleProgram

/-! # Public seed transformations and seed-dependent postprocessing -/

namespace NCConcave16991.OracleProgram

variable {Q R X Y Ω Ω' : Type*} [MeasurableSpace Q] [MeasurableSpace R]
  [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Ω] [MeasurableSpace Ω'] {T : ℕ}

def withSeed (P : Fixed Q R X Ω T) (f : Ω' → Ω) (hf : Measurable f) : Fixed Q R X Ω' T where
  ask t seed replies := P.ask t (f seed) replies
  finish seed replies := P.finish (f seed) replies
  ask_measurable t := (P.ask_measurable t).comp ((hf.comp measurable_fst).prodMk measurable_snd)
  finish_measurable := P.finish_measurable.comp ((hf.comp measurable_fst).prodMk measurable_snd)

theorem evalFrom_withSeed (P : Fixed Q R X Ω T) (f : Ω' → Ω) (hf : Measurable f)
    (oracle : Q → R) (seed : Ω') (k t : ℕ) (ht : t + k = T) (replies : Fin t → R) :
    evalFrom (withSeed P f hf) oracle seed k t ht replies =
      evalFrom P oracle (f seed) k t ht replies := by
  induction k generalizing t with
  | zero => rfl
  | succ k ih => exact ih (t + 1) _ _

theorem eval_withSeed (P : Fixed Q R X Ω T) (f : Ω' → Ω) (hf : Measurable f)
    (oracle : Q → R) (seed : Ω') :
    eval (withSeed P f hf) oracle seed = eval P oracle (f seed) :=
  evalFrom_withSeed P f hf oracle seed T 0 (by omega) Fin.elim0

def mapWithSeed (P : Fixed Q R X Ω T) (f : Ω → X → Y)
    (hf : Measurable (Function.uncurry f)) : Fixed Q R Y Ω T where
  ask := P.ask
  finish seed replies := f seed (P.finish seed replies)
  ask_measurable := P.ask_measurable
  finish_measurable := hf.comp (measurable_fst.prodMk P.finish_measurable)

theorem evalFrom_mapWithSeed (P : Fixed Q R X Ω T) (f : Ω → X → Y)
    (hf : Measurable (Function.uncurry f)) (oracle : Q → R) (seed : Ω)
    (k t : ℕ) (ht : t + k = T) (replies : Fin t → R) :
    evalFrom (mapWithSeed P f hf) oracle seed k t ht replies =
      f seed (evalFrom P oracle seed k t ht replies) := by
  induction k generalizing t with
  | zero => rfl
  | succ k ih => exact ih (t + 1) _ _

theorem eval_mapWithSeed (P : Fixed Q R X Ω T) (f : Ω → X → Y)
    (hf : Measurable (Function.uncurry f)) (oracle : Q → R) (seed : Ω) :
    eval (mapWithSeed P f hf) oracle seed = f seed (eval P oracle seed) :=
  evalFrom_mapWithSeed P f hf oracle seed T 0 (by omega) Fin.elim0

end NCConcave16991.OracleProgram
