import NCConcave16991.OracleProgramStateConsistency

/-! # Reply consistency is preserved by public program transformations -/

namespace NCConcave16991.OracleProgram

variable {Q R X Y Ω Ω' S : Type*} [MeasurableSpace Q] [MeasurableSpace R]
  [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Ω] [MeasurableSpace Ω'] {T U : ℕ}

theorem consistentFrom_map (P : Fixed Q R X Ω T) (f : X → Y) (hf : Measurable f)
    (oracle : S → Q → S × R) (A : Q → R) (seed : Ω)
    (k t : ℕ) (ht : t + k = T) (replies : Fin t → R) (state : S) :
    ConsistentFrom (map P f hf) oracle A seed k t ht replies state ↔
      ConsistentFrom P oracle A seed k t ht replies state := by
  induction k generalizing t state with
  | zero => rfl
  | succ k ih =>
    simp only [ConsistentFrom, map]
    exact and_congr_right (fun _ ↦ ih (t + 1) (by omega) _ _)

theorem consistent_map (P : Fixed Q R X Ω T) (f : X → Y) (hf : Measurable f)
    (oracle : S → Q → S × R) (A : Q → R) (seed : Ω) (state : S) :
    Consistent (map P f hf) oracle A seed state ↔ Consistent P oracle A seed state :=
  consistentFrom_map P f hf oracle A seed T 0 (by omega) Fin.elim0 state

theorem consistentFrom_mapWithSeed (P : Fixed Q R X Ω T) (f : Ω → X → Y)
    (hf : Measurable (Function.uncurry f)) (oracle : S → Q → S × R) (A : Q → R) (seed : Ω)
    (k t : ℕ) (ht : t + k = T) (replies : Fin t → R) (state : S) :
    ConsistentFrom (mapWithSeed P f hf) oracle A seed k t ht replies state ↔
      ConsistentFrom P oracle A seed k t ht replies state := by
  induction k generalizing t state with
  | zero => rfl
  | succ k ih =>
    simp only [ConsistentFrom, mapWithSeed]
    exact and_congr_right (fun _ ↦ ih (t + 1) (by omega) _ _)

theorem consistent_mapWithSeed (P : Fixed Q R X Ω T) (f : Ω → X → Y)
    (hf : Measurable (Function.uncurry f)) (oracle : S → Q → S × R) (A : Q → R) (seed : Ω) (state : S) :
    Consistent (mapWithSeed P f hf) oracle A seed state ↔ Consistent P oracle A seed state :=
  consistentFrom_mapWithSeed P f hf oracle A seed T 0 (by omega) Fin.elim0 state

theorem consistentFrom_withSeed (P : Fixed Q R X Ω T) (f : Ω' → Ω) (hf : Measurable f)
    (oracle : S → Q → S × R) (A : Q → R) (seed : Ω')
    (k t : ℕ) (ht : t + k = T) (replies : Fin t → R) (state : S) :
    ConsistentFrom (withSeed P f hf) oracle A seed k t ht replies state ↔
      ConsistentFrom P oracle A (f seed) k t ht replies state := by
  induction k generalizing t state with
  | zero => rfl
  | succ k ih =>
    simp only [ConsistentFrom, withSeed]
    exact and_congr_right (fun _ ↦ ih (t + 1) (by omega) _ _)

theorem consistent_withSeed (P : Fixed Q R X Ω T) (f : Ω' → Ω) (hf : Measurable f)
    (oracle : S → Q → S × R) (A : Q → R) (seed : Ω') (state : S) :
    Consistent (withSeed P f hf) oracle A seed state ↔ Consistent P oracle A (f seed) state :=
  consistentFrom_withSeed P f hf oracle A seed T 0 (by omega) Fin.elim0 state

theorem consistent_castBudget (P : Fixed Q R X Ω T) (h : T = U)
    (oracle : S → Q → S × R) (A : Q → R) (seed : Ω) (state : S) :
    Consistent (castBudget P h) oracle A seed state ↔ Consistent P oracle A seed state := by
  subst U
  rfl

variable {I : Type*} [MeasurableSpace I] [Countable I] [MeasurableSingletonClass I]

theorem consistentFrom_select (index : Ω → I) (hi : Measurable index) (program : I → Fixed Q R X Ω T)
    (oracle : S → Q → S × R) (A : Q → R) (seed : Ω)
    (k t : ℕ) (ht : t + k = T) (replies : Fin t → R) (state : S) :
    ConsistentFrom (select index hi program) oracle A seed k t ht replies state ↔
      ConsistentFrom (program (index seed)) oracle A seed k t ht replies state := by
  induction k generalizing t state with
  | zero => rfl
  | succ k ih =>
    simp only [ConsistentFrom, select]
    exact and_congr_right (fun _ ↦ ih (t + 1) (by omega) _ _)

theorem consistent_select (index : Ω → I) (hi : Measurable index) (program : I → Fixed Q R X Ω T)
    (oracle : S → Q → S × R) (A : Q → R) (seed : Ω) (state : S) :
    Consistent (select index hi program) oracle A seed state ↔
      Consistent (program (index seed)) oracle A seed state :=
  consistentFrom_select index hi program oracle A seed T 0 (by omega) Fin.elim0 state

end NCConcave16991.OracleProgram
