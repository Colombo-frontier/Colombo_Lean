import NCConcave16991.BranchOracleInterpreterMeasurable
import NCConcave16991.OracleProgramControl
import NCConcave16991.OracleProgramFold

/-! # Public padding of arbitrary early stopping reference policies -/

namespace NCConcave16991.BranchOracle.Reference
noncomputable section
open GlobalHard GlobalHardEuclidean

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1000000

variable {n M N : ℕ} [NeZero n] (V : Fin M → Fin (N + 1) → Type*)
  [∀ j k, NormedAddCommGroup (V j k)] [∀ j k, InnerProductSpace ℝ (V j k)]
  [∀ j k, FiniteDimensional ℝ (V j k)]
variable {D : ℝ} (K : KnownDualDomain (dualDimension V) D)

abbrev PaddedState := (Bool × PrimalSpace (primalDimension V)) × State (n := n) V K

def paddedInitial : PaddedState (n := n) V K := ((false, 0), initial V K)

def publicDefaultQuery : OracleQuery n (primalDimension V) K :=
  (0, 0, ⟨Classical.choose K.nonempty, Classical.choose_spec K.nonempty⟩)

variable {Ω : Type*} [MeasurableSpace Ω]
  (P : OraclePolicy.AdaptivePolicy K (n := n) (dx := primalDimension V) Ω)

def paddedNext (seed : Ω) (s : PaddedState (n := n) V K) :
    PrimalSpace (primalDimension V) ⊕ OracleQuery n (primalDimension V) K :=
  if s.1.1 then Sum.inl s.1.2 else P.next seed s.2.history

theorem paddedNext_measurable : Measurable (Function.uncurry (paddedNext V K P)) := by
  have hd : Measurable (fun a : Ω × PaddedState (n := n) V K ↦ a.2.1.1) :=
    measurable_fst.comp (measurable_fst.comp measurable_snd)
  have hp : Measurable (fun a : Ω × PaddedState (n := n) V K ↦ P.next a.1 a.2.2.history) :=
    P.next_measurable.comp
    (measurable_fst.prodMk ((history_measurable V K).comp (measurable_snd.comp measurable_snd)))
  have hx : Measurable (fun a : Ω × PaddedState (n := n) V K ↦
      (Sum.inl a.2.1.2 : PrimalSpace (primalDimension V) ⊕ OracleQuery n (primalDimension V) K)) :=
    measurable_inl.comp (measurable_snd.comp (measurable_fst.comp measurable_snd))
  exact hx.ite (hd.eq_const true).setOf hp

def paddedShouldQuery (a : Ω × PaddedState (n := n) V K) : Bool :=
  (paddedNext V K P a.1 a.2).elim (fun _ ↦ false) (fun _ ↦ true)

theorem paddedShouldQuery_measurable : Measurable (paddedShouldQuery V K P) :=
  (measurable_const.sumElim measurable_const).comp (paddedNext_measurable V K P)

def paddedQuery (a : Ω × PaddedState (n := n) V K) : OracleQuery n (primalDimension V) K :=
  (paddedNext V K P a.1 a.2).elim (fun _ ↦ publicDefaultQuery V K) id

theorem paddedQuery_measurable : Measurable (paddedQuery V K P) :=
  (measurable_const.sumElim measurable_id).comp (paddedNext_measurable V K P)

def paddedStop (a : Ω × PaddedState (n := n) V K) : PaddedState (n := n) V K :=
  ((true, (paddedNext V K P a.1 a.2).elim id (fun _ ↦ 0)), a.2.2)

theorem paddedStop_measurable : Measurable (paddedStop V K P) :=
  (measurable_const.prodMk ((measurable_id.sumElim measurable_const).comp
    (paddedNext_measurable V K P))).prodMk (measurable_snd.comp measurable_snd)

def finishPadded (seed : Ω) (s : PaddedState (n := n) V K) : PrimalSpace (primalDimension V) × State (n := n) V K :=
  (if s.1.1 then s.1.2 else P.final seed s.2.history, s.2)

theorem finishPadded_measurable : Measurable (Function.uncurry (finishPadded V K P)) := by
  have hd : Measurable (fun a : Ω × PaddedState (n := n) V K ↦ a.2.1.1) :=
    measurable_fst.comp (measurable_fst.comp measurable_snd)
  have hp : Measurable (fun a : Ω × PaddedState (n := n) V K ↦ P.final a.1 a.2.2.history) :=
    P.final_measurable.comp
    (measurable_fst.prodMk ((history_measurable V K).comp (measurable_snd.comp measurable_snd)))
  exact ((measurable_snd.comp (measurable_fst.comp measurable_snd)).ite
    (hd.eq_const true).setOf hp).prodMk (measurable_snd.comp measurable_snd)

variable (B : ∀ j : Fin M, ∀ t : Fin N,
    BranchGeometry.BranchFamily (ι := Fin n) (V j t.castSucc) (V j t.succ))
  (u : ∀ j, V j 0) (v : ∀ j, V j (Fin.last N))
  (ρ : ℝ) (site : Fin M → ℕ) (d c μ : ℝ)

def paddedStep (seed : Ω) (s : PaddedState (n := n) V K) : PaddedState (n := n) V K :=
  match paddedNext V K P seed s with
  | Sum.inl x => ((true, x), s.2)
  | Sum.inr q => ((false, 0), step V K B u v ρ site d c μ s.2 q)

def paddedExecute (seed : Ω) : ℕ → PaddedState (n := n) V K → PaddedState (n := n) V K
  | 0, s => s
  | t + 1, s => paddedExecute seed t (paddedStep V K P B u v ρ site d c μ seed s)

theorem executeBlocks_eq_paddedExecute (seed : Ω) (k t : ℕ) (s : PaddedState (n := n) V K) :
    OracleProgram.executeBlocks (fun _ ↦ paddedStep V K P B u v ρ site d c μ seed) k t s =
      paddedExecute V K P B u v ρ site d c μ seed k s := by
  induction k generalizing t s with
  | zero => rfl
  | succ k ih => exact ih (t + 1) _

theorem paddedExecute_stopped (seed : Ω) (t : ℕ) (x : PrimalSpace (primalDimension V)) (s : State (n := n) V K) :
    paddedExecute V K P B u v ρ site d c μ seed t ((true, x), s) = ((true, x), s) := by
  induction t with
  | zero => rfl
  | succ t ih => simpa only [paddedExecute, paddedStep, paddedNext, Bool.true_eq, ite_true] using ih

theorem finishPadded_execute_eq_runAux (seed : Ω) (t : ℕ) (s : State (n := n) V K) :
    finishPadded V K P seed (paddedExecute V K P B u v ρ site d c μ seed t ((false, 0), s)) =
      runAux V K B u v ρ site d c μ P seed t s := by
  induction t generalizing s with
  | zero => rfl
  | succ t ih =>
    cases hn : P.next seed s.history with
    | inl x =>
      simp only [paddedExecute, paddedStep, paddedNext, Bool.false_eq_true, ite_false, hn,
        paddedExecute_stopped, finishPadded, Bool.true_eq, ite_true, runAux]
    | inr q =>
      simpa only [paddedExecute, paddedStep, paddedNext, Bool.false_eq_true, ite_false, hn, runAux] using
        ih (step V K B u v ρ site d c μ s q)

end
end NCConcave16991.BranchOracle.Reference
