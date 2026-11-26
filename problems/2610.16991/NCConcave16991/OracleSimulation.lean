import NCConcave16991.OracleProgramLoop
import NCConcave16991.OracleMeasurability

/-! # One-query simulation of an arbitrary adaptive policy

A public measurable query map and reply map simulate any full-history policy.
The simulator retains the virtual target transcript, permits arbitrary stopping
and unqueried outputs, and pads stopped paths with ignored feasible queries.
Its constructor does not inspect either unknown oracle.
-/

noncomputable section

open MeasureTheory

namespace NCConcave16991.OracleSimulation

variable {n dx dy : ℕ} {D : ℝ} (K : KnownDualDomain dy D)
  {Ω Q R : Type*} [MeasurableSpace Ω] [MeasurableSpace Q] [MeasurableSpace R]

abbrev State := PrimalSpace dx ⊕ OraclePolicy.History K (n := n) (dx := dx)

variable (P : OraclePolicy.AdaptivePolicy K (n := n) (dx := dx) Ω)

def action (seed : Ω) (s : State K (n := n) (dx := dx)) : OraclePolicy.Action K (n := n) (dx := dx) :=
  s.elim Sum.inl (P.next seed)

theorem action_measurable : Measurable (Function.uncurry (action K P)) := by
  have hl : Measurable (fun a : Ω × PrimalSpace dx ↦ (Sum.inl a.2 : OraclePolicy.Action K (n := n))) :=
    measurable_inl.comp measurable_snd
  convert (hl.sumElim P.next_measurable).comp
    (MeasurableEquiv.prodSumDistrib Ω (PrimalSpace dx) (OraclePolicy.History K)).measurable
    using 1
  funext a
  rcases a with ⟨seed, s⟩
  cases s <;> rfl

variable (dummy : Q) (queryMap : OracleQuery n dx K → Q)
  (replyMap : OracleQuery n dx K → R → OracleAnswer dx dy)

def ask (seed : Ω) (s : State K (n := n) (dx := dx)) : Q :=
  (action K P seed s).elim (fun _ ↦ dummy) queryMap

theorem ask_measurable (hq : Measurable queryMap) :
    Measurable (Function.uncurry (ask K P dummy queryMap)) :=
  (measurable_const.sumElim hq).comp (action_measurable K P)

def update (seed : Ω) (s : State K (n := n) (dx := dx)) (r : R) : State K (n := n) (dx := dx) :=
  s.elim Sum.inl (fun h ↦ (P.next seed h).elim Sum.inl
    (fun q ↦ Sum.inr (OraclePolicy.appendHistory K h (q, replyMap q r))))

theorem update_measurable (hr : Measurable (Function.uncurry replyMap)) :
    Measurable (fun a : (Ω × State K (n := n) (dx := dx)) × R ↦
      update K P replyMap a.1.1 a.1.2 a.2) := by
  let H := OraclePolicy.History K (n := n) (dx := dx)
  have ha : Measurable (fun a : (H × R) × OraclePolicy.Action K (n := n) (dx := dx) ↦
      a.2.elim Sum.inl (fun q ↦ Sum.inr (OraclePolicy.appendHistory K a.1.1 (q, replyMap q a.1.2)))) := by
    have hl : Measurable (fun a : (H × R) × PrimalSpace dx ↦
        (Sum.inl a.2 : State K (n := n) (dx := dx))) := measurable_inl.comp measurable_snd
    have hq : Measurable (fun a : (H × R) × OracleQuery n dx K ↦
        (Sum.inr (OraclePolicy.appendHistory K a.1.1 (a.2, replyMap a.2 a.1.2)) : State K)) := by
      apply measurable_inr.comp
      exact (OraclePolicy.appendHistory_measurable K).comp
        ((measurable_fst.comp measurable_fst).prodMk
          (measurable_snd.prodMk (hr.comp (measurable_snd.prodMk (measurable_snd.comp measurable_fst)))))
    convert (hl.sumElim hq).comp
      (MeasurableEquiv.prodSumDistrib (H × R) (PrimalSpace dx) (OracleQuery n dx K)).measurable
      using 1
    funext a
    rcases a with ⟨b, s⟩
    cases s <;> rfl
  have hh : Measurable (fun a : (Ω × R) × H ↦
      (P.next a.1.1 a.2).elim Sum.inl
        (fun q ↦ Sum.inr (OraclePolicy.appendHistory K a.2 (q, replyMap q a.1.2)))) :=
    ha.comp ((measurable_snd.prodMk (measurable_snd.comp measurable_fst)).prodMk
      (P.next_measurable.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)))
  have hl : Measurable (fun a : (Ω × R) × PrimalSpace dx ↦
      (Sum.inl a.2 : State K (n := n) (dx := dx))) := measurable_inl.comp measurable_snd
  have hs := (hl.sumElim hh).comp
    (MeasurableEquiv.prodSumDistrib (Ω × R) (PrimalSpace dx) H).measurable
  convert hs.comp (((measurable_fst.comp measurable_fst).prodMk measurable_snd).prodMk
    (measurable_snd.comp measurable_fst))
    using 1
  funext a
  rcases a with ⟨⟨seed, s⟩, r⟩
  cases s <;> rfl

def finish (seed : Ω) (s : State K (n := n) (dx := dx)) : PrimalSpace dx :=
  s.elim id (P.final seed)

theorem finish_measurable : Measurable (Function.uncurry (finish K P)) := by
  convert (measurable_snd.sumElim P.final_measurable).comp
    (MeasurableEquiv.prodSumDistrib Ω (PrimalSpace dx) (OraclePolicy.History K)).measurable
    using 1
  funext a
  rcases a with ⟨seed, s⟩
  cases s <;> rfl

def program (hq : Measurable queryMap) (hr : Measurable (Function.uncurry replyMap))
    (budget : ℕ) : OracleProgram.Fixed Q R (PrimalSpace dx) Ω budget :=
  OracleProgram.stateLoop budget (fun _ ↦ Sum.inr (OraclePolicy.emptyHistory K)) measurable_const
    (fun _ ↦ ask K P dummy queryMap) (fun _ ↦ ask_measurable K P dummy queryMap hq)
    (fun _ ↦ update K P replyMap) (fun _ ↦ update_measurable K P replyMap hr)
    (finish K P) (finish_measurable K P)

theorem execute_finish (oracle : Q → R) (seed : Ω) (k t : ℕ)
    (s : State K (n := n) (dx := dx)) :
    finish K P seed
      (OracleProgram.executeStateFrom (fun _ ↦ ask K P dummy queryMap)
        (fun _ ↦ update K P replyMap) oracle seed k t s) =
      s.elim id (fun h ↦ (OraclePolicy.runAux K P
        (fun q ↦ replyMap q (oracle (queryMap q))) seed k h).1) := by
  induction k generalizing t s with
  | zero => rfl
  | succ k ih =>
    cases s with
    | inl x =>
      simpa only [OracleProgram.executeStateFrom, update, Sum.elim_inl, finish,
        OraclePolicy.runAux] using ih (t + 1) (Sum.inl x)
    | inr h =>
      cases he : P.next seed h with
      | inl x =>
        simpa only [OracleProgram.executeStateFrom, update, Sum.elim_inr, he,
          Sum.elim_inl, OraclePolicy.runAux, id_eq] using ih (t + 1) (Sum.inl x)
      | inr q =>
        simpa only [OracleProgram.executeStateFrom, update, Sum.elim_inr, he,
          ask, action, OraclePolicy.runAux] using
          ih (t + 1) (Sum.inr (OraclePolicy.appendHistory K h (q, replyMap q (oracle (queryMap q)))))

/-- Exact output equality for every seed and every oracle, with the same budget. -/
theorem eval_program (hq : Measurable queryMap) (hr : Measurable (Function.uncurry replyMap))
    (budget : ℕ) (oracle : Q → R) (seed : Ω) :
    OracleProgram.eval (program K P dummy queryMap replyMap hq hr budget) oracle seed =
      (OraclePolicy.run K P (fun q ↦ replyMap q (oracle (queryMap q))) seed budget).1 := by
  rw [program, OracleProgram.eval_stateLoop, execute_finish]
  rfl

end NCConcave16991.OracleSimulation
