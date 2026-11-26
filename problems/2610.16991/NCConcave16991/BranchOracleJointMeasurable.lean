import NCConcave16991.BranchOracleInterpreterMeasurable

/-! # Joint measurability of actual reference histories and their flat event

Only joint measurability of the literal reply renderer and source score is
used.  The latent parameter may carry any measurable law, independently of
the unrestricted private seed and the policy's full adaptive history.
-/

namespace NCConcave16991.BranchOracle.Reference
noncomputable section
open GlobalHard GlobalHardEuclidean

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000
set_option synthInstance.maxSize 4096
set_option maxHeartbeats 1000000

variable {n M N : ℕ} [NeZero n] (V : Fin M → Fin (N + 1) → Type*)
  [∀ j k, NormedAddCommGroup (V j k)] [∀ j k, InnerProductSpace ℝ (V j k)]
  [∀ j k, FiniteDimensional ℝ (V j k)]
variable {D : ℝ} (K : KnownDualDomain (dualDimension V) D)
variable {Θ : Type*} [MeasurableSpace Θ]
  (B : Θ → ∀ j : Fin M, ∀ t : Fin N, BranchGeometry.BranchFamily (ι := Fin n) (V j t.castSucc) (V j t.succ))
  (u : Θ → ∀ j, V j 0) (v : Θ → ∀ j, V j (Fin.last N))
  (ρ : ℝ) (site : Fin M → ℕ) (d c μ : ℝ)
  (hresponse : Measurable (fun a : Θ × (ℕ × OracleQuery n (primalDimension V) K) ↦
    referenceResponse V K (B a.1) (u a.1) (v a.1) a.2.1 d c μ a.2.2))

include hresponse

theorem step_joint_measurable : Measurable
    (fun a : Θ × (State (n := n) V K × OracleQuery n (primalDimension V) K) ↦
      step V K (B a.1) (u a.1) (v a.1) ρ site d c μ a.2.1 a.2.2) := by
  let X := Θ × (State (n := n) V K × OracleQuery n (primalDimension V) K)
  let after : X → ℕ × WordProfile (Fin n) := fun a ↦ roundUpdate V K ρ site a.2
  have ha : Measurable after := (roundUpdate_measurable (n := n) V K ρ site).comp measurable_snd
  let answer : X → OracleAnswer (primalDimension V) (dualDimension V) := fun a ↦
    referenceResponse V K (B a.1) (u a.1) (v a.1) (after a).1 d c μ a.2.2
  have hr : Measurable answer := by
    convert hresponse.comp
      (measurable_fst.prodMk (ha.fst.prodMk (measurable_snd.comp measurable_snd))) using 1
    funext a
    rfl
  let hist : X → OraclePolicy.History K (n := n) (dx := primalDimension V) := fun a ↦
    OraclePolicy.appendHistory K a.2.1.history (a.2.2, answer a)
  have hh : Measurable hist := (OraclePolicy.appendHistory_measurable K).comp
    (((history_measurable V K).comp (measurable_fst.comp measurable_snd)).prodMk
      ((measurable_snd.comp measurable_snd).prodMk hr))
  convert state_mk_measurable V K (fun a : X ↦ (after a).2) (fun a : X ↦ (after a).1) hist ha.snd ha.fst hh using 1
  funext a
  rfl

variable {Ω : Type*} [MeasurableSpace Ω]
  (P : OraclePolicy.AdaptivePolicy K (n := n) (dx := primalDimension V) Ω)

theorem runAux_joint_measurable (t : ℕ) : Measurable
    (fun a : (Θ × Ω) × State (n := n) V K ↦
      runAux V K (B a.1.1) (u a.1.1) (v a.1.1) ρ site d c μ P a.1.2 t a.2) := by
  induction t with
  | zero =>
    exact (P.final_measurable.comp
      ((measurable_snd.comp measurable_fst).prodMk ((history_measurable V K).comp measurable_snd))).prodMk measurable_snd
  | succ t ih =>
    let S := (Θ × Ω) × State (n := n) V K
    have hstop : Measurable (fun a : S × PrimalSpace (primalDimension V) ↦ (a.2, a.1.2)) :=
      measurable_snd.prodMk (measurable_snd.comp measurable_fst)
    have hquery : Measurable (fun a : S × OracleQuery n (primalDimension V) K ↦
        runAux V K (B a.1.1.1) (u a.1.1.1) (v a.1.1.1) ρ site d c μ P a.1.1.2 t
          (step V K (B a.1.1.1) (u a.1.1.1) (v a.1.1.1) ρ site d c μ a.1.2 a.2)) := by
      exact ih.comp ((measurable_fst.comp measurable_fst).prodMk
        ((step_joint_measurable V K B u v ρ site d c μ hresponse).comp
          ((measurable_fst.comp (measurable_fst.comp measurable_fst)).prodMk
            ((measurable_snd.comp measurable_fst).prodMk measurable_snd))))
    have hnext : Measurable (fun a : S ↦ P.next a.1.2 a.2.history) :=
      P.next_measurable.comp ((measurable_snd.comp measurable_fst).prodMk ((history_measurable V K).comp measurable_snd))
    have hb := (hstop.sumElim hquery).comp
      (MeasurableEquiv.prodSumDistrib S (PrimalSpace (primalDimension V)) (OracleQuery n (primalDimension V) K)).measurable
    have hc := hb.comp (measurable_id.prodMk hnext)
    convert hc using 1
    funext a
    cases he : P.next a.1.2 a.2.history <;>
      simp [runAux, Function.comp_apply, he, MeasurableEquiv.prodSumDistrib, MeasurableEquiv.sumProdDistrib,
        MeasurableEquiv.prodComm, MeasurableEquiv.sumCongr, Equiv.sumProdDistrib, Equiv.sumCongr]

theorem run_joint_measurable (budget : ℕ) : Measurable
    (fun a : Θ × Ω ↦ run V K (B a.1) (u a.1) (v a.1) ρ site d c μ P a.2 budget) :=
  (runAux_joint_measurable V K B u v ρ site d c μ hresponse P budget).comp
    (measurable_id.prodMk measurable_const)

variable (hscore : ∀ j : Fin M, Measurable (fun a : Θ × OracleQuery n (primalDimension V) K ↦
  stateScore (v a.1 j) (stateProj V j (queryGlobal V K a.2))))

include hscore

theorem stepFlat_joint_measurable : Measurable
    (fun a : Θ × (State (n := n) V K × OracleQuery n (primalDimension V) K) ↦
      StepFlat V K (B a.1) (u a.1) (v a.1) ρ site d c μ a.2.1 a.2.2) := by
  apply Measurable.forall
  intro j
  have hr := (released_measurable V K).comp (step_joint_measurable V K B u v ρ site d c μ hresponse)
  have hl : Measurable (fun a : Θ × (State (n := n) V K × OracleQuery n (primalDimension V) K) ↦
      (step V K (B a.1) (u a.1) (v a.1) ρ site d c μ a.2.1 a.2.2).released ≤ j.val) :=
    measurableSet_setOfPred.mp (measurableSet_le hr measurable_const)
  have hs : Measurable (fun a : Θ × (State (n := n) V K × OracleQuery n (primalDimension V) K) ↦
      stateScore (v a.1 j) (stateProj V j (queryGlobal V K a.2.2))) :=
    (hscore j).comp (measurable_fst.prodMk (measurable_snd.comp measurable_snd))
  exact hl.imp (measurableSet_setOfPred.mp (measurableSet_lt hs measurable_const))

theorem runFlat_joint_measurable (t : ℕ) : Measurable
    (fun a : (Θ × Ω) × State (n := n) V K ↦
      RunFlat V K (B a.1.1) (u a.1.1) (v a.1.1) ρ site d c μ P a.1.2 t a.2) := by
  induction t with
  | zero => exact measurable_const
  | succ t ih =>
    let S := (Θ × Ω) × State (n := n) V K
    have hstop : Measurable (fun _ : S × PrimalSpace (primalDimension V) ↦ True) := measurable_const
    have hstep : Measurable (fun a : S × OracleQuery n (primalDimension V) K ↦
        step V K (B a.1.1.1) (u a.1.1.1) (v a.1.1.1) ρ site d c μ a.1.2 a.2) :=
      (step_joint_measurable V K B u v ρ site d c μ hresponse).comp
      ((measurable_fst.comp (measurable_fst.comp measurable_fst)).prodMk
        ((measurable_snd.comp measurable_fst).prodMk measurable_snd))
    have hflat : Measurable (fun a : S × OracleQuery n (primalDimension V) K ↦
        StepFlat V K (B a.1.1.1) (u a.1.1.1) (v a.1.1.1) ρ site d c μ a.1.2 a.2) :=
      (stepFlat_joint_measurable V K B u v ρ site d c μ hresponse hscore).comp
      ((measurable_fst.comp (measurable_fst.comp measurable_fst)).prodMk
        ((measurable_snd.comp measurable_fst).prodMk measurable_snd))
    have hquery : Measurable (fun a : S × OracleQuery n (primalDimension V) K ↦
        StepFlat V K (B a.1.1.1) (u a.1.1.1) (v a.1.1.1) ρ site d c μ a.1.2 a.2 ∧
        RunFlat V K (B a.1.1.1) (u a.1.1.1) (v a.1.1.1) ρ site d c μ P a.1.1.2 t
          (step V K (B a.1.1.1) (u a.1.1.1) (v a.1.1.1) ρ site d c μ a.1.2 a.2)) :=
      hflat.and (ih.comp ((measurable_fst.comp measurable_fst).prodMk hstep))
    have hnext : Measurable (fun a : S ↦ P.next a.1.2 a.2.history) :=
      P.next_measurable.comp ((measurable_snd.comp measurable_fst).prodMk ((history_measurable V K).comp measurable_snd))
    have hb := (hstop.sumElim hquery).comp
      (MeasurableEquiv.prodSumDistrib S (PrimalSpace (primalDimension V)) (OracleQuery n (primalDimension V) K)).measurable
    have hc := hb.comp (measurable_id.prodMk hnext)
    convert hc using 1
    funext a
    cases he : P.next a.1.2 a.2.history <;>
      simp [RunFlat, Function.comp_apply, he, MeasurableEquiv.prodSumDistrib, MeasurableEquiv.sumProdDistrib,
        MeasurableEquiv.prodComm, MeasurableEquiv.sumCongr, Equiv.sumProdDistrib, Equiv.sumCongr]

theorem runFlat_initial_joint_measurable (budget : ℕ) : Measurable
    (fun a : Θ × Ω ↦ RunFlat V K (B a.1) (u a.1) (v a.1) ρ site d c μ P a.2 budget (initial V K)) :=
  (runFlat_joint_measurable V K B u v ρ site d c μ hresponse P hscore budget).comp
    (measurable_id.prodMk measurable_const)

end
end NCConcave16991.BranchOracle.Reference
