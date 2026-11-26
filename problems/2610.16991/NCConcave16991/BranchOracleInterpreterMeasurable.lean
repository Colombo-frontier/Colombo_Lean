import NCConcave16991.BranchOracleStateMeasurable
import NCConcave16991.BranchOracleResponseMeasurable
import NCConcave16991.OracleMeasurability

/-! # Measurability of the actual unrestricted branch reference execution -/

namespace NCConcave16991.BranchOracle.Reference
noncomputable section
open GlobalHardEuclidean

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000
set_option synthInstance.maxSize 2048
set_option maxSynthPendingDepth 4
set_option maxHeartbeats 1000000

variable {n M N : ℕ} [NeZero n] (V : Fin M → Fin (N + 1) → Type*)
  [∀ j k, NormedAddCommGroup (V j k)] [∀ j k, InnerProductSpace ℝ (V j k)]
  [∀ j k, FiniteDimensional ℝ (V j k)]
variable {D : ℝ} (K : KnownDualDomain (dualDimension V) D)
variable (B : ∀ j : Fin M, ∀ t : Fin N,
    BranchGeometry.BranchFamily (ι := Fin n) (V j t.castSucc) (V j t.succ))
  (u : ∀ j, V j 0) (v : ∀ j, V j (Fin.last N))
  (ρ : ℝ) (site : Fin M → ℕ) (d c μ : ℝ)

def roundUpdate (a : State (n := n) V K × OracleQuery n (primalDimension V) K) : ℕ × WordProfile (Fin n) :=
  WordProfile.close ρ site a.1.released (a.1.profile.matrixScheduleStep (fun _ ↦ a.2.1))

theorem roundUpdate_measurable : Measurable (roundUpdate (n := n) V K ρ site) := by
  have hi : Measurable (fun a : State (n := n) V K × OracleQuery n (primalDimension V) K ↦
      ((a.1.profile, a.1.released), a.2.1)) :=
    (((profile_measurable V K).comp measurable_fst).prodMk ((released_measurable V K).comp measurable_fst)).prodMk
      (measurable_fst.comp measurable_snd)
  exact (publicUpdate_measurable ρ site).comp hi

theorem roundResponse_measurable : Measurable
    (fun a : State (n := n) V K × OracleQuery n (primalDimension V) K ↦
      referenceResponse V K B u v (roundUpdate V K ρ site a).1 d c μ a.2) := by
  have hh := (referenceResponse_measurable V B K u v d c μ).comp
    ((roundUpdate_measurable (n := n) V K ρ site).fst.prodMk measurable_snd)
  convert hh using 1
  funext a
  rfl

theorem roundHistory_measurable : Measurable
    (fun a : State (n := n) V K × OracleQuery n (primalDimension V) K ↦
      OraclePolicy.appendHistory K a.1.history
        (a.2, referenceResponse V K B u v (roundUpdate V K ρ site a).1 d c μ a.2)) :=
  (OraclePolicy.appendHistory_measurable K).comp
    (((history_measurable V K).comp measurable_fst).prodMk
      (measurable_snd.prodMk (roundResponse_measurable V K B u v ρ site d c μ)))

theorem step_measurable :
    Measurable (fun a : State (n := n) V K × OracleQuery n (primalDimension V) K ↦ step V K B u v ρ site d c μ a.1 a.2) := by
  convert state_mk_measurable V K (fun a ↦ (roundUpdate V K ρ site a).2) (fun a ↦ (roundUpdate V K ρ site a).1)
    (fun a ↦ OraclePolicy.appendHistory K a.1.history (a.2, referenceResponse V K B u v (roundUpdate V K ρ site a).1 d c μ a.2))
    (roundUpdate_measurable (n := n) V K ρ site).snd (roundUpdate_measurable (n := n) V K ρ site).fst
    (roundHistory_measurable V K B u v ρ site d c μ) using 1
  funext a
  rfl

variable {Ω : Type*} [MeasurableSpace Ω]
  (P : OraclePolicy.AdaptivePolicy K (n := n) (dx := primalDimension V) Ω)

theorem runAux_measurable (t : ℕ) :
    Measurable (fun a : Ω × State (n := n) V K ↦ runAux V K B u v ρ site d c μ P a.1 t a.2) := by
  induction t with
  | zero => exact (P.final_measurable.comp (measurable_fst.prodMk ((history_measurable V K).comp measurable_snd))).prodMk measurable_snd
  | succ t ih =>
    let S := Ω × State (n := n) V K
    have hstop : Measurable (fun a : S × PrimalSpace (primalDimension V) ↦ (a.2, a.1.2)) :=
      measurable_snd.prodMk (measurable_snd.comp measurable_fst)
    have hquery : Measurable (fun a : S × OracleQuery n (primalDimension V) K ↦
        runAux V K B u v ρ site d c μ P a.1.1 t (step V K B u v ρ site d c μ a.1.2 a.2)) := by
      exact ih.comp ((measurable_fst.comp measurable_fst).prodMk
        ((step_measurable V K B u v ρ site d c μ).comp ((measurable_snd.comp measurable_fst).prodMk measurable_snd)))
    have hnext : Measurable (fun a : S ↦ P.next a.1 a.2.history) :=
      P.next_measurable.comp (measurable_fst.prodMk ((history_measurable V K).comp measurable_snd))
    have hb := (hstop.sumElim hquery).comp
      (MeasurableEquiv.prodSumDistrib S (PrimalSpace (primalDimension V)) (OracleQuery n (primalDimension V) K)).measurable
    have hc := hb.comp (measurable_id.prodMk hnext)
    convert hc using 1
    funext a
    cases he : P.next a.1 a.2.history <;>
      simp [runAux, Function.comp_apply, Function.uncurry, he,
        MeasurableEquiv.prodSumDistrib, MeasurableEquiv.sumProdDistrib,
        MeasurableEquiv.prodComm, MeasurableEquiv.sumCongr, Equiv.sumProdDistrib, Equiv.sumCongr]

theorem run_measurable (budget : ℕ) : Measurable (fun seed : Ω ↦ run V K B u v ρ site d c μ P seed budget) :=
  (runAux_measurable V K B u v ρ site d c μ P budget).comp (measurable_id.prodMk measurable_const)

theorem output_measurable (budget : ℕ) : Measurable (fun seed : Ω ↦ (run V K B u v ρ site d c μ P seed budget).1) :=
  measurable_fst.comp (run_measurable V K B u v ρ site d c μ P budget)

end
end NCConcave16991.BranchOracle.Reference
