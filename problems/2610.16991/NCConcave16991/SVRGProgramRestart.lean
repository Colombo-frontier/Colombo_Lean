import NCConcave16991.SVRGProgramEpoch

/-! # Independent restarted SVRG epochs as an actual oracle program -/

noncomputable section

open Set MeasureTheory

namespace NCConcave16991.SVRGProgram

variable {n dx dy : ℕ} {D : ℝ} {K : KnownDualDomain dy D}
  {Θ : Type*} [MeasurableSpace Θ] [MeasurableSpace (Fin n)]

def epochsProgram (F : DomainFamily (dx := dx) K Θ)
    (R : Θ × JointSpace dx dy → JointSpace dx dy) (hR : Measurable R)
    (ell μ : ℝ) : (J : ℕ) →
    OracleProgram.Fixed (OracleQuery n dx K) (OracleAnswer dx dy) (Point F)
      (FiniteProcess.History (InnerAlgorithm.Seed n (SVRG.epochLength ell μ)) J × Point F)
      (J * (n + 2 * SVRG.epochLength ell μ))
  | 0 => OracleProgram.castBudget (OracleProgram.pure Prod.snd measurable_snd) (by simp)
  | J + 1 => OracleProgram.castBudget
      (OracleProgram.bind
        (OracleProgram.withSeed (epochsProgram F R hR ell μ J)
          (fun a : FiniteProcess.History (InnerAlgorithm.Seed n (SVRG.epochLength ell μ)) (J + 1) × Point F ↦
            (a.1.1, a.2)) ((measurable_fst.comp measurable_fst).prodMk measurable_snd))
        (OracleProgram.withSeed (epochProgram F R hR (SVRG.epochStepSize ell μ) (SVRG.epochLength ell μ))
          (fun a : (FiniteProcess.History (InnerAlgorithm.Seed n (SVRG.epochLength ell μ)) (J + 1) × Point F) × Point F ↦
            (a.1.1.2, a.2))
          ((measurable_snd.comp (measurable_fst.comp measurable_fst)).prodMk measurable_snd)))
      (by ring)

variable {p : ProblemParameters} {K' : KnownDualDomain dy p.diameter}

set_option backward.isDefEq.respectTransparency false in
theorem eval_epochsProgram [MeasurableSpace (Fin p.n)] [MeasurableSingletonClass (Fin p.n)]
    (P : Problem p dx dy K') (F : DomainFamily (dx := dx) K' Θ)
    (R : Θ × JointSpace dx dy → JointSpace dx dy) (hR : Measurable R)
    (ell μ : ℝ) (J : ℕ)
    (ω : FiniteProcess.History (InnerAlgorithm.Seed p.n (SVRG.epochLength ell μ)) J)
    (point : Point F) :
    OracleProgram.eval (epochsProgram F R hR ell μ J) (oracleResponse P) (ω, point) =
      ⟨(point.1.1, (SVRG.epochsIterate (F.carrier point.1.1) (F.nonempty _) (F.closed _) (F.convex _)
        (fun i z ↦ signedComponentGradient P i z + R (point.1.1, z))
        ⟨point.1.2, point.2⟩ ell μ J ω : JointSpace dx dy)),
        (SVRG.epochsIterate (F.carrier point.1.1) (F.nonempty _) (F.closed _) (F.convex _)
        (fun i z ↦ signedComponentGradient P i z + R (point.1.1, z))
        ⟨point.1.2, point.2⟩ ell μ J ω).2⟩ := by
  letI : NeZero p.n := ⟨Nat.ne_of_gt p.n_pos⟩
  induction J with
  | zero =>
    simp only [epochsProgram, OracleProgram.eval_castBudget, OracleProgram.eval_pure]
    rfl
  | succ J ih =>
    simp only [epochsProgram, OracleProgram.eval_castBudget, OracleProgram.eval_bind,
      OracleProgram.eval_withSeed, ih, eval_epochProgram]
    rfl

end NCConcave16991.SVRGProgram
