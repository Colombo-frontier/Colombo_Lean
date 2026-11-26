import NCConcave16991.SVRGProgramRestart
import NCConcave16991.SVRGProgramResidual
import NCConcave16991.SVRGQueries

/-! # Complete finite-seed reply-driven SVRG residual engine -/

noncomputable section

open Set MeasureTheory

namespace NCConcave16991.SVRGProgram

variable {n dx dy : ℕ} {D : ℝ} {K : KnownDualDomain dy D}
  {Θ : Type*} [MeasurableSpace Θ] [MeasurableSpace (Fin n)]

/-- Exact query cost is J(n+2m)+2n; no unknown component function occurs here. -/
def engineProgram (F : DomainFamily (dx := dx) K Θ)
    (R : Θ × JointSpace dx dy → JointSpace dx dy) (hR : Measurable R)
    (ell μ : ℝ) (J : ℕ) :
    OracleProgram.Fixed (OracleQuery n dx K) (OracleAnswer dx dy) (Result F)
      (FiniteProcess.History (InnerAlgorithm.Seed n (SVRG.epochLength ell μ)) J × Point F)
      (SVRG.residualQueryBudget n ell μ J) :=
  OracleProgram.bind (epochsProgram F R hR ell μ J)
    (OracleProgram.withSeed (residualProgram F R hR ell) Prod.snd measurable_snd)

variable {p : ProblemParameters} {K' : KnownDualDomain dy p.diameter}

set_option backward.isDefEq.respectTransparency false in
theorem eval_engineProgram [MeasurableSpace (Fin p.n)] [MeasurableSingletonClass (Fin p.n)]
    (P : Problem p dx dy K') (F : DomainFamily (dx := dx) K' Θ)
    (R : Θ × JointSpace dx dy → JointSpace dx dy) (hR : Measurable R)
    (ell μ : ℝ) (J : ℕ)
    (ω : FiniteProcess.History (InnerAlgorithm.Seed p.n (SVRG.epochLength ell μ)) J)
    (point : Point F) :
    OracleProgram.eval (engineProgram F R hR ell μ J) (oracleResponse P) (ω, point) =
      directResult F
        (fun θ ↦ averageMap (fun i z ↦ signedComponentGradient P i z + R (θ, z))) ell
        ⟨(point.1.1, (SVRG.epochsIterate (F.carrier point.1.1) (F.nonempty _) (F.closed _) (F.convex _)
          (fun i z ↦ signedComponentGradient P i z + R (point.1.1, z))
          ⟨point.1.2, point.2⟩ ell μ J ω : JointSpace dx dy)),
          (SVRG.epochsIterate (F.carrier point.1.1) (F.nonempty _) (F.closed _) (F.convex _)
          (fun i z ↦ signedComponentGradient P i z + R (point.1.1, z))
          ⟨point.1.2, point.2⟩ ell μ J ω).2⟩ := by
  letI : NeZero p.n := ⟨Nat.ne_of_gt p.n_pos⟩
  rw [engineProgram, OracleProgram.eval_bind, OracleProgram.eval_withSeed,
    eval_epochsProgram, eval_residualProgram]

end NCConcave16991.SVRGProgram
