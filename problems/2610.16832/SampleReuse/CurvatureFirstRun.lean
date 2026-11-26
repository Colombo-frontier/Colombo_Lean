import SampleReuse.CurvatureFirstExecution

open MeasureTheory SecondOrder
open scoped Classical

namespace SampleReuse
noncomputable section

/-- The reply-only controller executes exactly the inspection semantics, using
the same persistent table and charging every requested derivative. -/
theorem curvatureFirstProgram_run {Ω : Type} {d T Bg BH : ℕ} (hBg : 0 < Bg) (hBH : 0 < BH)
    (P : Parameters) (ε γ scaleG scaleH : ℝ) (F : Ω → Point d → ℝ)
    (q₀ : PersistentQuery ((T+1)*Bg+(T+1)*BH) d)
    (tape : SampleTape ((T+1)*Bg+(T+1)*BH) Ω) (signs : ℕ → Bool)
    (m t : ℕ) (s : OptimizerCache d) :
    OracleProgram.run q₀ (fun q tape => persistentReply F tape q) (fun _ => tape)
      (curvatureFirstProgram hBg hBH P ε γ scaleG scaleH signs m t s)
      (curvatureFirstCallTime hBg hBH P ε γ scaleG scaleH F tape signs m t s) =
      .done (curvatureFirstExecute hBg hBH P ε γ scaleG scaleH F tape signs m t s) := by
  induction m generalizing t s with
  | zero => rfl
  | succ m ih =>
    have hH := checkpointProgram_run hBH scaleH P.hessianNoise P.hessianLip q₀ F
      (fun z => hessian (F z)) false Prod.snd (fun _ _ _ => rfl)
      (hessianReserve T Bg BH) t s.2.2.2 s.1 tape
    have hG := checkpointProgram_run hBg scaleG P.gradientNoise P.gradientLip q₀ F
      (fun z => gradient (F z)) true Prod.fst (fun _ _ _ => rfl)
      (gradientReserve T Bg BH) s.2.1 s.2.2.1 s.1 tape
    simp only [curvatureFirstCallTime, curvatureFirstExecute, curvatureFirstInspect]
    split_ifs with hh hg
    · simp only [curvatureFirstAdvance, Nat.add_zero]
      rw [curvatureFirstProgram, OracleProgram.run_bind_of_exact q₀ _ (fun _ => tape)
        (checkpointProgram_exact hBH scaleH P.hessianNoise P.hessianLip false Prod.snd
          (hessianReserve T Bg BH) t s.2.2.2 s.1) _ hH]
      simp only [hh, Bool.true_eq, if_true]
      exact ih (t+1) _
    · simp only [curvatureFirstAdvance, Nat.add_zero]
      rw [curvatureFirstProgram, OracleProgram.run_bind_of_exact q₀ _ (fun _ => tape)
        (checkpointProgram_exact hBH scaleH P.hessianNoise P.hessianLip false Prod.snd
          (hessianReserve T Bg BH) t s.2.2.2 s.1) _ hH]
      simp only [hh, Bool.false_eq_true, if_false]
      rw [← Nat.add_zero (checkpointCalls (B := Bg) scaleG P.gradientNoise P.gradientLip s.2.1 s.2.2.1 s.1),
        OracleProgram.run_bind_of_exact q₀ _ (fun _ => tape)
        (checkpointProgram_exact hBg scaleG P.gradientNoise P.gradientLip true Prod.fst
          (gradientReserve T Bg BH) s.2.1 s.2.2.1 s.1) _ hG]
      simp only [hg, if_true, OracleProgram.run]
    · simp only [curvatureFirstAdvance]
      rw [Nat.add_assoc, curvatureFirstProgram, OracleProgram.run_bind_of_exact q₀ _ (fun _ => tape)
        (checkpointProgram_exact hBH scaleH P.hessianNoise P.hessianLip false Prod.snd
          (hessianReserve T Bg BH) t s.2.2.2 s.1) _ hH]
      simp only [hh, Bool.false_eq_true, if_false]
      rw [OracleProgram.run_bind_of_exact q₀ _ (fun _ => tape)
        (checkpointProgram_exact hBg scaleG P.gradientNoise P.gradientLip true Prod.fst
          (gradientReserve T Bg BH) s.2.1 s.2.2.1 s.1) _ hG]
      simp only [hg, if_false]
      exact ih (t+1) _

/-- Numerical output of the compiled persistent-oracle policy at its actual
call count, with no access to sample identities by the policy. -/
theorem curvatureFirstProgram_compiled_output {Ω : Type} {d T Bg BH : ℕ}
    (hBg : 0 < Bg) (hBH : 0 < BH) (P : Parameters) (ε γ scaleG scaleH : ℝ)
    (F : Ω → Point d → ℝ) (q₀ : PersistentQuery ((T+1)*Bg+(T+1)*BH) d)
    (tape : SampleTape ((T+1)*Bg+(T+1)*BH) Ω) (signs : ℕ → Bool)
    (m t : ℕ) (s : OptimizerCache d) :
    let alg := OracleProgram.algorithm q₀ (0, 0) none
      (curvatureFirstProgram hBg hBH P ε γ scaleG scaleH signs m t s)
    let N := curvatureFirstCallTime hBg hBH P ε γ scaleG scaleH F tape signs m t s
    alg.output N (persistentRun alg.toQueryPolicy F tape N) =
      curvatureFirstExecute hBg hBH P ε γ scaleG scaleH F tape signs m t s := by
  dsimp only
  rw [persistentRun_eq_queryPolicyRun]
  change oracleAlgorithmOutput _ _ _ _ = _
  rw [OracleProgram.algorithm_output, curvatureFirstProgram_run]
  rfl

end
end SampleReuse
