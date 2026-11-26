import SampleReuse.CurvatureFirstRun
import SampleReuse.OracleDerivativeCounts

open MeasureTheory SecondOrder
open scoped Classical

namespace SampleReuse
noncomputable section

/-- Literal separate derivative counts along the actual controller execution.
The final successful inspection is included; the private sign is not a query. -/
def curvatureFirstDerivativeCounts {Ω : Type*} {d T Bg BH : ℕ} (hBg : 0 < Bg) (hBH : 0 < BH)
    (P : Parameters) (ε γ scaleG scaleH : ℝ) (F : Ω → Point d → ℝ)
    (tape : SampleTape ((T+1)*Bg+(T+1)*BH) Ω) (signs : ℕ → Bool) :
    ℕ → ℕ → OptimizerCache d → ℕ × ℕ
  | 0, _, _ => (0,0)
  | m+1, t, s =>
    let r := curvatureFirstInspect hBg hBH P ε γ scaleG scaleH F tape t s
    (r.gradientCalls,r.hessianCalls) +
      match curvatureFirstAdvance P ε γ (signs t) r with
      | none => (0,0)
      | some s' => curvatureFirstDerivativeCounts hBg hBH P ε γ scaleG scaleH F tape signs m (t+1) s'

theorem curvatureFirstDerivativeCounts_total {Ω : Type*} {d T Bg BH : ℕ} (hBg : 0 < Bg) (hBH : 0 < BH)
    (P : Parameters) (ε γ scaleG scaleH : ℝ) (F : Ω → Point d → ℝ)
    (tape : SampleTape ((T+1)*Bg+(T+1)*BH) Ω) (signs : ℕ → Bool)
    (m t : ℕ) (s : OptimizerCache d) :
    (curvatureFirstDerivativeCounts hBg hBH P ε γ scaleG scaleH F tape signs m t s).1 +
      (curvatureFirstDerivativeCounts hBg hBH P ε γ scaleG scaleH F tape signs m t s).2 =
      curvatureFirstCallTime hBg hBH P ε γ scaleG scaleH F tape signs m t s := by
  induction m generalizing t s with
  | zero => rfl
  | succ m ih =>
    simp only [curvatureFirstDerivativeCounts,curvatureFirstCallTime]
    cases he : curvatureFirstAdvance P ε γ (signs t)
      (curvatureFirstInspect hBg hBH P ε γ scaleG scaleH F tape t s) with
    | none => simp only [he,Prod.fst_add,Prod.snd_add,Nat.add_zero,Nat.zero_add,Nat.add_comm]
    | some s' =>
      simp only [he,Prod.fst_add,Prod.snd_add]
      have hh := ih (t+1) s'
      omega

theorem checkpointProgram_requestCounts {Ω E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H d B : ℕ} (hB : 0 < B) (scale σ L : ℝ) (flag : Bool) (project : PersistentReply d → E)
    (reserve : ℕ → Fin B → Fin H) (k : ℕ) (cache : TreeCache d E) (x : Point d)
    (F : Ω → Point d → ℝ) (tape : SampleTape H Ω) :
    OracleDerivativeCaps.requestCounts Prod.fst (fun q tape => persistentReply F tape q)
      (checkpointCalls (B := B) scale σ L k cache x) (fun _ => tape)
      (checkpointProgram hB scale σ L flag project reserve k cache x) =
      if flag then (checkpointCalls (B := B) scale σ L k cache x,0)
      else (0,checkpointCalls (B := B) scale σ L k cache x) := by
  unfold checkpointProgram checkpointCalls
  by_cases hk : k = 0
  · simp only [if_pos hk,fieldRootProgram]
    exact OracleDerivativeCaps.requestCounts_batch Prod.fst _ _ _ _ _ flag (fun _ => rfl)
  · simp only [if_neg hk]
    simpa only [fieldChordProgram,Nat.mul_comm] using
      OracleDerivativeCaps.requestCounts_batch Prod.fst (fun q tape => persistentReply F tape q)
        (fun _ => tape) _ (chordBatchQueries flag
          (fun i => reserve k (prefixHandles hB (checkpointBatchSize (B := B) scale σ L k cache x) i))
          x (cache (ancestorParent k)).1) _ flag (fun _ => rfl)

theorem curvatureFirstProgram_requestCounts {Ω : Type} {d T Bg BH : ℕ}
    (hBg : 0 < Bg) (hBH : 0 < BH) (P : Parameters) (ε γ scaleG scaleH : ℝ)
    (F : Ω → Point d → ℝ) (q₀ : PersistentQuery ((T+1)*Bg+(T+1)*BH) d)
    (tape : SampleTape ((T+1)*Bg+(T+1)*BH) Ω) (signs : ℕ → Bool)
    (m t : ℕ) (s : OptimizerCache d) :
    OracleDerivativeCaps.requestCounts Prod.fst (fun q tape => persistentReply F tape q)
      (curvatureFirstCallTime hBg hBH P ε γ scaleG scaleH F tape signs m t s) (fun _ => tape)
      (curvatureFirstProgram hBg hBH P ε γ scaleG scaleH signs m t s) =
      curvatureFirstDerivativeCounts hBg hBH P ε γ scaleG scaleH F tape signs m t s := by
  induction m generalizing t s with
  | zero => rfl
  | succ m ih =>
    have hH := checkpointProgram_run hBH scaleH P.hessianNoise P.hessianLip q₀ F
      (fun z => hessian (F z)) false Prod.snd (fun _ _ _ => rfl)
      (hessianReserve T Bg BH) t s.2.2.2 s.1 tape
    have hG := checkpointProgram_run hBg scaleG P.gradientNoise P.gradientLip q₀ F
      (fun z => gradient (F z)) true Prod.fst (fun _ _ _ => rfl)
      (gradientReserve T Bg BH) s.2.1 s.2.2.1 s.1 tape
    simp only [curvatureFirstCallTime,curvatureFirstDerivativeCounts,curvatureFirstInspect]
    split_ifs with hh hg
    · simp only [curvatureFirstAdvance,Nat.add_zero]
      rw [curvatureFirstProgram,OracleDerivativeCaps.requestCounts_bind_of_exact _ q₀ _ (fun _ => tape)
        (checkpointProgram_exact hBH scaleH P.hessianNoise P.hessianLip false Prod.snd
          (hessianReserve T Bg BH) t s.2.2.2 s.1) _ hH]
      simp only [hh,Bool.true_eq,if_true,checkpointProgram_requestCounts,ih,Prod.fst_add,Prod.snd_add,
        Nat.zero_add,Prod.mk_add_mk,Bool.false_eq_true,if_false]
      apply Prod.ext <;> simp only [Prod.fst_add,Prod.snd_add,Nat.zero_add]
    · simp only [curvatureFirstAdvance,Nat.add_zero]
      rw [curvatureFirstProgram,OracleDerivativeCaps.requestCounts_bind_of_exact _ q₀ _ (fun _ => tape)
        (checkpointProgram_exact hBH scaleH P.hessianNoise P.hessianLip false Prod.snd
          (hessianReserve T Bg BH) t s.2.2.2 s.1) _ hH]
      simp only [hh,Bool.false_eq_true,if_false]
      rw [← Nat.add_zero (checkpointCalls (B := Bg) scaleG P.gradientNoise P.gradientLip s.2.1 s.2.2.1 s.1),
        OracleDerivativeCaps.requestCounts_bind_of_exact _ q₀ _ (fun _ => tape)
        (checkpointProgram_exact hBg scaleG P.gradientNoise P.gradientLip true Prod.fst
          (gradientReserve T Bg BH) s.2.1 s.2.2.1 s.1) _ hG]
      simp only [hg,if_true,checkpointProgram_requestCounts,OracleDerivativeCaps.requestCounts,
        Prod.mk_add_mk,Nat.add_zero,Nat.zero_add,Bool.false_eq_true,if_false]
    · simp only [curvatureFirstAdvance]
      rw [Nat.add_assoc,curvatureFirstProgram,OracleDerivativeCaps.requestCounts_bind_of_exact _ q₀ _ (fun _ => tape)
        (checkpointProgram_exact hBH scaleH P.hessianNoise P.hessianLip false Prod.snd
          (hessianReserve T Bg BH) t s.2.2.2 s.1) _ hH]
      simp only [hh,Bool.false_eq_true,if_false]
      rw [OracleDerivativeCaps.requestCounts_bind_of_exact _ q₀ _ (fun _ => tape)
        (checkpointProgram_exact hBg scaleG P.gradientNoise P.gradientLip true Prod.fst
          (gradientReserve T Bg BH) s.2.1 s.2.2.1 s.1) _ hG]
      simp only [hg,if_false,checkpointProgram_requestCounts,ih,Prod.mk_add_mk,
        Nat.add_zero,Nat.zero_add,Bool.false_eq_true,if_true]
      rfl

end
end SampleReuse
