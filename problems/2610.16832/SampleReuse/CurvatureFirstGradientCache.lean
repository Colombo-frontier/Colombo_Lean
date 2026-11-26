import SampleReuse.CurvatureFirstGradientLocations

open MeasureTheory SecondOrder
open scoped Classical

namespace SampleReuse
noncomputable section

theorem curvatureFirstInspect_gradientCache {Ω : Type*} {d T Bg BH : ℕ}
    (hBg : 0 < Bg) (hBH : 0 < BH) (P : Parameters) (ε γ scaleG scaleH : ℝ)
    (F : Ω → Point d → ℝ) (tape : SampleTape ((T+1)*Bg+(T+1)*BH) Ω)
    (t : ℕ) (s : OptimizerCache d) :
    (curvatureFirstInspect hBg hBH P ε γ scaleG scaleH F tape t s).cache.2.2.1 =
      if curvatureTag (sourceCurvatureSelector (3*γ/4) (inspectionHessian hBH P scaleH F tape t s)) then s.2.2.1
      else Function.update s.2.2.1 s.2.1 (s.1,inspectionGradient hBg P scaleG F tape s) := by
  simp only [curvatureFirstInspect,inspectionHessian,inspectionGradient,installCheckpoint,checkpointValue]
  split_ifs <;> rfl

theorem curvatureFirstInspect_gradientClock {Ω : Type*} {d T Bg BH : ℕ}
    (hBg : 0 < Bg) (hBH : 0 < BH) (P : Parameters) (ε γ scaleG scaleH : ℝ)
    (F : Ω → Point d → ℝ) (tape : SampleTape ((T+1)*Bg+(T+1)*BH) Ω)
    (t : ℕ) (s : OptimizerCache d) :
    (curvatureFirstInspect hBg hBH P ε γ scaleG scaleH F tape t s).cache.2.1 =
      if curvatureTag (sourceCurvatureSelector (3*γ/4) (inspectionHessian hBH P scaleH F tape t s)) then s.2.1
      else s.2.1+1 := by
  simp only [curvatureFirstInspect,inspectionHessian]
  split_ifs <;> rfl

theorem curvatureMacroRun_gradientCache_preserves {Ω : Type*} {d T Bg BH : ℕ}
    (hBg : 0 < Bg) (hBH : 0 < BH) (P : Parameters) (ε γ scaleG scaleH : ℝ)
    (F : Ω → Point d → ℝ) (tape : SampleTape ((T+1)*Bg+(T+1)*BH) Ω)
    (signs : ℕ → Bool) (x₀ : Point d) (t j : ℕ)
    (hj : j < (curvatureMacroRun hBg hBH P ε γ scaleG scaleH F tape signs x₀ t).2.1) :
    (curvatureMacroRun hBg hBH P ε γ scaleG scaleH F tape signs x₀ (t+1)).2.2.1 j =
      (curvatureMacroRun hBg hBH P ε γ scaleG scaleH F tape signs x₀ t).2.2.1 j := by
  change (curvatureFirstInspect hBg hBH P ε γ scaleG scaleH F tape t
    (curvatureMacroRun hBg hBH P ε γ scaleG scaleH F tape signs x₀ t)).cache.2.2.1 j = _
  rw [curvatureFirstInspect_gradientCache]
  split_ifs
  · rfl
  · exact Function.update_of_ne hj.ne _ _

theorem curvatureMacroRun_gradientCache_preserves_interval {Ω : Type*} {d T Bg BH : ℕ}
    (hBg : 0 < Bg) (hBH : 0 < BH) (P : Parameters) (ε γ scaleG scaleH : ℝ)
    (F : Ω → Point d → ℝ) (tape : SampleTape ((T+1)*Bg+(T+1)*BH) Ω)
    (signs : ℕ → Bool) (x₀ : Point d) {s t j : ℕ} (hst : s ≤ t)
    (hj : j < (curvatureMacroRun hBg hBH P ε γ scaleG scaleH F tape signs x₀ s).2.1) :
    (curvatureMacroRun hBg hBH P ε γ scaleG scaleH F tape signs x₀ t).2.2.1 j =
      (curvatureMacroRun hBg hBH P ε γ scaleG scaleH F tape signs x₀ s).2.2.1 j := by
  induction t, hst using Nat.le_induction with
  | base => rfl
  | succ t ht ih =>
    rw [curvatureMacroRun_gradientCache_preserves hBg hBH P ε γ scaleG scaleH F tape signs x₀ t j
      (hj.trans_le (curvatureMacroRun_gradientIndex_mono hBg hBH P ε γ scaleG scaleH F tape signs x₀ ht))]
    exact ih

theorem curvatureMacroRun_gradientIndex_step {Ω : Type*} {d T Bg BH : ℕ}
    (hBg : 0 < Bg) (hBH : 0 < BH) (P : Parameters) (ε γ scaleG scaleH : ℝ)
    (F : Ω → Point d → ℝ) (tape : SampleTape ((T+1)*Bg+(T+1)*BH) Ω)
    (signs : ℕ → Bool) (x₀ : Point d) (t : ℕ) :
    (curvatureMacroRun hBg hBH P ε γ scaleG scaleH F tape signs x₀ (t+1)).2.1 ≤
      (curvatureMacroRun hBg hBH P ε γ scaleG scaleH F tape signs x₀ t).2.1+1 :=
  (curvatureFirstInspect_gradientIndex hBg hBH P ε γ scaleG scaleH F tape t _).2

theorem macroGradientTime_clock_eq {Ω : Type*} {d T Bg BH : ℕ}
    (hBg : 0 < Bg) (hBH : 0 < BH) (P : Parameters) (ε γ scaleG scaleH : ℝ)
    (F : Ω → Point d → ℝ) (h : SampleTape ((T+1)*BH) Ω) (signs : ℕ → Bool) (x₀ : Point d)
    (k : ℕ) (g : SampleTape ((T+1)*Bg) Ω)
    (ht : macroGradientTime hBg hBH P ε γ scaleG scaleH F h signs x₀ k g ≤ T) :
    (curvatureMacroRun hBg hBH P ε γ scaleG scaleH F (derivativeTapes g h) signs x₀
      (macroGradientTime hBg hBH P ε γ scaleG scaleH F h signs x₀ k g)).2.1 = k :=
  boundedClockTime_clock_eq _ k T rfl
    (curvatureMacroRun_gradientIndex_step hBg hBH P ε γ scaleG scaleH F (derivativeTapes g h) signs x₀) ht

theorem macroGradientTime_cache_entry {Ω : Type*} {d T Bg BH : ℕ}
    (hBg : 0 < Bg) (hBH : 0 < BH) (P : Parameters) (ε γ scaleG scaleH : ℝ)
    (F : Ω → Point d → ℝ) (h : SampleTape ((T+1)*BH) Ω) (signs : ℕ → Bool) (x₀ : Point d)
    (k : ℕ) (g : SampleTape ((T+1)*Bg) Ω)
    (ht : macroGradientTime hBg hBH P ε γ scaleG scaleH F h signs x₀ k g ≤ T) :
    let t := macroGradientTime hBg hBH P ε γ scaleG scaleH F h signs x₀ k g
    let s := curvatureMacroRun hBg hBH P ε γ scaleG scaleH F (derivativeTapes g h) signs x₀ t
    (curvatureMacroRun hBg hBH P ε γ scaleG scaleH F (derivativeTapes g h) signs x₀ (t+1)).2.2.1 k =
      (s.1,inspectionGradient hBg P scaleG F (derivativeTapes g h) s) := by
  dsimp only
  let t := macroGradientTime hBg hBH P ε γ scaleG scaleH F h signs x₀ k g
  let s := curvatureMacroRun hBg hBH P ε γ scaleG scaleH F (derivativeTapes g h) signs x₀ t
  have hk : s.2.1 = k := macroGradientTime_clock_eq hBg hBH P ε γ scaleG scaleH F h signs x₀ k g ht
  have hcross : k < (curvatureFirstInspect hBg hBH P ε γ scaleG scaleH F (derivativeTapes g h) t s).cache.2.1 :=
    boundedClockTime_crosses (fun t =>
      (curvatureMacroRun hBg hBH P ε γ scaleG scaleH F (derivativeTapes g h) signs x₀ t).2.1) k T ht
  rw [curvatureFirstInspect_gradientClock,hk] at hcross
  have htag : ¬curvatureTag (sourceCurvatureSelector (3*γ/4)
      (inspectionHessian hBH P scaleH F (derivativeTapes g h) t s)) = true := by
    intro hc
    simp only [if_pos hc,lt_self_iff_false] at hcross
  change (curvatureFirstInspect hBg hBH P ε γ scaleG scaleH F (derivativeTapes g h) t s).cache.2.2.1 k = _
  rw [curvatureFirstInspect_gradientCache,if_neg htag,hk,Function.update_self]

theorem macroGradientTime_before {Ω : Type*} {d T Bg BH : ℕ}
    (hBg : 0 < Bg) (hBH : 0 < BH) (P : Parameters) (ε γ scaleG scaleH : ℝ)
    (F : Ω → Point d → ℝ) (h : SampleTape ((T+1)*BH) Ω) (signs : ℕ → Bool) (x₀ : Point d)
    (j t : ℕ) (g : SampleTape ((T+1)*Bg) Ω)
    (hj : j < (curvatureMacroRun hBg hBH P ε γ scaleG scaleH F (derivativeTapes g h) signs x₀ t).2.1) :
    macroGradientTime hBg hBH P ε γ scaleG scaleH F h signs x₀ j g < t :=
  boundedClockTime_lt_of_crossed (fun t =>
    (curvatureMacroRun hBg hBH P ε γ scaleG scaleH F (derivativeTapes g h) signs x₀ t).2.1) j T rfl hj

theorem macroGradientCache_entry_before {Ω : Type*} {d T Bg BH : ℕ}
    (hBg : 0 < Bg) (hBH : 0 < BH) (P : Parameters) (ε γ scaleG scaleH : ℝ)
    (F : Ω → Point d → ℝ) (h : SampleTape ((T+1)*BH) Ω) (signs : ℕ → Bool) (x₀ : Point d)
    (j t : ℕ) (g : SampleTape ((T+1)*Bg) Ω) (ht : t ≤ T)
    (hj : j < (curvatureMacroRun hBg hBH P ε γ scaleG scaleH F (derivativeTapes g h) signs x₀ t).2.1) :
    let τ := macroGradientTime hBg hBH P ε γ scaleG scaleH F h signs x₀ j g
    let s := curvatureMacroRun hBg hBH P ε γ scaleG scaleH F (derivativeTapes g h) signs x₀ τ
    (curvatureMacroRun hBg hBH P ε γ scaleG scaleH F (derivativeTapes g h) signs x₀ t).2.2.1 j =
      (s.1,inspectionGradient hBg P scaleG F (derivativeTapes g h) s) := by
  have hτ := macroGradientTime_before hBg hBH P ε γ scaleG scaleH F h signs x₀ j t g hj
  have hτT := hτ.le.trans ht
  have hcross := boundedClockTime_crosses (fun t =>
    (curvatureMacroRun hBg hBH P ε γ scaleG scaleH F (derivativeTapes g h) signs x₀ t).2.1) j T hτT
  rw [curvatureMacroRun_gradientCache_preserves_interval hBg hBH P ε γ scaleG scaleH F
    (derivativeTapes g h) signs x₀ (Nat.succ_le_of_lt hτ) hcross]
  exact macroGradientTime_cache_entry hBg hBH P ε γ scaleG scaleH F h signs x₀ j g hτT

end
end SampleReuse
