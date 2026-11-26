import SampleReuse.CurvatureFirstJointAccuracy
import SampleReuse.CurvatureFirstOutputMeasurable
import SampleReuse.CurvatureFirstTermination
import SampleReuse.CurvatureFirstStoppedTrajectory

open MeasureTheory SecondOrder
open scoped Classical

namespace SampleReuse
noncomputable section

theorem macroAccurate_finiteValid {Ω : Type*} {d T Bg BH : ℕ}
    (hBg : 0 < Bg) (hBH : 0 < BH) (P : Parameters) (ε γ scaleG scaleH : ℝ)
    (f : Point d → ℝ) (F : Ω → Point d → ℝ) (x₀ : Point d)
    (tape : SampleTape ((T+1)*Bg+(T+1)*BH) Ω) (signs : ℕ → Bool)
    (hgood : MacroAccurate hBg hBH P ε γ scaleG scaleH (ε/4) (γ/4) f F x₀ tape signs)
    (m t : ℕ) (horizon : m+t ≤ T+1) (bits : Fin m → Bool)
    (heq : ∀ i : Fin m, signs (t+i.val) = bits i) :
    curvatureFirstFiniteValid hBg hBH P ε γ scaleG scaleH f F tape m t
      (curvatureMacroRun hBg hBH P ε γ scaleG scaleH F tape signs x₀ t) bits := by
  induction m generalizing t with
  | zero => trivial
  | succ m ih =>
    let s := curvatureMacroRun hBg hBH P ε γ scaleG scaleH F tape signs x₀ t
    let r := curvatureFirstInspect hBg hBH P ε γ scaleG scaleH F tape t s
    have hp : r.cache.1 = s.1 := curvatureFirstInspect_point hBg hBH P ε γ scaleG scaleH F tape t s
    have ht : t ≤ T := by omega
    have hv : ValidInspection f ε γ s.1 r.action :=
      curvatureFirstInspect_valid hBg hBH P ε γ scaleG scaleH f F tape t s (hgood.2 t ht) (hgood.1 t ht)
    have hh : signs t = bits 0 := by simpa only [Fin.val_zero,Nat.add_zero] using heq 0
    have htail : ∀ i : Fin m, signs (t+1+i.val) = Fin.tail bits i := by
      intro i
      simpa only [Fin.val_succ,Fin.tail,Nat.add_assoc,Nat.add_comm 1] using heq i.succ
    change ValidInspection f ε γ s.1 r.action ∧ _
    refine ⟨hv,?_⟩
    cases ha : r.action with
    | success => trivial
    | gradient g =>
      have hn : curvatureMacroRun hBg hBH P ε γ scaleG scaleH F tape signs x₀ (t+1) =
          (gradientMove P ε s.1 g,r.cache.2) := by
        change curvatureMacroAdvance P ε γ (signs t) r = _
        simp only [curvatureMacroAdvance,ha,inspectionNextPoint,hp]
      have hi := ih (t+1) (by omega) (Fin.tail bits) htail
      rw [hn] at hi
      exact hi
    | curvature v =>
      have hn : curvatureMacroRun hBg hBH P ε γ scaleG scaleH F tape signs x₀ (t+1) =
          (curvatureNext (γ/P.hessianLip) s.1 v (bits 0),r.cache.2) := by
        change curvatureMacroAdvance P ε γ (signs t) r = _
        simp only [curvatureMacroAdvance,ha,inspectionNextPoint,hp,hh]
      have hi := ih (t+1) (by omega) (Fin.tail bits) htail
      rw [hn] at hi
      exact hi

theorem macroAccurate_initial_finiteValid {Ω : Type*} {d T Bg BH M : ℕ}
    (hBg : 0 < Bg) (hBH : 0 < BH) (P : Parameters) (ε γ scaleG scaleH : ℝ)
    (f : Point d → ℝ) (F : Ω → Point d → ℝ) (x₀ : Point d)
    (tape : SampleTape ((T+1)*Bg+(T+1)*BH) Ω) (bits : Fin M → Bool) (horizon : M ≤ T+1)
    (hgood : MacroAccurate hBg hBH P ε γ scaleG scaleH (ε/4) (γ/4) f F x₀ tape (extendFiniteSigns bits)) :
    curvatureFirstFiniteValid hBg hBH P ε γ scaleG scaleH f F tape M 0 (optimizerInitial x₀) bits := by
  apply macroAccurate_finiteValid hBg hBH P ε γ scaleG scaleH f F x₀ tape
    (extendFiniteSigns bits) hgood M 0 (by omega) bits
  intro i
  simp only [Nat.zero_add,extendFiniteSigns,dif_pos i.isLt]

theorem extendFiniteSigns_measurable (M : ℕ) : Measurable (@extendFiniteSigns M) :=
  measurable_of_countable _

theorem curvatureFirstFiniteExecute_measurable {Ω A : Type}
    [MeasurableSpace Ω] [MeasurableSpace A] {d T Bg BH M : ℕ}
    (hBg : 0 < Bg) (hBH : 0 < BH) (P : Parameters) (ε γ scaleG scaleH : ℝ)
    (F : Ω → Point d → ℝ)
    (hFg : Measurable (fun w : Ω × Point d => gradient (F w.1) w.2))
    (hFH : Measurable (fun w : Ω × Point d => hessian (F w.1) w.2))
    (tape : A → SampleTape ((T+1)*Bg+(T+1)*BH) Ω) (htape : Measurable tape)
    (bits : A → Fin M → Bool) (hbits : Measurable bits) (x₀ : Point d) :
    Measurable (fun a => curvatureFirstFiniteExecute hBg hBH P ε γ scaleG scaleH F
      (tape a) M 0 (optimizerInitial x₀) (bits a)) := by
  have he (a : A) := curvatureFirstFiniteExecute_eq hBg hBH P ε γ scaleG scaleH F (tape a)
    (extendFiniteSigns (bits a)) M 0 (optimizerInitial x₀) (bits a)
    (fun i => by simp only [Nat.zero_add,extendFiniteSigns,dif_pos i.isLt])
  simp_rw [he]
  exact curvatureFirstExecute_measurable hBg hBH P ε γ scaleG scaleH F hFg hFH
    tape htape _ ((extendFiniteSigns_measurable M).comp hbits) M 0 _ measurable_const

/-- On the simultaneous estimator event, any returned point is a true SOSP. -/
theorem macroAccurate_output_sosp {Ω : Type*} {d T Bg BH M : ℕ}
    (hBg : 0 < Bg) (hBH : 0 < BH) (P : Parameters) (ε γ scaleG scaleH : ℝ)
    (f : Point d → ℝ) (F : Ω → Point d → ℝ) (x₀ : Point d)
    (tape : SampleTape ((T+1)*Bg+(T+1)*BH) Ω) (bits : Fin M → Bool) (horizon : M ≤ T+1)
    (hgood : MacroAccurate hBg hBH P ε γ scaleG scaleH (ε/4) (γ/4) f F x₀ tape (extendFiniteSigns bits))
    {x : Point d} (hout : curvatureFirstFiniteExecute hBg hBH P ε γ scaleG scaleH F tape M 0
      (optimizerInitial x₀) bits = some x) : IsSOSP f ε γ x :=
  curvatureFirstFiniteExecute_sosp hBg hBH P ε γ scaleG scaleH f F tape M 0 (optimizerInitial x₀) bits
    (macroAccurate_initial_finiteValid hBg hBH P ε γ scaleG scaleH f F x₀ tape bits horizon hgood) hout

/-- The actual joint probability of good-estimate execution exhausting its
iteration horizon is bounded by the proved finite-sign descent telescope. -/
theorem Admissible.curvatureFirst_joint_exhaustion {Ω : Type} [MeasurableSpace Ω]
    {d T Bg BH M : ℕ} {μ : Measure Ω} [IsProbabilityMeasure μ] {P : Parameters}
    {f : Point d → ℝ} {F : Ω → Point d → ℝ} {x₀ : Point d}
    (had : Admissible μ P f F x₀) (hBg : 0 < Bg) (hBH : 0 < BH)
    {ε γ : ℝ} (hε : 0 < ε) (hγ : 0 < γ) (scaleG scaleH : ℝ)
    (hM : 0 < M) (horizon : M ≤ T+1) :
    (((sampleTapeLaw ((T+1)*Bg) μ).prod (sampleTapeLaw ((T+1)*BH) μ)).prod
      (PMF.uniformOfFintype (Fin M → Bool)).toMeasure).real {w |
        MacroAccurate hBg hBH P ε γ scaleG scaleH (ε/4) (γ/4) f F x₀
          (derivativeTapes w.1.1 w.1.2) (extendFiniteSigns w.2) ∧
        curvatureFirstFiniteExecute hBg hBH P ε γ scaleG scaleH F
          (derivativeTapes w.1.1 w.1.2) M 0 (optimizerInitial x₀) w.2 = none} ≤
      P.gap/(optimizerMinDecrease P ε γ*M) := by
  let A := (SampleTape ((T+1)*Bg) Ω × SampleTape ((T+1)*BH) Ω) × (Fin M → Bool)
  have hg : MeasurableSet {w : A | MacroAccurate hBg hBH P ε γ scaleG scaleH (ε/4) (γ/4)
      f F x₀ (derivativeTapes w.1.1 w.1.2) (extendFiniteSigns w.2)} :=
    had.macroAccurate_measurableSet hBg hBH ε γ scaleG scaleH (ε/4) (γ/4)
      _ ((derivativeTapes_measurable _ _).comp measurable_fst)
      _ ((extendFiniteSigns_measurable M).comp measurable_snd)
  have ho : Measurable (fun w : A => curvatureFirstFiniteExecute hBg hBH P ε γ scaleG scaleH F
      (derivativeTapes w.1.1 w.1.2) M 0 (optimizerInitial x₀) w.2) :=
    curvatureFirstFiniteExecute_measurable hBg hBH P ε γ scaleG scaleH F
      had.gradient_measurable had.hessian_measurable _
      ((derivativeTapes_measurable _ _).comp measurable_fst) _ measurable_snd x₀
  apply product_event_real_bound_of_sections _ _ _ (hg.inter (ho (optimizerOutput_none_measurableSet d)))
    (div_nonneg P.gap_pos.le (mul_nonneg (optimizerMinDecrease_pos P hε hγ).le (Nat.cast_nonneg M)))
  intro tapes
  apply (measureReal_mono (μ := (PMF.uniformOfFintype (Fin M → Bool)).toMeasure) ?_).trans
    (had.curvatureFirst_valid_exhaustion hBg hBH hε hγ scaleG scaleH (derivativeTapes tapes.1 tapes.2) hM)
  intro bits hb
  exact ⟨macroAccurate_initial_finiteValid hBg hBH P ε γ scaleG scaleH f F x₀ _ bits horizon hb.1,hb.2⟩

end
end SampleReuse
