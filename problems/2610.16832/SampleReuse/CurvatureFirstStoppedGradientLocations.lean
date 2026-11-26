import SampleReuse.CurvatureFirstStoppedGradientClock
import SampleReuse.CurvatureFirstStoppedActive

open SecondOrder
open scoped Classical

namespace SampleReuse
noncomputable section

variable {Ω : Type*} {d T Bg BH M : ℕ}
  (hBg : 0 < Bg) (hBH : 0 < BH) (P : Parameters) (ε γ scaleG scaleH : ℝ)
  (f : Point d → ℝ) (F : Ω → Point d → ℝ)
  (tape : SampleTape ((T+1)*Bg+(T+1)*BH) Ω)

theorem stoppedGradientTime_eq_of_ready (x₀ : Point d) (w : Fin M → Bool) (k t : ℕ)
    (ht : t≤M)
    (ha : (curvatureStoppedRun hBg hBH P ε γ scaleG scaleH f F tape (extendFiniteSigns w) x₀ t).1=true)
    (hk : (curvatureStoppedRun hBg hBH P ε γ scaleG scaleH f F tape (extendFiniteSigns w) x₀ t).2.2.1≤k)
    (hr : t<M → stoppedGradientReady hBg hBH P ε γ scaleG scaleH f F tape x₀ k t w) :
    stoppedGradientTime hBg hBH P ε γ scaleG scaleH f F tape x₀ k w=t := by
  apply boundedSignEventTime_eq _ w ht hr
  intro j hj hrj
  have haj := curvatureStoppedRun_active_before hBg hBH P ε γ scaleG scaleH f F tape
    (extendFiniteSigns w) x₀ (Nat.succ_le_of_lt hj) ha
  have hkj := (curvatureStoppedRun_gradientClock_mono hBg hBH P ε γ scaleG scaleH f F tape
    (extendFiniteSigns w) x₀ (Nat.succ_le_of_lt hj)).trans hk
  rcases hrj with hrj | hrj
  · rw [haj] at hrj
    cases hrj
  · exact (not_lt_of_ge hkj) hrj

theorem stoppedGradientTime_eq_of_active_tag (x₀ : Point d) (w : Fin M → Bool) (t : ℕ)
    (ht : t≤M)
    (ha : (curvatureStoppedRun hBg hBH P ε γ scaleG scaleH f F tape (extendFiniteSigns w) x₀ t).1=true)
    (htag : ¬curvatureTag (sourceCurvatureSelector (3*γ/4) (inspectionHessian hBH P scaleH F tape t
      (curvatureStoppedRun hBg hBH P ε γ scaleG scaleH f F tape (extendFiniteSigns w) x₀ t).2))=true) :
    stoppedGradientTime hBg hBH P ε γ scaleG scaleH f F tape x₀
      (curvatureStoppedRun hBg hBH P ε γ scaleG scaleH f F tape (extendFiniteSigns w) x₀ t).2.2.1 w=t := by
  apply stoppedGradientTime_eq_of_ready hBg hBH P ε γ scaleG scaleH f F tape x₀ w _ t ht ha le_rfl
  intro _
  exact curvatureStoppedStep_gradientReady_of_tag hBg hBH P ε γ scaleG scaleH f F tape t _ _ ha htag

theorem stoppedGradientTime_eq_macro_of_crossed
    (g : SampleTape ((T+1)*Bg) Ω) (hh : SampleTape ((T+1)*BH) Ω)
    (x₀ : Point d) (w : Fin M → Bool) (j t : ℕ) (htM : t≤M) (htT : t≤T)
    (ha : (curvatureStoppedRun hBg hBH P ε γ scaleG scaleH f F (derivativeTapes g hh) (extendFiniteSigns w) x₀ t).1=true)
    (hj : j<(curvatureStoppedRun hBg hBH P ε γ scaleG scaleH f F (derivativeTapes g hh) (extendFiniteSigns w) x₀ t).2.2.1) :
    stoppedGradientTime hBg hBH P ε γ scaleG scaleH f F (derivativeTapes g hh) x₀ j w =
      macroGradientTime hBg hBH P ε γ scaleG scaleH F hh (extendFiniteSigns w) x₀ j g := by
  let τ := macroGradientTime hBg hBH P ε γ scaleG scaleH F hh (extendFiniteSigns w) x₀ j g
  have he := curvatureStoppedRun_eq_macro_of_active hBg hBH P ε γ scaleG scaleH f F
    (derivativeTapes g hh) (extendFiniteSigns w) x₀ t ha
  rw [he] at hj
  have hτ : τ<t := macroGradientTime_before hBg hBH P ε γ scaleG scaleH F hh (extendFiniteSigns w) x₀ j t g hj
  have haτ := curvatureStoppedRun_active_before hBg hBH P ε γ scaleG scaleH f F (derivativeTapes g hh)
    (extendFiniteSigns w) x₀ hτ.le ha
  have haτ' := curvatureStoppedRun_active_before hBg hBH P ε γ scaleG scaleH f F (derivativeTapes g hh)
    (extendFiniteSigns w) x₀ (Nat.succ_le_of_lt hτ) ha
  have heτ := curvatureStoppedRun_eq_macro_of_active hBg hBH P ε γ scaleG scaleH f F
    (derivativeTapes g hh) (extendFiniteSigns w) x₀ τ haτ
  have heτ' := curvatureStoppedRun_eq_macro_of_active hBg hBH P ε γ scaleG scaleH f F
    (derivativeTapes g hh) (extendFiniteSigns w) x₀ (τ+1) haτ'
  apply stoppedGradientTime_eq_of_ready hBg hBH P ε γ scaleG scaleH f F (derivativeTapes g hh)
    x₀ w j τ (hτ.le.trans htM) haτ
  · rw [heτ]
    exact (macroGradientTime_clock_eq hBg hBH P ε γ scaleG scaleH F hh (extendFiniteSigns w) x₀ j g (hτ.le.trans htT)).le
  · intro _
    apply Or.inr
    rw [heτ']
    exact boundedClockTime_crosses _ j T (hτ.le.trans htT)

theorem stoppedGradientCache_location_before
    (g : SampleTape ((T+1)*Bg) Ω) (hh : SampleTape ((T+1)*BH) Ω)
    (x₀ : Point d) (w : Fin M → Bool) (j t : ℕ) (htM : t≤M) (htT : t≤T)
    (ha : (curvatureStoppedRun hBg hBH P ε γ scaleG scaleH f F (derivativeTapes g hh) (extendFiniteSigns w) x₀ t).1=true)
    (hj : j<(curvatureStoppedRun hBg hBH P ε γ scaleG scaleH f F (derivativeTapes g hh) (extendFiniteSigns w) x₀ t).2.2.1) :
    ((curvatureStoppedRun hBg hBH P ε γ scaleG scaleH f F (derivativeTapes g hh) (extendFiniteSigns w) x₀ t).2.2.2.1 j).1 =
      stoppedTrajectoryPoint hBg hBH P ε γ scaleG scaleH f F (derivativeTapes g hh) x₀ w
        (stoppedGradientTime hBg hBH P ε γ scaleG scaleH f F (derivativeTapes g hh) x₀ j w) := by
  have he := curvatureStoppedRun_eq_macro_of_active hBg hBH P ε γ scaleG scaleH f F
    (derivativeTapes g hh) (extendFiniteSigns w) x₀ t ha
  have htau := stoppedGradientTime_eq_macro_of_crossed hBg hBH P ε γ scaleG scaleH f F g hh x₀ w j t htM htT ha hj
  rw [he] at hj
  have hτ := macroGradientTime_before hBg hBH P ε γ scaleG scaleH F hh (extendFiniteSigns w) x₀ j t g hj
  have haτ := curvatureStoppedRun_active_before hBg hBH P ε γ scaleG scaleH f F (derivativeTapes g hh)
    (extendFiniteSigns w) x₀ hτ.le ha
  rw [he,macroGradientCache_entry_before hBg hBH P ε γ scaleG scaleH F hh (extendFiniteSigns w) x₀ j t g htT hj,
    htau,stoppedTrajectoryPoint,curvatureStoppedRun_eq_macro_of_active hBg hBH P ε γ scaleG scaleH f F
      (derivativeTapes g hh) (extendFiniteSigns w) x₀ _ haτ]

end
end SampleReuse
