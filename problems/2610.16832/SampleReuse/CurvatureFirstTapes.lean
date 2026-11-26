import SampleReuse.CurvatureFirstFreshness

open MeasureTheory SecondOrder
open scoped Classical

namespace SampleReuse
noncomputable section

def derivativeTapes {Ω : Type*} {G H : ℕ} (g : SampleTape G Ω) (h : SampleTape H Ω) : SampleTape (G+H) Ω :=
  Fin.addCases g h

@[simp] theorem derivativeTapes_gradient {Ω : Type*} {T Bg BH : ℕ}
    (g : SampleTape ((T+1)*Bg) Ω) (h : SampleTape ((T+1)*BH) Ω) (k : ℕ) (i : Fin Bg) :
    derivativeTapes g h (gradientReserve T Bg BH k i) = g (treeBlockHandle T Bg k i) := by
  simp [derivativeTapes,gradientReserve]

@[simp] theorem derivativeTapes_hessian {Ω : Type*} {T Bg BH : ℕ}
    (g : SampleTape ((T+1)*Bg) Ω) (h : SampleTape ((T+1)*BH) Ω) (k : ℕ) (i : Fin BH) :
    derivativeTapes g h (hessianReserve T Bg BH k i) = h (treeBlockHandle T BH k i) := by
  simp [derivativeTapes,hessianReserve]

theorem derivativeTapes_measurable {Ω : Type*} [MeasurableSpace Ω] (G H : ℕ) :
    Measurable (fun w : SampleTape G Ω × SampleTape H Ω => derivativeTapes w.1 w.2) := by
  apply measurable_pi_lambda
  intro r
  refine Fin.addCases ?_ ?_ r
  · intro i
    simpa only [derivativeTapes,Fin.addCases_left] using (measurable_pi_apply i).comp measurable_fst
  · intro i
    simpa only [derivativeTapes,Fin.addCases_right] using (measurable_pi_apply i).comp measurable_snd

def macroHessianLocation {Ω : Type*} {d T Bg BH : ℕ} (hBg : 0 < Bg) (hBH : 0 < BH)
    (P : Parameters) (ε γ scaleG scaleH : ℝ) (F : Ω → Point d → ℝ)
    (g : SampleTape ((T+1)*Bg) Ω) (signs : ℕ → Bool) (x₀ : Point d)
    (t : ℕ) (h : SampleTape ((T+1)*BH) Ω) : Point d :=
  (curvatureMacroRun hBg hBH P ε γ scaleG scaleH F (derivativeTapes g h) signs x₀ t).1

theorem macroHessianLocation_depends {Ω : Type*} {d T Bg BH : ℕ}
    (hBg : 0 < Bg) (hBH : 0 < BH) (P : Parameters) (ε γ scaleG scaleH : ℝ)
    (F : Ω → Point d → ℝ) (g : SampleTape ((T+1)*Bg) Ω) (signs : ℕ → Bool) (x₀ : Point d)
    {t : ℕ} (ht : t ≤ T) (h h' : SampleTape ((T+1)*BH) Ω)
    (heq : ∀ r ∈ treePastHandles T BH t, h r = h' r) :
    macroHessianLocation hBg hBH P ε γ scaleG scaleH F g signs x₀ t h =
      macroHessianLocation hBg hBH P ε γ scaleG scaleH F g signs x₀ t h' := by
  apply congrArg Prod.fst
  apply curvatureMacroRun_depends_hessian_past
  · intro j hj i
    simp only [derivativeTapes_hessian]
    exact heq _ (treeBlockHandle_in_past (hj.le.trans ht) hj i)
  · intro j i
    simp only [derivativeTapes_gradient]

end
end SampleReuse
