import SampleReuse.CurvatureFirstStoppedQueryCounts
import SampleReuse.CurvatureFirstGradientCache

open SecondOrder
open scoped Classical

namespace SampleReuse
noncomputable section

theorem curvatureStoppedRun_gradientClock_mono {Ω : Type*} {d T Bg BH : ℕ}
    (hBg : 0 < Bg) (hBH : 0 < BH) (P : Parameters) (ε γ scaleG scaleH : ℝ)
    (f : Point d → ℝ) (F : Ω → Point d → ℝ) (tape : SampleTape ((T+1)*Bg+(T+1)*BH) Ω)
    (signs : ℕ → Bool) (x₀ : Point d) :
    Monotone (fun t => (curvatureStoppedRun hBg hBH P ε γ scaleG scaleH f F tape signs x₀ t).2.2.1) := by
  apply monotone_nat_of_le_succ
  intro t
  rw [curvatureStoppedRun,curvatureStoppedStep_gradientClock]
  exact Nat.le_add_right _ _

theorem curvatureStoppedRun_gradientClock_le_time {Ω : Type*} {d T Bg BH : ℕ}
    (hBg : 0 < Bg) (hBH : 0 < BH) (P : Parameters) (ε γ scaleG scaleH : ℝ)
    (f : Point d → ℝ) (F : Ω → Point d → ℝ) (tape : SampleTape ((T+1)*Bg+(T+1)*BH) Ω)
    (signs : ℕ → Bool) (x₀ : Point d) (t : ℕ) :
    (curvatureStoppedRun hBg hBH P ε γ scaleG scaleH f F tape signs x₀ t).2.2.1 ≤ t := by
  induction t with
  | zero => exact le_rfl
  | succ t ih =>
    rw [curvatureStoppedRun,curvatureStoppedStep_gradientClock]
    have ha : actionGradientCount (stoppedInspectionAction hBg hBH P ε γ scaleG scaleH f F tape t
      (curvatureStoppedRun hBg hBH P ε γ scaleG scaleH f F tape signs x₀ t)) ≤ 1 := by
      cases stoppedInspectionAction hBg hBH P ε γ scaleG scaleH f F tape t
        (curvatureStoppedRun hBg hBH P ε γ scaleG scaleH f F tape signs x₀ t) <;> simp only [actionGradientCount,Nat.zero_le,le_refl]
    omega

theorem curvatureStoppedStep_gradientReady_of_tag {Ω : Type*} {d T Bg BH : ℕ}
    (hBg : 0 < Bg) (hBH : 0 < BH) (P : Parameters) (ε γ scaleG scaleH : ℝ)
    (f : Point d → ℝ) (F : Ω → Point d → ℝ) (tape : SampleTape ((T+1)*Bg+(T+1)*BH) Ω)
    (t : ℕ) (s : StoppedOptimizerCache d) (b : Bool) (hs : s.1=true)
    (htag : ¬curvatureTag (sourceCurvatureSelector (3*γ/4) (inspectionHessian hBH P scaleH F tape t s.2))=true) :
    let s' := curvatureStoppedStep hBg hBH P ε γ scaleG scaleH f F tape t s b
    s'.1=false ∨ s.2.2.1<s'.2.2.1 := by
  simp only [curvatureStoppedStep,if_pos hs]
  split_ifs with hv
  · simp only [curvatureFirstAdvance,curvatureFirstInspect,inspectionHessian] at htag ⊢
    simp only [if_neg htag]
    split_ifs
    · exact Or.inl rfl
    · exact Or.inr (Nat.lt_succ_self _)
  · exact Or.inl rfl

theorem boundedSignEventTime_eq {M : ℕ} (ready : ℕ → (Fin M → Bool) → Prop)
    (w : Fin M → Bool) {t : ℕ} (ht : t≤M) (hr : t<M → ready t w)
    (hp : ∀ j<t, ¬ready j w) : boundedSignEventTime ready w=t := by
  apply Nat.le_antisymm
  · apply Nat.find_min'
    by_cases hM : M≤t
    · exact Or.inl hM
    · exact Or.inr (hr (by omega))
  · apply Nat.le_of_not_lt
    intro hlt
    unfold boundedSignEventTime at hlt
    have hh := Nat.find_spec (show ∃ j, M≤j ∨ ready j w from ⟨M,Or.inl le_rfl⟩)
    rcases hh with hM | hr'
    · omega
    · exact hp _ hlt hr'

end
end SampleReuse
