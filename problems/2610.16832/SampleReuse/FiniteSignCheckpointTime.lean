import SampleReuse.CurvatureFirstStoppedTrajectory

open SecondOrder
open scoped Classical

namespace SampleReuse
noncomputable section

def boundedSignEventTime {M : ℕ} (ready : ℕ → (Fin M → Bool) → Prop) (w : Fin M → Bool) : ℕ :=
  Nat.find (show ∃ t, M ≤ t ∨ ready t w from ⟨M,Or.inl le_rfl⟩)

theorem boundedSignEventTime_le {M : ℕ} (ready : ℕ → (Fin M → Bool) → Prop) (w : Fin M → Bool) :
    boundedSignEventTime ready w ≤ M := Nat.find_min' _ (Or.inl le_rfl)

theorem boundedSignEventTime_stopping {M : ℕ} (ready : ℕ → (Fin M → Bool) → Prop)
    (hready : ∀ (i : Fin M) j, j ≤ i.val → ∀ w w', SignPastEq i w w' → (ready j w ↔ ready j w')) :
    SignStoppingTime (boundedSignEventTime ready) := by
  intro i w w' he
  simp only [boundedSignEventTime,Nat.find_le_iff]
  constructor
  · rintro ⟨j,hji,hj⟩
    exact ⟨j,hji,hj.imp id ((hready i j hji w w' he).mp)⟩
  · rintro ⟨j,hji,hj⟩
    exact ⟨j,hji,hj.imp id ((hready i j hji w w' he).mpr)⟩

theorem curvatureStoppedStep_metadata {Ω : Type*} {d T Bg BH : ℕ}
    (hBg : 0 < Bg) (hBH : 0 < BH) (P : Parameters) (ε γ scaleG scaleH : ℝ)
    (f : Point d → ℝ) (F : Ω → Point d → ℝ) (tape : SampleTape ((T+1)*Bg+(T+1)*BH) Ω)
    (t : ℕ) (s : StoppedOptimizerCache d) (b b' : Bool) :
    let r := curvatureStoppedStep hBg hBH P ε γ scaleG scaleH f F tape t s b
    let r' := curvatureStoppedStep hBg hBH P ε γ scaleG scaleH f F tape t s b'
    r.1 = r'.1 ∧ r.2.2.1 = r'.2.2.1 := by
  simp only [curvatureStoppedStep]
  split_ifs
  · simp only [curvatureFirstAdvance]
    cases (curvatureFirstInspect hBg hBH P ε γ scaleG scaleH F tape t s.2).action <;> exact ⟨rfl,rfl⟩
  · exact ⟨rfl,rfl⟩
  · exact ⟨rfl,rfl⟩

def stoppedGradientReady {Ω : Type*} {d T Bg BH M : ℕ}
    (hBg : 0 < Bg) (hBH : 0 < BH) (P : Parameters) (ε γ scaleG scaleH : ℝ)
    (f : Point d → ℝ) (F : Ω → Point d → ℝ) (tape : SampleTape ((T+1)*Bg+(T+1)*BH) Ω)
    (x₀ : Point d) (k t : ℕ) (w : Fin M → Bool) : Prop :=
  let s := curvatureStoppedRun hBg hBH P ε γ scaleG scaleH f F tape (extendFiniteSigns w) x₀ (t+1)
  s.1 = false ∨ k < s.2.2.1

def stoppedGradientTime {Ω : Type*} {d T Bg BH M : ℕ}
    (hBg : 0 < Bg) (hBH : 0 < BH) (P : Parameters) (ε γ scaleG scaleH : ℝ)
    (f : Point d → ℝ) (F : Ω → Point d → ℝ) (tape : SampleTape ((T+1)*Bg+(T+1)*BH) Ω)
    (x₀ : Point d) (k : ℕ) : (Fin M → Bool) → ℕ :=
  boundedSignEventTime (stoppedGradientReady hBg hBH P ε γ scaleG scaleH f F tape x₀ k)

theorem stoppedGradientTime_stopping {Ω : Type*} {d T Bg BH M : ℕ}
    (hBg : 0 < Bg) (hBH : 0 < BH) (P : Parameters) (ε γ scaleG scaleH : ℝ)
    (f : Point d → ℝ) (F : Ω → Point d → ℝ) (tape : SampleTape ((T+1)*Bg+(T+1)*BH) Ω)
    (x₀ : Point d) (k : ℕ) :
    SignStoppingTime (stoppedGradientTime (M := M) hBg hBH P ε γ scaleG scaleH f F tape x₀ k) := by
  apply boundedSignEventTime_stopping
  intro i j hji w w' he
  have hs := curvatureStoppedRun_depends_sign_past hBg hBH P ε γ scaleG scaleH f F tape
    (extendFiniteSigns w) (extendFiniteSigns w') x₀ j
    (fun l hl => extendFiniteSigns_past i w w' he l (hl.trans_le hji))
  unfold stoppedGradientReady
  simp only [curvatureStoppedRun,hs]
  have hm := curvatureStoppedStep_metadata hBg hBH P ε γ scaleG scaleH f F tape j
    (curvatureStoppedRun hBg hBH P ε γ scaleG scaleH f F tape (extendFiniteSigns w') x₀ j)
    (extendFiniteSigns w j) (extendFiniteSigns w' j)
  rw [hm.1,hm.2]

theorem stoppedGradientTime_mono {Ω : Type*} {d T Bg BH M : ℕ}
    (hBg : 0 < Bg) (hBH : 0 < BH) (P : Parameters) (ε γ scaleG scaleH : ℝ)
    (f : Point d → ℝ) (F : Ω → Point d → ℝ) (tape : SampleTape ((T+1)*Bg+(T+1)*BH) Ω)
    (x₀ : Point d) (w : Fin M → Bool) :
    Monotone (fun k => stoppedGradientTime hBg hBH P ε γ scaleG scaleH f F tape x₀ k w) := by
  intro k l hkl
  apply Nat.find_min'
  have hh := Nat.find_spec (show ∃ t, M ≤ t ∨ stoppedGradientReady hBg hBH P ε γ scaleG scaleH f F tape x₀ l t w
    from ⟨M,Or.inl le_rfl⟩)
  rcases hh with hM | hready
  · exact Or.inl hM
  · exact Or.inr (hready.imp id (fun hh => hkl.trans_lt hh))

end
end SampleReuse
