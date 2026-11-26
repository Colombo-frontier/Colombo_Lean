import SecondOrder.IdealCorrection

open scoped InnerProductSpace Classical

namespace SecondOrder
noncomputable section

inductive CurvatureReply (d : ℕ)
  | certificate
  | negative (u : Point d)

def ValidCurvatureReply {d : ℕ} (F : Point d → ℝ) (γ : ℝ) (x : Point d) :
    CurvatureReply d → Prop
  | .certificate => ∀ v, -γ*‖v‖^2 ≤ ⟪hessian F x v,v⟫_ℝ
  | .negative u => ‖u‖ = 1 ∧ ⟪hessian F x u,u⟫_ℝ ≤ -γ/2

def decideMove {d : ℕ} (τ : ℝ) (g : Point d) (r : CurvatureReply d) : IdealMove d :=
  if 4*τ < ‖g‖ then .gradient g else
    match r with
    | .certificate => .halt
    | .negative u => .curvature u

/-- The manuscript's strict gradient threshold, valid tracker output and
valid curvature reply produce precisely a valid physical move. -/
theorem decideMove_valid {d : ℕ} {F : Point d → ℝ} {τ γ : ℝ}
    (hτ : 0 ≤ τ) (x g : Point d) (r : CurvatureReply d)
    (hg : ‖g-gradient F x‖ ≤ τ/2)
    (hr : ‖g‖ ≤ 4*τ → ValidCurvatureReply F γ x r) :
    ValidIdealMove F τ γ x (decideMove τ g r) := by
  unfold decideMove
  split
  · exact ⟨by linarith, le_of_lt (by assumption)⟩
  · rename_i hn
    have hs := le_of_not_gt hn
    have hc := hr hs
    cases r with
    | certificate =>
      refine ⟨?_, hc⟩
      have ht := norm_add_le (gradient F x-g) g
      rw [sub_add_cancel, norm_sub_rev (gradient F x) g] at ht
      linarith
    | negative u => exact hc

def correctVector {E : Type*} [NormedAddCommGroup E] (ρ : ℝ) (target estimate : E) : E :=
  if ‖estimate-target‖ ≤ ρ then estimate else target

theorem correctVector_accurate {E : Type*} [NormedAddCommGroup E] {ρ : ℝ}
    (hρ : 0 ≤ ρ) (target estimate : E) : ‖correctVector ρ target estimate-target‖ ≤ ρ := by
  unfold correctVector
  split
  · assumption
  · simpa using hρ

theorem correctVector_unchanged {E : Type*} [NormedAddCommGroup E] {ρ : ℝ}
    (target estimate : E) (h : ‖estimate-target‖ ≤ ρ) : correctVector ρ target estimate = estimate :=
  if_pos h

/-- Exact curvature fallback exists in every dimension, including dimension
zero. It is an analysis-only choice, with no eigensolver complexity claimed. -/
theorem exists_validCurvatureReply {d : ℕ} (F : Point d → ℝ) {γ : ℝ}
    (hγ : 0 < γ) (x : Point d) : ∃ r, ValidCurvatureReply F γ x r := by
  by_cases hc : ∀ v, -γ*‖v‖^2 ≤ ⟪hessian F x v,v⟫_ℝ
  · exact ⟨.certificate, hc⟩
  · obtain ⟨u, hu, hn⟩ := negative_unit_of_not_certificate (hessian F x) hγ hc
    exact ⟨.negative u, hu, hn⟩

def correctCurvature {d : ℕ} (F : Point d → ℝ) {γ : ℝ}
    (hγ : 0 < γ) (x : Point d) (r : CurvatureReply d) : CurvatureReply d :=
  if ValidCurvatureReply F γ x r then r else (exists_validCurvatureReply F hγ x).choose

theorem correctCurvature_valid {d : ℕ} (F : Point d → ℝ) {γ : ℝ}
    (hγ : 0 < γ) (x : Point d) (r : CurvatureReply d) :
    ValidCurvatureReply F γ x (correctCurvature F hγ x r) := by
  unfold correctCurvature
  split
  · assumption
  · exact (exists_validCurvatureReply F hγ x).choose_spec

theorem correctCurvature_unchanged {d : ℕ} (F : Point d → ℝ) {γ : ℝ}
    (hγ : 0 < γ) (x : Point d) (r : CurvatureReply d) (hr : ValidCurvatureReply F γ x r) :
    correctCurvature F hγ x r = r := if_pos hr

end
end SecondOrder
