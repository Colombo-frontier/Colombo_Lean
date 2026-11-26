import SecondOrder.IdealMixture

open MeasureTheory
open scoped InnerProductSpace Classical

namespace SecondOrder
noncomputable section

/-- Failure of the Rayleigh certificate yields a normalized direction. This
existence result is used only by the ideal correction, not as an oracle routine. -/
theorem negative_unit_of_not_certificate {d : ℕ} (H : Point d →L[ℝ] Point d)
    {γ : ℝ} (hγ : 0 < γ) (hc : ¬ ∀ v, -γ*‖v‖^2 ≤ ⟪H v,v⟫_ℝ) :
    ∃ u, ‖u‖ = 1 ∧ ⟪H u,u⟫_ℝ ≤ -γ/2 := by
  push_neg at hc
  obtain ⟨v, hv⟩ := hc
  have hv0 : v ≠ 0 := by intro hh; subst v; simp at hv
  have hn : 0 < ‖v‖ := norm_pos_iff.mpr hv0
  refine ⟨‖v‖⁻¹ • v, ?_, ?_⟩
  · simp [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hn), hn.ne']
  · have he : ⟪H (‖v‖⁻¹ • v),‖v‖⁻¹ • v⟫_ℝ = ‖v‖⁻¹^2*⟪H v,v⟫_ℝ := by
      simp only [map_smul, inner_smul_left, inner_smul_right, conj_trivial]
      ring
    rw [he]
    have hm := mul_lt_mul_of_pos_left hv (sq_pos_of_pos (inv_pos.mpr hn))
    have heq : ‖v‖⁻¹^2*(-γ*‖v‖^2) = -γ := by field_simp
    rw [heq] at hm
    linarith

theorem exists_validIdealMove {d : ℕ} (F : Point d → ℝ) {τ γ : ℝ}
    (hτ : 0 ≤ τ) (hγ : 0 < γ) (x : Point d) : ∃ a, ValidIdealMove F τ γ x a := by
  by_cases hg : 4*τ ≤ ‖gradient F x‖
  · exact ⟨.gradient (gradient F x), by simp [ValidIdealMove, hτ, hg]⟩
  · by_cases hc : ∀ v, -γ*‖v‖^2 ≤ ⟪hessian F x v,v⟫_ℝ
    · exact ⟨.halt, ⟨by linarith, hc⟩⟩
    · obtain ⟨u, hu, hd⟩ := negative_unit_of_not_certificate (hessian F x) hγ hc
      exact ⟨.curvature u, hu, hd⟩

def exactIdealMove {d : ℕ} (F : Point d → ℝ) {τ γ : ℝ}
    (hτ : 0 ≤ τ) (hγ : 0 < γ) (x : Point d) : IdealMove d :=
  (exists_validIdealMove F hτ hγ x).choose

theorem exactIdealMove_valid {d : ℕ} (F : Point d → ℝ) {τ γ : ℝ}
    (hτ : 0 ≤ τ) (hγ : 0 < γ) (x : Point d) :
    ValidIdealMove F τ γ x (exactIdealMove F hτ hγ x) :=
  (exists_validIdealMove F hτ hγ x).choose_spec

/-- Analysis-only correction of an invalid proposed physical move. The exact
fallback has no claimed computational cost or measurability here. -/
def correctedPolicy {d : ℕ} (F : Point d → ℝ) {τ γ : ℝ}
    (hτ : 0 ≤ τ) (hγ : 0 < γ) (policy : IdealPolicy d) : IdealPolicy d :=
  fun t w z => if ValidIdealMove F τ γ z.point (policy t w z)
    then policy t w z else exactIdealMove F hτ hγ z.point

theorem correctedPolicy_valid {d : ℕ} (F : Point d → ℝ) {τ γ : ℝ}
    (hτ : 0 ≤ τ) (hγ : 0 < γ) (L s : ℝ) (policy : IdealPolicy d) :
    ValidIdealPolicy F L s τ γ (correctedPolicy F hτ hγ policy) := by
  intro t w hr
  unfold correctedPolicy
  split
  · assumption
  · exact exactIdealMove_valid F hτ hγ _

/-- Every proposed move on this actual history has been valid so far.
The move selected by the new sign is checked before that sign is used. -/
def validHistory {d : ℕ} (F : Point d → ℝ) (L s τ γ : ℝ) (policy : IdealPolicy d) :
    (t : ℕ) → (Fin t → Bool) → Prop
  | 0, _ => True
  | t+1, w => validHistory F L s τ γ policy t (Fin.init w) ∧
      ((idealRun L s policy t (Fin.init w)).running = true →
        ValidIdealMove F τ γ (idealRun L s policy t (Fin.init w)).point
          (policy t (Fin.init w) (idealRun L s policy t (Fin.init w))))

theorem idealRun_corrected_agrees {d : ℕ} (F : Point d → ℝ) {τ γ : ℝ}
    (hτ : 0 ≤ τ) (hγ : 0 < γ) (L s : ℝ) (policy : IdealPolicy d)
    (t : ℕ) (w : Fin t → Bool) (hv : validHistory F L s τ γ policy t w) :
    idealRun L s (correctedPolicy F hτ hγ policy) t w = idealRun L s policy t w := by
  induction t with
  | zero => rfl
  | succ t ih =>
    have hh := ih (Fin.init w) hv.1
    simp only [idealRun, hh]
    cases hr : (idealRun L s policy t (Fin.init w)).running
    · simp [idealStep, hr]
    · have ha := hv.2 hr
      simp only [correctedPolicy, if_pos ha]

/-- A stopped output on a history without invalid moves is a genuine SOSP. -/
theorem idealRun_good_stopped_sosp {d : ℕ} (F : Point d → ℝ) {τ γ : ℝ}
    (hτ : 0 ≤ τ) (hγ : 0 < γ) (L s : ℝ) (policy : IdealPolicy d)
    (t : ℕ) (w : Fin t → Bool) (hv : validHistory F L s τ γ policy t w)
    (hs : (idealRun L s policy t w).running = false) :
    IsSOSP F (10*τ) γ (idealRun L s policy t w).point := by
  have he := idealRun_corrected_agrees F hτ hγ L s policy t w hv
  have hc := idealRun_stopped_sosp (correctedPolicy_valid F hτ hγ L s policy) t w
  rw [he] at hc
  exact hc hs

end
end SecondOrder
