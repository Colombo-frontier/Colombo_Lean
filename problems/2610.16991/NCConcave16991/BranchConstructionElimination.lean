import NCConcave16991.BranchConstructionOperator

/-! # Actual unconstrained dual elimination for the branching path -/

namespace NCConcave16991.BranchConstruction

noncomputable section

open Set
open scoped InnerProductSpace

variable {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {N : ℕ} (V : Fin (N + 1) → Type*)
  [∀ j, NormedAddCommGroup (V j)] [∀ j, InnerProductSpace ℝ (V j)]
  [∀ j, CompleteSpace (V j)] [∀ j, FiniteDimensional ℝ (V j)]
  (B : ∀ t : Fin N, BranchGeometry.BranchFamily (ι := ι) (V t.castSucc) (V t.succ))

def saddle (μ β r : ℝ) (h w : Layers V) : ℝ :=
  r * ⟪h, w⟫_ℝ - β / 2 * ⟪w, massOperator V B μ w⟫_ℝ

def optimizer (μ : ℝ) (hμ : 0 < μ) (β r : ℝ) (h : Layers V) : Layers V :=
  (r / β) • inverse V B μ hμ h

theorem saddle_complete_square (μ : ℝ) (hμ : 0 < μ) (β : ℝ) (hβ : 0 < β) (r : ℝ)
    (h w : Layers V) :
    saddle V B μ β r h w = r ^ 2 / (2 * β) * ⟪h, inverse V B μ hμ h⟫_ℝ -
      β / 2 * ⟪w - optimizer V B μ hμ β r h,
        massOperator V B μ (w - optimizer V B μ hμ β r h)⟫_ℝ := by
  have hc : ⟪inverse V B μ hμ h, massOperator V B μ w⟫_ℝ = ⟪h, w⟫_ℝ := by
    rw [massOperator_symmetric, mass_inverse]
  simp only [saddle, optimizer, map_sub, map_smul, inner_sub_left, inner_sub_right,
    real_inner_smul_left, real_inner_smul_right, mass_inverse, hc]
  simp only [real_inner_comm]
  field_simp [hβ.ne']
  <;> ring

theorem massOperator_energy_nonneg (μ : ℝ) (hμ : 0 < μ) (w : Layers V) :
    0 ≤ ⟪w, massOperator V B μ w⟫_ℝ :=
  (mul_nonneg hμ.le (sq_nonneg _)).trans (massOperator_coercive V B μ w)

theorem saddle_le_maximum (μ : ℝ) (hμ : 0 < μ) (β : ℝ) (hβ : 0 < β) (r : ℝ)
    (h w : Layers V) :
    saddle V B μ β r h w ≤ r ^ 2 / (2 * β) * ⟪h, inverse V B μ hμ h⟫_ℝ := by
  rw [saddle_complete_square V B μ hμ β hβ r h w]
  exact sub_le_self _ (mul_nonneg (div_nonneg hβ.le (by norm_num)) (massOperator_energy_nonneg V B μ hμ _))

theorem saddle_at_optimizer (μ : ℝ) (hμ : 0 < μ) (β : ℝ) (hβ : 0 < β) (r : ℝ) (h : Layers V) :
    saddle V B μ β r h (optimizer V B μ hμ β r h) =
      r ^ 2 / (2 * β) * ⟪h, inverse V B μ hμ h⟫_ℝ := by
  rw [saddle_complete_square V B μ hμ β hβ r]
  simp

theorem saddle_isGreatest (μ : ℝ) (hμ : 0 < μ) (β : ℝ) (hβ : 0 < β) (r : ℝ) (h : Layers V) :
    IsGreatest (range (saddle V B μ β r h)) (r ^ 2 / (2 * β) * ⟪h, inverse V B μ hμ h⟫_ℝ) := by
  refine ⟨⟨optimizer V B μ hμ β r h, saddle_at_optimizer V B μ hμ β hβ r h⟩, ?_⟩
  rintro _ ⟨w, rfl⟩
  exact saddle_le_maximum V B μ hμ β hβ r h w

theorem optimizer_unique (μ : ℝ) (hμ : 0 < μ) (β : ℝ) (hβ : 0 < β) (r : ℝ)
    (h w : Layers V) (hw : saddle V B μ β r h w =
      r ^ 2 / (2 * β) * ⟪h, inverse V B μ hμ h⟫_ℝ) : w = optimizer V B μ hμ β r h := by
  rw [saddle_complete_square V B μ hμ β hβ r] at hw
  have hE : ⟪w - optimizer V B μ hμ β r h,
      massOperator V B μ (w - optimizer V B μ hμ β r h)⟫_ℝ = 0 := by nlinarith
  have hh := massOperator_coercive V B μ (w - optimizer V B μ hμ β r h)
  rw [hE] at hh
  have hs : ‖w - optimizer V B μ hμ β r h‖ ^ 2 ≤ 0 :=
    (mul_le_mul_iff_right₀ hμ).mp (by simpa using hh)
  have hn : ‖w - optimizer V B μ hμ β r h‖ = 0 := by nlinarith [norm_nonneg (w - optimizer V B μ hμ β r h)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hn)

end

end NCConcave16991.BranchConstruction
