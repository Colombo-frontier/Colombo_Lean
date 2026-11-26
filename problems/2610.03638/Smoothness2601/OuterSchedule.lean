import Smoothness2601.HypergradientGeometry

/-! The manuscript's deterministic normalized outer length, step and restart
radius, with explicit sample-independent bounds. -/
noncomputable section
namespace Smoothness2601.OuterSchedule
open HypergradientGeometry

def stepsize (b : Budgets) (ε : ℝ) : ℝ := ε/(2*outerSmoothness b)
def iterations (b : Budgets) (ε : ℝ) : ℕ := ⌈4*b.Δ/(stepsize b ε*ε)⌉₊
def travel (b : Budgets) (ε : ℝ) : ℝ := (iterations b ε:ℝ)*stepsize b ε
def radius (b : Budgets) (ε : ℝ) : ℝ := b.R₀+(b.L₁/b.μ)*travel b ε
def countConstant (b : Budgets) : ℝ := 1+8*outerSmoothness b*b.Δ
def radiusConstant (b : Budgets) : ℝ := b.R₀+(b.L₁/b.μ)*(1/(2*outerSmoothness b)+4*b.Δ)

theorem stepsize_pos (b : Budgets) {ε : ℝ} (hε : 0 < ε) : 0 < stepsize b ε :=
  div_pos hε (mul_pos (by norm_num) (outerSmoothness_pos b))

theorem iterations_pos (b : Budgets) {ε : ℝ} (hε : 0 < ε) : 0 < iterations b ε := by
  have ht : 0 < 4*b.Δ/(stepsize b ε*ε) :=
    div_pos (mul_pos (by norm_num) b.Δ_pos) (mul_pos (stepsize_pos b hε) hε)
  have hh := ht.trans_le (Nat.le_ceil _)
  exact_mod_cast hh

theorem radius_nonneg (b : Budgets) {ε : ℝ} (hε : 0 < ε) : 0 ≤ radius b ε := by
  have hμ := b.μ_pos
  have hL := b.L₁_pos
  have hR := b.R₀_nonneg
  have hη := (stepsize_pos b hε).le
  unfold radius travel
  positivity

theorem countConstant_pos (b : Budgets) : 0 < countConstant b := by
  have hL := outerSmoothness_pos b
  have hΔ := b.Δ_pos
  unfold countConstant
  positivity

theorem radiusConstant_pos (b : Budgets) : 0 < radiusConstant b := by
  have hL := outerSmoothness_pos b
  have hL1 := b.L₁_pos
  have hμ := b.μ_pos
  have hΔ := b.Δ_pos
  have hR := b.R₀_nonneg
  unfold radiusConstant
  positivity

theorem iterations_upper (b : Budgets) {ε : ℝ} (hε : 0 < ε) :
    (iterations b ε:ℝ) ≤ 1+8*outerSmoothness b*b.Δ/ε ^ 2 := by
  have hη := stepsize_pos b hε
  have hn : 0 ≤ 4*b.Δ/(stepsize b ε*ε) := by have := b.Δ_pos; positivity
  have hh := (Nat.ceil_lt_add_one hn).le
  have he : 4*b.Δ/(stepsize b ε*ε) = 8*outerSmoothness b*b.Δ/ε ^ 2 := by
    unfold stepsize
    field_simp
    ring
  change (iterations b ε:ℝ) ≤ _ at hh
  rw [he] at hh
  linarith

theorem iterations_power_bound (b : Budgets) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    (iterations b ε:ℝ) ≤ countConstant b*(1/ε ^ 2) := by
  have hh := iterations_upper b hε
  have hw : 1 ≤ 1/ε ^ 2 := (le_div_iff₀ (sq_pos_of_pos hε)).mpr (by nlinarith)
  unfold countConstant
  simp only [div_eq_mul_inv] at hh hw ⊢
  nlinarith

theorem travel_bound (b : Budgets) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    travel b ε ≤ (1/(2*outerSmoothness b)+4*b.Δ)/ε := by
  have hη := stepsize_pos b hε
  have hL := outerSmoothness_pos b
  have hh := mul_le_mul_of_nonneg_right (iterations_upper b hε) hη.le
  have he : (1+8*outerSmoothness b*b.Δ/ε ^ 2)*stepsize b ε =
      stepsize b ε+4*b.Δ/ε := by
    unfold stepsize
    field_simp
    ring
  change travel b ε ≤ _ at hh
  rw [he] at hh
  have hs : stepsize b ε ≤ (1/(2*outerSmoothness b))/ε := by
    unfold stepsize
    apply (le_div_iff₀ hε).mpr
    have hε2 : ε ^ 2 ≤ 1 := by nlinarith
    calc
      _ = ε ^ 2/(2*outerSmoothness b) := by ring
      _ ≤ _ := div_le_div_of_nonneg_right hε2 (by positivity)
  exact hh.trans ((add_le_add_right hs _).trans_eq (by ring))

theorem radius_bound (b : Budgets) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    radius b ε ≤ radiusConstant b/ε := by
  have hκ : 0 ≤ b.L₁/b.μ := div_nonneg b.L₁_pos.le b.μ_pos.le
  have hR : b.R₀ ≤ b.R₀/ε := (le_div_iff₀ hε).mpr
    (by nlinarith [b.R₀_nonneg])
  have ht := mul_le_mul_of_nonneg_left (travel_bound b hε hε1) hκ
  exact (add_le_add hR ht).trans_eq (by unfold radiusConstant; ring)

theorem stationarity_budget (b : Budgets) {ε : ℝ} (hε : 0 < ε) :
    b.Δ/((iterations b ε:ℝ)*stepsize b ε)+2*(ε/8)+outerSmoothness b*stepsize b ε/2 ≤ 3*ε/4 := by
  have hη := stepsize_pos b hε
  have hK : 0 < (iterations b ε:ℝ) := Nat.cast_pos.mpr (iterations_pos b hε)
  have hl : 4*b.Δ/(stepsize b ε*ε) ≤ (iterations b ε:ℝ) := Nat.le_ceil _
  have hh := (div_le_iff₀ (mul_pos hη hε)).mp hl
  have hg : b.Δ/((iterations b ε:ℝ)*stepsize b ε) ≤ ε/4 :=
    (div_le_iff₀ (mul_pos hK hη)).mpr (by nlinarith)
  have he : outerSmoothness b*stepsize b ε/2 = ε/4 := by
    have hL := outerSmoothness_pos b
    unfold stepsize
    field_simp
    ring
  rw [he]
  linarith

end Smoothness2601.OuterSchedule
