import Bilevel.SmallGapRawTheorem

/-! Fixed numerical rescaling into the original prescribed primitive budgets.
The explicit lower threshold on chi makes precise the source's asymptotic
positive-variation normalized range. No gap restriction is introduced. -/

noncomputable section
open scoped RealInnerProductSpace

namespace Bilevel.Model.Primitive

variable {X Y : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
  {μ Lf Lg Cf ρ : ℝ}

/-- Enlarge regularity budgets and weaken the lower curvature without changing
any function, gradient, or Hessian block. -/
def rebudget (P : Model.Primitive (X := X) (Y := Y) μ Lf Lg Cf ρ)
    (μ' Lf' Lg' Cf' ρ' : ℝ) (hμ' : 0 < μ') (hμ : μ' ≤ μ)
    (hf : Lf ≤ Lf') (hg : Lg ≤ Lg') (hc : Cf ≤ Cf') (hr : ρ ≤ ρ') :
    Model.Primitive (X := X) (Y := Y) μ' Lf' Lg' Cf' ρ' where
  μ_pos := hμ'
  Lf_nonneg := P.Lf_nonneg.trans hf
  Lg_nonneg := P.Lg_nonneg.trans hg
  Cf_nonneg := P.Cf_nonneg.trans hc
  ρ_nonneg := P.ρ_nonneg.trans hr
  f := P.f
  g := P.g
  fx := P.fx
  fy := P.fy
  gx := P.gx
  gy := P.gy
  gyy := P.gyy
  gxy := P.gxy
  has_fx := P.has_fx
  has_fy := P.has_fy
  has_gx := P.has_gx
  has_gy := P.has_gy
  has_gyy := P.has_gyy
  has_gxy := P.has_gxy
  strong_convex := by
    intro x u v
    have h := mul_le_mul_of_nonneg_right hμ (sq_nonneg ‖v - u‖)
    linarith [P.strong_convex x u v]
  upper_bound := fun x y => (P.upper_bound x y).trans hc
  smooth_f := by
    intro x x' y y'
    exact (P.smooth_f x x' y y').trans
      (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ P.Lf_nonneg hf 2) (by positivity))
  smooth_g := by
    intro x x' y y'
    exact (P.smooth_g x x' y y').trans
      (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ P.Lg_nonneg hg 2) (by positivity))
  variation_yy := fun x x' y y' => (P.variation_yy x x' y y').trans
    (mul_le_mul_of_nonneg_right hr (Real.sqrt_nonneg _))
  variation_xy := fun x x' y y' => (P.variation_xy x x' y y').trans
    (mul_le_mul_of_nonneg_right hr (Real.sqrt_nonneg _))

end Bilevel.Model.Primitive

namespace Bilevel.SmallGapNormalization

open SmallGapInstance SmallGapLiftSupport

def normalizationConstant : ℝ := 74560 * C ^ 2

theorem normalizationConstant_ge : 16 ≤ normalizationConstant := by
  unfold normalizationConstant
  nlinarith [C_one_le]

theorem normalizationConstant_pos : 0 < normalizationConstant :=
  lt_of_lt_of_le (by norm_num) normalizationConstant_ge

structure Input where
  L : ℝ
  μ : ℝ
  ρ : ℝ
  ε : ℝ
  L_pos : 0 < L
  μ_pos : 0 < μ
  ε_pos : 0 < ε
  variation_range : normalizationConstant ≤ 1 + ρ / μ
  conditioning_range : 1 + ρ / μ ≤ L / μ
  accuracy : ε ≤ SmallGapScaling.accuracyConstant * L / ((1 + ρ / μ) * (L / μ))

namespace Input

variable (N : Input)

def κ : ℝ := N.L / N.μ
def χ : ℝ := 1 + N.ρ / N.μ

theorem χ_ge : normalizationConstant ≤ N.χ := N.variation_range
theorem χ_pos : 0 < N.χ := normalizationConstant_pos.trans_le N.χ_ge
theorem κ_pos : 0 < N.κ := div_pos N.L_pos N.μ_pos
theorem χ_le_κ : N.χ ≤ N.κ := N.conditioning_range
theorem κ_ge : 16 ≤ N.κ := normalizationConstant_ge.trans (N.χ_ge.trans N.χ_le_κ)

theorem μ_le_ρ : N.μ ≤ N.ρ := by
  have hχ : 2 ≤ 1 + N.ρ / N.μ := by
    have h := normalizationConstant_ge.trans N.variation_range
    linarith
  have hd : 1 ≤ N.ρ / N.μ := by linarith
  simpa only [one_mul] using (le_div_iff₀ N.μ_pos).mp hd

def internal : SmallGapScaling.Input where
  L := N.L / 4
  κ := N.κ / 8
  θ := N.χ / normalizationConstant
  ε := N.ε
  L_pos := div_pos N.L_pos (by norm_num)
  κ_ge_two := by have := N.κ_ge; linarith
  θ_ge_one := (one_le_div normalizationConstant_pos).mpr N.χ_ge
  θ_le_κ := (div_le_div_of_nonneg_right N.χ_le_κ normalizationConstant_pos.le).trans
    (div_le_div_of_nonneg_left N.κ_pos.le (by norm_num) (by linarith [normalizationConstant_ge]))
  ε_pos := N.ε_pos
  accuracy := by
    have ha : N.ε ≤ SmallGapScaling.accuracyConstant * N.L / (N.χ * N.κ) := N.accuracy
    have hb : 0 ≤ SmallGapScaling.accuracyConstant * N.L / (N.χ * N.κ) :=
      div_nonneg (mul_nonneg SmallGapScaling.accuracyConstant_pos.le N.L_pos.le)
        (mul_nonneg N.χ_pos.le N.κ_pos.le)
    have he : SmallGapScaling.accuracyConstant * (N.L / 4) /
        (N.χ / normalizationConstant * (N.κ / 8)) =
      (2 * normalizationConstant) * (SmallGapScaling.accuracyConstant * N.L / (N.χ * N.κ)) := by
      field_simp [N.χ_pos.ne', N.κ_pos.ne', normalizationConstant_pos.ne']
      ring
    rw [he]
    have hm := mul_le_mul_of_nonneg_right (show (1 : ℝ) ≤ 2 * normalizationConstant by
      linarith [normalizationConstant_ge]) hb
    exact ha.trans (by simpa only [one_mul] using hm)

theorem raw_μ : N.internal.parameters.μ = 2 * N.μ := by
  change (N.L / 4) / ((N.L / N.μ) / 8) = 2 * N.μ
  field_simp [N.L_pos.ne', N.μ_pos.ne']
  ring

theorem raw_μ_half : N.internal.parameters.μ / 2 = N.μ := by rw [N.raw_μ]; ring

theorem raw_L : N.internal.parameters.L = N.L / 4 := rfl

theorem raw_ρ : N.internal.parameters.rawRho = (N.μ + N.ρ) / 2 := by
  rw [N.internal.rawRho_scale]
  change 18640 * C ^ 2 * ((N.L / 4) / (N.κ / 8)) * (N.χ / normalizationConstant) = _
  have hμ : (N.L / 4) / (N.κ / 8) = 2 * N.μ := N.raw_μ
  rw [hμ]
  unfold normalizationConstant χ
  have hC := C_pos
  field_simp [N.μ_pos.ne']
  ring

theorem raw_ρ_le : N.internal.parameters.rawRho ≤ N.ρ := by
  rw [N.raw_ρ]
  linarith [N.μ_le_ρ]

/-- A concrete original `Primitive μ L L L ρ`, with no raw budget slack
remaining and with the same explicit three-dimensional objectives. -/
def primitive (ω : ℝ) (hω : |ω| ≤ 1) :
    Model.Primitive (X := ℝ) (Y := LowerSpace) N.μ N.L N.L N.L N.ρ :=
  (N.internal.parameters.primitive ω hω N.internal.scale_condition).rebudget
    N.μ N.L N.L N.L N.ρ N.μ_pos (by rw [N.raw_μ_half])
    (by rw [N.raw_L]; linarith [N.L_pos])
    (by rw [N.raw_L]; linarith [N.L_pos])
    (by rw [N.raw_L]; linarith [N.L_pos]) N.raw_ρ_le

def response (ω : ℝ) (hω : |ω| ≤ 1) : (N.primitive ω hω).Response where
  y := N.internal.parameters.response ω
  minimizes x := (N.internal.parameters.exact_response ω x hω N.internal.scale_condition).1

theorem initial_response (ω : ℝ) (hω : |ω| ≤ 1) : (N.response ω hω).y 0 = 0 :=
  N.internal.parameters.response_zero ω

theorem hyperobjective_eq (ω : ℝ) (hω : |ω| ≤ 1) :
    (N.primitive ω hω).hyperobjective (N.response ω hω) = N.internal.parameters.realizedObjective ω := rfl

def gap : ℝ := 8192 * normalizationConstant * N.ε ^ 2 / (N.L * N.χ * N.κ ^ 2)

theorem raw_gap : (8 * N.internal.ε) ^ 2 /
    (2 * (N.internal.κ ^ 2 * (N.internal.L * N.internal.θ))) = N.gap := by
  dsimp [internal, gap]
  field_simp
  ring

def gapCertificate (ω : ℝ) (hω : |ω| ≤ 1) (hsign : ω = 1 ∨ ω = -1) :
    (N.primitive ω hω).GapCertificate (N.response ω hω) 0 N.gap := by
  let xstar := Classical.choose (N.internal.raw_mean_claims ω hsign).finite_gap
  have hs := Classical.choose_spec (N.internal.raw_mean_claims ω hsign).finite_gap
  refine ⟨N.internal.parameters.realizedObjective ω xstar, hs.1, ?_⟩
  simpa only [N.raw_gap, N.hyperobjective_eq, xstar] using hs.2.2

theorem normalized_noise_scale (σ : ℝ) :
    N.internal.κ ^ 6 * N.internal.L ^ 2 * N.internal.θ ^ 2 * σ ^ 2 /
      ((39296 * C ^ 2) ^ 2 * N.internal.ε ^ 4) =
    N.κ ^ 6 * N.L ^ 2 * N.χ ^ 2 * σ ^ 2 /
      (4194304 * normalizationConstant ^ 2 * (39296 * C ^ 2) ^ 2 * N.ε ^ 4) := by
  dsimp [internal]
  field_simp
  ring

end Input
end Bilevel.SmallGapNormalization
