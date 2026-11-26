import Bilevel.LowerAlgebra
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Complex.ExponentialBounds

/-!
# Independent macro and middle widths in the chi-refinement manuscript

The definitions are the actual bounded macro width and natural-floor chain
lengths in `waG:eq:base-parameters` (uploaded source lines 4090--4107).
We prove the floor guarantees and the cancellation of the bounded macro width
in `waG:eq:count`. These are construction-parameter results, not a theorem
asserting the existence of a hard SFO instance or its information lower bound.
-/

noncomputable section
namespace Bilevel.ChiIndependentWidths

def macroWidth (bStar Δ L₀ : ℝ) : ℝ :=
  bStar * min 1 (Real.sqrt (Δ / L₀))

def macroLength (cS Δ L₀ b : ℝ) : ℕ :=
  Nat.floor (cS * Δ / (L₀ * b ^ 2))

def middleLength (cn b h : ℝ) : ℕ :=
  Nat.floor (cn * b ^ 2 / h ^ 2)

/-- This is exactly the manuscript's `floor (cn / xi₀²)`, with `xi₀ = h/b`. -/
theorem middleLength_eq_width_ratio (cn b h : ℝ) (hh : h ≠ 0) :
    middleLength cn b h = Nat.floor (cn / (h / b) ^ 2) := by
  unfold middleLength
  congr 1
  field_simp

theorem macroWidth_pos {bStar Δ L₀ : ℝ}
    (hb : 0 < bStar) (hΔ : 0 < Δ) (hL : 0 < L₀) :
    0 < macroWidth bStar Δ L₀ := by
  unfold macroWidth
  exact mul_pos hb (lt_min (by norm_num) (Real.sqrt_pos.2 (div_pos hΔ hL)))

theorem macroWidth_le {bStar Δ L₀ : ℝ} (hb : 0 ≤ bStar) :
    macroWidth bStar Δ L₀ ≤ bStar := by
  unfold macroWidth
  simpa using mul_le_mul_of_nonneg_left (min_le_left 1 (Real.sqrt (Δ / L₀))) hb

theorem macroWidth_sq {bStar Δ L₀ : ℝ} (hΔ : 0 ≤ Δ) (hL : 0 < L₀) :
    macroWidth bStar Δ L₀ ^ 2 = bStar ^ 2 * min 1 (Δ / L₀) := by
  have hr : 0 ≤ Δ / L₀ := div_nonneg hΔ hL.le
  have hs := Real.sq_sqrt hr
  by_cases h : Δ / L₀ ≤ 1
  · have hroot : Real.sqrt (Δ / L₀) ≤ 1 := by
      nlinarith [Real.sqrt_nonneg (Δ / L₀)]
    simp [macroWidth, min_eq_right hroot, min_eq_right h, mul_pow, hs]
  · have hroot : 1 ≤ Real.sqrt (Δ / L₀) := by
      nlinarith [Real.sqrt_nonneg (Δ / L₀)]
    simp [macroWidth, min_eq_left hroot, min_eq_left (le_of_not_ge h)]

/-- The bounded macro width never uses more than `bStar² Δ` gap units. -/
theorem macroWidth_gap_budget {bStar Δ L₀ : ℝ} (hΔ : 0 ≤ Δ) (hL : 0 < L₀) :
    L₀ * macroWidth bStar Δ L₀ ^ 2 ≤ bStar ^ 2 * Δ := by
  rw [macroWidth_sq hΔ hL]
  calc
    L₀ * (bStar ^ 2 * min 1 (Δ / L₀)) ≤
        L₀ * (bStar ^ 2 * (Δ / L₀)) := by
      gcongr
      exact min_le_right _ _
    _ = bStar ^ 2 * Δ := by field_simp

/-- In particular the macro floor argument is at least 128 for every gap. -/
theorem macro_argument_large {bStar Δ L₀ cS : ℝ}
    (hb : 0 < bStar) (hΔ : 0 < Δ) (hL : 0 < L₀)
    (hsmall : bStar ^ 2 ≤ cS / 128) :
    128 ≤ cS * Δ / (L₀ * macroWidth bStar Δ L₀ ^ 2) := by
  have hwidth := macroWidth_pos hb hΔ hL
  have hgap := macroWidth_gap_budget (bStar := bStar) hΔ.le hL
  apply (le_div_iff₀ (mul_pos hL (sq_pos_of_pos hwidth))).2
  nlinarith [mul_le_mul_of_nonneg_right hsmall hΔ.le]

theorem macroLength_ge_64 {bStar Δ L₀ cS : ℝ}
    (hb : 0 < bStar) (hΔ : 0 < Δ) (hL : 0 < L₀)
    (hsmall : bStar ^ 2 ≤ cS / 128) :
    64 ≤ macroLength cS Δ L₀ (macroWidth bStar Δ L₀) := by
  have hlarge := macro_argument_large hb hΔ hL hsmall
  have hhalf := LowerAlgebra.natFloor_half_lower _ (by linarith :
      2 ≤ cS * Δ / (L₀ * macroWidth bStar Δ L₀ ^ 2))
  have hreal : (64 : ℝ) ≤ (macroLength cS Δ L₀ (macroWidth bStar Δ L₀) : ℝ) := by
    unfold macroLength
    linarith
  exact_mod_cast hreal

/-- The manuscript's small width-ratio condition enforces the middle floor. -/
theorem middle_argument_large {cn b h : ℝ} (hh : 0 < h)
    (hsmall : h ^ 2 ≤ cn * b ^ 2 / 128) :
    128 ≤ cn * b ^ 2 / h ^ 2 := by
  apply (le_div_iff₀ (sq_pos_of_pos hh)).2
  linarith

theorem middleLength_ge_64 {cn b h : ℝ} (hh : 0 < h)
    (hsmall : h ^ 2 ≤ cn * b ^ 2 / 128) :
    64 ≤ middleLength cn b h := by
  have hlarge := middle_argument_large hh hsmall
  have hhalf := LowerAlgebra.natFloor_half_lower _ (by linarith :
      2 ≤ cn * b ^ 2 / h ^ 2)
  have hreal : (64 : ℝ) ≤ (middleLength cn b h : ℝ) := by
    unfold middleLength
    linarith
  exact_mod_cast hreal

/-- Actual natural-floor lengths retain a constant fraction of the product.
The macro width cancels, with no equation identifying it with response gain. -/
theorem stage_count_lower {cS cn Δ L₀ b h : ℝ}
    (hcn : 0 < cn)
    (hL : 0 < L₀) (hb : 0 < b) (hh : 0 < h)
    (hmacro : 2 ≤ cS * Δ / (L₀ * b ^ 2))
    (hmiddle : 2 ≤ cn * b ^ 2 / h ^ 2) :
    cS * cn * Δ / (4 * L₀ * h ^ 2) ≤
      ((macroLength cS Δ L₀ b * middleLength cn b h : ℕ) : ℝ) := by
  have hS := LowerAlgebra.natFloor_half_lower _ hmacro
  have hn := LowerAlgebra.natFloor_half_lower _ hmiddle
  have hprod := mul_le_mul hS hn (by positivity)
    (by positivity : 0 ≤ (Nat.floor (cS * Δ / (L₀ * b ^ 2)) : ℝ))
  have hid : (cS * Δ / (L₀ * b ^ 2) / 2) *
      (cn * b ^ 2 / h ^ 2 / 2) = cS * cn * Δ / (4 * L₀ * h ^ 2) := by
    field_simp
    ring
  rw [hid] at hprod
  simpa [macroLength, middleLength, Nat.cast_mul] using hprod

/-- Complete independent-width floor certificate for the chosen macro width. -/
theorem independent_width_certificate {bStar cS cn Δ L₀ h : ℝ}
    (hbStar : 0 < bStar) (hcn : 0 < cn)
    (hΔ : 0 < Δ) (hL : 0 < L₀) (hh : 0 < h)
    (hmacro : bStar ^ 2 ≤ cS / 128)
    (hmiddle : h ^ 2 ≤ cn * macroWidth bStar Δ L₀ ^ 2 / 128) :
    let b := macroWidth bStar Δ L₀
    64 ≤ macroLength cS Δ L₀ b ∧ 64 ≤ middleLength cn b h ∧
      cS * cn * Δ / (4 * L₀ * h ^ 2) ≤
        ((macroLength cS Δ L₀ b * middleLength cn b h : ℕ) : ℝ) := by
  dsimp only
  refine ⟨macroLength_ge_64 hbStar hΔ hL hmacro,
    middleLength_ge_64 hh hmiddle, ?_⟩
  exact stage_count_lower hcn hL (macroWidth_pos hbStar hΔ hL) hh
    (le_trans (by norm_num) (macro_argument_large hbStar hΔ hL hmacro))
    (le_trans (by norm_num) (middle_argument_large hh hmiddle))

/-- An elementary bound that makes the depth-dependent gain uniformly positive. -/
theorem depth_sq_le_pow (J : ℕ) : (J : ℝ)^2 ≤ (4 : ℝ)^J := by
  induction J with
  | zero => norm_num
  | succ J ih =>
    by_cases hj0 : J = 0
    · simp [hj0]
    · have hj : (1 : ℝ) ≤ J := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hj0
      rw [pow_succ (4 : ℝ) J]
      push_cast
      nlinarith [sq_nonneg ((J : ℝ) - 1)]

def depthGain (ω : ℝ) : ℝ :=
  Real.exp (- (Real.log 2 + (Real.log ω)^2) / 2)

theorem depthGain_pos (ω : ℝ) : 0 < depthGain ω := Real.exp_pos _

def chosenDepth (θ : ℝ) : ℕ :=
  Nat.floor (Real.log (Real.log (2 + θ)) / Real.log 4)

/-- The actual depth floor satisfies the logarithmic budget on the full range. -/
theorem chosenDepth_bound {θ : ℝ} (hθ : 1 ≤ θ) :
    (4 : ℝ) ^ chosenDepth θ ≤ Real.log (2 + θ) := by
  have harg : 0 < 2 + θ := by linarith
  have hexp : Real.exp 1 ≤ 2 + θ := by linarith [Real.exp_one_lt_d9]
  have hlog : 1 ≤ Real.log (2 + θ) := (Real.le_log_iff_exp_le harg).2 hexp
  have hlog4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hf := Nat.floor_le (div_nonneg (Real.log_nonneg hlog) hlog4.le)
  have hm := (le_div_iff₀ hlog4).1 hf
  have he := Real.exp_le_exp.mpr hm
  rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 4),
    Real.exp_log (by linarith : 0 < Real.log (2 + θ))] at he
  exact he

/-- A uniform, explicit gain for every depth with the source's log-depth bound.
No threshold depending on `kappa`, `theta`, or depth is used in this constant. -/
theorem uniform_depth_gain {κ θ ω : ℝ} (J : ℕ) (hκ : 2 ≤ κ)
    (hθ : 0 ≤ θ) (hθκ : θ ≤ κ^2) (hω : 0 < ω)
    (hdepth : (4 : ℝ)^J ≤ Real.log (2 + θ)) :
    depthGain ω ≤ κ * ω^J := by
  have hκp : 0 < κ := by linarith
  have hsq := depth_sq_le_pow J
  have ht : 2 + θ ≤ 2 * κ^2 := by nlinarith
  have hlog := Real.log_le_log (by positivity : 0 < 2 + θ) ht
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (pow_ne_zero 2 hκp.ne'),
    Real.log_pow] at hlog
  norm_num at hlog
  have hjlog := hsq.trans (hdepth.trans hlog)
  have hnonneg := sq_nonneg ((J : ℝ) + Real.log ω)
  have hlower : -(Real.log 2 + (Real.log ω)^2) / 2 ≤
      Real.log (κ * ω^J) := by
    rw [Real.log_mul hκp.ne' (pow_ne_zero J hω.ne'), Real.log_pow]
    nlinarith only [hnonneg, hjlog]
  have hexp := Real.exp_le_exp.mpr hlower
  rwa [Real.exp_log (mul_pos hκp (pow_pos hω J))] at hexp

/-- The public accuracy scale is controlled by the bounded macro width. -/
theorem public_scale_le {L L₀ Δ : ℝ} (hL₀ : 0 < L₀) (hΔ : 0 < Δ)
    (hL₀L : L₀ ≤ L) :
    min L (Real.sqrt (L * Δ)) ≤ L * min 1 (Real.sqrt (Δ / L₀)) := by
  have hL : 0 < L := hL₀.trans_le hL₀L
  have hr : 0 ≤ Real.sqrt (Δ / L₀) := Real.sqrt_nonneg _
  have hr2 := Real.sq_sqrt (div_nonneg hΔ.le hL₀.le)
  have hs2 := Real.sq_sqrt (mul_nonneg hL.le hΔ.le)
  by_cases h : 1 ≤ Real.sqrt (Δ / L₀)
  · simp [min_eq_left h]
  · rw [min_eq_right (le_of_not_ge h)]
    apply (min_le_right L _).trans
    apply (sq_le_sq₀ (Real.sqrt_nonneg _) (mul_nonneg hL.le hr)).mp
    have hd : L₀ * (Real.sqrt (Δ / L₀))^2 = Δ := by rw [hr2]; field_simp
    have hm := mul_nonneg (sub_nonneg.mpr hL₀L)
      (mul_nonneg hL.le (sq_nonneg (Real.sqrt (Δ / L₀))))
    nlinarith

def accuracyConstant (η bStar cn gain Cb : ℝ) : ℝ :=
  η * bStar * Real.sqrt (cn / 128) * gain / Cb

/-- Public accuracy implies the required middle-width inequality for the
actual calibrated `h0`. The only gain premise is independent of accuracy. -/
theorem public_accuracy_width {L Δ η bStar cn gain Cb K ω ε : ℝ} (J : ℕ)
    (hL : 0 < L) (hΔ : 0 < Δ) (hη : 0 < η) (hη1 : η ≤ 1)
    (hbStar : 0 < bStar) (hcn : 0 < cn) (hgain : 0 < gain)
    (hCb : 0 < Cb) (hK : 0 < K) (hω : 0 < ω) (hε : 0 < ε)
    (hKGain : gain ≤ K * ω^J)
    (hacc : ε ≤ accuracyConstant η bStar cn gain Cb *
      min L (Real.sqrt (L * Δ))) :
    (Cb * ε / (K * (η * L) * ω^J))^2 ≤
      cn * macroWidth bStar Δ (η * L)^2 / 128 := by
  have hL₀ : 0 < η * L := mul_pos hη hL
  have hwidth := macroWidth_pos hbStar hΔ hL₀
  have hroot : 0 < Real.sqrt (cn / 128) := Real.sqrt_pos.2 (by positivity)
  have hc : 0 < accuracyConstant η bStar cn gain Cb := by
    unfold accuracyConstant
    positivity
  have hscale := public_scale_le hL₀ hΔ (by nlinarith : η * L ≤ L)
  have hacc' := hacc.trans (mul_le_mul_of_nonneg_left hscale hc.le)
  have htarget : Cb * ε / (K * (η * L) * ω^J) ≤
      Real.sqrt (cn / 128) * macroWidth bStar Δ (η * L) := by
    apply (div_le_iff₀ (by positivity : 0 < K * (η * L) * ω^J)).2
    have h1 := mul_le_mul_of_nonneg_left hacc' hCb.le
    have h2 := mul_le_mul_of_nonneg_left hKGain
      (by positivity : 0 ≤ η * L * Real.sqrt (cn / 128) * macroWidth bStar Δ (η * L))
    have hcId : Cb * accuracyConstant η bStar cn gain Cb =
        η * bStar * Real.sqrt (cn / 128) * gain := by
      unfold accuracyConstant
      field_simp only [hCb.ne']
      ring
    rw [← mul_assoc, hcId] at h1
    simp only [macroWidth] at h1 h2 ⊢
    nlinarith
  have hsq := (sq_le_sq₀ (by positivity : 0 ≤ Cb * ε / (K * (η * L) * ω^J))
    (mul_nonneg hroot.le hwidth.le)).mpr htarget
  rw [mul_pow, Real.sq_sqrt (by positivity : 0 ≤ cn / 128)] at hsq
  nlinarith

theorem uniform_accuracy_constant_pos {η bStar cn cK Cb ω : ℝ}
    (hη : 0 < η) (hb : 0 < bStar) (hcn : 0 < cn) (hcK : 0 < cK)
    (hCb : 0 < Cb) :
    0 < accuracyConstant η bStar cn (cK * depthGain ω) Cb := by
  have := depthGain_pos ω
  unfold accuracyConstant
  positivity

/-- A conditioning-independent public accuracy constant proves both actual
floor bounds and their product for the manuscript's actual depth and widths.
The constant depends only on the fixed construction constants, not on
`L`, `Delta`, `kappa`, `theta`, `K`, or the recursion depth. -/
theorem uniform_floor_certificate {L Δ η bStar cS cn cK Cb K κ θ ω ε : ℝ}
    (hL : 0 < L) (hΔ : 0 < Δ) (hη : 0 < η) (hη1 : η ≤ 1)
    (hb : 0 < bStar) (hcn : 0 < cn) (hcK : 0 < cK) (hCb : 0 < Cb)
    (hκ : 2 ≤ κ) (hθ : 1 ≤ θ) (hθκ : θ ≤ κ^2)
    (hK : cK * κ ≤ K) (hω : 0 < ω) (hε : 0 < ε)
    (hmacro : bStar^2 ≤ cS / 128)
    (hacc : ε ≤ accuracyConstant η bStar cn (cK * depthGain ω) Cb *
      min L (Real.sqrt (L * Δ))) :
    let J := chosenDepth θ
    let b := macroWidth bStar Δ (η * L)
    let h := Cb * ε / (K * (η * L) * ω^J)
    64 ≤ macroLength cS Δ (η * L) b ∧ 64 ≤ middleLength cn b h ∧
      cS * cn * Δ / (4 * (η * L) * h^2) ≤
        ((macroLength cS Δ (η * L) b * middleLength cn b h : ℕ) : ℝ) := by
  have hκp : 0 < κ := by linarith
  have hKp : 0 < K := (mul_pos hcK hκp).trans_le hK
  have hgain := uniform_depth_gain (chosenDepth θ) hκ (by linarith) hθκ hω
    (chosenDepth_bound hθ)
  have hKGain : cK * depthGain ω ≤ K * ω ^ chosenDepth θ := by
    calc
      cK * depthGain ω ≤ cK * (κ * ω ^ chosenDepth θ) :=
        mul_le_mul_of_nonneg_left hgain hcK.le
      _ = (cK * κ) * ω ^ chosenDepth θ := by ring
      _ ≤ K * ω ^ chosenDepth θ :=
        mul_le_mul_of_nonneg_right hK (pow_nonneg hω.le _)
  have hmiddle := public_accuracy_width (chosenDepth θ) hL hΔ hη hη1 hb hcn
    (mul_pos hcK (depthGain_pos ω)) hCb hKp hω hε hKGain hacc
  exact independent_width_certificate hb hcn hΔ (mul_pos hη hL)
    (by positivity) hmacro hmiddle

end Bilevel.ChiIndependentWidths
