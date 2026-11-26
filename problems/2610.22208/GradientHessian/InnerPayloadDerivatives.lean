import GradientHessian.InnerDerivativeTools

/-! Absolute derivatives of the actual numerical force and gates and every
inner payload. Scalar compactness is used only for fixed one-dimensional
profiles; constants are chosen independently of ambient dimensions. -/

noncomputable section
namespace GradientHessian.Inner

open Set Filter EuclideanRegisters InnerCoordinates InverseGate
open RadialHigherDerivatives LatchLocalDerivatives
open scoped Topology InnerProductSpace

theorem scalar_compact_jet_bound (f : ℝ → ℝ) (hf : ContDiff ℝ 3 f) (K : ℝ)
    (n : ℕ) (hn : n ≤ 3) : ∃ C : ℝ, 0 < C ∧ ∀ i ≤ n, ∀ t ∈ Icc (-K) K,
      ‖iteratedFDeriv ℝ i f t‖ ≤ C := by
  induction n with
  | zero =>
    obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
      (hf.continuous.continuousOn : ContinuousOn f (Icc (-K) K))
    refine ⟨max 1 C, lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
    intro i hi t ht
    have hi0 : i = 0 := by omega
    subst i
    simpa only [norm_iteratedFDeriv_zero] using (hC t ht).trans (le_max_right 1 C)
  | succ n ih =>
    obtain ⟨C, hC, hb⟩ := ih (by omega)
    obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn
      ((hf.continuous_iteratedDeriv (n + 1) (by exact_mod_cast hn)).continuousOn :
        ContinuousOn (iteratedDeriv (n + 1) f) (Icc (-K) K))
    refine ⟨max C M, hC.trans_le (le_max_left _ _), ?_⟩
    intro i hi t ht
    by_cases hin : i ≤ n
    · exact (hb i hin t ht).trans (le_max_left _ _)
    · have hie : i = n + 1 := by omega
      subst i
      rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
      exact (hM t ht).trans (le_max_right _ _)

def scalarCompactConstant (f : ℝ → ℝ) (hf : ContDiff ℝ 3 f) (K : ℝ) : ℝ :=
  (scalar_compact_jet_bound f hf K 3 le_rfl).choose

theorem scalarCompactConstant_pos (f : ℝ → ℝ) (hf : ContDiff ℝ 3 f) (K : ℝ) :
    0 < scalarCompactConstant f hf K := (scalar_compact_jet_bound f hf K 3 le_rfl).choose_spec.1

theorem scalarCompactConstant_spec (f : ℝ → ℝ) (hf : ContDiff ℝ 3 f) (K : ℝ)
    {n : ℕ} (hn : n ≤ 3) {t : ℝ} (ht : t ∈ Icc (-K) K) :
    ‖iteratedFDeriv ℝ n f t‖ ≤ scalarCompactConstant f hf K :=
  (scalar_compact_jet_bound f hf K 3 le_rfl).choose_spec.2 n hn t ht

def thetaThree : ContDiff ℝ 3 IntegralProfiles.theta :=
  IntegralProfiles.theta_contDiff.of_le (by decide : (3 : WithTop ℕ∞) ≤ 4)
def thetaConstant : ℝ := 20 + scalarCompactConstant IntegralProfiles.theta thetaThree 10
def chiConstant : ℝ := scalarCompactConstant Profiles.chi Profiles.contDiff_chi 768

theorem thetaConstant_pos : 0 < thetaConstant := by
  unfold thetaConstant
  linarith [scalarCompactConstant_pos IntegralProfiles.theta thetaThree 10]
theorem chiConstant_pos : 0 < chiConstant := scalarCompactConstant_pos _ _ _

theorem theta_positive_plateau {t : ℝ} (ht : 9 ≤ t) : IntegralProfiles.theta t = 17 / 2 := by
  unfold IntegralProfiles.theta
  rw [IntegralProfiles.evenPrimitive_nonneg_arg (by norm_num : (0 : ℝ) ≤ 8) (by linarith),
    IntegralProfiles.primitive_plateau (by norm_num : (0 : ℝ) ≤ 8) (by linarith)]
  norm_num

theorem theta_negative_plateau {t : ℝ} (ht : t ≤ -9) : IntegralProfiles.theta t = -(17 / 2) := by
  unfold IntegralProfiles.theta
  rw [IntegralProfiles.evenPrimitive_nonpos_arg (by norm_num : (0 : ℝ) ≤ 8) (by linarith),
    IntegralProfiles.primitive_plateau (by norm_num : (0 : ℝ) ≤ 8) (by linarith)]
  norm_num

theorem theta_derivative_bound (n : ℕ) (hn : n ≤ 3) (t : ℝ) :
    ‖iteratedFDeriv ℝ n IntegralProfiles.theta t‖ ≤ thetaConstant := by
  by_cases ht : |t| ≤ 10
  · exact (scalarCompactConstant_spec _ thetaThree 10 hn (abs_le.mp ht)).trans
      (by unfold thetaConstant; linarith)
  · by_cases hn0 : n = 0
    · subst n
      rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs]
      exact (IntegralProfiles.theta_abs_bound t).trans (by
        unfold thetaConstant
        linarith [scalarCompactConstant_pos IntegralProfiles.theta thetaThree 10])
    · have hn1 : 1 ≤ n := by omega
      obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn0
      rcases lt_or_gt_of_ne (show t ≠ 0 by intro h; simp [h] at ht) with hneg | hpos
      · have ht' : t < -10 := by rw [abs_of_neg hneg] at ht; linarith
        have he : IntegralProfiles.theta =ᶠ[𝓝 t] (fun _ => -(17 / 2 : ℝ)) := by
          filter_upwards [gt_mem_nhds ht'] with x hx
          exact theta_negative_plateau (by linarith)
        rw [iteratedFDeriv_eq_of_eventuallyEq he, iteratedFDeriv_succ_const, Pi.zero_apply, norm_zero]
        exact thetaConstant_pos.le
      · have ht' : 10 < t := by rw [abs_of_pos hpos] at ht; linarith
        have he : IntegralProfiles.theta =ᶠ[𝓝 t] (fun _ => (17 / 2 : ℝ)) := by
          filter_upwards [lt_mem_nhds ht'] with x hx
          exact theta_positive_plateau (by linarith)
        rw [iteratedFDeriv_eq_of_eventuallyEq he, iteratedFDeriv_succ_const, Pi.zero_apply, norm_zero]
        exact thetaConstant_pos.le

def forcingConstant : ℝ := H₀ ^ 2 * (thetaConstant + 20)
def gateArgumentConstant : ℝ := 1 + ∑ j ∈ Finset.range 4,
  (radialConstant j * B₀ ^ (1 - (j : ℤ))) / alpha
def gateConstant (n : ℕ) : ℝ := n.factorial * chiConstant * gateArgumentConstant ^ n

theorem forcingConstant_pos : 0 < forcingConstant := by
  unfold forcingConstant
  have ht := thetaConstant_pos
  have hH := H₀_pos
  positivity
theorem gateArgumentConstant_ge_one : 1 ≤ gateArgumentConstant := by
  unfold gateArgumentConstant
  have hs : 0 ≤ ∑ j ∈ Finset.range 4, (radialConstant j * B₀ ^ (1 - (j : ℤ))) / alpha :=
    Finset.sum_nonneg (fun j _ => div_nonneg
      (mul_nonneg (radialConstant_pos j).le (zpow_nonneg B₀_pos.le _)) alpha_pos.le)
  linarith
theorem gateConstant_pos (n : ℕ) : 0 < gateConstant n := by
  unfold gateConstant
  have hc := chiConstant_pos
  have hg := lt_of_lt_of_le zero_lt_one gateArgumentConstant_ge_one
  have hn : (0 : ℝ) < n.factorial := Nat.cast_pos.mpr (Nat.factorial_pos n)
  positivity

variable {Y : Type*} [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]

theorem forcing_contDiff (b : Y) : ContDiff ℝ 3 (InverseGate.forcing b) := by
  unfold InverseGate.forcing forcingArg
  exact contDiff_const.mul (contDiff_const.add
    (thetaThree.comp ((innerSL ℝ b).contDiff.div_const _)))

theorem forcing_derivative_bound (b y : Y) (hb : ‖b‖ = H₀) {n : ℕ} (hn : n ≤ 3) :
    ‖iteratedFDeriv ℝ n (InverseGate.forcing b) y‖ ≤ forcingConstant := by
  by_cases hn0 : n = 0
  · subst n
    rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs, abs_of_nonneg (forcing_bounds b y).1]
    exact (forcing_bounds b y).2.trans (by
      unfold forcingConstant
      nlinarith [thetaConstant_pos, sq_nonneg H₀, mul_nonneg thetaConstant_pos.le (sq_nonneg H₀)])
  · have hn1 : 1 ≤ n := by omega
    let L : Y →L[ℝ] ℝ := ((H₀ ^ 2)⁻¹) • innerSL ℝ b
    have hL : ‖L‖ ≤ 1 := by
      simp only [L, norm_smul ((H₀ ^ 2)⁻¹) (innerSL ℝ b), innerSL_apply_norm,
        Real.norm_eq_abs, abs_inv, abs_pow, abs_of_pos H₀_pos, hb]
      norm_num [H₀]
    have hc : ContDiff ℝ 3 (IntegralProfiles.theta ∘ L) := thetaThree.comp L.contDiff
    have he : InverseGate.forcing b = fun x => H₀ ^ 2 • (IntegralProfiles.theta (L x)) + 10 * H₀ ^ 2 := by
      funext x
      simp [InverseGate.forcing, forcingArg, L, div_eq_mul_inv]
      ring
    rw [he, LocalizedProductDerivatives.iteratedFDeriv_add_const_of_pos (f := fun x => H₀ ^ 2 • IntegralProfiles.theta (L x)) hn1
      ((hc.const_smul (H₀ ^ 2)).contDiffAt.of_le (by exact_mod_cast hn)),
      iteratedFDeriv_const_smul_apply' (f := fun x => IntegralProfiles.theta (L x))
        (hc.contDiffAt.of_le (by exact_mod_cast hn)),
      norm_smul (H₀ ^ 2) (iteratedFDeriv ℝ n (fun x => IntegralProfiles.theta (L x)) y),
      Real.norm_eq_abs, abs_of_nonneg (sq_nonneg H₀)]
    have hd := (derivative_comp_linear_le L hL thetaThree hn y).trans (theta_derivative_bound n hn (L y))
    apply (mul_le_mul_of_nonneg_left hd (sq_nonneg H₀)).trans
    unfold forcingConstant
    nlinarith [sq_nonneg H₀]

theorem gateArg_abs_bound (a y : Y) (ha : ‖a‖ = 1) : |gateArg a y| ≤ 768 := by
  have hi := norm_inner_le_norm (𝕜 := ℝ) a (RadialSquash.squash B₀ y)
  rw [Real.norm_eq_abs, ha, one_mul] at hi
  have hs := RadialSquash.norm_squash_bound B₀_pos y
  unfold gateArg
  rw [abs_div, abs_of_pos alpha_pos, div_le_iff₀ alpha_pos]
  have hnum : 3 / 2 * B₀ = (768 : ℝ) * alpha := by norm_num [B₀, alpha, H₀]
  linarith

theorem gateArg_derivative_bound (a y : Y) (ha : ‖a‖ = 1) {n : ℕ}
    (hn1 : 1 ≤ n) (hn3 : n ≤ 3) :
    ‖iteratedFDeriv ℝ n (gateArg a) y‖ ≤ gateArgumentConstant ^ n := by
  let L : Y →L[ℝ] ℝ := alpha⁻¹ • innerSL ℝ a
  have hL : ‖L‖ = alpha⁻¹ := by
    dsimp only [L]
    rw [norm_smul alpha⁻¹ (innerSL ℝ a), Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr alpha_pos), innerSL_apply_norm, ha, mul_one]
  have he : gateArg a = L ∘ RadialSquash.squash B₀ := by
    funext x
    simp [gateArg, L, div_eq_mul_inv, mul_comm]
  have hh := L.norm_compContinuousMultilinearMap_le (iteratedFDeriv ℝ n (RadialSquash.squash B₀) y)
  rw [hL] at hh
  have hr := squash_derivative_bound n (by omega) B₀_pos y
  have hd : ‖iteratedFDeriv ℝ n (gateArg a) y‖ ≤
      (radialConstant n * B₀ ^ (1 - (n : ℤ))) / alpha := by
    rw [he, L.iteratedFDeriv_comp_left (RadialSquash.squash_contDiff B₀_pos).contDiffAt
      (by exact_mod_cast hn3.trans (by norm_num : 3 ≤ 4))]
    simpa only [div_eq_mul_inv, mul_comm] using hh.trans
      (mul_le_mul_of_nonneg_left hr (inv_nonneg.mpr alpha_pos.le))
  have hs : (radialConstant n * B₀ ^ (1 - (n : ℤ))) / alpha ≤ gateArgumentConstant := by
    have hsum := Finset.single_le_sum (s := Finset.range 4)
      (f := fun j : ℕ => (radialConstant j * B₀ ^ (1 - (j : ℤ))) / alpha)
      (fun j _ => div_nonneg (mul_nonneg (radialConstant_pos j).le
        (zpow_nonneg B₀_pos.le _)) alpha_pos.le) (a := n) (Finset.mem_range.mpr (by omega))
    unfold gateArgumentConstant
    linarith
  exact (hd.trans hs).trans (by
    simpa only [pow_one] using pow_le_pow_right₀ gateArgumentConstant_ge_one hn1)

theorem gate_derivative_bound (a y : Y) (ha : ‖a‖ = 1) {n : ℕ} (hn : n ≤ 3) :
    ‖iteratedFDeriv ℝ n (InverseGate.gate a) y‖ ≤ gateConstant n := by
  apply norm_iteratedFDeriv_comp_le Profiles.contDiff_chi
    ((gateArg_contDiff a).of_le (by decide : (3 : WithTop ℕ∞) ≤ 4)) (by exact_mod_cast hn) y
  · intro j hj
    exact scalarCompactConstant_spec _ Profiles.contDiff_chi 768 (hj.trans hn)
      (abs_le.mp (gateArg_abs_bound a y ha))
  · intro j hj hjn
    exact gateArg_derivative_bound a y ha hj (hjn.trans hn)

def payloadDerivativeConstant (n : ℕ) : ℝ := forcingConstant +
  ∑ j ∈ Finset.range (n + 1), (n.choose j : ℝ) * (8 * localConstant j) * gateConstant (n - j)
def payloadJetConstant : ℝ := 1 + ∑ n ∈ Finset.range 4, payloadDerivativeConstant n

theorem payloadDerivativeConstant_pos (n : ℕ) : 0 < payloadDerivativeConstant n := by
  have hs : 0 ≤ ∑ j ∈ Finset.range (n + 1),
      (n.choose j : ℝ) * (8 * localConstant j) * gateConstant (n - j) := by
    apply Finset.sum_nonneg
    intro j _
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (by have h := localConstant_pos j; positivity))
      (gateConstant_pos _).le
  unfold payloadDerivativeConstant
  linarith [forcingConstant_pos]

theorem payloadJetConstant_pos : 0 < payloadJetConstant := by
  unfold payloadJetConstant
  have hs : 0 ≤ ∑ n ∈ Finset.range 4, payloadDerivativeConstant n :=
    Finset.sum_nonneg (fun n _ => (payloadDerivativeConstant_pos n).le)
  linarith

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem lifted_forcing_derivative_bound (b : Y) (hb : ‖b‖ = H₀)
    (Z : Space Y E m (k + 2)) {n : ℕ} (hn : n ≤ 3) :
    ‖iteratedFDeriv ℝ n (fun W : Space Y E m (k + 2) =>
      InverseGate.forcing b (numerical Y E m (k + 2) W)) Z‖ ≤ forcingConstant :=
  (derivative_comp_linear_le (numerical Y E m (k + 2)) (numerical_norm_le _ _)
    (forcing_contDiff b) hn Z).trans (forcing_derivative_bound b _ hb hn)

theorem lifted_gate_derivative_bound (a : Y) (ha : ‖a‖ = 1)
    (Z : Space Y E m (k + 2)) {n : ℕ} (hn : n ≤ 3) :
    ‖iteratedFDeriv ℝ n (fun W : Space Y E m (k + 2) =>
      InverseGate.gate a (numerical Y E m (k + 2) W)) Z‖ ≤ gateConstant n :=
  (derivative_comp_linear_le (numerical Y E m (k + 2)) (numerical_norm_le _ _)
    (InverseGate.gate_contDiff a) hn Z).trans (gate_derivative_bound a _ ha hn)

theorem lifted_input_derivative_bound (v : Fin m → Fin (k + 2) → E)
    (i : Fin m) (hv : ‖v i 0‖ = 1) (Z : Space Y E m (k + 2)) {n : ℕ} (hn : n ≤ 3) :
    ‖iteratedFDeriv ℝ n (fun W : Space Y E m (k + 2) =>
      input (v i) (tasks Y E m (k + 2) W i)) Z‖ ≤ 8 * localConstant n := by
  have h := derivative_comp_linear_le (firstProjection (Y := Y) (E := E) m k i)
    (firstProjection_norm_le m k i) (LatchChain.incoming_contDiff 1 (v i 0)) hn Z
  exact h.trans (by
    simpa using (incoming_derivative_bound (by norm_num : (0 : ℝ) < 1)
      (v i 0) (firstProjection m k i Z) hv hn))

theorem payload_order_derivative_bound (b a : Fin m → Y) (v : Fin m → Fin (k + 2) → E)
    (i : Fin m) (hb : ‖b i‖ = H₀) (ha : ‖a i‖ = 1) (hv : ‖v i 0‖ = 1)
    (Z : Space Y E m (k + 2)) {n : ℕ} (hn : n ≤ 3) :
    ‖iteratedFDeriv ℝ n (fun W => payload b a v W i) Z‖ ≤ payloadDerivativeConstant n := by
  let U := fun W : Space Y E m (k + 2) => InverseGate.forcing (b i) (numerical Y E m (k + 2) W)
  let B := fun W : Space Y E m (k + 2) => input (v i) (tasks Y E m (k + 2) W i)
  let c := fun W : Space Y E m (k + 2) => InverseGate.gate (a i) (numerical Y E m (k + 2) W)
  have hU : ContDiff ℝ 3 U := (forcing_contDiff (b i)).comp (numerical Y E m (k + 2)).contDiff
  have hB : ContDiff ℝ 3 B := (input_contDiff (v i)).comp
    (taskProjection (Y := Y) (E := E) m k i).contDiff
  have hc : ContDiff ℝ 3 c := (InverseGate.gate_contDiff (a i)).comp (numerical Y E m (k + 2)).contDiff
  have hsum := norm_iteratedFDeriv_add_le hU (hB.mul hc) hn Z
  have hprod := norm_iteratedFDeriv_mul_le hB hc Z (by exact_mod_cast hn)
  change ‖iteratedFDeriv ℝ n (fun W => U W + B W * c W) Z‖ ≤ _
  apply hsum.trans
  apply add_le_add (lifted_forcing_derivative_bound (b i) hb Z hn)
  apply hprod.trans
  apply Finset.sum_le_sum
  intro j hj
  have hjn : j ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  have hnj : n - j ≤ 3 := (Nat.sub_le n j).trans hn
  apply mul_le_mul
  · exact mul_le_mul_of_nonneg_left (lifted_input_derivative_bound v i hv Z (hjn.trans hn))
      (Nat.cast_nonneg _)
  · exact lifted_gate_derivative_bound (a i) ha Z hnj
  · exact norm_nonneg _
  · exact mul_nonneg (Nat.cast_nonneg _) (by have h := localConstant_pos j; positivity)

/-- One fixed constant bounds every actual payload jet of order zero through
three on the full Euclidean space, despite the shared numerical coordinate. -/
theorem payload_derivative_bound (b a : Fin m → Y) (v : Fin m → Fin (k + 2) → E)
    (i : Fin m) (hb : ‖b i‖ = H₀) (ha : ‖a i‖ = 1) (hv : ‖v i 0‖ = 1)
    (Z : Space Y E m (k + 2)) {n : ℕ} (hn : n ≤ 3) :
    ‖iteratedFDeriv ℝ n (fun W => payload b a v W i) Z‖ ≤ payloadJetConstant := by
  apply (payload_order_derivative_bound b a v i hb ha hv Z hn).trans
  have hs := Finset.single_le_sum (s := Finset.range 4) (f := payloadDerivativeConstant)
    (fun j _ => (payloadDerivativeConstant_pos j).le) (a := n) (Finset.mem_range.mpr (by omega))
  unfold payloadJetConstant
  linarith

end GradientHessian.Inner
