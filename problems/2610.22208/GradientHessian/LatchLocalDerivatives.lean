import GradientHessian.LatchBounds
import GradientHessian.RadialHigherDerivatives

/-! Absolute tensor constants for the four actual scalar profiles used by a
latch. Compactness is used only on a fixed scalar interval, never on an
ambient-dimensional ball. -/

noncomputable section
namespace GradientHessian.LatchLocalDerivatives

open Set
open scoped InnerProductSpace
open Profiles IntegralProfiles RadialSquash RadialHigherDerivatives LatchActivation LatchChain

def scalarProfile (j : Fin 4) (t : ℝ) : ℝ :=
  if j = 0 then chi t * ell₀ t else
  if j = 1 then (1 - chi t) * ell₀ t else
  if j = 2 then chi t else varpi t

theorem scalarProfile_contDiff (j : Fin 4) : ContDiff ℝ 3 (scalarProfile j) := by
  have he : ContDiff ℝ 3 ell₀ := ell₀_contDiff.of_le (by decide : (3 : WithTop ℕ∞) ≤ 4)
  fin_cases j <;> simp only [scalarProfile, Fin.reduceFinMk, ↓reduceIte]
  · exact contDiff_chi.mul he
  · exact (contDiff_const.sub contDiff_chi).mul he
  · exact contDiff_chi
  · exact contDiff_varpi

theorem scalarProfile_jet_bound (j : Fin 4) (n : ℕ) (hn : n ≤ 3) :
    ∃ C : ℝ, 0 < C ∧ ∀ i ≤ n, ∀ t ∈ Icc (-12 : ℝ) 12,
      |iteratedDeriv i (scalarProfile j) t| ≤ C := by
  induction n with
  | zero =>
    obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
      ((scalarProfile_contDiff j).continuous.continuousOn :
        ContinuousOn (scalarProfile j) (Icc (-12 : ℝ) 12))
    refine ⟨max 1 C, lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
    intro i hi t ht
    have hi0 : i = 0 := by omega
    simpa only [hi0, iteratedDeriv_zero, Real.norm_eq_abs] using
      (hC t ht).trans (le_max_right 1 C)
  | succ n ih =>
    obtain ⟨C, hC, hb⟩ := ih (by omega)
    obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn
      (((scalarProfile_contDiff j).continuous_iteratedDeriv (n + 1)
        (by exact_mod_cast hn)).continuousOn :
          ContinuousOn (iteratedDeriv (n + 1) (scalarProfile j)) (Icc (-12 : ℝ) 12))
    refine ⟨max C M, hC.trans_le (le_max_left _ _), ?_⟩
    intro i hi t ht
    by_cases hin : i ≤ n
    · exact (hb i hin t ht).trans (le_max_left _ _)
    · have hie : i = n + 1 := by omega
      subst i
      exact (show |iteratedDeriv (n + 1) (scalarProfile j) t| ≤ M by
        simpa only [Real.norm_eq_abs] using hM t ht).trans (le_max_right _ _)

def scalarJetBound (j : Fin 4) : ℝ := (scalarProfile_jet_bound j 3 le_rfl).choose
def scalarConstant : ℝ := 1 + ∑ j : Fin 4, scalarJetBound j
def readoutConstant : ℝ := 1 + ∑ i ∈ Finset.range 4, radialConstant i * (8 : ℝ) ^ (1 - (i : ℤ))
def localConstant (n : ℕ) : ℝ := n.factorial * scalarConstant * readoutConstant ^ n

theorem scalarJetBound_pos (j : Fin 4) : 0 < scalarJetBound j :=
  (scalarProfile_jet_bound j 3 le_rfl).choose_spec.1

theorem scalarConstant_pos : 0 < scalarConstant := by
  have h : 0 ≤ ∑ j : Fin 4, scalarJetBound j :=
    Finset.sum_nonneg (fun j _ => (scalarJetBound_pos j).le)
  unfold scalarConstant
  linarith

theorem scalarConstant_spec (j : Fin 4) {i : ℕ} (hi : i ≤ 3)
    {t : ℝ} (ht : t ∈ Icc (-12 : ℝ) 12) :
    ‖iteratedFDeriv ℝ i (scalarProfile j) t‖ ≤ scalarConstant := by
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs]
  have h := (scalarProfile_jet_bound j 3 le_rfl).choose_spec.2 i hi t ht
  change |iteratedDeriv i (scalarProfile j) t| ≤ scalarJetBound j at h
  have hs : scalarJetBound j ≤ ∑ j : Fin 4, scalarJetBound j :=
    Finset.single_le_sum (fun j _ => (scalarJetBound_pos j).le) (Finset.mem_univ j)
  unfold scalarConstant
  exact h.trans (by linarith)

theorem readoutConstant_ge_one : 1 ≤ readoutConstant := by
  unfold readoutConstant
  have h : 0 ≤ ∑ i ∈ Finset.range 4, radialConstant i * (8 : ℝ) ^ (1 - (i : ℤ)) := by
    apply Finset.sum_nonneg
    intro i _
    exact mul_nonneg (radialConstant_pos i).le (zpow_nonneg (by norm_num) _)
  linarith

theorem readoutConstant_spec {i : ℕ} (hi : i ≤ 3) :
    radialConstant i * (8 : ℝ) ^ (1 - (i : ℤ)) ≤ readoutConstant := by
  have h : radialConstant i * (8 : ℝ) ^ (1 - (i : ℤ)) ≤
      ∑ j ∈ Finset.range 4, radialConstant j * (8 : ℝ) ^ (1 - (j : ℤ)) := by
    exact Finset.single_le_sum (s := Finset.range 4)
      (f := fun j : ℕ => radialConstant j * (8 : ℝ) ^ (1 - (j : ℤ)))
      (fun j _ => mul_nonneg (radialConstant_pos j).le (zpow_nonneg (by norm_num) _))
      (a := i) (Finset.mem_range.mpr (by omega))
  unfold readoutConstant
  linarith

theorem localConstant_pos (n : ℕ) : 0 < localConstant n := by
  have hC := scalarConstant_pos
  have hR : 0 < readoutConstant := lt_of_lt_of_le zero_lt_one readoutConstant_ge_one
  have hn : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  unfold localConstant
  positivity

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def composite (j : Fin 4) (v : E) (x : E) : ℝ := scalarProfile j (readout v x)

theorem readout_contDiff (v : E) : ContDiff ℝ 3 (readout v) := by
  have he : u 1 v = readout v := by funext x; simp [u]
  rw [← he]
  exact u_contDiff (1 : ℝ) v

theorem composite_contDiff (j : Fin 4) (v : E) : ContDiff ℝ 3 (composite j v) :=
  (scalarProfile_contDiff j).comp (readout_contDiff v)

theorem readout_abs_bound (v x : E) (hv : ‖v‖ = 1) : |readout v x| ≤ 12 := by
  have h := norm_inner_le_norm (𝕜 := ℝ) v (squash 8 x)
  rw [Real.norm_eq_abs, hv, one_mul] at h
  exact h.trans (by convert norm_squash_bound (by norm_num : (0 : ℝ) < 8) x using 1; norm_num)

theorem readout_derivative_bound (v x : E) (hv : ‖v‖ = 1) {i : ℕ}
    (hi1 : 1 ≤ i) (hi3 : i ≤ 3) :
    ‖iteratedFDeriv ℝ i (readout v) x‖ ≤ readoutConstant ^ i := by
  change ‖iteratedFDeriv ℝ i ((innerSL ℝ v) ∘ (squash 8)) x‖ ≤ _
  rw [(innerSL ℝ v).iteratedFDeriv_comp_left (squash_contDiff (by norm_num)).contDiffAt
    (by exact_mod_cast hi3.trans (by norm_num : 3 ≤ 4))]
  have h := (innerSL ℝ v).norm_compContinuousMultilinearMap_le (iteratedFDeriv ℝ i (squash 8) x)
  rw [innerSL_apply_norm, hv, one_mul] at h
  apply (h.trans (squash_derivative_bound i (by omega) (by norm_num) x)).trans
  exact (readoutConstant_spec hi3).trans (by
    simpa only [pow_one] using pow_le_pow_right₀ readoutConstant_ge_one hi1)

theorem composite_derivative_bound (j : Fin 4) (v x : E) (hv : ‖v‖ = 1)
    {n : ℕ} (hn : n ≤ 3) : ‖iteratedFDeriv ℝ n (composite j v) x‖ ≤ localConstant n := by
  apply norm_iteratedFDeriv_comp_le (scalarProfile_contDiff j) (readout_contDiff v)
    (by exact_mod_cast hn) x
  · intro i hi
    exact scalarConstant_spec j (hi.trans hn) (abs_le.mp (readout_abs_bound v x hv))
  · intro i hi hin
    exact readout_derivative_bound v x hv hi (hin.trans hn)

theorem scaled_composite_derivative_bound (j : Fin 4) {r : ℝ} (hr : 0 < r)
    (v x : E) (hv : ‖v‖ = 1) {n : ℕ} (hn : n ≤ 3) :
    ‖iteratedFDeriv ℝ n (fun y => scalarProfile j (u r v y)) x‖ ≤ localConstant n / r ^ n := by
  let A : E →L[ℝ] E := r⁻¹ • ContinuousLinearMap.id ℝ E
  have hA : ‖A‖ ≤ r⁻¹ := by
    dsimp only [A]
    rw [norm_smul r⁻¹ (ContinuousLinearMap.id ℝ E), Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr)]
    exact mul_le_of_le_one_right (inv_nonneg.mpr hr.le) ContinuousLinearMap.norm_id_le
  change ‖iteratedFDeriv ℝ n ((composite j v) ∘ A) x‖ ≤ _
  rw [A.iteratedFDeriv_comp_right (composite_contDiff j v) x (by exact_mod_cast hn)]
  calc
    _ ≤ ‖iteratedFDeriv ℝ n (composite j v) (A x)‖ * ‖A‖ ^ n := by
      simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using
        (iteratedFDeriv ℝ n (composite j v) (A x)).norm_compContinuousLinearMap_le (fun _ => A)
    _ ≤ localConstant n * (r⁻¹) ^ n := mul_le_mul
      (composite_derivative_bound j v (A x) hv hn)
      (pow_le_pow_left₀ (norm_nonneg A) hA n) (by positivity) (localConstant_pos n).le
    _ = _ := by rw [inv_pow, div_eq_mul_inv]

theorem incoming_derivative_bound {r : ℝ} (hr : 0 < r) (v x : E) (hv : ‖v‖ = 1)
    {n : ℕ} (hn : n ≤ 3) :
    ‖iteratedFDeriv ℝ n (incoming r v) x‖ ≤ (8 * localConstant n) * r ^ (1 - (n : ℤ)) := by
  let f := fun y : E => scalarProfile 1 (u r v y)
  have hf : ContDiff ℝ n f := ((scalarProfile_contDiff 1).comp (u_contDiff r v)).of_le
    (by exact_mod_cast hn)
  have he : incoming r v = (8 * r) • f := by
    funext y
    simp [incoming, f, scalarProfile]
    ring
  rw [he, iteratedFDeriv_const_smul_apply hf.contDiffAt,
    norm_smul (8 * r) (iteratedFDeriv ℝ n f x), Real.norm_eq_abs, abs_of_pos (by positivity : 0 < 8 * r)]
  calc
    _ ≤ (8 * r) * (localConstant n / r ^ n) := mul_le_mul_of_nonneg_left
      (scaled_composite_derivative_bound 1 hr v x hv hn) (by positivity)
    _ = _ := by rw [zpow_sub₀ hr.ne', zpow_one, zpow_natCast]; ring

def selfResidual (r : ℝ) (v x : E) : ℝ := -8 * r * chi (u r v x) * ell₀ (u r v x)

theorem selfResidual_contDiff (r : ℝ) (v : E) : ContDiff ℝ 3 (selfResidual r v) :=
  (contDiff_const.mul (contDiff_chi.comp (u_contDiff r v))).mul
    ((ell₀_contDiff.of_le (by decide : (3 : WithTop ℕ∞) ≤ 4)).comp (u_contDiff r v))

theorem selfResidual_derivative_bound {r : ℝ} (hr : 0 < r) (v x : E) (hv : ‖v‖ = 1)
    {n : ℕ} (hn : n ≤ 3) :
    ‖iteratedFDeriv ℝ n (selfResidual r v) x‖ ≤ (8 * localConstant n) * r ^ (1 - (n : ℤ)) := by
  let f := fun y : E => scalarProfile 0 (u r v y)
  have hf : ContDiff ℝ n f := ((scalarProfile_contDiff 0).comp (u_contDiff r v)).of_le
    (by exact_mod_cast hn)
  have he : selfResidual r v = (-8 * r) • f := by
    funext y
    simp [selfResidual, f, scalarProfile]
    ring
  rw [he, iteratedFDeriv_const_smul_apply hf.contDiffAt,
    norm_smul (-8 * r) (iteratedFDeriv ℝ n f x), Real.norm_eq_abs,
    abs_of_neg (by nlinarith : -8 * r < 0)]
  calc
    _ ≤ (8 * r) * (localConstant n / r ^ n) := by
      convert mul_le_mul_of_nonneg_left (scaled_composite_derivative_bound 0 hr v x hv hn)
        (by positivity : 0 ≤ 8 * r) using 1; ring
    _ = _ := by rw [zpow_sub₀ hr.ne', zpow_one, zpow_natCast]; ring

end GradientHessian.LatchLocalDerivatives
