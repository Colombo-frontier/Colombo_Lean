import NoisyZO.RadialProfileBounds
import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-!
# Dimension-free derivative bounds for the radial profile

The scalar cutoff has bounded derivatives of every fixed finite order.  The
quadratic map `x ↦ ‖x‖²` has dimension-free first- and second-derivative
bounds on the unit ball and vanishing higher derivatives.  The quantitative
composition and product rules therefore give bounds for the normalized
radial profile that are uniform in both the ambient dimension and the Boolean
direction.  These bounds supply a single positive hard-family amplitude for
all dimensions.
-/

open scoped ContDiff InnerProductSpace Topology
open Filter Set

namespace NoisyZO

noncomputable section

theorem iteratedFDeriv_smoothCutoffProfile_eq_zero_of_lt_quarter
    {i : ℕ} (hi : i ≠ 0) {u : ℝ} (hu : u < 1 / 4) :
    iteratedFDeriv ℝ i smoothCutoffProfile u = 0 := by
  have heq : smoothCutoffProfile =ᶠ[𝓝 u] (fun _ : ℝ ↦ 1) := by
    filter_upwards [Iio_mem_nhds hu] with v hv
    exact smoothCutoffProfile_eq_one_of_le_quarter (le_of_lt hv)
  have hderiv := (heq.iteratedFDeriv ℝ i).eq_of_nhds
  rw [hderiv]
  simpa only [Pi.zero_apply] using
    congrFun (iteratedFDeriv_const_of_ne (𝕜 := ℝ) (E := ℝ) hi (1 : ℝ)) u

theorem iteratedFDeriv_smoothCutoffProfile_eq_zero_of_one_lt
    {i : ℕ} (hi : i ≠ 0) {u : ℝ} (hu : 1 < u) :
    iteratedFDeriv ℝ i smoothCutoffProfile u = 0 := by
  have heq : smoothCutoffProfile =ᶠ[𝓝 u] (fun _ : ℝ ↦ 0) := by
    filter_upwards [Ioi_mem_nhds hu] with v hv
    exact smoothCutoffProfile_eq_zero_of_one_le (le_of_lt hv)
  have hderiv := (heq.iteratedFDeriv ℝ i).eq_of_nhds
  rw [hderiv]
  simpa only [Pi.zero_apply] using
    congrFun (iteratedFDeriv_const_of_ne (𝕜 := ℝ) (E := ℝ) hi (0 : ℝ)) u

theorem exists_bound_smoothCutoffProfile_iteratedFDeriv (i : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : ℝ,
      ‖iteratedFDeriv ℝ i smoothCutoffProfile u‖ ≤ C := by
  have hcont : Continuous (fun u : ℝ ↦
      ‖iteratedFDeriv ℝ i smoothCutoffProfile u‖) :=
    (smoothCutoffProfile_contDiff (n := i)).continuous_iteratedFDeriv
      le_rfl |>.norm
  obtain ⟨z, hz, hmax⟩ := isCompact_Icc.exists_isMaxOn
    (nonempty_Icc.2 (by norm_num : (1 / 4 : ℝ) ≤ 1)) hcont.continuousOn
  refine ⟨max 1 ‖iteratedFDeriv ℝ i smoothCutoffProfile z‖,
    le_trans zero_le_one (le_max_left _ _), fun u ↦ ?_⟩
  by_cases hi : i = 0
  · subst i
    rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs,
      abs_of_nonneg (smoothCutoffProfile_nonneg u)]
    exact (smoothCutoffProfile_le_one u).trans (le_max_left _ _)
  by_cases hu : u ∈ Set.Icc (1 / 4 : ℝ) 1
  · exact (hmax hu).trans (le_max_right _ _)
  · simp only [Set.mem_Icc, not_and_or, not_le] at hu
    rcases hu with hu | hu
    · rw [iteratedFDeriv_smoothCutoffProfile_eq_zero_of_lt_quarter hi hu,
        norm_zero]
      exact le_trans zero_le_one (le_max_left _ _)
    · rw [iteratedFDeriv_smoothCutoffProfile_eq_zero_of_one_lt hi hu,
        norm_zero]
      exact le_trans zero_le_one (le_max_left _ _)

theorem exists_uniform_bound_smoothCutoffProfile_iteratedFDeriv (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ i ≤ m, ∀ u : ℝ,
      ‖iteratedFDeriv ℝ i smoothCutoffProfile u‖ ≤ C := by
  choose A hA hbound using fun i : ℕ ↦
    exists_bound_smoothCutoffProfile_iteratedFDeriv i
  let C := ∑ i ∈ Finset.range (m + 1), A i
  refine ⟨C, ?_, ?_⟩
  · exact Finset.sum_nonneg fun i _hi ↦ hA i
  · intro i hi u
    exact (hbound i u).trans (Finset.single_le_sum
      (fun j hj ↦ hA j) (Finset.mem_range.2 (Nat.lt_succ_iff.2 hi)))

theorem norm_iteratedFDeriv_norm_sq_one_le
    {d : ℕ} {x : Point d} (hx : ‖x‖ ≤ 1) :
    ‖iteratedFDeriv ℝ 1 (fun z : Point d ↦ ‖z‖ ^ 2) x‖ ≤ 4 := by
  rw [norm_iteratedFDeriv_one, fderiv_norm_sq]
  simp only [Pi.smul_apply]
  rw [two_nsmul, ← two_smul ℝ]
  rw [norm_smul, innerSL_apply_norm]
  norm_num [Real.norm_eq_abs]
  nlinarith [norm_nonneg x]

theorem norm_iteratedFDeriv_norm_sq_two_le
    {d : ℕ} (x : Point d) :
    ‖iteratedFDeriv ℝ 2 (fun z : Point d ↦ ‖z‖ ^ 2) x‖ ≤ 4 ^ 2 := by
  rw [← norm_iteratedFDeriv_fderiv (n := 1), fderiv_norm_sq,
    norm_iteratedFDeriv_one]
  let L : Point d →L[ℝ] Point d →L[ℝ] ℝ :=
    2 • (innerSL ℝ : Point d →L[ℝ] Point d →L[ℝ] ℝ)
  change ‖fderiv ℝ L x‖ ≤ 4 ^ 2
  rw [ContinuousLinearMap.fderiv]
  have hinner : ‖(innerSL ℝ : Point d →L[ℝ] Point d →L[ℝ] ℝ)‖ ≤ 1 :=
    norm_innerSL_le ℝ
  dsimp only [L]
  rw [two_nsmul]
  calc
    ‖(innerSL ℝ : Point d →L[ℝ] Point d →L[ℝ] ℝ) + innerSL ℝ‖ ≤
        ‖(innerSL ℝ : Point d →L[ℝ] Point d →L[ℝ] ℝ)‖ + ‖innerSL ℝ‖ :=
      norm_add_le
        (innerSL ℝ : Point d →L[ℝ] Point d →L[ℝ] ℝ)
        (innerSL ℝ : Point d →L[ℝ] Point d →L[ℝ] ℝ)
    _ ≤ 2 := by linarith
    _ ≤ 4 ^ 2 := by norm_num

theorem iteratedFDeriv_continuousLinearMap_eq_zero_of_two_le
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : E →L[ℝ] F) {i : ℕ} (hi : 2 ≤ i) (x : E) :
    iteratedFDeriv ℝ i L x = 0 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hi
  rw [show 2 + m = (m + 1) + 1 by omega,
    iteratedFDeriv_succ_eq_comp_right]
  simp only [Function.comp_apply, ContinuousLinearMap.fderiv]
  have hm : m + 1 ≠ 0 := by omega
  have hz : iteratedFDeriv ℝ (m + 1) (fun _ : E ↦ L) x = 0 :=
    congrFun (iteratedFDeriv_const_of_ne (𝕜 := ℝ) (E := E) hm L) x
  rw [hz]
  exact (continuousMultilinearCurryRightEquiv' ℝ (m + 1) E F).symm.map_zero

theorem iteratedFDeriv_norm_sq_eq_zero_of_three_le
    {d i : ℕ} (hi : 3 ≤ i) (x : Point d) :
    iteratedFDeriv ℝ i (fun z : Point d ↦ ‖z‖ ^ 2) x = 0 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hi
  rw [show 3 + m = (m + 2) + 1 by omega,
    iteratedFDeriv_succ_eq_comp_right]
  simp only [Function.comp_apply]
  rw [fderiv_norm_sq]
  let L : Point d →L[ℝ] Point d →L[ℝ] ℝ :=
    2 • (innerSL ℝ : Point d →L[ℝ] Point d →L[ℝ] ℝ)
  change
    (continuousMultilinearCurryRightEquiv' ℝ (m + 2) (Point d) ℝ).symm
      (iteratedFDeriv ℝ (m + 2) L x) = 0
  rw [iteratedFDeriv_continuousLinearMap_eq_zero_of_two_le L (by omega) x]
  exact
    (continuousMultilinearCurryRightEquiv' ℝ (m + 2) (Point d) ℝ).symm.map_zero

theorem norm_iteratedFDeriv_norm_sq_le_four_pow
    {d : ℕ} {x : Point d} (hx : ‖x‖ ≤ 1) (i : ℕ) (hi : 1 ≤ i) :
    ‖iteratedFDeriv ℝ i (fun z : Point d ↦ ‖z‖ ^ 2) x‖ ≤ 4 ^ i := by
  by_cases hi1 : i = 1
  · subst i
    simpa using norm_iteratedFDeriv_norm_sq_one_le hx
  by_cases hi2 : i = 2
  · subst i
    exact norm_iteratedFDeriv_norm_sq_two_le x
  have hi3 : 3 ≤ i := by omega
  rw [iteratedFDeriv_norm_sq_eq_zero_of_three_le hi3, norm_zero]
  positivity

theorem exists_uniform_radialCutoffComposition_deriv_bound (m : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (i : ℕ), i ≤ m → ∀ (d : ℕ) (x : Point d),
      ‖x‖ ≤ 1 →
      ‖iteratedFDeriv ℝ i
        (fun z : Point d ↦ smoothCutoffProfile (‖z‖ ^ 2)) x‖ ≤ B := by
  obtain ⟨C, hC, hscalar⟩ :=
    exists_uniform_bound_smoothCutoffProfile_iteratedFDeriv m
  let term : ℕ → ℝ := fun i ↦ (Nat.factorial i : ℝ) * C * 4 ^ i
  let B := ∑ i ∈ Finset.range (m + 1), term i
  have hterm (i : ℕ) : 0 ≤ term i := by
    dsimp [term]
    positivity
  refine ⟨B, Finset.sum_nonneg fun i _hi ↦ hterm i, ?_⟩
  intro i hi d x hx
  have hcomp := norm_iteratedFDeriv_comp_le
    (smoothCutoffProfile_contDiff (n := m))
    (contDiff_norm_sq ℝ) (by exact_mod_cast hi) x
    (fun j hj ↦ hscalar j (hj.trans hi) (‖x‖ ^ 2))
    (fun j hj _hj' ↦ norm_iteratedFDeriv_norm_sq_le_four_pow hx j hj)
  have hcomp' :
      ‖iteratedFDeriv ℝ i
          (fun z : Point d ↦ smoothCutoffProfile (‖z‖ ^ 2)) x‖ ≤
        term i := by
    simpa only [Function.comp_def, term] using hcomp
  exact hcomp'.trans (Finset.single_le_sum
    (fun j _hj ↦ hterm j)
    (Finset.mem_range.2 (Nat.lt_succ_iff.2 hi)))

theorem norm_hypercubeDirection_le_one
    {d : ℕ} (s : Hypercube d) : ‖hypercubeDirection s‖ ≤ 1 := by
  by_cases hd : d = 0
  · subst d
    simp [hypercubeDirection, signPoint]
  · rw [norm_hypercubeDirection (Nat.pos_of_ne_zero hd) s]

theorem norm_iteratedFDeriv_inner_hypercubeDirection_le_one
    {d i : ℕ} (s : Hypercube d) {x : Point d} (hx : ‖x‖ ≤ 1) :
    ‖iteratedFDeriv ℝ i
      (fun w : Point d ↦ ⟪hypercubeDirection s, w⟫_ℝ) x‖ ≤ 1 := by
  by_cases hi0 : i = 0
  · subst i
    rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs]
    calc
      |⟪hypercubeDirection s, x⟫_ℝ| ≤
          ‖hypercubeDirection s‖ * ‖x‖ :=
        abs_real_inner_le_norm _ _
      _ ≤ 1 * 1 := mul_le_mul (norm_hypercubeDirection_le_one s) hx
        (norm_nonneg _) zero_le_one
      _ = 1 := one_mul _
  by_cases hi1 : i = 1
  · subst i
    rw [norm_iteratedFDeriv_one]
    let L : Point d →L[ℝ] ℝ := innerSL ℝ (hypercubeDirection s)
    change ‖fderiv ℝ L x‖ ≤ 1
    rw [ContinuousLinearMap.fderiv]
    dsimp only [L]
    rw [innerSL_apply_norm]
    exact norm_hypercubeDirection_le_one s
  · have hi2 : 2 ≤ i := by omega
    let L : Point d →L[ℝ] ℝ := innerSL ℝ (hypercubeDirection s)
    change ‖iteratedFDeriv ℝ i L x‖ ≤ 1
    rw [iteratedFDeriv_continuousLinearMap_eq_zero_of_two_le L hi2 x,
      norm_zero]
    norm_num

theorem exists_uniform_normalizedRadialProfile_deriv_bound (m : ℕ) :
    ∃ P : ℝ, 0 ≤ P ∧ ∀ (i : ℕ), i ≤ m → ∀ (d : ℕ) (s : Hypercube d)
      (x : Point d),
      ‖iteratedFDeriv ℝ i (normalizedRadialProfile s) x‖ ≤ P := by
  obtain ⟨B, hB, hcutoff⟩ :=
    exists_uniform_radialCutoffComposition_deriv_bound m
  let term : ℕ → ℝ := fun i ↦
    ∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ) * 1 * B
  let P := ∑ i ∈ Finset.range (m + 1), term i
  have hterm (i : ℕ) : 0 ≤ term i := by
    dsimp [term]
    exact Finset.sum_nonneg fun j _hj ↦ by positivity
  refine ⟨P, Finset.sum_nonneg fun i _hi ↦ hterm i, ?_⟩
  intro i hi d s x
  by_cases hx : ‖x‖ ≤ 1
  · rw [show normalizedRadialProfile s =
        fun w : Point d ↦ ⟪hypercubeDirection s, w⟫_ℝ *
          smoothCutoffProfile (‖w‖ ^ 2) by
      funext w
      exact normalizedRadialProfile_eq_inner s w]
    have hmul := norm_iteratedFDeriv_mul_le
      (𝕜 := ℝ) (N := (m : ℕ∞))
      (f := fun w : Point d ↦ ⟪hypercubeDirection s, w⟫_ℝ)
      (g := fun w : Point d ↦ smoothCutoffProfile (‖w‖ ^ 2))
      (by
        change ContDiff ℝ (m : ℕ∞)
          (innerSL ℝ (hypercubeDirection s) : Point d → ℝ)
        exact (innerSL ℝ (hypercubeDirection s)).contDiff)
      (smoothCutoffProfile_contDiff (n := m) |>.comp (contDiff_norm_sq ℝ))
      x (by exact_mod_cast hi)
    have hsum :
        ∑ j ∈ Finset.range (i + 1),
            (i.choose j : ℝ) *
              ‖iteratedFDeriv ℝ j
                (fun w : Point d ↦ ⟪hypercubeDirection s, w⟫_ℝ) x‖ *
              ‖iteratedFDeriv ℝ (i - j)
                (fun w : Point d ↦ smoothCutoffProfile (‖w‖ ^ 2)) x‖ ≤
          term i := by
      dsimp only [term]
      apply Finset.sum_le_sum
      intro j hj
      have hjle : j ≤ i := Nat.le_of_lt_succ (Finset.mem_range.1 hj)
      have hlin := norm_iteratedFDeriv_inner_hypercubeDirection_le_one s hx
        (i := j)
      have hrad := hcutoff (i - j) ((Nat.sub_le i j).trans hi) d x hx
      gcongr
    exact hmul.trans (hsum.trans (Finset.single_le_sum
      (fun j _hj ↦ hterm j)
      (Finset.mem_range.2 (Nat.lt_succ_iff.2 hi))))
  · have hx' : 1 < ‖x‖ := lt_of_not_ge hx
    have hmem : {w : Point d | 1 < ‖w‖} ∈ 𝓝 x :=
      (isOpen_lt continuous_const continuous_norm).mem_nhds hx'
    have heq : normalizedRadialProfile s =ᶠ[𝓝 x] (fun _ : Point d ↦ 0) := by
      filter_upwards [hmem] with w hw
      exact normalizedRadialProfile_eq_zero_of_one_le_norm s (le_of_lt hw)
    have hderiv := (heq.iteratedFDeriv ℝ i).eq_of_nhds
    rw [hderiv, iteratedFDeriv_fun_zero, Pi.zero_apply, norm_zero]
    exact Finset.sum_nonneg fun j _hj ↦ hterm j

/-- One pair of derivative constants works for the unit radial profile in
every dimension and every Boolean direction. -/
theorem exists_dimensionFree_unitRadialProfileCertificates
    (o : SmoothnessOrder) :
    ∃ M₂ H : ℝ, ∀ (d : ℕ) (s : Hypercube d),
      UnitRadialProfileCertificate o d s M₂ H := by
  obtain ⟨C, hC, hbound⟩ :=
    exists_uniform_normalizedRadialProfile_deriv_bound
      (max 2 (o.k + 1))
  refine ⟨C, 2 * C, fun d s ↦ ?_⟩
  have hsmooth : ContDiff ℝ ∞ (normalizedRadialProfile s) :=
    normalizedRadialProfile_contDiff_infty s
  refine
    { M₂_nonneg := hC
      H_nonneg := mul_nonneg (by norm_num) hC
      gradient_lipschitz := ?_
      higher_holder := ?_ }
  · intro x y
    rw [norm_gradient_sub_eq_iteratedFDeriv_one_sub]
    apply norm_iteratedFDeriv_sub_le_of_uniform_next_bound
      (normalizedRadialProfile s) 1 hsmooth C
    intro z
    simpa only [one_add_one_eq_two] using
      hbound 2 (by omega) d s z
  · intro x y
    apply norm_iteratedFDeriv_sub_le_two_mul_rpow_of_bounds
      (normalizedRadialProfile s) o.k o.alpha C
      o.alpha_pos o.alpha_le_one hC
    · intro z
      exact hbound o.k (by omega) d s z
    · intro u v
      apply norm_iteratedFDeriv_sub_le_of_uniform_next_bound
        (normalizedRadialProfile s) o.k hsmooth C
      intro z
      exact hbound (o.k + 1) (by omega) d s z

/-- A positive amplitude, independent of the dimension, satisfies both
smallness conditions for the common unit-profile constants. -/
theorem exists_dimensionFree_admissible_amplitude_and_unitProfileCertificates
    (o : SmoothnessOrder) :
    ∃ a M₂ H : ℝ,
      0 < a ∧ a ≤ 1 / 4 ∧
      (∀ (d : ℕ) (s : Hypercube d),
        UnitRadialProfileCertificate o d s M₂ H) ∧
      a * M₂ ≤ 1 ∧ a * H ≤ 1 := by
  obtain ⟨M₂, H, cert⟩ :=
    exists_dimensionFree_unitRadialProfileCertificates o
  have hM₂ : 0 ≤ M₂ := (cert 0 default).M₂_nonneg
  have hH : 0 ≤ H := (cert 0 default).H_nonneg
  let D : ℝ := 4 * (1 + M₂ + H)
  have hD : 0 < D := by
    dsimp [D]
    nlinarith
  have hfourD : (4 : ℝ) ≤ D := by
    dsimp [D]
    nlinarith
  have hM₂D : M₂ ≤ D := by
    dsimp [D]
    nlinarith
  have hHD : H ≤ D := by
    dsimp [D]
    nlinarith
  refine ⟨D⁻¹, M₂, H, inv_pos.2 hD, ?_, cert, ?_, ?_⟩
  · rw [show (1 / 4 : ℝ) = (4 : ℝ)⁻¹ by norm_num]
    exact (inv_le_inv₀ hD (by norm_num)).2 hfourD
  · rw [inv_mul_eq_div]
    exact (div_le_one hD).2 hM₂D
  · rw [inv_mul_eq_div]
    exact (div_le_one hD).2 hHD

/-- Dimension-free analytic data for the entire lower hard family.  The
amplitude and both profile constants depend only on the smoothness order. -/
structure DimensionFreeRadialProfileData (o : SmoothnessOrder) where
  amplitude : ℝ
  M₂ : ℝ
  H : ℝ
  amplitude_pos : 0 < amplitude
  amplitude_le_quarter : amplitude ≤ 1 / 4
  profile : ∀ (d : ℕ) (s : Hypercube d),
    UnitRadialProfileCertificate o d s M₂ H
  amplitude_mul_M₂_le_one : amplitude * M₂ ≤ 1
  amplitude_mul_H_le_one : amplitude * H ≤ 1

/-- Dimension-free radial-profile data exists for every smoothness order. -/
theorem dimensionFreeRadialProfileData_nonempty (o : SmoothnessOrder) :
    Nonempty (DimensionFreeRadialProfileData o) := by
  obtain ⟨a, M₂, H, ha, ha4, profile, haM₂, haH⟩ :=
    exists_dimensionFree_admissible_amplitude_and_unitProfileCertificates o
  exact ⟨
    { amplitude := a
      M₂ := M₂
      H := H
      amplitude_pos := ha
      amplitude_le_quarter := ha4
      profile := profile
      amplitude_mul_M₂_le_one := haM₂
      amplitude_mul_H_le_one := haH }⟩

/-- A fixed choice of dimension-free radial-profile data. -/
noncomputable def dimensionFreeRadialProfileData (o : SmoothnessOrder) :
    DimensionFreeRadialProfileData o :=
  Classical.choice (dimensionFreeRadialProfileData_nonempty o)

end

end NoisyZO
