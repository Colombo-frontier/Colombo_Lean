import NoisyZO.UniformMeasures
import NoisyZO.SmoothCutoff
import NoisyZO.BetaFourBall
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff
import Mathlib.MeasureTheory.Integral.IntervalIntegral.MeanValue
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Function.L2Space

open MeasureTheory Metric Set Filter
open scoped ContDiff InnerProductSpace Gradient Topology Interval

namespace NoisyZO

noncomputable section

def boundaryCutoff (n : ℕ) {d : ℕ} (x : Point d) : ℝ :=
  smoothCutoffProfile
    (1 / 4 + (n + 1 : ℝ) * (‖x‖ ^ 2 - 1))

theorem smoothCutoffProfile_antitone : Antitone smoothCutoffProfile := by
  intro x y hxy
  apply Real.smoothTransition.monotone
  linarith

theorem deriv_smoothCutoffProfile_nonpos (u : ℝ) :
    deriv smoothCutoffProfile u ≤ 0 :=
  smoothCutoffProfile_antitone.deriv_nonpos

theorem deriv_smoothCutoffProfile_eq_zero_of_lt_quarter
    {u : ℝ} (hu : u < 1 / 4) :
    deriv smoothCutoffProfile u = 0 := by
  have heq : smoothCutoffProfile =ᶠ[𝓝 u] fun _ ↦ (1 : ℝ) := by
    filter_upwards [eventually_lt_nhds hu] with z hz
    exact smoothCutoffProfile_eq_one_of_le_quarter hz.le
  simpa using heq.deriv_eq

theorem deriv_smoothCutoffProfile_eq_zero_of_one_lt
    {u : ℝ} (hu : 1 < u) :
    deriv smoothCutoffProfile u = 0 := by
  have heq : smoothCutoffProfile =ᶠ[𝓝 u] fun _ ↦ (0 : ℝ) := by
    filter_upwards [eventually_gt_nhds hu] with z hz
    exact smoothCutoffProfile_eq_zero_of_one_le hz.le
  simpa using heq.deriv_eq

theorem boundaryCutoff_contDiff_infty (n d : ℕ) :
    ContDiff ℝ ∞ (boundaryCutoff n : Point d → ℝ) := by
  apply smoothCutoffProfile_contDiff_infty.comp
  exact contDiff_const.add
    (contDiff_const.mul ((contDiff_norm_sq ℝ).sub contDiff_const))

theorem boundaryCutoff_hasCompactSupport (n d : ℕ) :
    HasCompactSupport (boundaryCutoff n : Point d → ℝ) := by
  apply HasCompactSupport.intro (isCompact_closedBall (0 : Point d) 2)
  intro x hx
  have hxnorm : 2 < ‖x‖ := by
    simpa [mem_closedBall, dist_zero_right, not_le] using hx
  apply smoothCutoffProfile_eq_zero_of_one_le
  have hn : (1 : ℝ) ≤ n + 1 := by norm_cast; omega
  have hsq : 4 < ‖x‖ ^ 2 := by nlinarith [sq_nonneg (‖x‖ - 2)]
  have hdiff : 3 ≤ ‖x‖ ^ 2 - 1 := by linarith
  have hmul : 3 ≤ (n + 1 : ℝ) * (‖x‖ ^ 2 - 1) := by
    nlinarith [mul_le_mul hn hdiff (by norm_num : (0 : ℝ) ≤ 3)
      (by linarith : (0 : ℝ) ≤ n + 1)]
  linarith

theorem boundaryCutoff_eq_zero_of_two_lt_norm
    (n : ℕ) {d : ℕ} {x : Point d} (hx : 2 < ‖x‖) :
    boundaryCutoff n x = 0 := by
  apply smoothCutoffProfile_eq_zero_of_one_le
  have hn : (1 : ℝ) ≤ n + 1 := by norm_cast; omega
  have hsq : 4 < ‖x‖ ^ 2 := by nlinarith [sq_nonneg (‖x‖ - 2)]
  have hdiff : 3 ≤ ‖x‖ ^ 2 - 1 := by linarith
  have hmul : 3 ≤ (n + 1 : ℝ) * (‖x‖ ^ 2 - 1) := by
    nlinarith [mul_le_mul hn hdiff (by norm_num : (0 : ℝ) ≤ 3)
      (by linarith : (0 : ℝ) ≤ n + 1)]
  linarith

theorem boundaryCutoff_eq_one_of_norm_le_one
    (n : ℕ) {d : ℕ} {x : Point d} (hx : ‖x‖ ≤ 1) :
    boundaryCutoff n x = 1 := by
  apply smoothCutoffProfile_eq_one_of_le_quarter
  have hn : 0 ≤ (n + 1 : ℝ) := by norm_cast; omega
  have hsq : ‖x‖ ^ 2 ≤ 1 := by nlinarith [sq_nonneg (‖x‖ - 1), norm_nonneg x]
  have hmul : (n + 1 : ℝ) * (‖x‖ ^ 2 - 1) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hn (by linarith)
  linarith

theorem boundaryCutoff_fderiv_apply
    (n : ℕ) {d : ℕ} (x v : Point d) :
    fderiv ℝ (boundaryCutoff n : Point d → ℝ) x v =
      deriv smoothCutoffProfile
          (1 / 4 + (n + 1 : ℝ) * (‖x‖ ^ 2 - 1)) *
        (2 * (n + 1 : ℝ) * ⟪x, v⟫_ℝ) := by
  let q : Point d → ℝ := fun y ↦
    1 / 4 + (n + 1 : ℝ) * (‖y‖ ^ 2 - 1)
  have hχ : DifferentiableAt ℝ smoothCutoffProfile (q x) :=
    (smoothCutoffProfile_contDiff (n := 1)).differentiable (by simp) (q x)
  have hq : DifferentiableAt ℝ q x := by
    apply (show ContDiff ℝ ∞ q by
      dsimp only [q]
      exact contDiff_const.add
        (contDiff_const.mul ((contDiff_norm_sq ℝ).sub contDiff_const))).differentiable
    simp
  change fderiv ℝ (smoothCutoffProfile ∘ q) x v = _
  rw [fderiv_comp x hχ hq]
  simp only [ContinuousLinearMap.comp_apply, fderiv_eq_deriv_mul]
  congr 1
  dsimp only [q]
  rw [fderiv_const_add, fderiv_const_mul, fderiv_sub_const]
  change (n + 1 : ℝ) *
      (fderiv ℝ (fun y : Point d ↦ ‖y‖ ^ 2) x v) = _
  rw [fderiv_norm_sq]
  · simp [two_smul]
    ring
  · have hdq : ContDiff ℝ 1 (fun y : Point d ↦ ‖y‖ ^ 2 - 1) :=
      (contDiff_norm_sq ℝ).sub contDiff_const
    exact hdq.differentiable one_ne_zero x

theorem boundaryCutoff_integrationByParts
    {d : ℕ} (g : Point d → ℝ) (hg : ContDiff ℝ 1 g)
    (n : ℕ) (v : Point d) :
    (∫ y, boundaryCutoff n y * fderiv ℝ g y v ∂volume) =
      -∫ y, fderiv ℝ (boundaryCutoff n : Point d → ℝ) y v * g y
        ∂volume := by
  have hcut : ContDiff ℝ 1 (boundaryCutoff n : Point d → ℝ) :=
    (boundaryCutoff_contDiff_infty n d).of_le (by simp)
  have hcutComp : HasCompactSupport (boundaryCutoff n : Point d → ℝ) :=
    boundaryCutoff_hasCompactSupport n d
  apply integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
  · apply Continuous.integrable_of_hasCompactSupport
    · exact ((hcut.continuous_fderiv one_ne_zero).clm_apply continuous_const).mul
        hg.continuous
    · exact (hcutComp.fderiv_apply ℝ v).mul_right
  · apply Continuous.integrable_of_hasCompactSupport
    · exact hcut.continuous.mul
        ((hg.continuous_fderiv one_ne_zero).clm_apply continuous_const)
    · exact hcutComp.mul_right
  · exact (hcut.continuous.mul hg.continuous).integrable_of_hasCompactSupport
      hcutComp.mul_right
  · exact fun _ _ ↦ hcut.differentiable one_ne_zero _
  · exact fun _ _ ↦ hg.differentiable one_ne_zero _

theorem tendsto_integral_boundaryCutoff_mul_fderiv
    {d : ℕ} (g : Point d → ℝ) (hg : ContDiff ℝ 1 g)
    (v : Point d) :
    Tendsto
      (fun n ↦ ∫ y, boundaryCutoff n y * fderiv ℝ g y v ∂volume)
      atTop
      (𝓝 (∫ y in closedBall (0 : Point d) 1, fderiv ℝ g y v ∂volume)) := by
  let hfun : Point d → ℝ := fun y ↦ fderiv ℝ g y v
  let K : Set (Point d) := closedBall 0 2
  have hhcont : Continuous hfun :=
    (hg.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hboundInt : Integrable (K.indicator fun y ↦ ‖hfun y‖) volume := by
    rw [integrable_indicator_iff (isClosed_closedBall.measurableSet)]
    exact hhcont.norm.continuousOn.integrableOn_compact
      (isCompact_closedBall (0 : Point d) 2)
  have hmeas (n : ℕ) : AEStronglyMeasurable
      (fun y ↦ boundaryCutoff n y * hfun y) volume :=
    ((boundaryCutoff_contDiff_infty n d).continuous.mul hhcont).aestronglyMeasurable
  have hbound (n : ℕ) : ∀ᵐ y ∂(volume : Measure (Point d)),
      ‖boundaryCutoff n y * hfun y‖ ≤
        K.indicator (fun z ↦ ‖hfun z‖) y := by
    filter_upwards with y
    by_cases hy : y ∈ K
    · rw [indicator_of_mem hy, norm_mul, Real.norm_eq_abs]
      change |smoothCutoffProfile
        (1 / 4 + (n + 1 : ℝ) * (‖y‖ ^ 2 - 1))| * ‖hfun y‖ ≤ ‖hfun y‖
      rw [abs_of_nonneg (smoothCutoffProfile_nonneg _)]
      exact mul_le_of_le_one_left (norm_nonneg (hfun y))
        (smoothCutoffProfile_le_one _)
    · rw [indicator_of_notMem hy]
      have hynorm : 2 < ‖y‖ := by
        simpa [K, mem_closedBall, dist_zero_right, not_le] using hy
      rw [boundaryCutoff_eq_zero_of_two_lt_norm n hynorm, zero_mul, norm_zero]
  have hlim : ∀ᵐ y ∂(volume : Measure (Point d)),
      Tendsto (fun n ↦ boundaryCutoff n y * hfun y) atTop
        (𝓝 ((closedBall (0 : Point d) 1).indicator hfun y)) := by
    filter_upwards with y
    by_cases hy : ‖y‖ ≤ 1
    · have hymem : y ∈ closedBall (0 : Point d) 1 := by
        simpa [mem_closedBall, dist_zero_right]
      simp only [indicator_of_mem hymem]
      simp_rw [boundaryCutoff_eq_one_of_norm_le_one (hx := hy), one_mul]
      exact tendsto_const_nhds
    · have hdelta : 0 < ‖y‖ ^ 2 - 1 := by
        have hy' : 1 < ‖y‖ := lt_of_not_ge hy
        nlinarith [sq_nonneg (‖y‖ - 1), norm_nonneg y]
      obtain ⟨N, hN⟩ := exists_nat_gt ((3 / 4 : ℝ) / (‖y‖ ^ 2 - 1))
      have hymem : y ∉ closedBall (0 : Point d) 1 := by
        simpa [mem_closedBall, dist_zero_right, not_le] using lt_of_not_ge hy
      rw [indicator_of_notMem hymem]
      apply (tendsto_congr' ?_).2 tendsto_const_nhds
      filter_upwards [eventually_ge_atTop N] with n hn
      rw [boundaryCutoff, smoothCutoffProfile_eq_zero_of_one_le, zero_mul]
      have hnR : (N : ℝ) ≤ n := by exact_mod_cast hn
      have hlarge : (3 / 4 : ℝ) ≤ (n + 1) * (‖y‖ ^ 2 - 1) := by
        apply (div_le_iff₀ hdelta).1
        exact (le_of_lt hN).trans <| hnR.trans <| by linarith
      linarith
  have htend := tendsto_integral_of_dominated_convergence
    (K.indicator fun y ↦ ‖hfun y‖) hmeas hboundInt hbound hlim
  simpa only [hfun, integral_indicator isClosed_closedBall.measurableSet] using htend

theorem integral_volume_eq_integral_polar
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {d : ℕ} (hd : 0 < d) (f : Point d → F) :
    (∫ x, f x ∂(volume : Measure (Point d))) =
      ∫ p : sphere (0 : Point d) 1 × Ioi (0 : ℝ),
        f (p.2.1 • p.1.1)
          ∂(volume : Measure (Point d)).toSphere.prod
            (Measure.volumeIoiPow (d - 1)) := by
  letI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  calc
    (∫ x, f x ∂(volume : Measure (Point d))) =
        ∫ x : ({(0 : Point d)}ᶜ : Set (Point d)), f x.1
          ∂Measure.comap Subtype.val volume := by
      rw [integral_subtype_comap (measurableSet_singleton _).compl f,
        restrict_compl_singleton]
    _ = ∫ p : sphere (0 : Point d) 1 × Ioi (0 : ℝ),
        f (p.2.1 • p.1.1)
          ∂(volume : Measure (Point d)).toSphere.prod
            (Measure.volumeIoiPow (d - 1)) := by
      convert
        (volume : Measure (Point d)).measurePreserving_homeomorphUnitSphereProd.integral_comp
          (homeomorphUnitSphereProd (Point d)).measurableEmbedding
          (fun p : sphere (0 : Point d) 1 × Ioi (0 : ℝ) ↦
            f (p.2.1 • p.1.1)) using 1
      · apply integral_congr_ae
        filter_upwards with x
        congr 1
        have hx : (x.1 : Point d) ≠ 0 := by
          intro h
          apply x.2
          simp [h]
        simp [hx]
      · simp [Point]

theorem integral_volumeIoiPow_eq
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (m : ℕ) (f : Ioi (0 : ℝ) → F) :
    (∫ r, f r ∂Measure.volumeIoiPow m) =
      ∫ r in Ioi (0 : ℝ), r ^ m •
        (if hr : 0 < r then f ⟨r, by simpa using hr⟩ else 0) := by
  simp only [Measure.volumeIoiPow, ENNReal.ofReal]
  rw [integral_withDensity_eq_integral_smul (by fun_prop)]
  let fext : ℝ → F := fun r ↦
    Real.toNNReal (r ^ m) •
      (if hr : 0 < r then f ⟨r, by simpa using hr⟩ else 0)
  calc
    (∫ r : Ioi (0 : ℝ), Real.toNNReal (r.1 ^ m) • f r
        ∂Measure.comap Subtype.val volume) =
        ∫ r : Ioi (0 : ℝ), fext r.1
          ∂Measure.comap Subtype.val volume := by
      apply integral_congr_ae
      filter_upwards with r
      have hr : 0 < (r : ℝ) := r.2
      simp [fext, hr, Real.coe_toNNReal _ (pow_nonneg hr.le m)]
    _ = ∫ r in Ioi (0 : ℝ), fext r :=
      integral_subtype_comap measurableSet_Ioi fext
    _ = ∫ r in Ioi (0 : ℝ), r ^ m •
        (if hr : 0 < r then f ⟨r, by simpa using hr⟩ else 0) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro r hr
      have hr' : 0 < r := hr
      simp [fext, hr', NNReal.smul_def,
        max_eq_left (pow_nonneg hr'.le m)]

def radialBoundaryCutoff (n : ℕ) (r : ℝ) : ℝ :=
  smoothCutoffProfile
    (1 / 4 + (n + 1 : ℝ) * (r ^ 2 - 1))

def radialBoundaryKernel (n : ℕ) (r : ℝ) : ℝ :=
  -deriv (radialBoundaryCutoff n) r

def boundaryRadius (n : ℕ) : ℝ :=
  Real.sqrt (1 + 3 / (4 * (n + 1 : ℝ)))

theorem radialBoundaryCutoff_contDiff_infty (n : ℕ) :
    ContDiff ℝ ∞ (radialBoundaryCutoff n) := by
  apply smoothCutoffProfile_contDiff_infty.comp
  exact contDiff_const.add
    (contDiff_const.mul ((contDiff_id.pow 2).sub contDiff_const))

theorem deriv_radialBoundaryCutoff (n : ℕ) (r : ℝ) :
    deriv (radialBoundaryCutoff n) r =
      deriv smoothCutoffProfile
          (1 / 4 + (n + 1 : ℝ) * (r ^ 2 - 1)) *
        (2 * (n + 1 : ℝ) * r) := by
  let q : ℝ → ℝ := fun s ↦
    1 / 4 + (n + 1 : ℝ) * (s ^ 2 - 1)
  have hchi : DifferentiableAt ℝ smoothCutoffProfile (q r) :=
    (smoothCutoffProfile_contDiff (n := 1)).differentiable (by simp) (q r)
  have hq : HasDerivAt q (2 * (n + 1 : ℝ) * r) r := by
    convert (hasDerivAt_const r (1 / 4 : ℝ)).add
      (((hasDerivAt_pow 2 r).sub_const 1).const_mul (n + 1 : ℝ)) using 1 <;>
      simp [q] <;> ring
  change deriv (smoothCutoffProfile ∘ q) r = _
  exact (hchi.hasDerivAt.comp r hq).deriv

theorem radialBoundaryKernel_formula (n : ℕ) (r : ℝ) :
    radialBoundaryKernel n r =
      -deriv smoothCutoffProfile
          (1 / 4 + (n + 1 : ℝ) * (r ^ 2 - 1)) *
        (2 * (n + 1 : ℝ) * r) := by
  rw [radialBoundaryKernel, deriv_radialBoundaryCutoff]
  ring

theorem boundaryRadius_sq (n : ℕ) :
    boundaryRadius n ^ 2 = 1 + 3 / (4 * (n + 1 : ℝ)) := by
  rw [boundaryRadius, Real.sq_sqrt]
  positivity

theorem one_le_boundaryRadius (n : ℕ) : 1 ≤ boundaryRadius n := by
  have hs := boundaryRadius_sq n
  have hr : 0 ≤ boundaryRadius n := Real.sqrt_nonneg _
  nlinarith [show (0 : ℝ) ≤ 3 / (4 * (n + 1 : ℝ)) by positivity]

theorem boundaryRadius_le_two (n : ℕ) : boundaryRadius n ≤ 2 := by
  have hs := boundaryRadius_sq n
  have hr : 0 ≤ boundaryRadius n := Real.sqrt_nonneg _
  have hn : (1 : ℝ) ≤ n + 1 := by norm_cast; omega
  have hfrac : (3 : ℝ) / (4 * (n + 1 : ℝ)) ≤ 3 / 4 := by
    apply (div_le_div_iff₀ (by positivity) (by norm_num)).2
    nlinarith
  nlinarith

theorem radialBoundaryCutoff_one (n : ℕ) :
    radialBoundaryCutoff n 1 = 1 := by
  rw [radialBoundaryCutoff]
  convert smoothCutoffProfile_eq_one_of_le_quarter (u := (1 / 4 : ℝ)) (by norm_num) using 1 <;>
    norm_num

theorem radialBoundaryCutoff_boundaryRadius (n : ℕ) :
    radialBoundaryCutoff n (boundaryRadius n) = 0 := by
  apply smoothCutoffProfile_eq_zero_of_one_le
  rw [boundaryRadius_sq]
  have hn : (0 : ℝ) < n + 1 := by positivity
  field_simp
  norm_num

theorem radialBoundaryKernel_nonneg
    (n : ℕ) {r : ℝ} (hr : 0 ≤ r) :
    0 ≤ radialBoundaryKernel n r := by
  rw [radialBoundaryKernel_formula]
  exact mul_nonneg (neg_nonneg.mpr (deriv_smoothCutoffProfile_nonpos _)) (by positivity)

theorem radialBoundaryKernel_eq_zero_of_pos_of_lt_one
    (n : ℕ) {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    radialBoundaryKernel n r = 0 := by
  rw [radialBoundaryKernel_formula,
    deriv_smoothCutoffProfile_eq_zero_of_lt_quarter]
  · simp
  · have hn : (0 : ℝ) < n + 1 := by positivity
    have hrsq : r ^ 2 < 1 := by nlinarith [sq_nonneg (r - 1)]
    nlinarith

theorem radialBoundaryKernel_eq_zero_of_boundaryRadius_lt
    (n : ℕ) {r : ℝ} (hr : boundaryRadius n < r) :
    radialBoundaryKernel n r = 0 := by
  rw [radialBoundaryKernel_formula,
    deriv_smoothCutoffProfile_eq_zero_of_one_lt]
  · simp
  · have hn : (0 : ℝ) < n + 1 := by positivity
    have hR0 : 0 ≤ boundaryRadius n := Real.sqrt_nonneg _
    have hrsq : boundaryRadius n ^ 2 < r ^ 2 := by nlinarith
    rw [boundaryRadius_sq] at hrsq
    have hcancel : (n + 1 : ℝ) * (3 / (4 * (n + 1 : ℝ))) = 3 / 4 := by
      field_simp
    nlinarith

theorem radialBoundaryKernel_continuous (n : ℕ) :
    Continuous (radialBoundaryKernel n) := by
  exact ((radialBoundaryCutoff_contDiff_infty n).of_le (by simp)).continuous_deriv_one.neg

theorem radialBoundaryKernel_intervalIntegrable (n : ℕ) :
    IntervalIntegrable (radialBoundaryKernel n) volume 1 (boundaryRadius n) := by
  exact Continuous.intervalIntegrable (μ := volume)
    (radialBoundaryKernel_continuous n) 1 (boundaryRadius n)

theorem integral_radialBoundaryKernel (n : ℕ) :
    (∫ r in (1 : ℝ)..boundaryRadius n, radialBoundaryKernel n r) = 1 := by
  change (∫ r in (1 : ℝ)..boundaryRadius n,
    -deriv (radialBoundaryCutoff n) r) = 1
  rw [intervalIntegral.integral_neg]
  rw [intervalIntegral.integral_deriv_of_contDiffOn_Icc
    ((radialBoundaryCutoff_contDiff_infty n).of_le (by simp)).contDiffOn
    (one_le_boundaryRadius n)]
  rw [radialBoundaryCutoff_boundaryRadius, radialBoundaryCutoff_one]
  norm_num

theorem boundaryRadius_tendsto_one :
    Tendsto boundaryRadius atTop (𝓝 1) := by
  have hbase : Tendsto (fun n : ℕ ↦ (1 : ℝ) / (n + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hfrac : Tendsto
      (fun n : ℕ ↦ (3 : ℝ) / (4 * (n + 1 : ℝ))) atTop (𝓝 0) := by
    convert hbase.const_mul (3 / 4 : ℝ) using 1
    · funext n
      field_simp
    · norm_num
  have hin : Tendsto
      (fun n : ℕ ↦ 1 + (3 : ℝ) / (4 * (n + 1 : ℝ))) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.add hfrac
  have hsqrt := Real.continuous_sqrt.continuousAt.tendsto.comp hin
  convert hsqrt using 1
  · rfl
  · norm_num

theorem tendsto_intervalIntegral_mul_radialBoundaryKernel
    (A : ℝ → ℝ) (hA : Continuous A) :
    Tendsto
      (fun n ↦ ∫ r in (1 : ℝ)..boundaryRadius n,
        A r * radialBoundaryKernel n r)
      atTop (𝓝 (A 1)) := by
  have hex : ∀ n : ℕ, ∃ c : ℝ,
      c ∈ Icc (1 : ℝ) (boundaryRadius n) ∧
        (∫ r in (1 : ℝ)..boundaryRadius n,
          A r * radialBoundaryKernel n r) = A c := by
    intro n
    obtain ⟨c, hc, heq⟩ :=
      exists_eq_const_mul_intervalIntegral_of_nonneg
        (hA.continuousOn)
        (radialBoundaryKernel_intervalIntegrable n)
        (fun r hr ↦ radialBoundaryKernel_nonneg n (by
          have hr' : r ∈ Ioc (1 : ℝ) (boundaryRadius n) := by
            simpa [uIoc_of_le (one_le_boundaryRadius n)] using hr
          linarith [hr'.1]))
    refine ⟨c, ?_, ?_⟩
    · simpa [uIcc_of_le (one_le_boundaryRadius n)] using hc
    · simpa [integral_radialBoundaryKernel n] using heq
  choose c hc hEq using hex
  have hc_tend : Tendsto c atTop (𝓝 1) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
      tendsto_const_nhds boundaryRadius_tendsto_one
    · exact Eventually.of_forall fun n ↦ (hc n).1
    · exact Eventually.of_forall fun n ↦ (hc n).2
  exact (hA.tendsto 1 |>.comp hc_tend).congr'
    (Eventually.of_forall fun n ↦ (hEq n).symm)

theorem integral_Ioi_mul_radialBoundaryKernel_eq_interval
    (n : ℕ) (A : ℝ → ℝ) :
    (∫ r in Ioi (0 : ℝ), A r * radialBoundaryKernel n r) =
      ∫ r in (1 : ℝ)..boundaryRadius n,
        A r * radialBoundaryKernel n r := by
  calc
    (∫ r in Ioi (0 : ℝ), A r * radialBoundaryKernel n r) =
        ∫ r in Icc (1 : ℝ) (boundaryRadius n),
          A r * radialBoundaryKernel n r := by
      apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
      · intro r hr
        exact (by linarith [hr.1] : (0 : ℝ) < r)
      · intro r hr
        rcases hr with ⟨hr0, hrnot⟩
        rw [mem_Icc, not_and_or, not_le] at hrnot
        rcases hrnot with hr1 | hrR
        · rw [radialBoundaryKernel_eq_zero_of_pos_of_lt_one n hr0 hr1,
            mul_zero]
        · rw [radialBoundaryKernel_eq_zero_of_boundaryRadius_lt n (lt_of_not_ge hrR),
            mul_zero]
    _ = ∫ r in Ioc (1 : ℝ) (boundaryRadius n),
          A r * radialBoundaryKernel n r := integral_Icc_eq_integral_Ioc
    _ = ∫ r in (1 : ℝ)..boundaryRadius n,
          A r * radialBoundaryKernel n r := by
      rw [intervalIntegral.integral_of_le (one_le_boundaryRadius n)]

def polarBoundaryAverage {d : ℕ} (g : Point d → ℝ) (v : Point d)
    (n : ℕ) (u : sphere (0 : Point d) 1) : ℝ :=
  ∫ r in (1 : ℝ)..boundaryRadius n,
    (r ^ (d - 1) * g (r • (u : Point d)) * ⟪(u : Point d), v⟫_ℝ) *
      radialBoundaryKernel n r

theorem polarBoundaryAverage_continuous
    {d : ℕ} (g : Point d → ℝ) (hg : Continuous g)
    (v : Point d) (n : ℕ) :
    Continuous (polarBoundaryAverage g v n) := by
  let H : sphere (0 : Point d) 1 → ℝ → ℝ := fun u r ↦
    (r ^ (d - 1) * g (r • (u : Point d)) * ⟪(u : Point d), v⟫_ℝ) *
      radialBoundaryKernel n r
  have hH : Continuous H.uncurry := by
    dsimp only [H, Function.uncurry_apply_pair]
    apply Continuous.mul
    · fun_prop
    · exact (radialBoundaryKernel_continuous n).comp continuous_snd
  have hint : Continuous
      (fun u ↦ ∫ r in Icc (1 : ℝ) (boundaryRadius n), H u r) :=
    continuous_parametric_integral_of_continuous hH isCompact_Icc
  apply hint.congr
  intro u
  rw [polarBoundaryAverage, intervalIntegral.integral_of_le
    (one_le_boundaryRadius n), ← integral_Icc_eq_integral_Ioc]

theorem tendsto_polarBoundaryAverage
    {d : ℕ} (g : Point d → ℝ) (hg : Continuous g)
    (v : Point d) (u : sphere (0 : Point d) 1) :
    Tendsto (fun n ↦ polarBoundaryAverage g v n u) atTop
      (𝓝 (g u * ⟪(u : Point d), v⟫_ℝ)) := by
  let A : ℝ → ℝ := fun r ↦
    r ^ (d - 1) * g (r • (u : Point d)) * ⟪(u : Point d), v⟫_ℝ
  have hA : Continuous A := by
    dsimp only [A]
    fun_prop
  have ht := tendsto_intervalIntegral_mul_radialBoundaryKernel A hA
  simpa [polarBoundaryAverage, A] using ht

theorem tendsto_integral_polarBoundaryAverage
    {d : ℕ} (hd : 0 < d) (g : Point d → ℝ) (hg : Continuous g)
    (v : Point d) :
    Tendsto
      (fun n ↦ ∫ u, polarBoundaryAverage g v n u
        ∂(volume : Measure (Point d)).toSphere)
      atTop
      (𝓝 (∫ u : sphere (0 : Point d) 1,
        g u * ⟪(u : Point d), v⟫_ℝ
          ∂(volume : Measure (Point d)).toSphere)) := by
  let H : sphere (0 : Point d) 1 × ℝ → ℝ := fun p ↦
    p.2 ^ (d - 1) * g (p.2 • (p.1 : Point d)) *
      ⟪(p.1 : Point d), v⟫_ℝ
  have hH : Continuous H := by
    dsimp only [H]
    fun_prop
  obtain ⟨B, hB⟩ :=
    (isCompact_univ.prod (isCompact_Icc : IsCompact (Icc (1 : ℝ) 2))).bddAbove_image
      hH.norm.continuousOn
  have hbound (n : ℕ) (u : sphere (0 : Point d) 1) :
      ‖polarBoundaryAverage g v n u‖ ≤ B := by
    let A : ℝ → ℝ := fun r ↦ H (u, r)
    have hA : Continuous A := hH.comp (by fun_prop)
    obtain ⟨c, hc, heq⟩ :=
      exists_eq_const_mul_intervalIntegral_of_nonneg
        hA.continuousOn
        (radialBoundaryKernel_intervalIntegrable n)
        (fun r hr ↦ radialBoundaryKernel_nonneg n (by
          have hr' : r ∈ Ioc (1 : ℝ) (boundaryRadius n) := by
            simpa [uIoc_of_le (one_le_boundaryRadius n)] using hr
          linarith [hr'.1]))
    have hc' : c ∈ Icc (1 : ℝ) 2 := by
      have hcI : c ∈ Icc (1 : ℝ) (boundaryRadius n) := by
        simpa [uIcc_of_le (one_le_boundaryRadius n)] using hc
      exact ⟨hcI.1, hcI.2.trans (boundaryRadius_le_two n)⟩
    have havg : polarBoundaryAverage g v n u = A c := by
      simpa [polarBoundaryAverage, A, H, integral_radialBoundaryKernel n] using heq
    rw [havg]
    exact hB (mem_image_of_mem _ ⟨mem_univ u, hc'⟩)
  apply tendsto_integral_of_dominated_convergence
    (fun _ : sphere (0 : Point d) 1 ↦ B)
  · exact fun n ↦ (polarBoundaryAverage_continuous g hg v n).aestronglyMeasurable
  · exact integrable_const B
  · exact fun n ↦ Eventually.of_forall (hbound n)
  · exact Eventually.of_forall fun u ↦ tendsto_polarBoundaryAverage g hg v u

theorem integrable_polar_comp
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {d : ℕ} (hd : 0 < d) (f : Point d → F)
    (hf : Integrable f (volume : Measure (Point d))) :
    Integrable
      (fun p : sphere (0 : Point d) 1 × Ioi (0 : ℝ) ↦
        f (p.2.1 • p.1.1))
      ((volume : Measure (Point d)).toSphere.prod
        (Measure.volumeIoiPow (d - 1))) := by
  letI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  have hsub : Integrable
      (f ∘ (↑) : ({(0 : Point d)}ᶜ : Set (Point d)) → F)
      (Measure.comap Subtype.val volume) :=
    (integrableOn_iff_comap_subtypeVal
      (f := f) (μ := volume) (measurableSet_singleton _).compl).mp hf.integrableOn
  have hequiv :=
    (volume : Measure (Point d)).measurePreserving_homeomorphUnitSphereProd.integrable_comp_emb
      (homeomorphUnitSphereProd (Point d)).measurableEmbedding
      (g := fun p : sphere (0 : Point d) 1 × Ioi (0 : ℝ) ↦
        f (p.2.1 • p.1.1))
  have hsource : Integrable
      ((fun p : sphere (0 : Point d) 1 × Ioi (0 : ℝ) ↦
        f (p.2.1 • p.1.1)) ∘ homeomorphUnitSphereProd (Point d))
      (Measure.comap Subtype.val volume) := by
    convert hsub using 1
    funext x
    have hx : (x.1 : Point d) ≠ 0 := by
      intro h
      apply x.2
      simp [h]
    simp [Function.comp_def, hx]
  simpa [Point] using hequiv.mp hsource

theorem neg_integral_boundaryCutoff_fderiv_mul_eq_polarBoundaryAverage
    {d : ℕ} (hd : 0 < d) (g : Point d → ℝ) (hg : Continuous g)
    (v : Point d) (n : ℕ) :
    -(∫ y, fderiv ℝ (boundaryCutoff n : Point d → ℝ) y v * g y
        ∂volume) =
      ∫ u, polarBoundaryAverage g v n u
        ∂(volume : Measure (Point d)).toSphere := by
  let q : Point d → ℝ := fun y ↦
    -(fderiv ℝ (boundaryCutoff n : Point d → ℝ) y v * g y)
  have hqcont : Continuous q := by
    dsimp only [q]
    exact (((boundaryCutoff_contDiff_infty n d).of_le (by simp)).continuous_fderiv
      one_ne_zero |>.clm_apply continuous_const |>.mul hg).neg
  have hqint : Integrable q (volume : Measure (Point d)) := by
    apply Continuous.integrable_of_hasCompactSupport hqcont
    exact ((boundaryCutoff_hasCompactSupport n d).fderiv_apply ℝ v).mul_right.neg
  calc
    -(∫ y, fderiv ℝ (boundaryCutoff n : Point d → ℝ) y v * g y
        ∂volume) = ∫ y, q y ∂volume := by
      rw [integral_neg]
    _ = ∫ p : sphere (0 : Point d) 1 × Ioi (0 : ℝ),
        q (p.2.1 • p.1.1)
          ∂(volume : Measure (Point d)).toSphere.prod
            (Measure.volumeIoiPow (d - 1)) :=
      integral_volume_eq_integral_polar hd q
    _ = ∫ u : sphere (0 : Point d) 1,
        ∫ r : Ioi (0 : ℝ), q (r.1 • (u : Point d))
          ∂Measure.volumeIoiPow (d - 1)
          ∂(volume : Measure (Point d)).toSphere := by
      rw [integral_prod _ (integrable_polar_comp hd q hqint)]
    _ = ∫ u, polarBoundaryAverage g v n u
        ∂(volume : Measure (Point d)).toSphere := by
      apply integral_congr_ae
      filter_upwards with u
      rw [integral_volumeIoiPow_eq]
      change (∫ r in Ioi (0 : ℝ), r ^ (d - 1) •
          (if hr : 0 < r then q (r • (u : Point d)) else 0)) =
        polarBoundaryAverage g v n u
      calc
        (∫ r in Ioi (0 : ℝ), r ^ (d - 1) •
            (if hr : 0 < r then q (r • (u : Point d)) else 0)) =
            ∫ r in Ioi (0 : ℝ),
              (r ^ (d - 1) * g (r • (u : Point d)) *
                ⟪(u : Point d), v⟫_ℝ) * radialBoundaryKernel n r := by
          apply setIntegral_congr_fun measurableSet_Ioi
          intro r hr
          have hr0 : 0 < r := hr
          have hu : ‖(u : Point d)‖ = 1 := by
            simpa [mem_sphere, dist_zero_right] using u.property
          simp only [hr0, ↓reduceDIte, q, boundaryCutoff_fderiv_apply,
            radialBoundaryKernel_formula, smul_eq_mul]
          rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr0, hu]
          simp only [mul_one, real_inner_smul_left]
          ring
        _ = polarBoundaryAverage g v n u := by
          rw [integral_Ioi_mul_radialBoundaryKernel_eq_interval]
          rfl

theorem integral_closedBall_fderiv_eq_integral_toSphere_mul_inner
    {d : ℕ} (hd : 0 < d) (g : Point d → ℝ) (hg : ContDiff ℝ 1 g)
    (v : Point d) :
    (∫ y in closedBall (0 : Point d) 1, fderiv ℝ g y v ∂volume) =
      ∫ u : sphere (0 : Point d) 1,
        g u * ⟪(u : Point d), v⟫_ℝ
          ∂(volume : Measure (Point d)).toSphere := by
  let a : ℕ → ℝ := fun n ↦
    ∫ y, boundaryCutoff n y * fderiv ℝ g y v ∂volume
  let b : ℕ → ℝ := fun n ↦
    ∫ u, polarBoundaryAverage g v n u
      ∂(volume : Measure (Point d)).toSphere
  have hab : a = b := by
    funext n
    exact (boundaryCutoff_integrationByParts g hg n v).trans
      (neg_integral_boundaryCutoff_fderiv_mul_eq_polarBoundaryAverage
        hd g hg.continuous v n)
  have ha : Tendsto a atTop
      (𝓝 (∫ y in closedBall (0 : Point d) 1,
        fderiv ℝ g y v ∂volume)) :=
    tendsto_integral_boundaryCutoff_mul_fderiv g hg v
  have hb : Tendsto b atTop
      (𝓝 (∫ u : sphere (0 : Point d) 1,
        g u * ⟪(u : Point d), v⟫_ℝ
          ∂(volume : Measure (Point d)).toSphere)) :=
    tendsto_integral_polarBoundaryAverage hd g hg.continuous v
  exact tendsto_nhds_unique ha (hab ▸ hb)

theorem closedBall_ae_eq_ball_volume {d : ℕ} (hd : 0 < d) :
    closedBall (0 : Point d) 1 =ᵐ[(volume : Measure (Point d))]
      ball 0 1 := by
  letI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  apply (ae_eq_of_subset_of_measure_ge ball_subset_closedBall ?_
    measurableSet_ball.nullMeasurableSet measure_closedBall_lt_top.ne).symm
  rw [Measure.addHaar_closedBall_eq_addHaar_ball volume]

theorem contDiff_one_gradient_continuous
    {d : ℕ} {g : Point d → ℝ} (hg : ContDiff ℝ 1 g) :
    Continuous (∇ g) := by
  change Continuous (fun x ↦
    (InnerProductSpace.toDual ℝ (Point d)).symm (fderiv ℝ g x))
  exact (InnerProductSpace.toDual ℝ (Point d)).symm.continuous.comp
    (hg.continuous_fderiv one_ne_zero)

theorem integral_closedBall_gradient_eq_integral_toSphere_smul
    {d : ℕ} (hd : 0 < d) (g : Point d → ℝ) (hg : ContDiff ℝ 1 g) :
    (∫ y in closedBall (0 : Point d) 1, ∇ g y ∂volume) =
      ∫ u : sphere (0 : Point d) 1,
        g u • (u : Point d)
          ∂(volume : Measure (Point d)).toSphere := by
  have hgradInt : IntegrableOn (∇ g) (closedBall (0 : Point d) 1) volume :=
    (contDiff_one_gradient_continuous hg).continuousOn.integrableOn_compact
      (isCompact_closedBall (0 : Point d) 1)
  have hsphereInt : Integrable
      (fun u : sphere (0 : Point d) 1 ↦ g u • (u : Point d))
      (volume : Measure (Point d)).toSphere := by
    rw [← integrableOn_univ]
    exact (show Continuous (fun u : sphere (0 : Point d) 1 ↦
      g u • (u : Point d)) by fun_prop).continuousOn.integrableOn_compact
        isCompact_univ
  apply ext_inner_left ℝ
  intro v
  rw [← integral_inner hgradInt v, ← integral_inner hsphereInt v]
  calc
    (∫ y in closedBall (0 : Point d) 1, ⟪v, ∇ g y⟫_ℝ ∂volume) =
        ∫ y in closedBall (0 : Point d) 1, fderiv ℝ g y v ∂volume := by
      apply setIntegral_congr_fun measurableSet_closedBall
      intro y _
      change ⟪v, ∇ g y⟫_ℝ = fderiv ℝ g y v
      rw [real_inner_comm, inner_gradient_left]
    _ = ∫ u : sphere (0 : Point d) 1,
        g u * ⟪(u : Point d), v⟫_ℝ
          ∂(volume : Measure (Point d)).toSphere :=
      integral_closedBall_fderiv_eq_integral_toSphere_mul_inner hd g hg v
    _ = ∫ u : sphere (0 : Point d) 1,
        ⟪v, g u • (u : Point d)⟫_ℝ
          ∂(volume : Measure (Point d)).toSphere := by
      apply integral_congr_ae
      filter_upwards with u
      rw [real_inner_smul_right, real_inner_comm (u : Point d) v]

theorem integral_ball_gradient_eq_integral_toSphere_smul
    {d : ℕ} (hd : 0 < d) (g : Point d → ℝ) (hg : ContDiff ℝ 1 g) :
    (∫ y in ball (0 : Point d) 1, ∇ g y ∂volume) =
      ∫ u : sphere (0 : Point d) 1,
        g u • (u : Point d)
          ∂(volume : Measure (Point d)).toSphere := by
  rw [← integral_closedBall_gradient_eq_integral_toSphere_smul hd g hg]
  exact setIntegral_congr_set (closedBall_ae_eq_ball_volume hd).symm

theorem integral_uniformUnitBall_eq_mass_inv_smul
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (d : ℕ) (f : Point d → F) :
    (∫ x, f x ∂(uniformUnitBall d : Measure (Point d))) =
      ((unitBallFiniteMeasure d).mass⁻¹ : ℝ) •
        ∫ x in ball (0 : Point d) 1, f x ∂volume := by
  rw [show (uniformUnitBall d : Measure (Point d)) =
      (unitBallFiniteMeasure d).mass⁻¹ •
        (unitBallFiniteMeasure d : Measure (Point d)) by
    exact (unitBallFiniteMeasure d).toMeasure_normalize_eq_of_nonzero
      (unitBallFiniteMeasure_ne_zero d)]
  rw [integral_smul_nnreal_measure]
  rfl

theorem integral_uniformUnitSphereSubtype_eq_mass_inv_smul
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {d : ℕ} (hd : 0 < d) (f : sphere (0 : Point d) 1 → F) :
    (∫ u, f u
        ∂(uniformUnitSphereSubtype d hd :
          Measure (sphere (0 : Point d) 1))) =
      ((unitSphereFiniteMeasure d).mass⁻¹ : ℝ) •
        ∫ u, f u ∂(volume : Measure (Point d)).toSphere := by
  letI : Nonempty (sphere (0 : Point d) 1) := unitSphere_nonempty hd
  rw [show (uniformUnitSphereSubtype d hd :
      Measure (sphere (0 : Point d) 1)) =
      (unitSphereFiniteMeasure d).mass⁻¹ •
        (unitSphereFiniteMeasure d : Measure (sphere (0 : Point d) 1)) by
    exact (unitSphereFiniteMeasure d).toMeasure_normalize_eq_of_nonzero
      (unitSphereFiniteMeasure_ne_zero hd)]
  rw [integral_smul_nnreal_measure]
  rfl

theorem integral_uniformUnitSphere_eq_subtype
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {d : ℕ} (hd : 0 < d) (f : Point d → F) (hf : Continuous f) :
    (∫ u, f u ∂(uniformUnitSphere d hd : Measure (Point d))) =
      ∫ u : sphere (0 : Point d) 1, f u
        ∂(uniformUnitSphereSubtype d hd :
          Measure (sphere (0 : Point d) 1)) := by
  rw [uniformUnitSphere, ProbabilityMeasure.toMeasure_map]
  exact integral_map_of_stronglyMeasurable (by fun_prop) hf.stronglyMeasurable

theorem unitSphere_mass_eq_dim_mul_unitBall_mass
    {d : ℕ} (hd : 0 < d) :
    ((unitSphereFiniteMeasure d).mass : ℝ) =
      (d : ℝ) * (unitBallFiniteMeasure d).mass := by
  letI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  have hs : ((unitSphereFiniteMeasure d).mass : ℝ) =
      (volume : Measure (Point d)).toSphere.real univ := by
    have h := congrArg ENNReal.toReal
      (FiniteMeasure.ennreal_mass (μ := unitSphereFiniteMeasure d))
    simpa [unitSphereFiniteMeasure, measureReal_def] using h
  have hb : ((unitBallFiniteMeasure d).mass : ℝ) =
      volume.real (ball (0 : Point d) 1) := by
    have h := congrArg ENNReal.toReal
      (FiniteMeasure.ennreal_mass (μ := unitBallFiniteMeasure d))
    simpa [unitBallFiniteMeasure, measureReal_def] using h
  rw [hs, hb]
  simpa [Point] using
    (Measure.toSphere_real_apply_univ (μ := (volume : Measure (Point d))))

theorem integral_uniformUnitSphere_dim_smul_eq_uniformUnitBall_gradient
    {d : ℕ} (hd : 0 < d) (g : Point d → ℝ) (hg : ContDiff ℝ 1 g) :
    (∫ u, (d : ℝ) • (g u • u)
        ∂(uniformUnitSphere d hd : Measure (Point d))) =
      ∫ y, ∇ g y ∂(uniformUnitBall d : Measure (Point d)) := by
  have hcont : Continuous (fun u : Point d ↦ (d : ℝ) • (g u • u)) := by
    fun_prop
  rw [integral_uniformUnitSphere_eq_subtype hd _ hcont]
  rw [integral_uniformUnitSphereSubtype_eq_mass_inv_smul hd]
  rw [integral_smul]
  rw [integral_uniformUnitBall_eq_mass_inv_smul]
  rw [integral_ball_gradient_eq_integral_toSphere_smul hd g hg]
  have hm : ((unitBallFiniteMeasure d).mass : ℝ) ≠ 0 := by
    exact_mod_cast
      ((unitBallFiniteMeasure d).mass_nonzero_iff.mpr
        (unitBallFiniteMeasure_ne_zero d))
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hd)
  rw [unitSphere_mass_eq_dim_mul_unitBall_mass hd]
  rw [smul_smul]
  congr 1
  field_simp

theorem gradient_affine_smul
    {d : ℕ} (f : Point d → ℝ) (hf : ContDiff ℝ 1 f)
    (x : Point d) (r : ℝ) (y : Point d) :
    ∇ (fun z ↦ f (x + r • z)) y = r • ∇ f (x + r • y) := by
  let q : Point d → Point d := fun z ↦ x + r • z
  have hf' : DifferentiableAt ℝ f (q y) :=
    hf.differentiable one_ne_zero (q y)
  have hq : DifferentiableAt ℝ q y := by
    dsimp only [q]
    fun_prop
  change ∇ (f ∘ q) y = r • ∇ f (q y)
  apply ext_inner_right ℝ
  intro v
  rw [inner_gradient_left, real_inner_smul_left]
  rw [fderiv_comp y hf' hq]
  have hqf : fderiv ℝ q y v = r • v := by
    dsimp only [q]
    rw [fderiv_const_add]
    change fderiv ℝ (fun z : Point d ↦ r • z) y v = r • v
    have hlin : HasFDerivAt (fun z : Point d ↦ r • z)
        (r • ContinuousLinearMap.id ℝ (Point d)) y :=
      (hasFDerivAt_id y).const_smul r
    rw [hlin.fderiv]
    simp
  rw [ContinuousLinearMap.comp_apply, hqf, ← inner_gradient_left,
    real_inner_smul_right]

theorem continuous_integrable_uniformUnitSphere
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {d : ℕ} (hd : 0 < d) (f : Point d → F) (hf : Continuous f) :
    Integrable f (uniformUnitSphere d hd : Measure (Point d)) := by
  rw [uniformUnitSphere, ProbabilityMeasure.toMeasure_map]
  apply (integrable_map_measure hf.aestronglyMeasurable (by fun_prop)).2
  rw [← integrableOn_univ]
  exact (hf.comp continuous_subtype_val).continuousOn.integrableOn_compact
    isCompact_univ

end

end NoisyZO
