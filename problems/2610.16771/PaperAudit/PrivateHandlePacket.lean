import Mathlib

namespace PaperAudit.PrivateHandlePacket


section LegacyAnalyticPrefix







open scoped Topology ContDiff NNReal

namespace FlatCubic

structure Profile where
  chi : ℝ → ℝ
  smooth : ContDiff ℝ ∞ chi
  mono : Monotone chi
  nonneg : ∀ x : ℝ, 0 ≤ chi x
  le_one : ∀ x : ℝ, chi x ≤ 1
  flat : ∀ x : ℝ, x ≤ 1 / 2 → chi x = 0
  saturated : ∀ x : ℝ, 1 ≤ x → chi x = 1

noncomputable def canonicalProfile : Profile where
  chi := fun x => Real.smoothTransition (2 * x - 1)
  smooth := by fun_prop
  mono := by
    intro x y hxy
    exact Real.smoothTransition.monotone (by linarith)
  nonneg := fun x => Real.smoothTransition.nonneg _
  le_one := fun x => Real.smoothTransition.le_one _
  flat := by
    intro x hx
    exact Real.smoothTransition.zero_of_nonpos (by linarith)
  saturated := by
    intro x hx
    exact Real.smoothTransition.one_of_one_le (by linarith)

noncomputable def rawp (P : Profile) (delta Delta t : ℝ) : ℝ :=
  if t ≤ Delta then t ^ 2 * P.chi (t / delta) else 2 * Delta * t - Delta ^ 2

noncomputable def primitive (P : Profile) (delta Delta t : ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..t, rawp P delta Delta s

noncomputable def edge (P : Profile) (delta Delta t : ℝ) : ℝ :=
  primitive P delta Delta |t|

theorem edge_even (P : Profile) (delta Delta t : ℝ) :
    edge P delta Delta (-t) = edge P delta Delta t := by
  simp only [edge, abs_neg]

theorem rawp_flat (P : Profile) (delta Delta t : ℝ)
    (hd : 0 < delta) (hdD : delta ≤ Delta) (ht : t ≤ delta / 2) :
    rawp P delta Delta t = 0 := by
  have htD : t ≤ Delta := by linarith
  have harg : t / delta ≤ 1 / 2 := by
    apply (div_le_iff₀ hd).mpr
    linarith only [ht]
  simp only [rawp, if_pos htD, P.flat _ harg, mul_zero]

theorem rawp_nonneg (P : Profile) (delta Delta t : ℝ)
    (hD : 0 ≤ Delta) (ht : 0 ≤ t) : 0 ≤ rawp P delta Delta t := by
  by_cases htd : t ≤ Delta
  · simp only [rawp, if_pos htd]
    exact mul_nonneg (sq_nonneg _) (P.nonneg _)
  · simp only [rawp, if_neg htd]
    have hDt : Delta < t := lt_of_not_ge htd
    nlinarith only [hD, ht, hDt]

theorem rawp_le_square (P : Profile) (delta Delta t : ℝ) :
    rawp P delta Delta t ≤ t ^ 2 := by
  by_cases htd : t ≤ Delta
  · simp only [rawp, if_pos htd]
    exact mul_le_of_le_one_right (sq_nonneg _) (P.le_one _)
  · simp only [rawp, if_neg htd]
    nlinarith only [sq_nonneg (t - Delta)]

theorem rawp_monotoneOn_nonnegative (P : Profile) (delta Delta : ℝ)
    (hd : 0 < delta) (hdD : delta ≤ Delta) :
    MonotoneOn (rawp P delta Delta) (Set.Ici 0) := by
  intro x hx y hy hxy
  have hx0 : 0 ≤ x := hx
  have hy0 : 0 ≤ y := hy
  have hD : 0 < Delta := lt_of_lt_of_le hd hdD
  by_cases hyD : y ≤ Delta
  · have hxD : x ≤ Delta := le_trans hxy hyD
    simp only [rawp, if_pos hyD, if_pos hxD]
    have hsq : x ^ 2 ≤ y ^ 2 := by nlinarith only [hx0, hy0, hxy]
    have hchi : P.chi (x / delta) ≤ P.chi (y / delta) :=
      P.mono (div_le_div_of_nonneg_right hxy (le_of_lt hd))
    exact le_trans (mul_le_mul_of_nonneg_right hsq (P.nonneg _))
      (mul_le_mul_of_nonneg_left hchi (sq_nonneg y))
  · have hDy : Delta < y := lt_of_not_ge hyD
    by_cases hxD : x ≤ Delta
    · have hsq : x ^ 2 ≤ Delta ^ 2 := by nlinarith only [hx0, hD, hxD]
      have hp := rawp_le_square P delta Delta x
      simp only [rawp, if_neg hyD]
      have hlast : Delta ^ 2 ≤ 2 * Delta * y - Delta ^ 2 := by
        nlinarith only [hD, hDy]
      exact le_trans hp (le_trans hsq hlast)
    · simp only [rawp, if_neg hyD, if_neg hxD]
      nlinarith only [hxy, hD]

theorem rawp_continuous (P : Profile) (delta Delta : ℝ)
    (hd : 0 < delta) (hdD : delta ≤ Delta) : Continuous (rawp P delta Delta) := by
  have hchi : Continuous P.chi := P.smooth.continuous
  have hl : Continuous (fun t : ℝ => t ^ 2 * P.chi (t / delta)) := by fun_prop
  have hr : Continuous (fun t : ℝ => 2 * Delta * t - Delta ^ 2) := by fun_prop
  apply hl.if_le hr continuous_id continuous_const
  intro t ht
  change t = Delta at ht
  subst t
  have harg : 1 ≤ Delta / delta := by
    apply (le_div_iff₀ hd).mpr
    simpa only [one_mul] using hdD
  rw [P.saturated _ harg]
  ring

theorem primitive_hasDerivAt (P : Profile) (delta Delta t : ℝ)
    (hd : 0 < delta) (hdD : delta ≤ Delta) :
    HasDerivAt (primitive P delta Delta) (rawp P delta Delta t) t := by
  have hcont := rawp_continuous P delta Delta hd hdD
  exact intervalIntegral.integral_hasDerivAt_right (hcont.intervalIntegrable 0 t)
    hcont.aestronglyMeasurable.stronglyMeasurableAtFilter hcont.continuousAt

theorem edge_flat_value (P : Profile) (delta Delta t : ℝ)
    (hd : 0 < delta) (hdD : delta ≤ Delta) (ht : |t| ≤ delta / 2) :
    edge P delta Delta t = 0 := by
  unfold edge primitive
  have hz : Set.EqOn (rawp P delta Delta) (fun _ : ℝ => 0) (Set.uIcc 0 |t|) := by
    intro s hs
    rw [Set.uIcc_of_le (abs_nonneg t)] at hs
    exact rawp_flat P delta Delta s hd hdD (le_trans hs.2 ht)
  rw [intervalIntegral.integral_congr hz]
  simp

theorem edge_hasDerivAt_pos (P : Profile) (delta Delta t : ℝ)
    (hd : 0 < delta) (hdD : delta ≤ Delta) (ht : 0 < t) :
    HasDerivAt (edge P delta Delta) (rawp P delta Delta t) t := by
  have he : edge P delta Delta =ᶠ[𝓝 t] primitive P delta Delta := by
    filter_upwards [eventually_gt_nhds ht] with s hs
    simp only [edge, abs_of_pos hs]
  exact (primitive_hasDerivAt P delta Delta t hd hdD).congr_of_eventuallyEq he

theorem edge_deriv_zero_interior (P : Profile) (delta Delta t : ℝ)
    (hd : 0 < delta) (hdD : delta ≤ Delta) (ht : |t| < delta / 2) :
    deriv (edge P delta Delta) t = 0 := by
  have hopen : IsOpen {s : ℝ | |s| < delta / 2} := isOpen_lt continuous_abs continuous_const
  have he : edge P delta Delta =ᶠ[𝓝 t] (fun _ => 0) := by
    filter_upwards [hopen.mem_nhds ht] with s hs
    exact edge_flat_value P delta Delta s hd hdD (le_of_lt hs)
  rw [he.deriv_eq]
  simp

theorem edge_second_deriv_zero_interior (P : Profile) (delta Delta t : ℝ)
    (hd : 0 < delta) (hdD : delta ≤ Delta) (ht : |t| < delta / 2) :
    deriv (deriv (edge P delta Delta)) t = 0 := by
  have hopen : IsOpen {s : ℝ | |s| < delta / 2} := isOpen_lt continuous_abs continuous_const
  have he : deriv (edge P delta Delta) =ᶠ[𝓝 t] (fun _ => 0) := by
    filter_upwards [hopen.mem_nhds ht] with s hs
    exact edge_deriv_zero_interior P delta Delta s hd hdD hs
  rw [he.deriv_eq]
  simp

theorem edge_deriv_nonneg_le_square_nonnegative (P : Profile) (delta Delta t : ℝ)
    (hd : 0 < delta) (hdD : delta ≤ Delta) (ht : 0 ≤ t) :
    0 ≤ deriv (edge P delta Delta) t ∧ deriv (edge P delta Delta) t ≤ t ^ 2 := by
  by_cases htpos : 0 < t
  · rw [(edge_hasDerivAt_pos P delta Delta t hd hdD htpos).deriv]
    exact ⟨rawp_nonneg P delta Delta t (le_trans (le_of_lt hd) hdD) ht,
      rawp_le_square P delta Delta t⟩
  · have hz : t = 0 := le_antisymm (le_of_not_gt htpos) ht
    subst t
    rw [edge_deriv_zero_interior P delta Delta 0 hd hdD (by simpa using half_pos hd)]
    norm_num


theorem profile_deriv_nonneg (P : Profile) (t : ℝ) : 0 ≤ deriv P.chi t :=
  P.mono.deriv_nonneg

theorem profile_deriv_zero_of_saturated (P : Profile) (t : ℝ) (ht : 1 ≤ t) :
    deriv P.chi t = 0 := by
  have hm : IsLocalMax P.chi t := Filter.Eventually.of_forall (fun z => by
    rw [P.saturated t ht]
    exact P.le_one z)
  exact hm.hasDerivAt_eq_zero ((P.smooth.differentiable (by simp)) t).hasDerivAt

theorem profile_deriv_zero_of_flat (P : Profile) (t : ℝ) (ht : t ≤ 1 / 2) :
    deriv P.chi t = 0 := by
  have hm : IsLocalMin P.chi t := Filter.Eventually.of_forall (fun z => by
    rw [P.flat t ht]
    exact P.nonneg z)
  exact hm.hasDerivAt_eq_zero ((P.smooth.differentiable (by simp)) t).hasDerivAt

noncomputable def leftSlope (P : Profile) (delta t : ℝ) : ℝ :=
  2 * t * P.chi (t / delta) + (t ^ 2 / delta) * deriv P.chi (t / delta)

noncomputable def slope (P : Profile) (delta Delta t : ℝ) : ℝ :=
  leftSlope P delta (min t Delta)

theorem left_hasDerivAt (P : Profile) (delta t : ℝ) :
    HasDerivAt (fun z : ℝ => z ^ 2 * P.chi (z / delta)) (leftSlope P delta t) t := by
  have hc := (((P.smooth.differentiable (by simp)) (t / delta)).hasDerivAt).comp t
    ((hasDerivAt_id t).div_const delta)
  have hp := ((hasDerivAt_id t).pow 2).mul hc
  convert! hp using 1 <;> simp [leftSlope, Function.comp_def, div_eq_mul_inv] <;> ring

theorem leftSlope_continuous (P : Profile) (delta : ℝ) : Continuous (leftSlope P delta) := by
  have hc : Continuous P.chi := P.smooth.continuous
  have hd : Continuous (deriv P.chi) := P.smooth.continuous_deriv (by simp)
  unfold leftSlope
  fun_prop

theorem leftSlope_at_Delta (P : Profile) (delta Delta : ℝ)
    (hd : 0 < delta) (hdD : delta ≤ Delta) : leftSlope P delta Delta = 2 * Delta := by
  have ha : 1 ≤ Delta / delta := by
    apply (le_div_iff₀ hd).mpr
    simpa only [one_mul] using hdD
  simp only [leftSlope, P.saturated _ ha, profile_deriv_zero_of_saturated P _ ha,
    mul_one, mul_zero, add_zero]

theorem slope_continuous (P : Profile) (delta Delta : ℝ) : Continuous (slope P delta Delta) := by
  exact (leftSlope_continuous P delta).comp (continuous_id.min continuous_const)

theorem rawp_hasDerivAt (P : Profile) (delta Delta : ℝ)
    (hd : 0 < delta) (hdD : delta ≤ Delta) (t : ℝ) :
    HasDerivAt (rawp P delta Delta) (slope P delta Delta t) t := by
  have hoff : ∀ z : ℝ, z ≠ Delta →
      HasDerivAt (rawp P delta Delta) (slope P delta Delta z) z := by
    intro z hz
    rcases lt_or_gt_of_ne hz with hlt | hgt
    · have he : rawp P delta Delta =ᶠ[𝓝 z] (fun v : ℝ => v ^ 2 * P.chi (v / delta)) := by
        filter_upwards [eventually_lt_nhds hlt] with v hv
        simp only [rawp, if_pos (le_of_lt hv)]
      have hh := (left_hasDerivAt P delta z).congr_of_eventuallyEq he
      simpa only [slope, min_eq_left (le_of_lt hlt)] using hh
    · have he : rawp P delta Delta =ᶠ[𝓝 z] (fun v : ℝ => 2 * Delta * v - Delta ^ 2) := by
        filter_upwards [eventually_gt_nhds hgt] with v hv
        simp only [rawp, if_neg (not_le_of_gt hv)]
      have hh := (((hasDerivAt_id z).const_mul (2 * Delta)).sub_const (Delta ^ 2)).congr_of_eventuallyEq he
      simpa only [slope, min_eq_right (le_of_lt hgt), leftSlope_at_Delta P delta Delta hd hdD, mul_one] using hh
  exact hasDerivAt_of_hasDerivAt_of_ne' hoff
    (rawp_continuous P delta Delta hd hdD).continuousAt
    (slope_continuous P delta Delta).continuousAt t

theorem rawp_contDiff_one (P : Profile) (delta Delta : ℝ)
    (hd : 0 < delta) (hdD : delta ≤ Delta) : ContDiff ℝ 1 (rawp P delta Delta) := by
  rw [contDiff_one_iff_deriv]
  have he : deriv (rawp P delta Delta) = slope P delta Delta := by
    funext t
    exact (rawp_hasDerivAt P delta Delta hd hdD t).deriv
  exact ⟨fun t => (rawp_hasDerivAt P delta Delta hd hdD t).differentiableAt,
    by rw [he]; exact slope_continuous P delta Delta⟩

theorem primitive_contDiff_two (P : Profile) (delta Delta : ℝ)
    (hd : 0 < delta) (hdD : delta ≤ Delta) : ContDiff ℝ 2 (primitive P delta Delta) := by
  change ContDiff ℝ (1 + 1) (primitive P delta Delta)
  rw [contDiff_succ_iff_deriv]
  have he : deriv (primitive P delta Delta) = rawp P delta Delta := by
    funext t
    exact (primitive_hasDerivAt P delta Delta t hd hdD).deriv
  refine ⟨fun t => (primitive_hasDerivAt P delta Delta t hd hdD).differentiableAt, ?_, ?_⟩
  · simp
  · rw [he]
    exact rawp_contDiff_one P delta Delta hd hdD

theorem edge_contDiff_two (P : Profile) (delta Delta : ℝ)
    (hd : 0 < delta) (hdD : delta ≤ Delta) : ContDiff ℝ 2 (edge P delta Delta) := by
  rw [contDiff_iff_contDiffAt]
  intro t
  by_cases ht : t = 0
  · subst t
    have hopen : IsOpen {s : ℝ | |s| < delta / 2} := isOpen_lt continuous_abs continuous_const
    have ht0 : |(0 : ℝ)| < delta / 2 := by simpa using half_pos hd
    have he : edge P delta Delta =ᶠ[𝓝 0] (fun _ : ℝ => 0) := by
      filter_upwards [hopen.mem_nhds ht0] with s hs
      exact edge_flat_value P delta Delta s hd hdD (le_of_lt hs)
    exact contDiffAt_const.congr_of_eventuallyEq he
  · exact (primitive_contDiff_two P delta Delta hd hdD).contDiffAt.comp t (contDiffAt_abs ht)


noncomputable def signedp (P : Profile) (delta Delta t : ℝ) : ℝ :=
  if 0 ≤ t then rawp P delta Delta t else -rawp P delta Delta (-t)

theorem edge_hasDerivAt (P : Profile) (delta Delta : ℝ)
    (hd : 0 < delta) (hdD : delta ≤ Delta) (t : ℝ) :
    HasDerivAt (edge P delta Delta) (signedp P delta Delta t) t := by
  rcases lt_trichotomy 0 t with ht | ht | ht
  · simpa only [signedp, if_pos (le_of_lt ht)] using edge_hasDerivAt_pos P delta Delta t hd hdD ht
  · subst t
    have hh := ((edge_contDiff_two P delta Delta hd hdD).differentiable (by norm_num) 0).hasDerivAt
    rw [edge_deriv_zero_interior P delta Delta 0 hd hdD (by simpa using half_pos hd)] at hh
    have hp0 := rawp_flat P delta Delta 0 hd hdD (by linarith)
    simpa only [signedp, le_refl, if_true, hp0] using hh
  · have he : edge P delta Delta =ᶠ[𝓝 t] (fun z => primitive P delta Delta (-z)) := by
      filter_upwards [eventually_lt_nhds ht] with z hz
      simp only [edge, abs_of_neg hz]
    have hh := (primitive_hasDerivAt P delta Delta (-t) hd hdD).comp t ((hasDerivAt_id t).neg)
    have hh' : HasDerivAt (fun z => primitive P delta Delta (-z)) (-rawp P delta Delta (-t)) t := by
      convert! hh using 1 <;> simp [Function.comp_def]
    simpa only [signedp, if_neg (not_le_of_gt ht)] using hh'.congr_of_eventuallyEq he

theorem signedp_hasDerivAt (P : Profile) (delta Delta : ℝ)
    (hd : 0 < delta) (hdD : delta ≤ Delta) (t : ℝ) :
    HasDerivAt (signedp P delta Delta) (slope P delta Delta |t|) t := by
  rcases lt_trichotomy 0 t with ht | ht | ht
  · have he : signedp P delta Delta =ᶠ[𝓝 t] rawp P delta Delta := by
      filter_upwards [eventually_gt_nhds ht] with z hz
      simp only [signedp, if_pos (le_of_lt hz)]
    simpa only [abs_of_pos ht] using (rawp_hasDerivAt P delta Delta hd hdD t).congr_of_eventuallyEq he
  · subst t
    have hopen : IsOpen {s : ℝ | |s| < delta / 2} := isOpen_lt continuous_abs continuous_const
    have ht0 : |(0 : ℝ)| < delta / 2 := by simpa using half_pos hd
    have he : signedp P delta Delta =ᶠ[𝓝 0] (fun _ : ℝ => 0) := by
      filter_upwards [hopen.mem_nhds ht0] with z hz
      by_cases hzp : 0 ≤ z
      · simp only [signedp, if_pos hzp]
        exact rawp_flat P delta Delta z hd hdD (le_trans (le_abs_self z) (le_of_lt hz))
      · simp only [signedp, if_neg hzp]
        rw [rawp_flat P delta Delta (-z) hd hdD (le_trans (neg_le_abs z) (le_of_lt hz))]
        simp
    have hh := (hasDerivAt_const (0 : ℝ) (0 : ℝ)).congr_of_eventuallyEq he
    have hD0 : 0 ≤ Delta := le_trans (le_of_lt hd) hdD
    simpa only [slope, abs_zero, min_eq_left hD0, leftSlope, zero_mul, mul_zero, zero_pow (by norm_num : 2 ≠ 0), zero_div, add_zero] using hh
  · have he : signedp P delta Delta =ᶠ[𝓝 t] (fun z => -rawp P delta Delta (-z)) := by
      filter_upwards [eventually_lt_nhds ht] with z hz
      simp only [signedp, if_neg (not_le_of_gt hz)]
    have hh := ((rawp_hasDerivAt P delta Delta hd hdD (-t)).comp t ((hasDerivAt_id t).neg)).neg
    have hh' : HasDerivAt (fun z => -rawp P delta Delta (-z)) (slope P delta Delta (-t)) t := by
      convert! hh using 1 <;> simp [Function.comp_def]
    simpa only [abs_of_neg ht] using hh'.congr_of_eventuallyEq he

theorem edge_deriv_eq_signedp (P : Profile) (delta Delta : ℝ)
    (hd : 0 < delta) (hdD : delta ≤ Delta) : deriv (edge P delta Delta) = signedp P delta Delta := by
  funext t
  exact (edge_hasDerivAt P delta Delta hd hdD t).deriv

theorem edge_second_deriv_eq_slope_abs (P : Profile) (delta Delta : ℝ)
    (hd : 0 < delta) (hdD : delta ≤ Delta) (t : ℝ) :
    deriv (deriv (edge P delta Delta)) t = slope P delta Delta |t| := by
  rw [edge_deriv_eq_signedp P delta Delta hd hdD]
  exact (signedp_hasDerivAt P delta Delta hd hdD t).deriv

theorem slope_nonneg_nonnegative (P : Profile) (delta Delta t : ℝ)
    (hd : 0 < delta) (hD : 0 ≤ Delta) (ht : 0 ≤ t) :
    0 ≤ slope P delta Delta t := by
  have hm : 0 ≤ min t Delta := le_min ht hD
  have hc := P.nonneg ((min t Delta) / delta)
  have hdc := profile_deriv_nonneg P ((min t Delta) / delta)
  dsimp [slope, leftSlope]
  positivity

theorem edge_convex (P : Profile) (delta Delta : ℝ)
    (hd : 0 < delta) (hdD : delta ≤ Delta) : ConvexOn ℝ Set.univ (edge P delta Delta) := by
  have hc := edge_contDiff_two P delta Delta hd hdD
  apply convexOn_univ_of_deriv2_nonneg (hc.differentiable (by norm_num)) hc.differentiable_deriv_two
  intro t
  change 0 ≤ deriv (deriv (edge P delta Delta)) t
  rw [edge_second_deriv_eq_slope_abs P delta Delta hd hdD]
  exact slope_nonneg_nonnegative P delta Delta |t| hd (le_trans (le_of_lt hd) hdD) (abs_nonneg t)

theorem edge_flat_jets_closed (P : Profile) (delta Delta t : ℝ)
    (hd : 0 < delta) (hdD : delta ≤ Delta) (ht : |t| ≤ delta / 2) :
    edge P delta Delta t = 0 ∧ deriv (edge P delta Delta) t = 0 ∧
      deriv (deriv (edge P delta Delta)) t = 0 := by
  refine ⟨edge_flat_value P delta Delta t hd hdD ht, ?_, ?_⟩
  · rw [edge_deriv_eq_signedp P delta Delta hd hdD]
    by_cases hp : 0 ≤ t
    · simp only [signedp, if_pos hp]
      exact rawp_flat P delta Delta t hd hdD (le_trans (le_abs_self t) ht)
    · simp only [signedp, if_neg hp]
      rw [rawp_flat P delta Delta (-t) hd hdD (le_trans (neg_le_abs t) ht)]
      simp
  · rw [edge_second_deriv_eq_slope_abs P delta Delta hd hdD]
    have htd : |t| ≤ Delta := by linarith
    have harg : |t| / delta ≤ 1 / 2 := by
      apply (div_le_iff₀ hd).mpr
      linarith only [ht]
    simp only [slope, min_eq_left htd, leftSlope, P.flat _ harg,
      profile_deriv_zero_of_flat P _ harg, mul_zero, add_zero]


theorem profile_second_deriv_zero (P : Profile) (t : ℝ)
    (ht : deriv P.chi t = 0) : deriv (deriv P.chi) t = 0 := by
  have hs : ContDiff ℝ ∞ (deriv P.chi) := (contDiff_infty_iff_deriv.mp P.smooth).2
  have hm : IsLocalMin (deriv P.chi) t := Filter.Eventually.of_forall (fun z => by
    rw [ht]
    exact profile_deriv_nonneg P z)
  exact hm.hasDerivAt_eq_zero ((hs.differentiable (by simp)) t).hasDerivAt

theorem profile_derivative_bounds (P : Profile) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t : ℝ,
      ‖deriv P.chi t‖ ≤ M ∧ ‖deriv (deriv P.chi) t‖ ≤ M := by
  have hd1 : Continuous (deriv P.chi) := P.smooth.continuous_deriv (by simp)
  have hs2 : ContDiff ℝ ∞ (deriv P.chi) := (contDiff_infty_iff_deriv.mp P.smooth).2
  have hd2 : Continuous (deriv (deriv P.chi)) := hs2.continuous_deriv (by simp)
  obtain ⟨M1, hM1⟩ := isCompact_Icc.bddAbove_image
    (hd1.norm.continuousOn : ContinuousOn (fun t : ℝ => ‖deriv P.chi t‖) (Set.Icc (1 / 2) 1))
  obtain ⟨M2, hM2⟩ := isCompact_Icc.bddAbove_image
    (hd2.norm.continuousOn : ContinuousOn (fun t : ℝ => ‖deriv (deriv P.chi) t‖) (Set.Icc (1 / 2) 1))
  let M : ℝ := |M1| + |M2| + 1
  have hM : 0 ≤ M := by dsimp [M]; positivity
  refine ⟨M, hM, ?_⟩
  intro t
  by_cases hin : t ∈ Set.Icc (1 / 2 : ℝ) 1
  · have h1 := hM1 (Set.mem_image_of_mem (fun t : ℝ => ‖deriv P.chi t‖) hin)
    have h2 := hM2 (Set.mem_image_of_mem (fun t : ℝ => ‖deriv (deriv P.chi) t‖) hin)
    simp only [Real.norm_eq_abs] at h1 h2 ⊢
    dsimp [M]
    constructor <;> linarith [le_abs_self M1, le_abs_self M2, abs_nonneg M1, abs_nonneg M2]
  · have hzero : deriv P.chi t = 0 := by
      by_cases hlo : t ≤ 1 / 2
      · exact profile_deriv_zero_of_flat P t hlo
      · have hhi : 1 ≤ t := by
          by_contra hh
          exact hin ⟨le_of_not_ge hlo, le_of_lt (lt_of_not_ge hh)⟩
        exact profile_deriv_zero_of_saturated P t hhi
    rw [hzero, profile_second_deriv_zero P t hzero]
    simpa only [norm_zero] using And.intro hM hM

noncomputable def leftCurvature (P : Profile) (delta t : ℝ) : ℝ :=
  2 * P.chi (t / delta) + 4 * (t / delta) * deriv P.chi (t / delta) +
    (t / delta) ^ 2 * deriv (deriv P.chi) (t / delta)

theorem leftSlope_hasDerivAt (P : Profile) (delta t : ℝ) :
    HasDerivAt (leftSlope P delta) (leftCurvature P delta t) t := by
  have hPdiff : Differentiable ℝ P.chi := P.smooth.differentiable (by simp)
  have hDdiff : Differentiable ℝ (deriv P.chi) :=
    ((contDiff_infty_iff_deriv.mp P.smooth).2).differentiable (by simp)
  have h1 := ((hPdiff (t / delta)).hasDerivAt).comp t ((hasDerivAt_id t).div_const delta)
  have h2 := ((hDdiff (t / delta)).hasDerivAt).comp t ((hasDerivAt_id t).div_const delta)
  have hh := (((hasDerivAt_id t).const_mul 2).mul h1).add
    ((((hasDerivAt_id t).pow 2).div_const delta).mul h2)
  convert! hh using 1 <;> simp [leftSlope, leftCurvature, Function.comp_def, div_eq_mul_inv] <;> ring

theorem leftCurvature_uniform_bound (P : Profile) (M : ℝ) (hM : 0 ≤ M)
    (hbound : ∀ r : ℝ, ‖deriv P.chi r‖ ≤ M ∧ ‖deriv (deriv P.chi) r‖ ≤ M)
    (delta t : ℝ) : ‖leftCurvature P delta t‖ ≤ 2 + 5 * M := by
  let r : ℝ := t / delta
  change ‖2 * P.chi r + 4 * r * deriv P.chi r + r ^ 2 * deriv (deriv P.chi) r‖ ≤ 2 + 5 * M
  by_cases hlo : r ≤ 1 / 2
  · have hD := profile_deriv_zero_of_flat P r hlo
    have hD2 := profile_second_deriv_zero P r hD
    simp only [P.flat r hlo, hD, hD2, mul_zero, add_zero, norm_zero]
    linarith only [hM]
  · by_cases hhi : 1 ≤ r
    · have hD := profile_deriv_zero_of_saturated P r hhi
      have hD2 := profile_second_deriv_zero P r hD
      simp only [P.saturated r hhi, hD, hD2, mul_one, mul_zero, add_zero]
      norm_num
      linarith only [hM]
    · have hr0 : 0 ≤ r := by linarith only [hlo]
      have hr1 : r ≤ 1 := le_of_lt (lt_of_not_ge hhi)
      have hD0 := profile_deriv_nonneg P r
      have hD1 : deriv P.chi r ≤ M := by
        have hb := (hbound r).1
        rw [Real.norm_eq_abs, abs_of_nonneg hD0] at hb
        exact hb
      have hC0 := P.nonneg r
      have hC1 := P.le_one r
      have ht0 : |2 * P.chi r| ≤ 2 := by
        rw [abs_of_nonneg (mul_nonneg (by norm_num) hC0)]
        linarith only [hC1]
      have ht1 : |4 * r * deriv P.chi r| ≤ 4 * M := by
        rw [abs_of_nonneg (mul_nonneg (mul_nonneg (by norm_num) hr0) hD0)]
        have hp := mul_le_mul hr1 hD1 hD0 (by norm_num : (0 : ℝ) ≤ 1)
        nlinarith only [hp]
      have hrabs : |r| ≤ 1 := by rw [abs_of_nonneg hr0]; exact hr1
      have hrsq : |r| ^ 2 ≤ 1 := by nlinarith only [hrabs, abs_nonneg r]
      have ht2 : |r ^ 2 * deriv (deriv P.chi) r| ≤ M := by
        rw [abs_mul, abs_pow]
        have hb := (hbound r).2
        rw [Real.norm_eq_abs] at hb
        have hp := mul_le_mul hrsq hb (abs_nonneg (deriv (deriv P.chi) r)) (by norm_num : (0 : ℝ) ≤ 1)
        simpa only [one_mul] using hp
      rw [Real.norm_eq_abs]
      change |2 * P.chi r + 4 * r * deriv P.chi r + r ^ 2 * deriv (deriv P.chi) r| ≤ _
      have ha := abs_add_le (2 * P.chi r + 4 * r * deriv P.chi r) (r ^ 2 * deriv (deriv P.chi) r)
      have hb := abs_add_le (2 * P.chi r) (4 * r * deriv P.chi r)
      linarith only [ha, hb, ht0, ht1, ht2]

theorem leftSlope_uniform_lipschitz (P : Profile) :
    ∃ C : ℝ≥0, ∀ delta : ℝ, LipschitzWith C (leftSlope P delta) := by
  obtain ⟨M, hM, hbound⟩ := profile_derivative_bounds P
  let C : ℝ≥0 := ⟨2 + 5 * M, by positivity⟩
  refine ⟨C, ?_⟩
  intro delta
  apply lipschitzWith_of_nnnorm_deriv_le
    (fun t => (leftSlope_hasDerivAt P delta t).differentiableAt)
  intro t
  have h := leftCurvature_uniform_bound P M hM hbound delta t
  rw [(leftSlope_hasDerivAt P delta t).deriv]
  exact_mod_cast h


theorem edge_uniform_hessian_regularity (P : Profile) :
    ∃ C : ℝ≥0, ∀ delta Delta : ℝ, 0 < delta → delta ≤ Delta →
      (∀ t : ℝ, 0 ≤ deriv (deriv (edge P delta Delta)) t ∧
        deriv (deriv (edge P delta Delta)) t ≤ (C : ℝ) * Delta) ∧
      LipschitzWith C (deriv (deriv (edge P delta Delta))) := by
  obtain ⟨C, hC⟩ := leftSlope_uniform_lipschitz P
  refine ⟨C, ?_⟩
  intro delta Delta hd hdD
  have hD : 0 ≤ Delta := le_trans (le_of_lt hd) hdD
  have hs0 : leftSlope P delta 0 = 0 := by simp [leftSlope]
  have hq : LipschitzWith C (slope P delta Delta) := by
    convert! (hC delta).comp (LipschitzWith.id.min_const Delta) using 1 <;>
      simp [slope, Function.comp_def]
  have ha : LipschitzWith 1 (fun t : ℝ => |t|) := by
    convert! (lipschitzWith_one_norm : LipschitzWith 1 (norm : ℝ → ℝ)) using 1 <;>
      simp [Real.norm_eq_abs]
  have he : deriv (deriv (edge P delta Delta)) = (fun t => slope P delta Delta |t|) := by
    funext t
    exact edge_second_deriv_eq_slope_abs P delta Delta hd hdD t
  constructor
  · intro t
    rw [edge_second_deriv_eq_slope_abs P delta Delta hd hdD]
    have hn := slope_nonneg_nonnegative P delta Delta |t| hd hD (abs_nonneg t)
    refine ⟨hn, ?_⟩
    have hb := (hC delta).norm_sub_le (min |t| Delta) 0
    rw [hs0, sub_zero, sub_zero] at hb
    have hm : 0 ≤ min |t| Delta := le_min (abs_nonneg t) hD
    simp only [Real.norm_eq_abs, abs_of_nonneg hm] at hb
    have hlast := mul_le_mul_of_nonneg_left (min_le_right |t| Delta) (NNReal.coe_nonneg C)
    have hnorm : |slope P delta Delta (|t|)| ≤ (C : ℝ) * Delta := by
      simpa only [slope] using le_trans hb hlast
    rw [abs_of_nonneg hn] at hnorm
    exact hnorm
  · rw [he]
    convert! hq.comp ha using 1 <;> simp [Function.comp_def]

noncomputable def usualOuter (Delta t : ℝ) : ℝ :=
  if t ≤ Delta then t ^ 3 / 3 else Delta * t ^ 2 - Delta ^ 2 * t + Delta ^ 3 / 3

noncomputable def usualP (Delta t : ℝ) : ℝ :=
  if t ≤ Delta then t ^ 2 else 2 * Delta * t - Delta ^ 2

noncomputable def usualEdge (Delta t : ℝ) : ℝ := usualOuter Delta |t|

noncomputable def usualSignedP (Delta t : ℝ) : ℝ :=
  if 0 ≤ t then usualP Delta t else -usualP Delta (-t)

theorem usualEdge_explicit (Delta t : ℝ) :
    usualEdge Delta t = if |t| ≤ Delta then |t| ^ 3 / 3 else
      Delta * t ^ 2 - Delta ^ 2 * |t| + Delta ^ 3 / 3 := by
  simp only [usualEdge, usualOuter, sq_abs]

theorem usualOuter_continuous (Delta : ℝ) : Continuous (usualOuter Delta) := by
  have hl : Continuous (fun t : ℝ => t ^ 3 / 3) := by fun_prop
  have hr : Continuous (fun t : ℝ => Delta * t ^ 2 - Delta ^ 2 * t + Delta ^ 3 / 3) := by fun_prop
  apply hl.if_le hr continuous_id continuous_const
  intro t ht
  change t = Delta at ht
  subst t
  ring

theorem usualP_continuous (Delta : ℝ) : Continuous (usualP Delta) := by
  have hl : Continuous (fun t : ℝ => t ^ 2) := by fun_prop
  have hr : Continuous (fun t : ℝ => 2 * Delta * t - Delta ^ 2) := by fun_prop
  apply hl.if_le hr continuous_id continuous_const
  intro t ht
  change t = Delta at ht
  subst t
  ring

theorem usualOuter_hasDerivAt (Delta t : ℝ) :
    HasDerivAt (usualOuter Delta) (usualP Delta t) t := by
  have hoff : ∀ z : ℝ, z ≠ Delta → HasDerivAt (usualOuter Delta) (usualP Delta z) z := by
    intro z hz
    rcases lt_or_gt_of_ne hz with hlt | hgt
    · have he : usualOuter Delta =ᶠ[𝓝 z] (fun v : ℝ => v ^ 3 / 3) := by
        filter_upwards [eventually_lt_nhds hlt] with v hv
        simp only [usualOuter, if_pos (le_of_lt hv)]
      have hh := (((hasDerivAt_id z).pow 3).div_const 3).congr_of_eventuallyEq he
      convert! hh using 1 <;> simp [usualP, if_pos (le_of_lt hlt)] <;> ring
    · have he : usualOuter Delta =ᶠ[𝓝 z]
          (fun v : ℝ => Delta * v ^ 2 - Delta ^ 2 * v + Delta ^ 3 / 3) := by
        filter_upwards [eventually_gt_nhds hgt] with v hv
        simp only [usualOuter, if_neg (not_le_of_gt hv)]
      have hh := (((((hasDerivAt_id z).pow 2).const_mul Delta).sub
        ((hasDerivAt_id z).const_mul (Delta ^ 2))).add_const (Delta ^ 3 / 3)).congr_of_eventuallyEq he
      convert! hh using 1 <;> simp [usualP, if_neg (not_le_of_gt hgt)] <;> ring
  exact hasDerivAt_of_hasDerivAt_of_ne' hoff
    (usualOuter_continuous Delta).continuousAt (usualP_continuous Delta).continuousAt t

theorem usualP_hasDerivAt (Delta t : ℝ) :
    HasDerivAt (usualP Delta) (2 * min t Delta) t := by
  have hoff : ∀ z : ℝ, z ≠ Delta → HasDerivAt (usualP Delta) (2 * min z Delta) z := by
    intro z hz
    rcases lt_or_gt_of_ne hz with hlt | hgt
    · have he : usualP Delta =ᶠ[𝓝 z] (fun v : ℝ => v ^ 2) := by
        filter_upwards [eventually_lt_nhds hlt] with v hv
        simp only [usualP, if_pos (le_of_lt hv)]
      have hh := ((hasDerivAt_id z).pow 2).congr_of_eventuallyEq he
      convert! hh using 1 <;> simp [min_eq_left (le_of_lt hlt)]
    · have he : usualP Delta =ᶠ[𝓝 z] (fun v : ℝ => 2 * Delta * v - Delta ^ 2) := by
        filter_upwards [eventually_gt_nhds hgt] with v hv
        simp only [usualP, if_neg (not_le_of_gt hv)]
      have hh := (((hasDerivAt_id z).const_mul (2 * Delta)).sub_const (Delta ^ 2)).congr_of_eventuallyEq he
      convert! hh using 1 <;> simp [min_eq_right (le_of_lt hgt)]
  have hc : Continuous (fun z : ℝ => 2 * min z Delta) := by fun_prop
  exact hasDerivAt_of_hasDerivAt_of_ne' hoff (usualP_continuous Delta).continuousAt hc.continuousAt t

theorem usualEdge_hasDerivAt_nonzero (Delta t : ℝ) (ht : t ≠ 0) :
    HasDerivAt (usualEdge Delta) (usualSignedP Delta t) t := by
  rcases lt_or_gt_of_ne ht with hn | hp
  · have he : usualEdge Delta =ᶠ[𝓝 t] (fun z => usualOuter Delta (-z)) := by
      filter_upwards [eventually_lt_nhds hn] with z hz
      simp only [usualEdge, abs_of_neg hz]
    have hh := (usualOuter_hasDerivAt Delta (-t)).comp t ((hasDerivAt_id t).neg)
    have hh' : HasDerivAt (fun z => usualOuter Delta (-z)) (-usualP Delta (-t)) t := by
      convert! hh using 1 <;> simp
    simpa only [usualSignedP, if_neg (not_le_of_gt hn)] using hh'.congr_of_eventuallyEq he
  · have he : usualEdge Delta =ᶠ[𝓝 t] usualOuter Delta := by
      filter_upwards [eventually_gt_nhds hp] with z hz
      simp only [usualEdge, abs_of_pos hz]
    simpa only [usualSignedP, if_pos (le_of_lt hp)] using
      (usualOuter_hasDerivAt Delta t).congr_of_eventuallyEq he

theorem usualSignedP_hasDerivAt_nonzero (Delta t : ℝ) (ht : t ≠ 0) :
    HasDerivAt (usualSignedP Delta) (2 * min |t| Delta) t := by
  rcases lt_or_gt_of_ne ht with hn | hp
  · have he : usualSignedP Delta =ᶠ[𝓝 t] (fun z => -usualP Delta (-z)) := by
      filter_upwards [eventually_lt_nhds hn] with z hz
      simp only [usualSignedP, if_neg (not_le_of_gt hz)]
    have hh := ((usualP_hasDerivAt Delta (-t)).comp t ((hasDerivAt_id t).neg)).neg
    have hh' : HasDerivAt (fun z => -usualP Delta (-z)) (2 * min (-t) Delta) t := by
      convert! hh using 1 <;> simp
    simpa only [abs_of_neg hn] using hh'.congr_of_eventuallyEq he
  · have he : usualSignedP Delta =ᶠ[𝓝 t] usualP Delta := by
      filter_upwards [eventually_gt_nhds hp] with z hz
      simp only [usualSignedP, if_pos (le_of_lt hz)]
    simpa only [abs_of_pos hp] using (usualP_hasDerivAt Delta t).congr_of_eventuallyEq he

theorem usualEdge_second_deriv_nonzero (Delta t : ℝ) (ht : t ≠ 0) :
    deriv (deriv (usualEdge Delta)) t = 2 * min |t| Delta := by
  have hev : ∀ᶠ z : ℝ in 𝓝 t, z ≠ 0 := by
    rcases lt_or_gt_of_ne ht with hn | hp
    · exact (eventually_lt_nhds hn).mono (fun z hz => ne_of_lt hz)
    · exact (eventually_gt_nhds hp).mono (fun z hz => ne_of_gt hz)
  have he : deriv (usualEdge Delta) =ᶠ[𝓝 t] usualSignedP Delta := by
    filter_upwards [hev] with z hz
    exact (usualEdge_hasDerivAt_nonzero Delta z hz).deriv
  rw [he.deriv_eq]
  exact (usualSignedP_hasDerivAt_nonzero Delta t ht).deriv

theorem rawp_matches_usual_after_delta (P : Profile) (delta Delta t : ℝ)
    (hd : 0 < delta) (ht : delta ≤ t) : rawp P delta Delta t = usualP Delta t := by
  have ha : 1 ≤ t / delta := by
    apply (le_div_iff₀ hd).mpr
    simpa only [one_mul] using ht
  simp only [rawp, usualP, P.saturated _ ha, mul_one]

theorem slope_matches_usual_after_delta (P : Profile) (delta Delta t : ℝ)
    (hd : 0 < delta) (hdD : delta ≤ Delta) (ht : delta ≤ t) :
    slope P delta Delta t = 2 * min t Delta := by
  have hm : delta ≤ min t Delta := le_min ht hdD
  have ha : 1 ≤ min t Delta / delta := by
    apply (le_div_iff₀ hd).mpr
    simpa only [one_mul] using hm
  simp only [slope, leftSlope, P.saturated _ ha, profile_deriv_zero_of_saturated P _ ha,
    mul_one, mul_zero, add_zero]

theorem edge_matches_usual_derivatives_outside_core (P : Profile) (delta Delta t : ℝ)
    (hd : 0 < delta) (hdD : delta ≤ Delta) (ht : delta ≤ |t|) :
    deriv (edge P delta Delta) t = deriv (usualEdge Delta) t ∧
    deriv (deriv (edge P delta Delta)) t = deriv (deriv (usualEdge Delta)) t := by
  have hne : t ≠ 0 := by intro hzero; subst t; simp only [abs_zero] at ht; linarith only [hd, ht]
  constructor
  · rw [edge_deriv_eq_signedp P delta Delta hd hdD,
      (usualEdge_hasDerivAt_nonzero Delta t hne).deriv]
    by_cases hp : 0 ≤ t
    · simp only [signedp, usualSignedP, if_pos hp]
      exact rawp_matches_usual_after_delta P delta Delta t hd (by simpa only [abs_of_nonneg hp] using ht)
    · simp only [signedp, usualSignedP, if_neg hp]
      rw [rawp_matches_usual_after_delta P delta Delta (-t) hd
        (by simpa only [abs_of_neg (lt_of_not_ge hp)] using ht)]
  · rw [edge_second_deriv_eq_slope_abs P delta Delta hd hdD,
      usualEdge_second_deriv_nonzero Delta t hne]
    exact slope_matches_usual_after_delta P delta Delta |t| hd hdD ht


theorem primitive_minus_usual_constant_after_delta (P : Profile) (delta Delta u : ℝ)
    (hd : 0 < delta) (hdD : delta ≤ Delta) (hu : delta ≤ u) :
    primitive P delta Delta u - usualOuter Delta u =
      primitive P delta Delta delta - usualOuter Delta delta := by
  have hder : ∀ z ∈ Set.uIcc delta u,
      HasDerivAt (fun v : ℝ => primitive P delta Delta v - usualOuter Delta v) 0 z := by
    intro z hz
    rw [Set.uIcc_of_le hu] at hz
    have hh := (primitive_hasDerivAt P delta Delta z hd hdD).sub (usualOuter_hasDerivAt Delta z)
    convert! hh using 1 <;> simp [rawp_matches_usual_after_delta P delta Delta z hd hz.1]
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt hder
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (0 : ℝ)) MeasureTheory.volume delta u)
  simp only [intervalIntegral.integral_zero] at he
  linarith only [he]

theorem edge_additive_correction_bound (P : Profile) (delta Delta : ℝ)
    (hd : 0 < delta) (hdD : delta ≤ Delta) :
    ∃ a : ℝ, |a| ≤ delta ^ 3 / 3 ∧ ∀ t : ℝ, delta ≤ |t| →
      edge P delta Delta t = usualEdge Delta t + a := by
  let a : ℝ := primitive P delta Delta delta - usualOuter Delta delta
  have hpcont := rawp_continuous P delta Delta hd hdD
  have hD : 0 ≤ Delta := le_trans (le_of_lt hd) hdD
  have hlo : 0 ≤ primitive P delta Delta delta := by
    exact intervalIntegral.integral_nonneg (le_of_lt hd)
      (fun t ht => rawp_nonneg P delta Delta t hD ht.1)
  have hup : primitive P delta Delta delta ≤ delta ^ 3 / 3 := by
    have hpint : IntervalIntegrable (rawp P delta Delta) MeasureTheory.volume 0 delta :=
      hpcont.intervalIntegrable 0 delta
    have hpoly : IntervalIntegrable (fun t : ℝ => t ^ 2) MeasureTheory.volume 0 delta :=
      (continuous_id.pow 2).intervalIntegrable 0 delta
    have hh := intervalIntegral.integral_mono_on (le_of_lt hd) hpint hpoly
      (fun t _ => rawp_le_square P delta Delta t)
    norm_num [integral_pow] at hh
    simpa only [primitive] using hh
  have hau : usualOuter Delta delta = delta ^ 3 / 3 := by simp only [usualOuter, if_pos hdD]
  refine ⟨a, ?_, ?_⟩
  · dsimp [a]
    rw [hau]
    apply abs_le.mpr
    constructor <;> linarith only [hlo, hup]
  · intro t ht
    have hc := primitive_minus_usual_constant_after_delta P delta Delta |t| hd hdD ht
    change primitive P delta Delta |t| = usualOuter Delta |t| + a
    dsimp [a]
    linarith only [hc]

theorem flat_cubic_all_items (P : Profile) :
    ∃ C : ℝ≥0, ∀ delta Delta : ℝ, 0 < delta → delta ≤ Delta →
      (∀ t : ℝ, edge P delta Delta (-t) = edge P delta Delta t) ∧
      ConvexOn ℝ Set.univ (edge P delta Delta) ∧
      ContDiff ℝ 2 (edge P delta Delta) ∧
      (∀ t : ℝ, |t| ≤ delta / 2 →
        edge P delta Delta t = 0 ∧ deriv (edge P delta Delta) t = 0 ∧
          deriv (deriv (edge P delta Delta)) t = 0) ∧
      (∀ t : ℝ, 0 ≤ t → 0 ≤ deriv (edge P delta Delta) t ∧
        deriv (edge P delta Delta) t ≤ t ^ 2) ∧
      (∀ t : ℝ, delta ≤ |t| →
        deriv (edge P delta Delta) t = deriv (usualEdge Delta) t ∧
        deriv (deriv (edge P delta Delta)) t = deriv (deriv (usualEdge Delta)) t) ∧
      (∀ t : ℝ, 0 ≤ deriv (deriv (edge P delta Delta)) t ∧
        deriv (deriv (edge P delta Delta)) t ≤ (C : ℝ) * Delta) ∧
      LipschitzWith C (deriv (deriv (edge P delta Delta))) ∧
      (∃ a : ℝ, |a| ≤ delta ^ 3 / 3 ∧ ∀ t : ℝ, delta ≤ |t| →
        edge P delta Delta t = usualEdge Delta t + a) := by
  obtain ⟨C, hC⟩ := edge_uniform_hessian_regularity P
  refine ⟨C, ?_⟩
  intro delta Delta hd hdD
  exact ⟨edge_even P delta Delta, edge_convex P delta Delta hd hdD,
    edge_contDiff_two P delta Delta hd hdD,
    fun t ht => edge_flat_jets_closed P delta Delta t hd hdD ht,
    fun t ht => edge_deriv_nonneg_le_square_nonnegative P delta Delta t hd hdD ht,
    fun t ht => edge_matches_usual_derivatives_outside_core P delta Delta t hd hdD ht,
    (hC delta Delta hd hdD).1, (hC delta Delta hd hdD).2,
    edge_additive_correction_bound P delta Delta hd hdD⟩


structure HalfProfile where
  chi : ℝ → ℝ
  smoothOn : ContDiffOn ℝ ∞ chi (Set.Ici 0)
  monoOn : MonotoneOn chi (Set.Ici 0)
  nonneg : ∀ x : ℝ, 0 ≤ x → 0 ≤ chi x
  le_one : ∀ x : ℝ, 0 ≤ x → chi x ≤ 1
  flat : ∀ x : ℝ, 0 ≤ x → x ≤ 1 / 2 → chi x = 0
  saturated : ∀ x : ℝ, 1 ≤ x → chi x = 1

noncomputable def extendProfile (P : HalfProfile) : Profile where
  chi := fun x => if 0 ≤ x then P.chi x else 0
  smooth := by
    rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : 0 < x
    · have he : (fun z : ℝ => if 0 ≤ z then P.chi z else 0) =ᶠ[𝓝 x] P.chi := by
        filter_upwards [eventually_gt_nhds hx] with z hz
        simp only [if_pos (le_of_lt hz)]
      exact (P.smoothOn.contDiffAt (Ici_mem_nhds hx)).congr_of_eventuallyEq he
    · have hxhalf : x < 1 / 2 := by linarith only [le_of_not_gt hx]
      have he : (fun z : ℝ => if 0 ≤ z then P.chi z else 0) =ᶠ[𝓝 x] (fun _ => 0) := by
        filter_upwards [eventually_lt_nhds hxhalf] with z hz
        by_cases hzp : 0 ≤ z
        · simp only [if_pos hzp, P.flat z hzp (le_of_lt hz)]
        · simp only [if_neg hzp]
      exact contDiffAt_const.congr_of_eventuallyEq he
  mono := by
    intro x y hxy
    by_cases hx : 0 ≤ x
    · have hy : 0 ≤ y := le_trans hx hxy
      simp only [if_pos hx, if_pos hy]
      exact P.monoOn hx hy hxy
    · simp only [if_neg hx]
      by_cases hy : 0 ≤ y
      · simp only [if_pos hy]
        exact P.nonneg y hy
      · simp only [if_neg hy]
        exact le_refl 0
  nonneg := by
    intro x
    by_cases hx : 0 ≤ x
    · simpa only [if_pos hx] using P.nonneg x hx
    · simp only [if_neg hx, le_refl]
  le_one := by
    intro x
    by_cases hx : 0 ≤ x
    · simpa only [if_pos hx] using P.le_one x hx
    · simp only [if_neg hx, zero_le_one]
  flat := by
    intro x hx
    by_cases hp : 0 ≤ x
    · simp only [if_pos hp, P.flat x hp hx]
    · simp only [if_neg hp]
  saturated := by
    intro x hx
    have hp : 0 ≤ x := by linarith only [hx]
    simp only [if_pos hp, P.saturated x hx]

noncomputable def halfRawp (P : HalfProfile) (delta Delta t : ℝ) : ℝ :=
  if t ≤ Delta then t ^ 2 * P.chi (t / delta) else 2 * Delta * t - Delta ^ 2

noncomputable def halfEdge (P : HalfProfile) (delta Delta t : ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..|t|, halfRawp P delta Delta s

theorem halfEdge_eq_extended (P : HalfProfile) (delta Delta : ℝ) (hd : 0 < delta) :
    halfEdge P delta Delta = edge (extendProfile P) delta Delta := by
  funext t
  unfold halfEdge edge primitive
  apply intervalIntegral.integral_congr
  intro z hz
  rw [Set.uIcc_of_le (abs_nonneg t)] at hz
  have ha : 0 ≤ z / delta := div_nonneg hz.1 (le_of_lt hd)
  simp only [halfRawp, rawp, extendProfile, if_pos ha]

theorem flat_cubic_halfline_all_items (P : HalfProfile) :
    ∃ C : ℝ≥0, ∀ delta Delta : ℝ, 0 < delta → delta ≤ Delta →
      (∀ t : ℝ, halfEdge P delta Delta (-t) = halfEdge P delta Delta t) ∧
      ConvexOn ℝ Set.univ (halfEdge P delta Delta) ∧
      ContDiff ℝ 2 (halfEdge P delta Delta) ∧
      (∀ t : ℝ, |t| ≤ delta / 2 →
        halfEdge P delta Delta t = 0 ∧ deriv (halfEdge P delta Delta) t = 0 ∧
          deriv (deriv (halfEdge P delta Delta)) t = 0) ∧
      (∀ t : ℝ, 0 ≤ t → 0 ≤ deriv (halfEdge P delta Delta) t ∧
        deriv (halfEdge P delta Delta) t ≤ t ^ 2) ∧
      (∀ t : ℝ, delta ≤ |t| →
        deriv (halfEdge P delta Delta) t = deriv (usualEdge Delta) t ∧
        deriv (deriv (halfEdge P delta Delta)) t = deriv (deriv (usualEdge Delta)) t) ∧
      (∀ t : ℝ, 0 ≤ deriv (deriv (halfEdge P delta Delta)) t ∧
        deriv (deriv (halfEdge P delta Delta)) t ≤ (C : ℝ) * Delta) ∧
      LipschitzWith C (deriv (deriv (halfEdge P delta Delta))) ∧
      (∃ a : ℝ, |a| ≤ delta ^ 3 / 3 ∧ ∀ t : ℝ, delta ≤ |t| →
        halfEdge P delta Delta t = usualEdge Delta t + a)  := by
  obtain ⟨C, hC⟩ := flat_cubic_all_items (extendProfile P)
  refine ⟨C, ?_⟩
  intro delta Delta hd hdD
  have he := halfEdge_eq_extended P delta Delta hd
  simpa only [← he] using hC delta Delta hd hdD

end FlatCubic


open scoped ContDiff NNReal

namespace FangqingScalarEdgeJetBounds

noncomputable section

def doubled (g : ℝ → ℝ) (t : ℝ) : ℝ := g (2 * t)

theorem doubled_contDiff (g : ℝ → ℝ) (hg : ContDiff ℝ 2 g) :
    ContDiff ℝ 2 (doubled g) := hg.comp (contDiff_const.mul contDiff_id)

theorem doubled_deriv (g : ℝ → ℝ) (hg : Differentiable ℝ g) (t : ℝ) :
    deriv (doubled g) t = 2 * deriv g (2 * t) := by
  have h := (hg (2 * t)).hasDerivAt.comp t ((hasDerivAt_id t).const_mul 2)
  convert! h.deriv using 1 <;> try ring

theorem doubled_second_deriv (g : ℝ → ℝ) (hg : ContDiff ℝ 2 g) (t : ℝ) :
    deriv (deriv (doubled g)) t = 4 * deriv (deriv g) (2 * t) := by
  have heq : deriv (doubled g) = fun s => 2 * deriv g (2 * s) := by
    funext s
    exact doubled_deriv g (hg.differentiable (by norm_num)) s
  rw [heq]
  have h := (((hg.differentiable_deriv_two) (2 * t)).hasDerivAt.comp t
    ((hasDerivAt_id t).const_mul 2)).const_mul 2
  convert! h.deriv using 1 <;> try ring

theorem scalar_second_jet_difference (g : ℝ → ℝ) (x y : ℝ) :
    ‖iteratedFDeriv ℝ 2 g x - iteratedFDeriv ℝ 2 g y‖ =
      |deriv (deriv g) x - deriv (deriv g) y| := by
  rw [iteratedFDeriv_eq_equiv_comp]
  simp only [Function.comp_apply]
  rw [← map_sub, LinearIsometryEquiv.norm_map]
  simp only [iteratedDeriv_succ, iteratedDeriv_zero, Real.norm_eq_abs]

theorem doubled_edge_budgets (P : FlatCubic.Profile) :
    ∃ C : ℝ≥0, ∀ delta Delta : ℝ, 0 < delta → delta ≤ Delta →
      ContDiff ℝ 2 (doubled (FlatCubic.edge P delta Delta)) ∧
      (∀ t, ‖iteratedFDeriv ℝ 2 (doubled (FlatCubic.edge P delta Delta)) t‖ ≤ (4 * C : ℝ) * Delta) ∧
      (∀ x y, ‖iteratedFDeriv ℝ 2 (doubled (FlatCubic.edge P delta Delta)) x -
        iteratedFDeriv ℝ 2 (doubled (FlatCubic.edge P delta Delta)) y‖ ≤
          (8 * C : ℝ) * ‖x - y‖) := by
  obtain ⟨C, hC⟩ := FlatCubic.edge_uniform_hessian_regularity P
  refine ⟨C, ?_⟩
  intro delta Delta hd hdD
  have hgc := FlatCubic.edge_contDiff_two P delta Delta hd hdD
  obtain ⟨hb, hl⟩ := hC delta Delta hd hdD
  refine ⟨doubled_contDiff _ hgc, ?_, ?_⟩
  · intro t
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
    simp only [iteratedDeriv_succ, iteratedDeriv_zero]
    rw [doubled_second_deriv _ hgc, Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (hb (2 * t)).1]
    have h := mul_le_mul_of_nonneg_left (hb (2 * t)).2 (by norm_num : (0 : ℝ) ≤ 4)
    simp only [abs_of_pos (by norm_num : (0 : ℝ) < 4),
      abs_of_pos (by norm_num : (0 : ℝ) < 2)] at h ⊢
    nlinarith only [(hb (2 * t)).2]
  · intro x y
    rw [scalar_second_jet_difference, doubled_second_deriv _ hgc, doubled_second_deriv _ hgc,
      ← mul_sub, abs_mul]
    have h := mul_le_mul_of_nonneg_left (hl.norm_sub_le (2 * x) (2 * y)) (by norm_num : (0 : ℝ) ≤ 4)
    simp only [Real.norm_eq_abs, ← mul_sub, abs_mul] at h ⊢
    simp only [abs_of_pos (by norm_num : (0 : ℝ) < 4),
      abs_of_pos (by norm_num : (0 : ℝ) < 2)] at h ⊢
    nlinarith only [h]

end
end FangqingScalarEdgeJetBounds


open scoped BigOperators

namespace FangqingPathIncidenceBounds

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def pathDirection (n : ℕ) (v : Fin (n + 1) → E) (i : Fin n) : E :=
  v i.castSucc - v i.succ

def normalizedPath (n : ℕ) (v : Fin (n + 1) → E) (i : Fin n) : E →L[ℝ] ℝ :=
  (1 / 2 : ℝ) • innerSL ℝ (pathDirection n v i)

theorem normalizedPath_energy (n : ℕ) (v : Fin (n + 1) → E) (hv : Orthonormal ℝ v) (z : E) :
    (∑ i, ‖normalizedPath n v i z‖ ^ 2) ≤ ‖z‖ ^ 2 := by
  have hB : (∑ i, (inner ℝ (v i) z) ^ 2) ≤ ‖z‖ ^ 2 := by
    simpa only [Real.norm_eq_abs, sq_abs] using hv.sum_inner_products_le (s := Finset.univ) (x := z)
  have hl : (∑ i : Fin n, (inner ℝ (v i.castSucc) z) ^ 2) ≤ ‖z‖ ^ 2 := by
    have h := Fin.sum_univ_castSucc (fun i : Fin (n + 1) => (inner ℝ (v i) z) ^ 2)
    have hn := sq_nonneg (inner ℝ (v (Fin.last n)) z)
    linarith only [hB, h, hn]
  have hr : (∑ i : Fin n, (inner ℝ (v i.succ) z) ^ 2) ≤ ‖z‖ ^ 2 := by
    have h := Fin.sum_univ_succ (fun i : Fin (n + 1) => (inner ℝ (v i) z) ^ 2)
    have hn := sq_nonneg (inner ℝ (v 0) z)
    linarith only [hB, h, hn]
  have ht : ∀ i : Fin n, ‖normalizedPath n v i z‖ ^ 2 ≤
      (1 / 2 : ℝ) * ((inner ℝ (v i.castSucc) z) ^ 2 + (inner ℝ (v i.succ) z) ^ 2) := by
    intro i
    simp only [normalizedPath, ContinuousLinearMap.smul_apply, smul_eq_mul, innerSL_apply_apply,
      pathDirection, inner_sub_left, Real.norm_eq_abs, sq_abs]
    nlinarith only [sq_nonneg (inner ℝ (v i.castSucc) z + inner ℝ (v i.succ) z)]
  calc
    _ ≤ ∑ i : Fin n, (1 / 2 : ℝ) *
        ((inner ℝ (v i.castSucc) z) ^ 2 + (inner ℝ (v i.succ) z) ^ 2) :=
      Finset.sum_le_sum (fun i _ => ht i)
    _ = (1 / 2 : ℝ) * ((∑ i : Fin n, (inner ℝ (v i.castSucc) z) ^ 2) +
        (∑ i : Fin n, (inner ℝ (v i.succ) z) ^ 2)) := by
      rw [← Finset.mul_sum, Finset.sum_add_distrib]
    _ ≤ _ := by linarith only [hl, hr]

theorem normalizedPath_argument (n : ℕ) (v : Fin (n + 1) → E) (i : Fin n) (z : E) :
    2 * normalizedPath n v i z = inner ℝ (pathDirection n v i) z := by
  simp only [normalizedPath, ContinuousLinearMap.smul_apply, smul_eq_mul, innerSL_apply_apply]
  ring

end
end FangqingPathIncidenceBounds


open scoped BigOperators ContDiff

namespace FangqingDisjointBlockBounds

noncomputable section

variable {I X E : Type*} [Fintype I]
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem projection_norm_le (P : I → X →L[ℝ] E)
    (henergy : ∀ v : X, (∑ i, ‖P i v‖ ^ 2) ≤ ‖v‖ ^ 2) (i : I) (v : X) :
    ‖P i v‖ ≤ ‖v‖ := by
  classical
  have hh := (Finset.single_le_sum (fun j (_ : j ∈ (Finset.univ : Finset I)) => sq_nonneg ‖P j v‖)
    (Finset.mem_univ i)).trans (henergy v)
  nlinarith [norm_nonneg (P i v), norm_nonneg v]

theorem sum_product_norm_le (P : I → X →L[ℝ] E)
    (henergy : ∀ v : X, (∑ i, ‖P i v‖ ^ 2) ≤ ‖v‖ ^ 2) (v w : X) :
    (∑ i, ‖P i v‖ * ‖P i w‖) ≤ ‖v‖ * ‖w‖ := by
  have hh := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ
    (fun i => ‖P i v‖) (fun i => ‖P i w‖)
  have hv : Real.sqrt (∑ i, ‖P i v‖ ^ 2) ≤ ‖v‖ := by
    exact (Real.sqrt_le_sqrt (henergy v)).trans_eq (Real.sqrt_sq (norm_nonneg v))
  have hw : Real.sqrt (∑ i, ‖P i w‖ ^ 2) ≤ ‖w‖ := by
    exact (Real.sqrt_le_sqrt (henergy w)).trans_eq (Real.sqrt_sq (norm_nonneg w))
  exact hh.trans (mul_le_mul hv hw (Real.sqrt_nonneg _) (norm_nonneg v))

theorem sum_triple_norm_le (P : I → X →L[ℝ] E)
    (henergy : ∀ v : X, (∑ i, ‖P i v‖ ^ 2) ≤ ‖v‖ ^ 2) (v w z : X) :
    (∑ i, ‖P i v‖ * ‖P i w‖ * ‖P i z‖) ≤ ‖v‖ * ‖w‖ * ‖z‖ := by
  calc
    _ ≤ ∑ i, (‖P i v‖ * ‖P i w‖) * ‖z‖ := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_left (projection_norm_le P henergy i z) (by positivity)
    _ = (∑ i, ‖P i v‖ * ‖P i w‖) * ‖z‖ := by rw [Finset.sum_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right (sum_product_norm_le P henergy v w) (norm_nonneg z)

def blockSum (P : I → X →L[ℝ] E) (f : I → E → ℝ) (x : X) : ℝ :=
  ∑ i, f i (P i x)

theorem blockSum_iterated_apply (P : I → X →L[ℝ] E) (f : I → E → ℝ)
    (N : ℕ∞ω) (hf : ∀ i, ContDiff ℝ N (f i)) (j : ℕ) (hj : (j : ℕ∞ω) ≤ N)
    (x : X) (v : Fin j → X) :
    iteratedFDeriv ℝ j (blockSum P f) x v =
      ∑ i, iteratedFDeriv ℝ j (f i) (P i x) (fun k => P i (v k)) := by
  have hcont : ∀ i, ContDiff ℝ N (fun z => f i (P i z)) :=
    fun i => (hf i).comp (P i).contDiff
  unfold blockSum
  rw [iteratedFDeriv_fun_sum_apply (fun i _ => ((hcont i).of_le hj).contDiffAt)]
  rw [sum_apply]
  apply Finset.sum_congr rfl
  intro i hi
  change iteratedFDeriv ℝ j ((f i) ∘ P i) x v = _
  rw [(P i).iteratedFDeriv_comp_right (hf i) x hj]
  rfl

theorem second_blockSum_bound (P : I → X →L[ℝ] E) (f : I → E → ℝ)
    (hf : ∀ i, ContDiff ℝ 3 (f i))
    (henergy : ∀ v : X, (∑ i, ‖P i v‖ ^ 2) ≤ ‖v‖ ^ 2)
    (C : ℝ) (hC : 0 ≤ C) (x : X)
    (hlocal : ∀ i, ‖iteratedFDeriv ℝ 2 (f i) (P i x)‖ ≤ C) :
    ‖iteratedFDeriv ℝ 2 (blockSum P f) x‖ ≤ C := by
  apply ContinuousMultilinearMap.opNorm_le_bound hC
  intro v
  rw [blockSum_iterated_apply P f 3 hf 2 (by norm_num)]
  calc
    _ ≤ ∑ i, ‖iteratedFDeriv ℝ 2 (f i) (P i x) (fun k => P i (v k))‖ := norm_sum_le _ _
    _ ≤ ∑ i, C * (‖P i (v 0)‖ * ‖P i (v 1)‖) := by
      apply Finset.sum_le_sum
      intro i hi
      have hh := (iteratedFDeriv ℝ 2 (f i) (P i x)).le_opNorm (fun k => P i (v k))
      simp only [Fin.prod_univ_two] at hh
      exact hh.trans (mul_le_mul_of_nonneg_right (hlocal i) (by positivity))
    _ = C * (∑ i, ‖P i (v 0)‖ * ‖P i (v 1)‖) := by rw [Finset.mul_sum]
    _ ≤ C * (‖v 0‖ * ‖v 1‖) := mul_le_mul_of_nonneg_left
      (sum_product_norm_le P henergy (v 0) (v 1)) hC
    _ = C * ∏ k, ‖v k‖ := by rw [Fin.prod_univ_two]

theorem third_blockSum_bound (P : I → X →L[ℝ] E) (f : I → E → ℝ)
    (hf : ∀ i, ContDiff ℝ 3 (f i))
    (henergy : ∀ v : X, (∑ i, ‖P i v‖ ^ 2) ≤ ‖v‖ ^ 2)
    (C : ℝ) (hC : 0 ≤ C) (x : X)
    (hlocal : ∀ i, ‖iteratedFDeriv ℝ 3 (f i) (P i x)‖ ≤ C) :
    ‖iteratedFDeriv ℝ 3 (blockSum P f) x‖ ≤ C := by
  apply ContinuousMultilinearMap.opNorm_le_bound hC
  intro v
  rw [blockSum_iterated_apply P f 3 hf 3 (by norm_num)]
  calc
    _ ≤ ∑ i, ‖iteratedFDeriv ℝ 3 (f i) (P i x) (fun k => P i (v k))‖ := norm_sum_le _ _
    _ ≤ ∑ i, C * (‖P i (v 0)‖ * ‖P i (v 1)‖ * ‖P i (v 2)‖) := by
      apply Finset.sum_le_sum
      intro i hi
      have hh := (iteratedFDeriv ℝ 3 (f i) (P i x)).le_opNorm (fun k => P i (v k))
      simp only [Fin.prod_univ_three] at hh
      convert hh.trans (mul_le_mul_of_nonneg_right (hlocal i) (by positivity)) using 1 <;> ring
    _ = C * (∑ i, ‖P i (v 0)‖ * ‖P i (v 1)‖ * ‖P i (v 2)‖) := by rw [Finset.mul_sum]
    _ ≤ C * (‖v 0‖ * ‖v 1‖ * ‖v 2‖) := mul_le_mul_of_nonneg_left
      (sum_triple_norm_le P henergy (v 0) (v 1) (v 2)) hC
    _ = C * ∏ k, ‖v k‖ := by rw [Fin.prod_univ_three]

end
end FangqingDisjointBlockBounds


open scoped BigOperators ContDiff

namespace FangqingC2BlockRegularity

open FangqingDisjointBlockBounds

noncomputable section

variable {I X E : Type*} [Fintype I]
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem second_blockSum_bound_c2 (P : I → X →L[ℝ] E) (f : I → E → ℝ)
    (hf : ∀ i, ContDiff ℝ 2 (f i))
    (henergy : ∀ v : X, (∑ i, ‖P i v‖ ^ 2) ≤ ‖v‖ ^ 2)
    (C : ℝ) (hC : 0 ≤ C) (x : X)
    (hlocal : ∀ i, ‖iteratedFDeriv ℝ 2 (f i) (P i x)‖ ≤ C) :
    ‖iteratedFDeriv ℝ 2 (blockSum P f) x‖ ≤ C := by
  apply ContinuousMultilinearMap.opNorm_le_bound hC
  intro v
  rw [blockSum_iterated_apply P f 2 hf 2 le_rfl]
  calc
    _ ≤ ∑ i, ‖iteratedFDeriv ℝ 2 (f i) (P i x) (fun k => P i (v k))‖ := norm_sum_le _ _
    _ ≤ ∑ i, C * (‖P i (v 0)‖ * ‖P i (v 1)‖) := by
      apply Finset.sum_le_sum
      intro i hi
      have hh := (iteratedFDeriv ℝ 2 (f i) (P i x)).le_opNorm (fun k => P i (v k))
      simp only [Fin.prod_univ_two] at hh
      exact hh.trans (mul_le_mul_of_nonneg_right (hlocal i) (by positivity))
    _ = C * (∑ i, ‖P i (v 0)‖ * ‖P i (v 1)‖) := by rw [Finset.mul_sum]
    _ ≤ C * (‖v 0‖ * ‖v 1‖) := mul_le_mul_of_nonneg_left
      (sum_product_norm_le P henergy (v 0) (v 1)) hC
    _ = C * ∏ k, ‖v k‖ := by rw [Fin.prod_univ_two]

theorem blockSum_second_jet_lipschitz (P : I → X →L[ℝ] E) (f : I → E → ℝ)
    (hf : ∀ i, ContDiff ℝ 2 (f i))
    (henergy : ∀ v : X, (∑ i, ‖P i v‖ ^ 2) ≤ ‖v‖ ^ 2)
    (rho : ℝ) (hrho : 0 ≤ rho)
    (hlocal : ∀ i u w, ‖iteratedFDeriv ℝ 2 (f i) u - iteratedFDeriv ℝ 2 (f i) w‖ ≤
      rho * ‖u - w‖) (x y : X) :
    ‖iteratedFDeriv ℝ 2 (blockSum P f) x - iteratedFDeriv ℝ 2 (blockSum P f) y‖ ≤
      rho * ‖x - y‖ := by
  apply ContinuousMultilinearMap.opNorm_le_bound (mul_nonneg hrho (norm_nonneg _))
  intro v
  rw [ContinuousMultilinearMap.sub_apply,
    blockSum_iterated_apply P f 2 hf 2 le_rfl,
    blockSum_iterated_apply P f 2 hf 2 le_rfl, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i, ‖iteratedFDeriv ℝ 2 (f i) (P i x) (fun k => P i (v k)) -
        iteratedFDeriv ℝ 2 (f i) (P i y) (fun k => P i (v k))‖ := norm_sum_le _ _
    _ ≤ ∑ i, rho * (‖P i (x - y)‖ * ‖P i (v 0)‖ * ‖P i (v 1)‖) := by
      apply Finset.sum_le_sum
      intro i hi
      have hh := (iteratedFDeriv ℝ 2 (f i) (P i x) -
        iteratedFDeriv ℝ 2 (f i) (P i y)).le_opNorm (fun k => P i (v k))
      rw [ContinuousMultilinearMap.sub_apply] at hh
      simp only [Fin.prod_univ_two] at hh
      have hb := hlocal i (P i x) (P i y)
      rw [← map_sub] at hb
      have hm := mul_le_mul_of_nonneg_right hb
        (by positivity : 0 ≤ ‖P i (v 0)‖ * ‖P i (v 1)‖)
      nlinarith only [hh, hm]
    _ = rho * (∑ i, ‖P i (x - y)‖ * ‖P i (v 0)‖ * ‖P i (v 1)‖) := by rw [Finset.mul_sum]
    _ ≤ rho * (‖x - y‖ * ‖v 0‖ * ‖v 1‖) := mul_le_mul_of_nonneg_left
      (sum_triple_norm_le P henergy (x - y) (v 0) (v 1)) hrho
    _ = (rho * ‖x - y‖) * ∏ k, ‖v k‖ := by rw [Fin.prod_univ_two]; ring

theorem hessian_difference_norm_le_second_jet (f : X → ℝ) (x y : X) :
    ‖fderiv ℝ (fderiv ℝ f) x - fderiv ℝ (fderiv ℝ f) y‖ ≤
      ‖iteratedFDeriv ℝ 2 f x - iteratedFDeriv ℝ 2 f y‖ := by
  refine (fderiv ℝ (fderiv ℝ f) x - fderiv ℝ (fderiv ℝ f) y).opNorm_le_bound (norm_nonneg _) ?_
  intro v
  refine ((fderiv ℝ (fderiv ℝ f) x - fderiv ℝ (fderiv ℝ f) y) v).opNorm_le_bound
    (mul_nonneg (norm_nonneg _) (norm_nonneg v)) ?_
  intro w
  have hh := (iteratedFDeriv ℝ 2 f x - iteratedFDeriv ℝ 2 f y).le_opNorm ![v, w]
  simp only [ContinuousMultilinearMap.sub_apply, iteratedFDeriv_two_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Fin.prod_univ_two] at hh
  convert! hh using 1 <;> (try simp only [ContinuousLinearMap.sub_apply]) <;> ring

theorem blockSum_actual_hessian_lipschitz (P : I → X →L[ℝ] E) (f : I → E → ℝ)
    (hf : ∀ i, ContDiff ℝ 2 (f i))
    (henergy : ∀ v : X, (∑ i, ‖P i v‖ ^ 2) ≤ ‖v‖ ^ 2)
    (rho : ℝ) (hrho : 0 ≤ rho)
    (hlocal : ∀ i u w, ‖iteratedFDeriv ℝ 2 (f i) u - iteratedFDeriv ℝ 2 (f i) w‖ ≤
      rho * ‖u - w‖) (x y : X) :
    ‖fderiv ℝ (fderiv ℝ (blockSum P f)) x - fderiv ℝ (fderiv ℝ (blockSum P f)) y‖ ≤
      rho * ‖x - y‖ := by
  exact (hessian_difference_norm_le_second_jet (blockSum P f) x y).trans
    (blockSum_second_jet_lipschitz P f hf henergy rho hrho hlocal x y)

end
end FangqingC2BlockRegularity


open scoped ContDiff NNReal

namespace FangqingJetToRegularity

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]

theorem hessian_norm_eq_second_jet (f : X → ℝ) (x : X) :
    ‖fderiv ℝ (fderiv ℝ f) x‖ = ‖iteratedFDeriv ℝ 2 f x‖ := by
  rw [← norm_iteratedFDeriv_one, norm_iteratedFDeriv_fderiv]

theorem derivative_lipschitz_from_second_jet (f : X → ℝ) (hf : ContDiff ℝ 2 f)
    (L : ℝ≥0) (hbound : ∀ x, ‖iteratedFDeriv ℝ 2 f x‖ ≤ L) :
    LipschitzWith L (fderiv ℝ f) := by
  apply lipschitzWith_of_nnnorm_fderiv_le
    ((hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num))
  intro x
  have hb := hbound x
  rw [← hessian_norm_eq_second_jet] at hb
  exact_mod_cast hb

theorem second_jet_lipschitz_from_third_jet (f : X → ℝ) (hf : ContDiff ℝ 3 f)
    (rho : ℝ≥0) (hbound : ∀ x, ‖iteratedFDeriv ℝ 3 f x‖ ≤ rho) :
    LipschitzWith rho (iteratedFDeriv ℝ 2 f) := by
  apply lipschitzWith_of_nnnorm_fderiv_le
    (hf.differentiable_iteratedFDeriv (m := 2) (by norm_num))
  intro x
  have hb := hbound x
  rw [← norm_fderiv_iteratedFDeriv] at hb
  exact_mod_cast hb

theorem hessian_difference_norm_le_second_jet (f : X → ℝ) (x y : X) :
    ‖fderiv ℝ (fderiv ℝ f) x - fderiv ℝ (fderiv ℝ f) y‖ ≤
      ‖iteratedFDeriv ℝ 2 f x - iteratedFDeriv ℝ 2 f y‖ := by
  refine (fderiv ℝ (fderiv ℝ f) x - fderiv ℝ (fderiv ℝ f) y).opNorm_le_bound (norm_nonneg _) ?_
  intro v
  refine ((fderiv ℝ (fderiv ℝ f) x - fderiv ℝ (fderiv ℝ f) y) v).opNorm_le_bound
    (mul_nonneg (norm_nonneg _) (norm_nonneg v)) ?_
  intro w
  have hh := (iteratedFDeriv ℝ 2 f x - iteratedFDeriv ℝ 2 f y).le_opNorm ![v, w]
  simp only [ContinuousMultilinearMap.sub_apply, iteratedFDeriv_two_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Fin.prod_univ_two] at hh
  convert! hh using 1 <;> (try simp only [ContinuousLinearMap.sub_apply]) <;> ring

theorem hessian_lipschitz_from_second_jet_lipschitz (f : X → ℝ)
    (rho : ℝ≥0) (hh : LipschitzWith rho (iteratedFDeriv ℝ 2 f)) :
    LipschitzWith rho (fderiv ℝ (fderiv ℝ f)) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simpa only [dist_eq_norm] using
    (hessian_difference_norm_le_second_jet f x y).trans (hh.norm_sub_le x y)

theorem hessian_lipschitz_from_third_jet (f : X → ℝ) (hf : ContDiff ℝ 3 f)
    (rho : ℝ≥0) (hbound : ∀ x, ‖iteratedFDeriv ℝ 3 f x‖ ≤ rho) :
    LipschitzWith rho (fderiv ℝ (fderiv ℝ f)) :=
  hessian_lipschitz_from_second_jet_lipschitz f rho
    (second_jet_lipschitz_from_third_jet f hf rho hbound)

theorem gradient_lipschitz_from_second_jet (f : X → ℝ) (hf : ContDiff ℝ 2 f)
    (L : ℝ≥0) (hbound : ∀ x, ‖iteratedFDeriv ℝ 2 f x‖ ≤ L) :
    LipschitzWith L (gradient f) := by
  have hh := derivative_lipschitz_from_second_jet f hf L hbound
  simpa only [one_mul, gradient, Function.comp_def] using!
    (InnerProductSpace.toDual ℝ X).symm.lipschitz.comp hh

end FangqingJetToRegularity


open scoped Topology BigOperators

namespace FangqingPacketLeakage

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [Fintype ι]

noncomputable def edgeSum (g : ℝ → ℝ) (d : ι → E) (y : E) : ℝ :=
  ∑ i, g (inner ℝ (d i) y)

noncomputable def edgeGradient (g : ℝ → ℝ) (d : ι → E) (y : E) : E →L[ℝ] ℝ :=
  ∑ i, deriv g (inner ℝ (d i) y) • innerSL ℝ (d i)

noncomputable def edgeHessian (g : ℝ → ℝ) (d : ι → E) (y : E) :
    E →L[ℝ] (E →L[ℝ] ℝ) :=
  ∑ i, ((deriv (deriv g) (inner ℝ (d i) y)) • innerSL ℝ (d i)).smulRight
    (innerSL ℝ (d i))

theorem hasFDerivAt_edgeSum (g : ℝ → ℝ) (hg : Differentiable ℝ g)
    (d : ι → E) (y : E) :
    HasFDerivAt (edgeSum g d) (edgeGradient g d y) y := by
  classical
  have hi : ∀ i : ι, HasFDerivAt (fun z => g (inner ℝ (d i) z))
      (deriv g (inner ℝ (d i) y) • innerSL ℝ (d i)) y := by
    intro i
    simpa only [Function.comp_def, innerSL_apply_apply] using
      (hg (inner ℝ (d i) y)).hasDerivAt.comp_hasFDerivAt y
        (innerSL ℝ (d i)).hasFDerivAt
  simpa only [edgeSum, edgeGradient] using!
    HasFDerivAt.fun_sum (u := Finset.univ) (fun i _hi => hi i)

theorem hasFDerivAt_edgeGradient (g : ℝ → ℝ) (hg : Differentiable ℝ (deriv g))
    (d : ι → E) (y : E) :
    HasFDerivAt (edgeGradient g d) (edgeHessian g d y) y := by
  classical
  have hi : ∀ i : ι, HasFDerivAt
      (fun z => deriv g (inner ℝ (d i) z) • innerSL ℝ (d i))
      (((deriv (deriv g) (inner ℝ (d i) y)) • innerSL ℝ (d i)).smulRight
        (innerSL ℝ (d i))) y := by
    intro i
    have hscalar : HasFDerivAt (fun z => deriv g (inner ℝ (d i) z))
        ((deriv (deriv g) (inner ℝ (d i) y)) • innerSL ℝ (d i)) y := by
      simpa only [Function.comp_def, innerSL_apply_apply] using
        (hg (inner ℝ (d i) y)).hasDerivAt.comp_hasFDerivAt y
          (innerSL ℝ (d i)).hasFDerivAt
    exact hscalar.smul_const (innerSL ℝ (d i))
  simpa only [edgeGradient, edgeHessian] using!
    HasFDerivAt.fun_sum (u := Finset.univ) (fun i _hi => hi i)

theorem hessian_edgeSum_apply (g : ℝ → ℝ) (hg : ContDiff ℝ 2 g)
    (d : ι → E) (y h k : E) :
    fderiv ℝ (fderiv ℝ (edgeSum g d)) y h k =
      ∑ i, deriv (deriv g) (inner ℝ (d i) y) * inner ℝ (d i) h * inner ℝ (d i) k := by
  have hfun : fderiv ℝ (edgeSum g d) = edgeGradient g d := by
    funext z
    exact (hasFDerivAt_edgeSum g (hg.differentiable (by norm_num)) d z).fderiv
  rw [hfun, (hasFDerivAt_edgeGradient g hg.differentiable_deriv_two d y).fderiv]
  simp [edgeHessian, innerSL_apply_apply, mul_assoc]

noncomputable def queryCoeff (n : ℕ) (t : ℝ) (i : Fin (n + 3)) : ℝ :=
  if i.val = 0 then 3 * t else if i.val = 1 then 2 * t else t

noncomputable def queryPoint (n : ℕ) (v : Fin (n + 3) → E) (t : ℝ) : E :=
  ∑ i, queryCoeff n t i • v i

noncomputable def pathDirection (n : ℕ) (v : Fin (n + 3) → E)
    (i : Fin (n + 2)) : E := v i.castSucc - v i.succ

theorem query_inner (n : ℕ) (v : Fin (n + 3) → E) (hv : Orthonormal ℝ v)
    (t : ℝ) (i : Fin (n + 3)) :
    inner ℝ (v i) (queryPoint n v t) = queryCoeff n t i :=
  hv.inner_right_fintype (queryCoeff n t) i

theorem path_argument (n : ℕ) (v : Fin (n + 3) → E) (hv : Orthonormal ℝ v)
    (t : ℝ) (i : Fin (n + 2)) :
    inner ℝ (pathDirection n v i) (queryPoint n v t) =
      if i.val = 0 then t else if i.val = 1 then t else 0 := by
  rw [pathDirection, inner_sub_left, query_inner n v hv t, query_inner n v hv t]
  dsimp only [queryCoeff, Fin.val_castSucc, Fin.val_succ]
  by_cases hi0 : i.val = 0
  · simp [hi0] <;> ring
  · by_cases hi1 : i.val = 1
    · simp [hi0, hi1] <;> ring
    · have hs0 : i.val + 1 ≠ 0 := by omega
      have hs1 : i.val + 1 ≠ 1 := by omega
      simp [hi0, hi1, hs0, hs1]

theorem query_norm_sq (n : ℕ) (v : Fin (n + 3) → E) (hv : Orthonormal ℝ v)
    (t : ℝ) :
    ‖queryPoint n v t‖ ^ 2 = ((n : ℝ) + 14) * t ^ 2 := by
  have hnorm : ‖queryPoint n v t‖ ^ 2 = ∑ i, queryCoeff n t i ^ 2 := by
    rw [← real_inner_self_eq_norm_sq]
    simpa only [queryPoint, RCLike.conj_to_real, pow_two] using
      hv.inner_sum (queryCoeff n t) (queryCoeff n t) Finset.univ
  rw [hnorm, Fin.sum_univ_succ, Fin.sum_univ_succ]
  simp [queryCoeff] <;> push_cast <;> ring

noncomputable def twoEdgeOperator (c : ℝ) (v₀ v₁ v₂ : E) : E →L[ℝ] E :=
  c • ((innerSL ℝ (v₀ - v₁)).smulRight (v₀ - v₁) +
    (innerSL ℝ (v₁ - v₂)).smulRight (v₁ - v₂))

theorem twoEdgeOperator_first (n : ℕ) (v : Fin (n + 3) → E)
    (hv : Orthonormal ℝ v) (c : ℝ) :
    twoEdgeOperator c (v 0) (v 1) (v 2) (v 0) = c • (v 0 - v 1) := by
  have h01 : (0 : Fin (n + 3)) ≠ 1 := by
    apply ne_of_apply_ne (fun i : Fin (n + 3) => i.val)
    change (0 : ℕ) ≠ 1 % (n + 3)
    rw [Nat.mod_eq_of_lt (by omega)]
    norm_num
  have h02 : (0 : Fin (n + 3)) ≠ 2 := by
    apply ne_of_apply_ne (fun i : Fin (n + 3) => i.val)
    change (0 : ℕ) ≠ 2 % (n + 3)
    rw [Nat.mod_eq_of_lt (by omega)]
    norm_num
  simp [twoEdgeOperator, innerSL_apply_apply, inner_sub_left,
    orthonormal_iff_ite.mp hv, hv.norm_eq_one, h01, h02, Ne.symm h01, Ne.symm h02]

theorem twoEdgeOperator_second (n : ℕ) (v : Fin (n + 3) → E)
    (hv : Orthonormal ℝ v) (c : ℝ) :
    twoEdgeOperator c (v 0) (v 1) (v 2) (v 1) =
      c • ((2 : ℝ) • v 1 - v 0 - v 2) := by
  have h01 : (0 : Fin (n + 3)) ≠ 1 := by
    apply ne_of_apply_ne (fun i : Fin (n + 3) => i.val)
    change (0 : ℕ) ≠ 1 % (n + 3)
    rw [Nat.mod_eq_of_lt (by omega)]
    norm_num
  have h12 : (1 : Fin (n + 3)) ≠ 2 := by
    apply ne_of_apply_ne (fun i : Fin (n + 3) => i.val)
    change 1 % (n + 3) ≠ 2 % (n + 3)
    rw [Nat.mod_eq_of_lt (show 1 < n + 3 by omega),
      Nat.mod_eq_of_lt (show 2 < n + 3 by omega)]
    norm_num
  simp [twoEdgeOperator, innerSL_apply_apply, inner_sub_left,
    orthonormal_iff_ite.mp hv, hv.norm_eq_one, h01, h12, Ne.symm h01, Ne.symm h12]
  module

theorem recover_first_two_tails (n : ℕ) (v : Fin (n + 3) → E)
    (hv : Orthonormal ℝ v) (c : ℝ) (hc : c ≠ 0) :
    v 1 = v 0 - c⁻¹ • twoEdgeOperator c (v 0) (v 1) (v 2) (v 0) ∧
    v 2 = (2 : ℝ) • v 1 - v 0 -
      c⁻¹ • twoEdgeOperator c (v 0) (v 1) (v 2) (v 1) := by
  rw [twoEdgeOperator_first n v hv c, twoEdgeOperator_second n v hv c]
  simp only [smul_smul, inv_mul_cancel₀ hc, one_smul]
  constructor <;> module

theorem ceiling_dimension_bound (n : ℕ) (q Cm : ℝ) (hCm : 0 ≤ Cm)
    (hq : 1 ≤ q) (hlarge : Cm + 12 ≤ q) (hm : n + 3 = Nat.ceil (Cm * q)) :
    (n : ℝ) + 14 ≤ q ^ 2 := by
  have hq0 : 0 ≤ q := by linarith
  have hm' := Nat.ceil_lt_add_one (mul_nonneg hCm hq0)
  rw [← hm] at hm'
  push_cast at hm'
  have hmul := mul_le_mul_of_nonneg_right hlarge hq0
  nlinarith

theorem query_inside_public_scale (n : ℕ) (v : Fin (n + 3) → E)
    (hv : Orthonormal ℝ v) (q omega CR : ℝ) (hq : 1 ≤ q) (hw : 0 < omega)
    (hCR : 1 ≤ CR) (hdim : (n : ℝ) + 14 ≤ q ^ 2) :
    ‖queryPoint n v (omega / 2)‖ < CR * q * Real.sqrt q * omega := by
  have hq0 : 0 < q := by linarith
  have hp : 0 < q * omega := mul_pos hq0 hw
  have hsqrt : 1 ≤ Real.sqrt q := by simpa using Real.sqrt_le_sqrt hq
  have hprod : 1 ≤ CR * Real.sqrt q := one_le_mul_of_one_le_of_one_le hCR hsqrt
  have hR := mul_le_mul_of_nonneg_right hprod hp.le
  have hnorm := query_norm_sq n v hv (omega / 2)
  have hm := mul_le_mul_of_nonneg_right hdim (sq_nonneg (omega / 2))
  have hnormlt : ‖queryPoint n v (omega / 2)‖ < q * omega := by
    have hsqpos := sq_pos_of_pos hp
    nlinarith [norm_nonneg (queryPoint n v (omega / 2))]
  have hR' : q * omega ≤ CR * q * Real.sqrt q * omega := by nlinarith only [hR]
  exact lt_of_lt_of_le hnormlt hR'

theorem hessian_path_query (n : ℕ) (v : Fin (n + 3) → E) (hv : Orthonormal ℝ v)
    (g : ℝ → ℝ) (hg : ContDiff ℝ 2 g) (t c : ℝ)
    (hgt : deriv (deriv g) t = c) (hg0 : deriv (deriv g) 0 = 0) (h k : E) :
    fderiv ℝ (fderiv ℝ (edgeSum g (pathDirection n v))) (queryPoint n v t) h k =
      inner ℝ (twoEdgeOperator c (v 0) (v 1) (v 2) h) k := by
  rw [hessian_edgeSum_apply g hg]
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
  have htail : ∀ i : Fin n,
      deriv (deriv g) (inner ℝ (pathDirection n v i.succ.succ) (queryPoint n v t)) = 0 := by
    intro i
    rw [path_argument n v hv t]
    simp [hg0]
  simp_rw [htail]
  have harg0 : inner ℝ (pathDirection n v 0) (queryPoint n v t) = t := by
    simpa using path_argument n v hv t (0 : Fin (n + 2))
  have harg1 : inner ℝ (pathDirection n v (Fin.succ 0)) (queryPoint n v t) = t := by
    simpa using path_argument n v hv t (Fin.succ (0 : Fin (n + 1)))
  rw [harg0, harg1, hgt]
  simp only [zero_mul, Finset.sum_const_zero, add_zero]
  change c * inner ℝ (v 0 - v 1) h * inner ℝ (v 0 - v 1) k +
      c * inner ℝ (v 1 - v 2) h * inner ℝ (v 1 - v 2) k = _
  simp [twoEdgeOperator, innerSL_apply_apply, inner_add_left, inner_smul_left,
    inner_sub_left]
  ring

theorem second_fderiv_of_eventuallyEq (f g : E → ℝ) (y : E)
    (heq : f =ᶠ[𝓝 y] g) :
    fderiv ℝ (fderiv ℝ f) y = fderiv ℝ (fderiv ℝ g) y := by
  have hD : fderiv ℝ f =ᶠ[𝓝 y] fderiv ℝ g := heq.fderiv
  exact hD.fderiv_eq

noncomputable def localized (χ collar : ℝ → ℝ) (R : ℝ)
    (Q hidden : E → ℝ) (y : E) : ℝ :=
  Q y + χ (‖y‖ / R) * hidden y + collar (‖y‖ / R)

theorem shell_inner_eventuallyEq
    (χ collar : ℝ → ℝ) (R : ℝ) (hR : 0 < R)
    (hχ : ∀ s : ℝ, 0 ≤ s → s ≤ 1 → χ s = 1)
    (hc : ∀ s : ℝ, 0 ≤ s → s ≤ 1 → collar s = 0)
    (Q hidden : E → ℝ) (y : E) (hy : ‖y‖ < R) :
    localized χ collar R Q hidden =ᶠ[𝓝 y] (fun z => Q z + hidden z) := by
  have hball : Metric.ball (0 : E) R ∈ 𝓝 y :=
    Metric.isOpen_ball.mem_nhds (by simpa using hy)
  filter_upwards [hball] with z hz
  have hzR : ‖z‖ < R := by simpa using hz
  have hratio : ‖z‖ / R ≤ 1 := le_of_lt ((div_lt_one hR).mpr hzR)
  have hratio0 : 0 ≤ ‖z‖ / R := div_nonneg (norm_nonneg _) hR.le
  simp [localized, hχ _ hratio0 hratio, hc _ hratio0 hratio]

theorem shell_inner_hessian
    (χ collar : ℝ → ℝ) (R : ℝ) (hR : 0 < R)
    (hχ : ∀ s : ℝ, 0 ≤ s → s ≤ 1 → χ s = 1)
    (hc : ∀ s : ℝ, 0 ≤ s → s ≤ 1 → collar s = 0)
    (Q hidden : E → ℝ) (y : E) (hy : ‖y‖ < R) :
    fderiv ℝ (fderiv ℝ (localized χ collar R Q hidden)) y =
      fderiv ℝ (fderiv ℝ (fun z => Q z + hidden z)) y :=
  second_fderiv_of_eventuallyEq _ _ y
    (shell_inner_eventuallyEq χ collar R hR hχ hc Q hidden y hy)

noncomputable def linearSeed (s : ℝ) (handle : E) : E →L[ℝ] ℝ :=
  (-s) • innerSL ℝ handle

noncomputable def boundedSeed (φ : ℝ → ℝ) (s A : ℝ) (handle : E) (y : E) : ℝ :=
  -(s * A) * φ (inner ℝ handle y / A)

theorem boundedSeed_linear_eventuallyEq (φ : ℝ → ℝ) (s A : ℝ) (hA : 0 < A)
    (hφ : ∀ r : ℝ, |r| < 1 → φ r = r) (handle y : E)
    (hy : inner ℝ handle y = 0) :
    boundedSeed φ s A handle =ᶠ[𝓝 y] (linearSeed s handle : E → ℝ) := by
  have hc : Continuous (fun z : E => inner ℝ handle z / A) :=
    (innerSL ℝ handle).continuous.div_const A
  have hn : {z : E | |inner ℝ handle z / A| < 1} ∈ 𝓝 y := by
    exact (isOpen_lt (hc.norm) continuous_const).mem_nhds (by simp [hy])
  filter_upwards [hn] with z hz
  simp only [boundedSeed, hφ _ hz, linearSeed, ContinuousLinearMap.smul_apply,
    innerSL_apply_apply, smul_eq_mul]
  field_simp

theorem hessian_total_apply (Q : E → ℝ) (G : E → E →L[ℝ] ℝ)
    (DG : E →L[ℝ] (E →L[ℝ] ℝ))
    (hQ : ∀ z, HasFDerivAt Q (G z) z)
    (g : ℝ → ℝ) (hg : ContDiff ℝ 2 g) (d : ι → E)
    (scale : ℝ) (seed : E →L[ℝ] ℝ) (y h k : E) (hG : HasFDerivAt G DG y) :
    fderiv ℝ (fderiv ℝ (fun z => Q z + scale * edgeSum g d z + seed z)) y h k =
      DG h k + scale * fderiv ℝ (fderiv ℝ (edgeSum g d)) y h k := by
  have hfirst : fderiv ℝ (fun z => Q z + scale * edgeSum g d z + seed z) =
      fun z => G z + scale • edgeGradient g d z + seed := by
    funext z
    exact (((hQ z).add ((hasFDerivAt_edgeSum g
      (hg.differentiable (by norm_num)) d z).const_mul scale)).add seed.hasFDerivAt).fderiv
  rw [hfirst]
  have hd := (hG.add
    ((hasFDerivAt_edgeGradient g hg.differentiable_deriv_two d y).const_smul scale)).add
      (hasFDerivAt_const seed y)
  have hd' : HasFDerivAt (fun z => G z + scale • edgeGradient g d z + seed)
      (DG + scale • edgeHessian g d y + 0) y := by
    simpa only [Pi.add_apply, Pi.smul_apply] using! hd
  rw [hd'.fderiv, hessian_edgeSum_apply g hg]
  simp [edgeHessian, innerSL_apply_apply, mul_assoc, Finset.mul_sum]

noncomputable def activeEndpoint (χ collar φ : ℝ → ℝ) (R : ℝ)
    (Q : E → ℝ) (g : ℝ → ℝ) (d : ι → E) (scale s A : ℝ) (handle : E) : E → ℝ :=
  localized χ collar R Q
    (fun z => scale * edgeSum g d z + boundedSeed φ s A handle z)

theorem activeEndpoint_hessian_query
    (n : ℕ) (v : Fin (n + 3) → E) (hv : Orthonormal ℝ v)
    (Q : E → ℝ) (G : E → E →L[ℝ] ℝ) (DG : E →L[ℝ] (E →L[ℝ] ℝ))
    (hQ : ∀ z, HasFDerivAt Q (G z) z)
    (g : ℝ → ℝ) (hg : ContDiff ℝ 2 g) (t c : ℝ)
    (hgt : deriv (deriv g) t = c) (hg0 : deriv (deriv g) 0 = 0)
    (χ collar φ : ℝ → ℝ) (R : ℝ) (hR : 0 < R)
    (hχ : ∀ s : ℝ, 0 ≤ s → s ≤ 1 → χ s = 1)
    (hc : ∀ s : ℝ, 0 ≤ s → s ≤ 1 → collar s = 0)
    (hφ : ∀ r : ℝ, |r| < 1 → φ r = r)
    (scale s A : ℝ) (hA : 0 < A) (handle : E)
    (hhandle : inner ℝ handle (queryPoint n v t) = 0)
    (hinner : ‖queryPoint n v t‖ < R)
    (hG : HasFDerivAt G DG (queryPoint n v t)) (h k : E) :
    fderiv ℝ (fderiv ℝ (activeEndpoint χ collar φ R Q g (pathDirection n v)
      scale s A handle)) (queryPoint n v t) h k =
      DG h k + scale * inner ℝ (twoEdgeOperator c (v 0) (v 1) (v 2) h) k := by
  have hseed := boundedSeed_linear_eventuallyEq φ s A hA hφ handle
    (queryPoint n v t) hhandle
  have hlocal := shell_inner_eventuallyEq χ collar R hR hχ hc Q
    (fun z => scale * edgeSum g (pathDirection n v) z + boundedSeed φ s A handle z)
    (queryPoint n v t) hinner
  have heq : activeEndpoint χ collar φ R Q g (pathDirection n v) scale s A handle
      =ᶠ[𝓝 (queryPoint n v t)]
      (fun z => Q z + scale * edgeSum g (pathDirection n v) z + linearSeed s handle z) := by
    filter_upwards [hlocal, hseed] with z hz hs
    simpa only [activeEndpoint, hs, add_assoc] using hz
  rw [second_fderiv_of_eventuallyEq _ _ _ heq,
    hessian_total_apply Q G DG hQ g hg (pathDirection n v) scale (linearSeed s handle)
      (queryPoint n v t) h k hG,
    hessian_path_query n v hv g hg t c hgt hg0]

end FangqingPacketLeakage


open scoped BigOperators ContDiff NNReal

namespace FangqingPathEdgeRegularity

open FangqingPacketLeakage FangqingPathIncidenceBounds FangqingScalarEdgeJetBounds
  FangqingDisjointBlockBounds FangqingC2BlockRegularity FangqingJetToRegularity

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

def pathEdge (P : FlatCubic.Profile) (delta Delta : ℝ) (n : ℕ) (v : Fin (n + 1) → E) : E → ℝ :=
  edgeSum (FlatCubic.edge P delta Delta) (pathDirection n v)

theorem pathEdge_eq_blockSum (P : FlatCubic.Profile) (delta Delta : ℝ)
    (n : ℕ) (v : Fin (n + 1) → E) :
    pathEdge P delta Delta n v = blockSum (normalizedPath n v)
      (fun _ => doubled (FlatCubic.edge P delta Delta)) := by
  funext z
  unfold pathEdge edgeSum blockSum doubled
  apply Finset.sum_congr rfl
  intro i hi
  change FlatCubic.edge P delta Delta _ = FlatCubic.edge P delta Delta (2 * normalizedPath n v i z)
  rw [normalizedPath_argument]

theorem pathEdge_contDiff (P : FlatCubic.Profile) (delta Delta : ℝ)
    (hd : 0 < delta) (hdD : delta ≤ Delta) (n : ℕ) (v : Fin (n + 1) → E) :
    ContDiff ℝ 2 (pathEdge P delta Delta n v) := by
  classical
  unfold pathEdge edgeSum
  apply ContDiff.sum
  intro i hi
  exact (FlatCubic.edge_contDiff_two P delta Delta hd hdD).comp (innerSL ℝ (pathDirection n v i)).contDiff

theorem pathEdge_convex (P : FlatCubic.Profile) (delta Delta : ℝ)
    (hd : 0 < delta) (hdD : delta ≤ Delta) (n : ℕ) (v : Fin (n + 1) → E) :
    ConvexOn ℝ (Set.univ : Set E) (pathEdge P delta Delta n v) := by
  refine ⟨convex_univ, ?_⟩
  intro x hx y hy a b ha hb hab
  have hc := FlatCubic.edge_convex P delta Delta hd hdD
  unfold pathEdge edgeSum
  simp only [Finset.mul_sum, smul_eq_mul]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i hi
  have hh := hc.2 (Set.mem_univ (inner ℝ (pathDirection n v i) x))
    (Set.mem_univ (inner ℝ (pathDirection n v i) y)) ha hb hab
  simpa only [inner_add_right, inner_smul_right, smul_eq_mul] using hh

universe u

theorem actual_pathEdge_regularity (P : FlatCubic.Profile) :
    ∃ C : ℝ≥0, ∀ (F : Type u) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F],
      ∀ delta Delta : ℝ, 0 < delta → delta ≤ Delta →
      ∀ (n : ℕ) (v : Fin (n + 1) → F), Orthonormal ℝ v →
      ContDiff ℝ 2 (pathEdge P delta Delta n v) ∧
      ConvexOn ℝ (Set.univ : Set F) (pathEdge P delta Delta n v) ∧
      (∀ z, ‖iteratedFDeriv ℝ 2 (pathEdge P delta Delta n v) z‖ ≤ (4 * C : ℝ) * Delta) ∧
      (∀ x y, ‖iteratedFDeriv ℝ 2 (pathEdge P delta Delta n v) x -
        iteratedFDeriv ℝ 2 (pathEdge P delta Delta n v) y‖ ≤ (8 * C : ℝ) * ‖x - y‖) ∧
      (∀ x y, ‖fderiv ℝ (fderiv ℝ (pathEdge P delta Delta n v)) x -
        fderiv ℝ (fderiv ℝ (pathEdge P delta Delta n v)) y‖ ≤ (8 * C : ℝ) * ‖x - y‖) := by
  obtain ⟨C, hC⟩ := doubled_edge_budgets P
  refine ⟨C, ?_⟩
  intro F inst inst' inst'' delta Delta hd hdD n v hv
  have hDelta : 0 < Delta := hd.trans_le hdD
  obtain ⟨hc, hb, hl⟩ := hC delta Delta hd hdD
  have he := pathEdge_eq_blockSum P delta Delta n v
  have henergy := normalizedPath_energy n v hv
  have h2 : ∀ z, ‖iteratedFDeriv ℝ 2 (pathEdge P delta Delta n v) z‖ ≤ (4 * C : ℝ) * Delta := by
    intro z
    rw [he]
    exact second_blockSum_bound_c2 (normalizedPath n v) (fun _ => doubled (FlatCubic.edge P delta Delta))
      (fun _ => hc) henergy ((4 * C : ℝ) * Delta) (by positivity) z (fun _ => hb _)
  have hLip : ∀ x y, ‖iteratedFDeriv ℝ 2 (pathEdge P delta Delta n v) x -
      iteratedFDeriv ℝ 2 (pathEdge P delta Delta n v) y‖ ≤ (8 * C : ℝ) * ‖x - y‖ := by
    intro x y
    rw [he]
    exact blockSum_second_jet_lipschitz (normalizedPath n v) (fun _ => doubled (FlatCubic.edge P delta Delta))
      (fun _ => hc) henergy (8 * C : ℝ) (by positivity) (fun _ x y => hl x y) x y
  exact ⟨pathEdge_contDiff P delta Delta hd hdD n v, pathEdge_convex P delta Delta hd hdD n v,
    h2, hLip, fun x y => (FangqingJetToRegularity.hessian_difference_norm_le_second_jet _ x y).trans (hLip x y)⟩

end
end FangqingPathEdgeRegularity


namespace FangqingAmplifier

abbrev Pair (A : Type*) := WithLp 2 (A × A)
abbrev Space (A W : Type*) := WithLp 2 (Pair A × W)

variable {A W : Type*}
  [NormedAddCommGroup A] [InnerProductSpace ℝ A]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W]

def mkBlock (a b : A) (w : W) : Space A W :=
  WithLp.toLp 2 (WithLp.toLp 2 (a, b), w)

theorem smul_mkBlock (r : ℝ) (a b : A) (w : W) :
    r • mkBlock a b w = mkBlock (r • a) (r • b) (r • w) := by
  rfl

def aCoord (z : Space A W) : A := z.fst.fst
def bCoord (z : Space A W) : A := z.fst.snd
def wCoord (z : Space A W) : W := z.snd

theorem inner_mkBlock_left (a b : A) (w : W) (z : Space A W) :
    inner ℝ (mkBlock a b w) z =
      inner ℝ a (aCoord z) + inner ℝ b (bCoord z) + inner ℝ w (wCoord z) := by
  rfl

theorem inner_mkBlock_right (z : Space A W) (a b : A) (w : W) :
    inner ℝ z (mkBlock a b w) =
      inner ℝ (aCoord z) a + inner ℝ (bCoord z) b + inner ℝ (wCoord z) w := by
  rfl

noncomputable def aL : Space A W →L[ℝ] A :=
  (WithLp.fstL 2 ℝ A A).comp (WithLp.fstL 2 ℝ (Pair A) W)

noncomputable def bL : Space A W →L[ℝ] A :=
  (WithLp.sndL 2 ℝ A A).comp (WithLp.fstL 2 ℝ (Pair A) W)

noncomputable def wL : Space A W →L[ℝ] W := WithLp.sndL 2 ℝ (Pair A) W

noncomputable def pairL
    {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    (f g : D →L[ℝ] A) : D →L[ℝ] Pair A :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ A A).symm.toContinuousLinearMap.comp (f.prod g)

noncomputable def blockL
    {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    (f g : D →L[ℝ] A) (k : D →L[ℝ] W) : D →L[ℝ] Space A W :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ (Pair A) W).symm.toContinuousLinearMap.comp
    ((pairL f g).prod k)

noncomputable def H (q ν : ℝ) : Space A W →L[ℝ] Space A W :=
  blockL
    (ν • ((2 : ℝ) • aL - Real.sqrt q • bL))
    (ν • ((q + 1) • bL - Real.sqrt q • aL))
    (ν • wL)

theorem H_apply (q ν : ℝ) (z : Space A W) :
    H q ν z = mkBlock
      (ν • ((2 : ℝ) • aCoord z - Real.sqrt q • bCoord z))
      (ν • ((q + 1) • bCoord z - Real.sqrt q • aCoord z))
      (ν • wCoord z) := by
  rfl

theorem norm_sq_components (z : Space A W) :
    ‖z‖ ^ 2 = ‖aCoord z‖ ^ 2 + ‖bCoord z‖ ^ 2 + ‖wCoord z‖ ^ 2 := by
  simp [aCoord, bCoord, wCoord, WithLp.prod_norm_sq_eq_of_L2]

theorem H_symmetric (q ν : ℝ) :
    (H (A := A) (W := W) q ν).toLinearMap.IsSymmetric := by
  intro x y
  change inner ℝ (H q ν x) y = inner ℝ x (H q ν y)
  simp only [H_apply, inner_mkBlock_left, inner_mkBlock_right,
    inner_smul_left, inner_smul_right, inner_sub_left, inner_sub_right,
    RCLike.conj_to_real]
  ring

noncomputable def Q (q ν : ℝ) (z : Space A W) : ℝ :=
  ν / 2 * ((2 : ℝ) * ‖aCoord z‖ ^ 2 + (q + 1) * ‖bCoord z‖ ^ 2 -
    2 * Real.sqrt q * inner ℝ (aCoord z) (bCoord z) + ‖wCoord z‖ ^ 2)

theorem inner_H_self (q ν : ℝ) (z : Space A W) :
    inner ℝ (H q ν z) z =
      ν * ((2 : ℝ) * ‖aCoord z‖ ^ 2 + (q + 1) * ‖bCoord z‖ ^ 2 -
        2 * Real.sqrt q * inner ℝ (aCoord z) (bCoord z) + ‖wCoord z‖ ^ 2) := by
  simp only [H_apply, inner_mkBlock_left,
    inner_smul_left, inner_sub_left, RCLike.conj_to_real,
    real_inner_self_eq_norm_sq]
  rw [real_inner_comm (bCoord z) (aCoord z)]
  ring

theorem lower_square_identity (q ν : ℝ) (hq : 0 ≤ q) (z : Space A W) :
    inner ℝ (H q ν z) z - ν * ‖z‖ ^ 2 =
      ν * ‖aCoord z - Real.sqrt q • bCoord z‖ ^ 2 := by
  rw [inner_H_self, norm_sq_components, norm_sub_sq_real]
  simp only [norm_smul, Real.norm_eq_abs, inner_smul_right, mul_pow, sq_abs,
    Real.sq_sqrt hq]
  ring

theorem upper_square_identity (q ν : ℝ) (hq : 0 ≤ q) (z : Space A W) :
    ν * (q + 2) * ‖z‖ ^ 2 - inner ℝ (H q ν z) z =
      ν * (‖Real.sqrt q • aCoord z + bCoord z‖ ^ 2 +
        (q + 1) * ‖wCoord z‖ ^ 2) := by
  rw [inner_H_self, norm_sq_components, norm_add_sq_real]
  simp only [norm_smul, Real.norm_eq_abs, inner_smul_left, RCLike.conj_to_real,
    mul_pow, sq_abs, Real.sq_sqrt hq]
  ring

theorem rayleigh_bounds (q ν : ℝ) (hq : 0 ≤ q) (hν : 0 ≤ ν)
    (z : Space A W) :
    ν * ‖z‖ ^ 2 ≤ inner ℝ (H q ν z) z ∧
      inner ℝ (H q ν z) z ≤ ν * (q + 2) * ‖z‖ ^ 2 := by
  constructor
  · have h := lower_square_identity q ν hq z
    have hnonneg : 0 ≤ ν * ‖aCoord z - Real.sqrt q • bCoord z‖ ^ 2 :=
      mul_nonneg hν (sq_nonneg _)
    linarith
  · have h := upper_square_identity q ν hq z
    have hnonneg : 0 ≤ ν * (‖Real.sqrt q • aCoord z + bCoord z‖ ^ 2 +
        (q + 1) * ‖wCoord z‖ ^ 2) := by positivity
    linarith

theorem Q_eq_half_inner (q ν : ℝ) (z : Space A W) :
    Q q ν z = (1 / 2 : ℝ) * (H q ν).reApplyInnerSelf z := by
  change Q q ν z = (1 / 2 : ℝ) * inner ℝ (H q ν z) z
  rw [inner_H_self]
  unfold Q
  ring

theorem hasFDerivAt_Q (q ν : ℝ) (z : Space A W) :
    HasFDerivAt (Q q ν) (innerSL ℝ (H q ν z)) z := by
  have hfun : Q (A := A) (W := W) q ν =
      fun x => (1 / 2 : ℝ) * (H q ν).reApplyInnerSelf x :=
    funext (Q_eq_half_inner q ν)
  rw [hfun]
  have hd := ((H_symmetric (A := A) (W := W) q ν).hasStrictFDerivAt_reApplyInnerSelf z).hasFDerivAt.const_mul (1 / 2 : ℝ)
  convert! hd using 1
  ext u
  simp only [two_smul, ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
    smul_eq_mul]
  ring

theorem hessian_Q_apply (q ν : ℝ) (z d e : Space A W) :
    fderiv ℝ (fderiv ℝ (Q q ν)) z d e = inner ℝ (H q ν d) e := by
  let G : Space A W →L[ℝ] (Space A W →L[ℝ] ℝ) :=
    (innerSL ℝ).comp (H q ν)
  have hfun : fderiv ℝ (Q (A := A) (W := W) q ν) = G := by
    funext x
    exact (hasFDerivAt_Q q ν x).fderiv
  rw [hfun, G.fderiv]
  rfl

theorem eigenvalue_bounds (q ν : ℝ) (hq : 0 ≤ q) (hν : 0 ≤ ν) {eigenvalue : ℝ}
    (heigenvalue : Module.End.HasEigenvalue
      (H (A := A) (W := W) q ν).toLinearMap eigenvalue) :
    ν ≤ eigenvalue ∧ eigenvalue ≤ ν * (q + 2) := by
  obtain ⟨z, hz⟩ := heigenvalue.exists_hasEigenvector
  have hzpos : 0 < ‖z‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hz.2)
  have hmap : H q ν z = eigenvalue • z := hz.apply_eq_smul
  have hb := rayleigh_bounds q ν hq hν z
  rw [hmap, inner_smul_left, RCLike.conj_to_real, real_inner_self_eq_norm_sq] at hb
  constructor <;> nlinarith [hb.1, hb.2]

theorem spectrum_bounds [FiniteDimensional ℝ A] [FiniteDimensional ℝ W]
    (q ν : ℝ) (hq : 0 ≤ q) (hν : 0 ≤ ν) {eigenvalue : ℝ}
    (heigenvalue : eigenvalue ∈ spectrum ℝ (H (A := A) (W := W) q ν).toLinearMap) :
    ν ≤ eigenvalue ∧ eigenvalue ≤ ν * (q + 2) := by
  exact eigenvalue_bounds q ν hq hν
    (Module.End.HasEigenvalue.of_mem_spectrum heigenvalue)

theorem H_handle_coords (q ν : ℝ) (h : A) (α β : ℝ) :
    H q ν (mkBlock (α • h) (β • h) (0 : W)) =
      mkBlock ((ν * (2 * α - Real.sqrt q * β)) • h)
        ((ν * ((q + 1) * β - Real.sqrt q * α)) • h) 0 := by
  rw [H_apply]
  apply (WithLp.ext_iff 2).mpr
  apply Prod.ext
  · apply (WithLp.ext_iff 2).mpr
    apply Prod.ext
    · change ν • ((2 : ℝ) • (α • h) - Real.sqrt q • (β • h)) =
        (ν * (2 * α - Real.sqrt q * β)) • h
      module
    · change ν • ((q + 1) • (β • h) - Real.sqrt q • (α • h)) =
        (ν * ((q + 1) * β - Real.sqrt q * α)) • h
      module
  · change ν • (0 : W) = 0
    simp

theorem krylov_coords (q ν : ℝ) (h : A) (n : ℕ) :
    ∃ α β : ℝ,
      (H (A := A) (W := W) q ν)^[n] (mkBlock h 0 0) =
        mkBlock (α • h) (β • h) 0 := by
  induction n with
  | zero =>
    refine ⟨1, 0, ?_⟩
    simp
  | succ n ih =>
    obtain ⟨α, β, heq⟩ := ih
    refine ⟨ν * (2 * α - Real.sqrt q * β),
      ν * ((q + 1) * β - Real.sqrt q * α), ?_⟩
    rw [Function.iterate_succ_apply', heq]
    exact H_handle_coords q ν h α β

theorem krylov_no_W (q ν : ℝ) (h : A) (n : ℕ) :
    wCoord ((H (A := A) (W := W) q ν)^[n] (mkBlock h 0 0)) = 0 := by
  obtain ⟨α, β, heq⟩ := krylov_coords (W := W) q ν h n
  rw [heq]
  rfl

theorem krylov_in_paired_span (q ν : ℝ) (h : A) (n : ℕ) :
    (H (A := A) (W := W) q ν)^[n] (mkBlock h 0 0) ∈
      Submodule.span ℝ ({mkBlock h 0 (0 : W), mkBlock 0 h 0} : Set (Space A W)) := by
  obtain ⟨α, β, heq⟩ := krylov_coords (W := W) q ν h n
  apply Submodule.mem_span_pair.mpr
  refine ⟨α, β, ?_⟩
  rw [heq]
  apply (WithLp.ext_iff 2).mpr
  apply Prod.ext
  · apply (WithLp.ext_iff 2).mpr
    apply Prod.ext <;> simp [mkBlock]
  · simp [mkBlock]

theorem H_low_eigenvector (q ν : ℝ) (hq : 0 ≤ q) (h : A) :
    H q ν (mkBlock (Real.sqrt q • h) h (0 : W)) =
      ν • mkBlock (Real.sqrt q • h) h 0 := by
  have hs : Real.sqrt q * Real.sqrt q = q := Real.mul_self_sqrt hq
  have h1 : ν * (2 * Real.sqrt q - Real.sqrt q * 1) = ν * Real.sqrt q := by ring
  have h2 : ν * ((q + 1) * 1 - Real.sqrt q * Real.sqrt q) = ν := by rw [hs]; ring
  have hh := H_handle_coords (W := W) q ν h (Real.sqrt q) 1
  rw [smul_mkBlock]
  simpa only [one_smul, h1, h2, smul_smul, smul_zero] using hh

theorem H_high_eigenvector (q ν : ℝ) (hq : 0 ≤ q) (h : A) :
    H q ν (mkBlock h (-Real.sqrt q • h) (0 : W)) =
      (ν * (q + 2)) • mkBlock h (-Real.sqrt q • h) 0 := by
  have hs : Real.sqrt q * Real.sqrt q = q := Real.mul_self_sqrt hq
  have h1 : ν * (2 * 1 - Real.sqrt q * (-Real.sqrt q)) = ν * (q + 2) := by
    calc
      _ = ν * (Real.sqrt q * Real.sqrt q + 2) := by ring
      _ = ν * (q + 2) := by rw [hs]
  have h2 : ν * ((q + 1) * (-Real.sqrt q) - Real.sqrt q * 1) =
      (ν * (q + 2)) * (-Real.sqrt q) := by ring
  have hh := H_handle_coords (W := W) q ν h 1 (-Real.sqrt q)
  rw [smul_mkBlock]
  simpa only [one_smul, h1, h2, smul_smul, smul_zero] using hh

abbrev PhysicalSpace (A B W : Type*) := WithLp 2 (WithLp 2 (A × B) × W)

variable {B : Type*} [NormedAddCommGroup B] [InnerProductSpace ℝ B]

def mkPhysical (a : A) (b : B) (w : W) : PhysicalSpace A B W :=
  WithLp.toLp 2 (WithLp.toLp 2 (a, b), w)

noncomputable def coordinates (C : A ≃ₗᵢ[ℝ] B) :
    Space A W ≃ₗᵢ[ℝ] PhysicalSpace A B W :=
  LinearIsometryEquiv.withLpProdCongr 2
    (LinearIsometryEquiv.withLpProdCongr 2 (LinearIsometryEquiv.refl ℝ A) C)
    (LinearIsometryEquiv.refl ℝ W)

theorem coordinates_mk (C : A ≃ₗᵢ[ℝ] B) (a b : A) (w : W) :
    coordinates C (mkBlock a b w) = mkPhysical a (C b) w := by
  rfl

theorem coordinates_symm_mk (C : A ≃ₗᵢ[ℝ] B) (a : A) (b : B) (w : W) :
    (coordinates C).symm (mkPhysical a b w) = mkBlock a (C.symm b) w := by
  rfl

theorem coordinates_norm (C : A ≃ₗᵢ[ℝ] B) (z : Space A W) :
    ‖coordinates C z‖ = ‖z‖ := (coordinates C).norm_map z

theorem coordinates_inner (C : A ≃ₗᵢ[ℝ] B) (z u : Space A W) :
    inner ℝ (coordinates C z) (coordinates C u) = inner ℝ z u :=
  (coordinates C).inner_map_map z u

noncomputable def QPhysical (q ν : ℝ) (C : A ≃ₗᵢ[ℝ] B)
    (z : PhysicalSpace A B W) : ℝ :=
  ν / 2 * ((2 : ℝ) * ‖z.fst.fst‖ ^ 2 + (q + 1) * ‖z.fst.snd‖ ^ 2 -
    2 * Real.sqrt q * inner ℝ (C z.fst.fst) z.fst.snd + ‖z.snd‖ ^ 2)

theorem QPhysical_coordinates (q ν : ℝ) (C : A ≃ₗᵢ[ℝ] B) (z : Space A W) :
    QPhysical q ν C (coordinates C z) = Q q ν z := by
  simp [QPhysical, Q, coordinates, aCoord, bCoord, wCoord]

noncomputable def HPhysical (q ν : ℝ) (C : A ≃ₗᵢ[ℝ] B) :
    PhysicalSpace A B W →L[ℝ] PhysicalSpace A B W :=
  (coordinates C).toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((H q ν).comp (coordinates C).symm.toContinuousLinearEquiv.toContinuousLinearMap)

theorem HPhysical_coordinates (q ν : ℝ) (C : A ≃ₗᵢ[ℝ] B) (z : Space A W) :
    HPhysical q ν C (coordinates C z) = coordinates C (H q ν z) := by
  simp [HPhysical]

theorem HPhysical_symmetric (q ν : ℝ) (C : A ≃ₗᵢ[ℝ] B) :
    (HPhysical (W := W) q ν C).toLinearMap.IsSymmetric := by
  intro x y
  change inner ℝ (HPhysical q ν C x) y = inner ℝ x (HPhysical q ν C y)
  obtain ⟨x, rfl⟩ := (coordinates C).surjective x
  obtain ⟨y, rfl⟩ := (coordinates C).surjective y
  simpa only [HPhysical_coordinates, coordinates_inner] using
    (H_symmetric (A := A) (W := W) q ν).apply_clm x y

theorem physical_rayleigh_bounds (q ν : ℝ) (hq : 0 ≤ q) (hν : 0 ≤ ν)
    (C : A ≃ₗᵢ[ℝ] B) (z : PhysicalSpace A B W) :
    ν * ‖z‖ ^ 2 ≤ inner ℝ (HPhysical q ν C z) z ∧
      inner ℝ (HPhysical q ν C z) z ≤ ν * (q + 2) * ‖z‖ ^ 2 := by
  obtain ⟨z, rfl⟩ := (coordinates C).surjective z
  simpa only [HPhysical_coordinates, coordinates_inner, coordinates_norm] using
    rayleigh_bounds q ν hq hν z

theorem QPhysical_eq_half_inner (q ν : ℝ) (C : A ≃ₗᵢ[ℝ] B)
    (z : PhysicalSpace A B W) :
    QPhysical q ν C z = (1 / 2 : ℝ) * (HPhysical q ν C).reApplyInnerSelf z := by
  obtain ⟨z, rfl⟩ := (coordinates C).surjective z
  change QPhysical q ν C (coordinates C z) =
    (1 / 2 : ℝ) * inner ℝ (HPhysical q ν C (coordinates C z)) (coordinates C z)
  rw [QPhysical_coordinates, HPhysical_coordinates, coordinates_inner]
  exact Q_eq_half_inner q ν z

theorem hasFDerivAt_QPhysical (q ν : ℝ) (C : A ≃ₗᵢ[ℝ] B)
    (z : PhysicalSpace A B W) :
    HasFDerivAt (QPhysical q ν C) (innerSL ℝ (HPhysical q ν C z)) z := by
  have hfun : QPhysical (W := W) q ν C =
      fun x => (1 / 2 : ℝ) * (HPhysical q ν C).reApplyInnerSelf x :=
    funext (QPhysical_eq_half_inner q ν C)
  rw [hfun]
  have hd := ((HPhysical_symmetric (W := W) q ν C).hasStrictFDerivAt_reApplyInnerSelf z).hasFDerivAt.const_mul (1 / 2 : ℝ)
  convert! hd using 1
  ext u
  simp only [two_smul, ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
    smul_eq_mul]
  ring

theorem hessian_QPhysical_apply (q ν : ℝ) (C : A ≃ₗᵢ[ℝ] B)
    (z d e : PhysicalSpace A B W) :
    fderiv ℝ (fderiv ℝ (QPhysical q ν C)) z d e =
      inner ℝ (HPhysical q ν C d) e := by
  let G : PhysicalSpace A B W →L[ℝ] (PhysicalSpace A B W →L[ℝ] ℝ) :=
    (innerSL ℝ).comp (HPhysical q ν C)
  have hfun : fderiv ℝ (QPhysical (W := W) q ν C) = G := by
    funext x
    exact (hasFDerivAt_QPhysical q ν C x).fderiv
  rw [hfun, G.fderiv]
  rfl

theorem physical_eigenvalue_bounds (q ν : ℝ) (hq : 0 ≤ q) (hν : 0 ≤ ν)
    (C : A ≃ₗᵢ[ℝ] B) {eigenvalue : ℝ}
    (heigenvalue : Module.End.HasEigenvalue
      (HPhysical (W := W) q ν C).toLinearMap eigenvalue) :
    ν ≤ eigenvalue ∧ eigenvalue ≤ ν * (q + 2) := by
  obtain ⟨z, hz⟩ := heigenvalue.exists_hasEigenvector
  have hzpos : 0 < ‖z‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hz.2)
  have hmap : HPhysical q ν C z = eigenvalue • z := hz.apply_eq_smul
  have hb := physical_rayleigh_bounds q ν hq hν C z
  rw [hmap, inner_smul_left, RCLike.conj_to_real, real_inner_self_eq_norm_sq] at hb
  constructor <;> nlinarith [hb.1, hb.2]

theorem physical_spectrum_bounds
    [FiniteDimensional ℝ A] [FiniteDimensional ℝ B] [FiniteDimensional ℝ W]
    (q ν : ℝ) (hq : 0 ≤ q) (hν : 0 ≤ ν) (C : A ≃ₗᵢ[ℝ] B) {eigenvalue : ℝ}
    (heigenvalue : eigenvalue ∈ spectrum ℝ (HPhysical (W := W) q ν C).toLinearMap) :
    ν ≤ eigenvalue ∧ eigenvalue ≤ ν * (q + 2) := by
  exact physical_eigenvalue_bounds q ν hq hν C
    (Module.End.HasEigenvalue.of_mem_spectrum heigenvalue)

theorem physical_paired_matrix (q ν : ℝ) (C : A ≃ₗᵢ[ℝ] B)
    (h : A) (α β : ℝ) :
    HPhysical q ν C (mkPhysical (α • h) (β • C h) (0 : W)) =
      mkPhysical ((ν * (2 * α - Real.sqrt q * β)) • h)
        ((ν * ((q + 1) * β - Real.sqrt q * α)) • C h) 0 := by
  have hh := congrArg (coordinates C) (H_handle_coords (W := W) q ν h α β)
  simpa only [← HPhysical_coordinates, coordinates_mk, map_smul] using hh

theorem physical_low_eigenvector (q ν : ℝ) (hq : 0 ≤ q) (C : A ≃ₗᵢ[ℝ] B)
    (h : A) :
    HPhysical q ν C (mkPhysical (Real.sqrt q • h) (C h) (0 : W)) =
      ν • mkPhysical (Real.sqrt q • h) (C h) 0 := by
  have hh := congrArg (coordinates C) (H_low_eigenvector (W := W) q ν hq h)
  simpa only [← HPhysical_coordinates, coordinates_mk, map_smul] using hh

theorem physical_high_eigenvector (q ν : ℝ) (hq : 0 ≤ q) (C : A ≃ₗᵢ[ℝ] B)
    (h : A) :
    HPhysical q ν C (mkPhysical h (-Real.sqrt q • C h) (0 : W)) =
      (ν * (q + 2)) • mkPhysical h (-Real.sqrt q • C h) 0 := by
  have hh := congrArg (coordinates C) (H_high_eigenvector (W := W) q ν hq h)
  simpa only [← HPhysical_coordinates, coordinates_mk, map_smul] using hh

theorem physical_iterate_coordinates (q ν : ℝ) (C : A ≃ₗᵢ[ℝ] B)
    (z : Space A W) (n : ℕ) :
    (HPhysical (W := W) q ν C)^[n] (coordinates C z) =
      coordinates C ((H q ν)^[n] z) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, HPhysical_coordinates,
      Function.iterate_succ_apply']

theorem physical_krylov_coords (q ν : ℝ) (C : A ≃ₗᵢ[ℝ] B) (h : A) (n : ℕ) :
    ∃ α β : ℝ,
      (HPhysical (W := W) q ν C)^[n] (mkPhysical h 0 0) =
        mkPhysical (α • h) (β • C h) 0 := by
  obtain ⟨α, β, heq⟩ := krylov_coords (W := W) q ν h n
  refine ⟨α, β, ?_⟩
  have hstart : coordinates C (mkBlock h 0 (0 : W)) = mkPhysical h 0 0 := by
    simpa only [map_zero] using coordinates_mk C h 0 (0 : W)
  rw [← hstart, physical_iterate_coordinates, heq, coordinates_mk]
  simp only [map_smul]

theorem physical_krylov_no_W (q ν : ℝ) (C : A ≃ₗᵢ[ℝ] B) (h : A) (n : ℕ) :
    ((HPhysical (W := W) q ν C)^[n] (mkPhysical h 0 0)).snd = 0 := by
  obtain ⟨α, β, heq⟩ := physical_krylov_coords (W := W) q ν C h n
  rw [heq]
  rfl

theorem physical_krylov_in_paired_span (q ν : ℝ) (C : A ≃ₗᵢ[ℝ] B)
    (h : A) (n : ℕ) :
    (HPhysical (W := W) q ν C)^[n] (mkPhysical h 0 0) ∈
      Submodule.span ℝ ({mkPhysical h 0 (0 : W), mkPhysical 0 (C h) 0} :
        Set (PhysicalSpace A B W)) := by
  obtain ⟨α, β, heq⟩ := physical_krylov_coords (W := W) q ν C h n
  apply Submodule.mem_span_pair.mpr
  refine ⟨α, β, ?_⟩
  rw [heq]
  apply (WithLp.ext_iff 2).mpr
  apply Prod.ext
  · apply (WithLp.ext_iff 2).mpr
    apply Prod.ext <;> simp [mkPhysical]
  · simp [mkPhysical]

noncomputable def publicIsometryEquiv
    [FiniteDimensional ℝ A] [FiniteDimensional ℝ B]
    (C : A →ₗᵢ[ℝ] B) (hdim : Module.finrank ℝ A = Module.finrank ℝ B) :
    A ≃ₗᵢ[ℝ] B :=
  LinearIsometryEquiv.ofSurjective C
    ((LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp C.injective)

theorem publicIsometryEquiv_apply
    [FiniteDimensional ℝ A] [FiniteDimensional ℝ B]
    (C : A →ₗᵢ[ℝ] B) (hdim : Module.finrank ℝ A = Module.finrank ℝ B) (a : A) :
    publicIsometryEquiv C hdim a = C a := by
  rfl

theorem physical_paired_eigenvalues (q ν : ℝ) (hq : 0 ≤ q)
    (C : A ≃ₗᵢ[ℝ] B) (h : A) (hne : h ≠ 0) :
    Module.End.HasEigenvalue (HPhysical (W := W) q ν C).toLinearMap ν ∧
      Module.End.HasEigenvalue (HPhysical (W := W) q ν C).toLinearMap (ν * (q + 2)) := by
  have hlow_ne : mkPhysical (Real.sqrt q • h) (C h) (0 : W) ≠ 0 := by
    intro heq
    have hb := congrArg (fun z : PhysicalSpace A B W => z.fst.snd) heq
    change C h = 0 at hb
    apply hne
    apply C.injective
    simpa only [map_zero] using hb
  have hhigh_ne : mkPhysical h (-Real.sqrt q • C h) (0 : W) ≠ 0 := by
    intro heq
    have ha := congrArg (fun z : PhysicalSpace A B W => z.fst.fst) heq
    change h = 0 at ha
    exact hne ha
  have hlow : Module.End.HasEigenvector (HPhysical (W := W) q ν C).toLinearMap ν
      (mkPhysical (Real.sqrt q • h) (C h) 0) := by
    apply Module.End.hasEigenvector_iff.mpr
    exact ⟨Module.End.mem_eigenspace_iff.mpr (physical_low_eigenvector q ν hq C h),
      hlow_ne⟩
  have hhigh : Module.End.HasEigenvector (HPhysical (W := W) q ν C).toLinearMap
      (ν * (q + 2)) (mkPhysical h (-Real.sqrt q • C h) 0) := by
    apply Module.End.hasEigenvector_iff.mpr
    exact ⟨Module.End.mem_eigenspace_iff.mpr (physical_high_eigenvector q ν hq C h),
      hhigh_ne⟩
  exact ⟨Module.End.hasEigenvalue_of_hasEigenvector hlow,
    Module.End.hasEigenvalue_of_hasEigenvector hhigh⟩

theorem physical_krylov_space_le (q ν : ℝ) (C : A ≃ₗᵢ[ℝ] B) (h : A) :
    Submodule.span ℝ (Set.range (fun n : ℕ =>
      (HPhysical (W := W) q ν C)^[n] (mkPhysical h 0 0))) ≤
      Submodule.span ℝ ({mkPhysical h 0 (0 : W), mkPhysical 0 (C h) 0} :
        Set (PhysicalSpace A B W)) := by
  apply Submodule.span_le.mpr
  intro z hz
  obtain ⟨n, rfl⟩ := hz
  exact physical_krylov_in_paired_span q ν C h n

theorem amplifier_spectrum
    [FiniteDimensional ℝ A] [FiniteDimensional ℝ B] [FiniteDimensional ℝ W]
    (C : A →ₗᵢ[ℝ] B) (hdim : Module.finrank ℝ A = Module.finrank ℝ B)
    (q ν : ℝ) (hq : 1 ≤ q) (hν : 0 < ν) :
    let CE := publicIsometryEquiv C hdim
    (∀ z d e : PhysicalSpace A B W,
      fderiv ℝ (fderiv ℝ (QPhysical q ν CE)) z d e =
        inner ℝ (HPhysical q ν CE d) e) ∧
    (∀ eigenvalue ∈ spectrum ℝ (HPhysical (W := W) q ν CE).toLinearMap,
      ν ≤ eigenvalue ∧ eigenvalue ≤ ν * (q + 2)) ∧
    (∀ (h : A) (α β : ℝ),
      HPhysical q ν CE (mkPhysical (α • h) (β • CE h) (0 : W)) =
        mkPhysical ((ν * (2 * α - Real.sqrt q * β)) • h)
          ((ν * ((q + 1) * β - Real.sqrt q * α)) • CE h) 0) ∧
    (∀ h : A, h ≠ 0 →
      Module.End.HasEigenvalue (HPhysical (W := W) q ν CE).toLinearMap ν ∧
        Module.End.HasEigenvalue (HPhysical (W := W) q ν CE).toLinearMap (ν * (q + 2))) ∧
    (∀ h : A,
      Submodule.span ℝ (Set.range (fun n : ℕ =>
        (HPhysical (W := W) q ν CE)^[n] (mkPhysical h 0 0))) ≤
          Submodule.span ℝ ({mkPhysical h 0 (0 : W), mkPhysical 0 (CE h) 0} :
            Set (PhysicalSpace A B W))) ∧
    (∀ (h : A) (n : ℕ),
      ((HPhysical (W := W) q ν CE)^[n] (mkPhysical h 0 0)).snd = 0) := by
  let CE := publicIsometryEquiv C hdim
  have hq0 : 0 ≤ q := le_trans zero_le_one hq
  exact ⟨hessian_QPhysical_apply q ν CE,
    fun _ he => physical_spectrum_bounds q ν hq0 hν.le CE he,
    physical_paired_matrix q ν CE,
    physical_paired_eigenvalues q ν hq0 CE,
    physical_krylov_space_le q ν CE,
    physical_krylov_no_W q ν CE⟩

end FangqingAmplifier


namespace FangqingAmplifierPairMatrix

noncomputable def M (q : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![2, -Real.sqrt q; -Real.sqrt q, q + 1]

theorem matrix_trace (q : ℝ) : (M q).trace = q + 3 := by
  simp [M, Matrix.trace, Fin.sum_univ_two]
  ring

theorem matrix_det (q : ℝ) (hq : 0 ≤ q) : (M q).det = q + 2 := by
  have hs := Real.sq_sqrt hq
  calc
    (M q).det = 2 * (q + 1) - (-Real.sqrt q) * (-Real.sqrt q) := by
      simp [M, Matrix.det_fin_two]
    _ = q + 2 := by nlinarith [hs]

theorem matrix_charpoly (q : ℝ) (hq : 0 ≤ q) :
    (M q).charpoly =
      (Polynomial.X - Polynomial.C 1) * (Polynomial.X - Polynomial.C (q + 2)) := by
  rw [Matrix.charpoly_fin_two, matrix_trace, matrix_det q hq]
  simp only [map_add, map_ofNat, map_one]
  ring

theorem matrix_spectrum (q : ℝ) (hq : 0 ≤ q) (t : ℝ) :
    t ∈ spectrum ℝ (M q) ↔ t = 1 ∨ t = q + 2 := by
  rw [Matrix.mem_spectrum_iff_isRoot_charpoly, matrix_charpoly q hq]
  simp [Polynomial.IsRoot, sub_eq_zero]

theorem matrix_action (q α β : ℝ) :
    (M q).mulVec ![α, β] =
      ![2 * α - Real.sqrt q * β, (q + 1) * β - Real.sqrt q * α] := by
  ext i
  fin_cases i <;> simp [M, Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> ring

end FangqingAmplifierPairMatrix

namespace FangqingAmplifier

variable {A B W : Type*}
  [NormedAddCommGroup A] [InnerProductSpace ℝ A]
  [NormedAddCommGroup B] [InnerProductSpace ℝ B]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W]

theorem smul_mkPhysical (r : ℝ) (a : A) (b : B) (w : W) :
    r • mkPhysical a b w = mkPhysical (r • a) (r • b) (r • w) := by
  rfl

theorem physical_paired_matrix_explicit (q ν : ℝ) (C : A ≃ₗᵢ[ℝ] B)
    (h : A) (α β : ℝ) :
    HPhysical q ν C (mkPhysical (α • h) (β • C h) (0 : W)) =
      ν • mkPhysical
        (((FangqingAmplifierPairMatrix.M q).mulVec ![α, β]) 0 • h)
        (((FangqingAmplifierPairMatrix.M q).mulVec ![α, β]) 1 • C h) 0 := by
  rw [FangqingAmplifierPairMatrix.matrix_action, smul_mkPhysical]
  simpa only [Matrix.cons_val_zero, Matrix.cons_val_one, smul_smul, smul_zero] using
    physical_paired_matrix (W := W) q ν C h α β

theorem amplifier_spectrum_complete
    [FiniteDimensional ℝ A] [FiniteDimensional ℝ B] [FiniteDimensional ℝ W]
    (C : A →ₗᵢ[ℝ] B) (hdim : Module.finrank ℝ A = Module.finrank ℝ B)
    (q ν : ℝ) (hq : 1 ≤ q) (hν : 0 < ν) :
    let CE := publicIsometryEquiv C hdim
    (∀ z d e : PhysicalSpace A B W,
      fderiv ℝ (fderiv ℝ (QPhysical q ν CE)) z d e =
        inner ℝ (HPhysical q ν CE d) e) ∧
    (∀ eigenvalue ∈ spectrum ℝ (HPhysical (W := W) q ν CE).toLinearMap,
      ν ≤ eigenvalue ∧ eigenvalue ≤ ν * (q + 2)) ∧
    (∀ (h : A) (α β : ℝ),
      HPhysical q ν CE (mkPhysical (α • h) (β • CE h) (0 : W)) =
        ν • mkPhysical
          (((FangqingAmplifierPairMatrix.M q).mulVec ![α, β]) 0 • h)
          (((FangqingAmplifierPairMatrix.M q).mulVec ![α, β]) 1 • CE h) 0) ∧
    (∀ t : ℝ, t ∈ spectrum ℝ (FangqingAmplifierPairMatrix.M q) ↔
      t = 1 ∨ t = q + 2) ∧
    (∀ h : A, h ≠ 0 →
      Module.End.HasEigenvalue (HPhysical (W := W) q ν CE).toLinearMap ν ∧
        Module.End.HasEigenvalue (HPhysical (W := W) q ν CE).toLinearMap (ν * (q + 2))) ∧
    (∀ h : A,
      Submodule.span ℝ (Set.range (fun n : ℕ =>
        (HPhysical (W := W) q ν CE)^[n] (mkPhysical h 0 0))) ≤
          Submodule.span ℝ ({mkPhysical h 0 (0 : W), mkPhysical 0 (CE h) 0} :
            Set (PhysicalSpace A B W))) ∧
    (∀ (h : A) (n : ℕ),
      ((HPhysical (W := W) q ν CE)^[n] (mkPhysical h 0 0)).snd = 0) := by
  let CE := publicIsometryEquiv C hdim
  have hq0 : 0 ≤ q := le_trans zero_le_one hq
  exact ⟨hessian_QPhysical_apply q ν CE,
    fun _ he => physical_spectrum_bounds q ν hq0 hν.le CE he,
    physical_paired_matrix_explicit q ν CE,
    FangqingAmplifierPairMatrix.matrix_spectrum q hq0,
    physical_paired_eigenvalues q ν hq0 CE,
    physical_krylov_space_le q ν CE,
    physical_krylov_no_W q ν CE⟩

end FangqingAmplifier


open scoped ContDiff

namespace FangqingHessianStrongConvexity

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def line (f : E → ℝ) (mu : ℝ) (x v : E) (t : ℝ) : ℝ :=
  f (x + t • v) - mu / 2 * ‖x + t • v‖ ^ 2

def lineFirst (f : E → ℝ) (mu : ℝ) (x v : E) (t : ℝ) : ℝ :=
  fderiv ℝ f (x + t • v) v - mu * inner ℝ (x + t • v) v

def lineSecond (f : E → ℝ) (mu : ℝ) (x v : E) (t : ℝ) : ℝ :=
  fderiv ℝ (fderiv ℝ f) (x + t • v) v v - mu * ‖v‖ ^ 2

theorem hasDerivAt_line (f : E → ℝ) (mu : ℝ) (hf : ContDiff ℝ 2 f)
    (x v : E) (t : ℝ) : HasDerivAt (line f mu x v) (lineFirst f mu x v t) t := by
  have hc : HasDerivAt (fun t : ℝ => x + t • v) v t := by
    simpa only [id_eq, one_smul] using (((hasDerivAt_id t).smul_const v).const_add x)
  have hg := ((hf.differentiable (by norm_num)) (x + t • v)).hasFDerivAt.comp_hasDerivAt t hc
  have hn := hc.norm_sq
  convert! hg.sub (hn.const_mul (mu / 2)) using 1 <;>
    simp only [line, lineFirst, Function.comp_def] <;> ring

theorem hasDerivAt_lineFirst (f : E → ℝ) (mu : ℝ) (hf : ContDiff ℝ 2 f)
    (x v : E) (t : ℝ) : HasDerivAt (lineFirst f mu x v) (lineSecond f mu x v t) t := by
  have hc : HasDerivAt (fun t : ℝ => x + t • v) v t := by
    simpa only [id_eq, one_smul] using (((hasDerivAt_id t).smul_const v).const_add x)
  have hd := (((hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num))
    (x + t • v)).hasFDerivAt.comp_hasDerivAt t hc
  have hval := hd.clm_apply (hasDerivAt_const t v)
  have hi := HasDerivAt.inner ℝ hc (hasDerivAt_const t v)
  convert! hval.sub (hi.const_mul mu) using 1 <;>
    simp only [lineFirst, lineSecond, Function.comp_def, ContinuousLinearMap.map_zero,
      inner_zero_right, add_zero, zero_add, real_inner_self_eq_norm_sq]


theorem convex_line_of_convex (h : E → ℝ) (hc : ConvexOn ℝ (Set.univ : Set E) h)
    (x v : E) : ConvexOn ℝ (Set.univ : Set ℝ) (fun t => h (x + t • v)) := by
  refine ⟨convex_univ, ?_⟩
  intro s hs t ht a b ha hb hab
  have hvec : x + (a * s + b * t) • v = a • (x + s • v) + b • (x + t • v) := by
    calc
      _ = (a + b) • x + (a * s + b * t) • v := by rw [hab, one_smul]
      _ = _ := by simp only [smul_add, add_smul, mul_smul]; abel
  simpa only [hvec, smul_eq_mul] using
    hc.2 (Set.mem_univ _) (Set.mem_univ _) ha hb hab

theorem hessian_lower_of_strongConvex (f : E → ℝ) (mu : ℝ)
    (hf : ContDiff ℝ 2 f) (hsc : StrongConvexOn (Set.univ : Set E) mu f) (x v : E) :
    mu * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ f) x v v := by
  have hline : ConvexOn ℝ (Set.univ : Set ℝ) (line f mu x v) :=
    convex_line_of_convex (fun z => f z - mu / 2 * ‖z‖ ^ 2)
      (strongConvexOn_iff_convex.mp hsc) x v
  have hmono := hline.monotoneOn_deriv
    (fun t _ => (hasDerivAt_line f mu hf x v t).differentiableAt)
  have hderiv : deriv (line f mu x v) = lineFirst f mu x v := by
    funext t
    exact (hasDerivAt_line f mu hf x v t).deriv
  rw [hderiv] at hmono
  have hmono' : Monotone (lineFirst f mu x v) := fun s t hst =>
    hmono (Set.mem_univ s) (Set.mem_univ t) hst
  have hn := (hasDerivAt_lineFirst f mu hf x v 0).nonneg_of_monotone hmono'
  simpa only [lineSecond, zero_smul, add_zero, sub_nonneg] using hn

theorem strongConvex_of_hessian_lower (f : E → ℝ) (mu : ℝ)
    (hf : ContDiff ℝ 2 f)
    (hlower : ∀ x v : E, mu * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ f) x v v) :
    StrongConvexOn (Set.univ : Set E) mu f := by
  apply strongConvexOn_iff_convex.mpr
  refine ⟨convex_univ, ?_⟩
  intro x hx y hy a b ha hb hab
  let v := y - x
  have hline : ConvexOn ℝ (Set.univ : Set ℝ) (line f mu x v) := by
    apply convexOn_of_hasDerivWithinAt2_nonneg convex_univ
      (fun t _ => (hasDerivAt_line f mu hf x v t).continuousAt.continuousWithinAt)
      (fun t _ => (hasDerivAt_line f mu hf x v t).hasDerivWithinAt)
      (fun t _ => (hasDerivAt_lineFirst f mu hf x v t).hasDerivWithinAt)
    intro t ht
    exact sub_nonneg.mpr (hlower (x + t • v) v)
  have hvec : x + b • (y - x) = a • x + b • y := by
    calc
      x + b • (y - x) = (1 - b) • x + b • y := by
        rw [sub_smul, one_smul, smul_sub]
        abel
      _ = _ := by rw [show 1 - b = a by linarith only [hab]]
  have hh := hline.2 (Set.mem_univ (0 : ℝ)) (Set.mem_univ (1 : ℝ)) ha hb hab
  simpa only [line, v, smul_eq_mul, mul_zero, mul_one, zero_add, zero_smul,
    add_zero, one_smul, add_sub_cancel, hvec] using hh

theorem strongConvex_iff_hessian_lower (f : E → ℝ) (mu : ℝ) (hf : ContDiff ℝ 2 f) :
    StrongConvexOn (Set.univ : Set E) mu f ↔
      ∀ x v : E, mu * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ f) x v v :=
  ⟨fun hsc => hessian_lower_of_strongConvex f mu hf hsc,
    strongConvex_of_hessian_lower f mu hf⟩

end
end FangqingHessianStrongConvexity


open scoped ContDiff NNReal

namespace FangqingAmplifierRegularity

open FangqingAmplifier FangqingHessianStrongConvexity

set_option maxHeartbeats 1200000

noncomputable section

theorem operator_half_quadratic_contDiff {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (H : X →L[ℝ] X) : ContDiff ℝ 2 (fun z => (1 / 2 : ℝ) * inner ℝ (H z) z) :=
  contDiff_const.mul (H.contDiff.inner ℝ contDiff_id)

theorem innerSL_comp_norm_le {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (H : X →L[ℝ] X) : ‖(innerSL ℝ).comp H‖ ≤ ‖H‖ := by
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (by simpa only [one_mul] using mul_le_mul_of_nonneg_right (norm_innerSL_le ℝ) (norm_nonneg H))

variable {A B W : Type*}
  [NormedAddCommGroup A] [InnerProductSpace ℝ A] [CompleteSpace A]
  [NormedAddCommGroup B] [InnerProductSpace ℝ B] [CompleteSpace B]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]

theorem physical_operator_norm_bound (q nu : ℝ) (hq : 0 ≤ q) (hnu : 0 ≤ nu)
    (C : A ≃ₗᵢ[ℝ] B) :
    ‖HPhysical (W := W) q nu C‖ ≤ nu * (q + 2) := by
  rw [ContinuousLinearMap.norm_eq_iSup_rayleighQuotient _ (HPhysical_symmetric q nu C)]
  apply ciSup_le
  intro z
  have hh := physical_rayleigh_bounds q nu hq hnu C z
  have h0 : 0 ≤ inner ℝ (HPhysical q nu C z) z := (by positivity : 0 ≤ nu * ‖z‖ ^ 2).trans hh.1
  change |inner ℝ (HPhysical q nu C z) z / ‖z‖ ^ 2| ≤ nu * (q + 2)
  rw [abs_of_nonneg (div_nonneg h0 (sq_nonneg _))]
  by_cases hz : z = 0
  · simp only [hz, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0), div_zero]
    positivity
  · exact (div_le_iff₀ (pow_pos (norm_pos_iff.mpr hz) 2)).mpr hh.2

theorem physical_quadratic_contDiff (q nu : ℝ) (C : A ≃ₗᵢ[ℝ] B) :
    ContDiff ℝ 2 (QPhysical (W := W) q nu C) := by
  have heq : QPhysical (W := W) q nu C =
      fun z => (1 / 2 : ℝ) * inner ℝ (HPhysical q nu C z) z :=
    funext (QPhysical_eq_half_inner q nu C)
  rw [heq]
  exact operator_half_quadratic_contDiff (X := PhysicalSpace A B W) (HPhysical (W := W) q nu C)

theorem physical_quadratic_hessian_constant (q nu : ℝ) (C : A ≃ₗᵢ[ℝ] B) (z : PhysicalSpace A B W) :
    fderiv ℝ (fderiv ℝ (QPhysical q nu C)) z = (innerSL ℝ).comp (HPhysical q nu C) := by
  ext v w
  exact hessian_QPhysical_apply q nu C z v w

theorem physical_quadratic_second_jet_bound (q nu : ℝ) (hq : 0 ≤ q) (hnu : 0 ≤ nu)
    (C : A ≃ₗᵢ[ℝ] B) (z : PhysicalSpace A B W) :
    ‖iteratedFDeriv ℝ 2 (QPhysical q nu C) z‖ ≤ nu * (q + 2) := by
  rw [← FangqingJetToRegularity.hessian_norm_eq_second_jet, physical_quadratic_hessian_constant]
  exact (innerSL_comp_norm_le (HPhysical (W := W) q nu C)).trans
    (physical_operator_norm_bound q nu hq hnu C)

theorem physical_quadratic_strongConvex (q nu : ℝ) (hq : 0 ≤ q) (hnu : 0 ≤ nu)
    (C : A ≃ₗᵢ[ℝ] B) :
    StrongConvexOn (Set.univ : Set (PhysicalSpace A B W)) nu (QPhysical q nu C) := by
  apply strongConvex_of_hessian_lower _ nu (physical_quadratic_contDiff q nu C)
  intro z v
  rw [hessian_QPhysical_apply]
  exact (physical_rayleigh_bounds q nu hq hnu C v).1

end
end FangqingAmplifierRegularity


open scoped ContDiff

namespace FangqingC2HessianAlgebra

variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

theorem first_pullback (f : Y → ℝ) (P : X →L[ℝ] Y)
    (hf : Differentiable ℝ f) (x h : X) :
    fderiv ℝ (f ∘ P) x h = fderiv ℝ f (P x) (P h) := by
  rw [((hf (P x)).hasFDerivAt.comp x P.hasFDerivAt).fderiv]
  rfl

theorem hessian_pullback (f : Y → ℝ) (P : X →L[ℝ] Y)
    (hf : ContDiff ℝ 2 f) (x h k : X) :
    fderiv ℝ (fderiv ℝ (f ∘ P)) x h k = fderiv ℝ (fderiv ℝ f) (P x) (P h) (P k) := by
  have hh := congrArg (fun T => T ![h, k]) (P.iteratedFDeriv_comp_right hf x (i := 2) le_rfl)
  simpa only [iteratedFDeriv_two_apply, ContinuousMultilinearMap.compContinuousLinearMap_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one] using! hh

theorem hessian_add (f g : X → ℝ) (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) (x h k : X) :
    fderiv ℝ (fderiv ℝ (fun z => f z + g z)) x h k =
      fderiv ℝ (fderiv ℝ f) x h k + fderiv ℝ (fderiv ℝ g) x h k := by
  have hh := congrArg (fun T => T ![h, k])
    (fun_iteratedFDeriv_add_apply hf.contDiffAt hg.contDiffAt (x := x))
  simpa only [iteratedFDeriv_two_apply, ContinuousMultilinearMap.add_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one] using! hh

theorem hessian_sub (f g : X → ℝ) (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) (x h k : X) :
    fderiv ℝ (fderiv ℝ (fun z => f z - g z)) x h k =
      fderiv ℝ (fderiv ℝ f) x h k - fderiv ℝ (fderiv ℝ g) x h k := by
  have hh := congrArg (fun T => T ![h, k])
    (fun_iteratedFDeriv_sub_apply hf.contDiffAt hg.contDiffAt (x := x))
  simpa only [iteratedFDeriv_two_apply, ContinuousMultilinearMap.sub_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one] using! hh

theorem hessian_const_mul (f : X → ℝ) (hf : ContDiff ℝ 2 f) (c : ℝ) (x h k : X) :
    fderiv ℝ (fderiv ℝ (fun z => c * f z)) x h k = c * fderiv ℝ (fderiv ℝ f) x h k := by
  have hh := congrArg (fun T => T ![h, k])
    (iteratedFDeriv_const_smul_apply (a := c) hf.contDiffAt (x := x))
  simpa only [iteratedFDeriv_two_apply, ContinuousMultilinearMap.smul_apply, smul_eq_mul,
    Matrix.cons_val_zero, Matrix.cons_val_one] using! hh

theorem hessian_mul (f g : X → ℝ) (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) (x h k : X) :
    fderiv ℝ (fderiv ℝ (fun z => f z * g z)) x h k =
      f x * fderiv ℝ (fderiv ℝ g) x h k +
      fderiv ℝ f x h * fderiv ℝ g x k +
      fderiv ℝ f x k * fderiv ℝ g x h +
      g x * fderiv ℝ (fderiv ℝ f) x h k := by
  have hdf := hf.differentiable (by norm_num)
  have hdg := hg.differentiable (by norm_num)
  have hdf2 := (hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have hdg2 := (hg.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have hfirst : fderiv ℝ (fun z => f z * g z) =
      (fun z => f z • fderiv ℝ g z + g z • fderiv ℝ f z) := by
    funext z
    have hh := ((hdf z).hasFDerivAt.mul (hdg z).hasFDerivAt).fderiv
    convert! hh using 1
  have hsecond := (((hdf x).hasFDerivAt.smul (hdg2 x).hasFDerivAt).add
    ((hdg x).hasFDerivAt.smul (hdf2 x).hasFDerivAt))
  have hfun2 : (f • fderiv ℝ g + g • fderiv ℝ f) =
      (fun z => f z • fderiv ℝ g z + g z • fderiv ℝ f z) := rfl
  rw [hfun2] at hsecond
  rw [hfirst, hsecond.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply, smul_eq_mul]
  ring

end FangqingC2HessianAlgebra


open scoped ContDiff

namespace FangqingUnlocalizedPacketRegularity

open FangqingC2HessianAlgebra FangqingHessianStrongConvexity FangqingJetToRegularity

noncomputable section

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]

def packet (Q edge : X → ℝ) (scale : ℝ) (seed : X →L[ℝ] ℝ) (z : X) : ℝ :=
  Q z + scale * edge z - seed z

theorem hessian_linear (seed : X →L[ℝ] ℝ) (x : X) :
    fderiv ℝ (fderiv ℝ (seed : X → ℝ)) x = 0 := by
  have hh : fderiv ℝ (seed : X → ℝ) = fun _ => seed := funext (fun z => seed.fderiv)
  rw [hh]
  exact (hasFDerivAt_const seed x).fderiv

theorem packet_contDiff (Q edge : X → ℝ) (scale : ℝ) (seed : X →L[ℝ] ℝ)
    (hQ : ContDiff ℝ 2 Q) (he : ContDiff ℝ 2 edge) :
    ContDiff ℝ 2 (packet Q edge scale seed) :=
  (hQ.add (contDiff_const.mul he)).sub seed.contDiff

theorem packet_hessian (Q edge : X → ℝ) (scale : ℝ) (seed : X →L[ℝ] ℝ)
    (hQ : ContDiff ℝ 2 Q) (he : ContDiff ℝ 2 edge) (x : X) :
    fderiv ℝ (fderiv ℝ (packet Q edge scale seed)) x =
      fderiv ℝ (fderiv ℝ Q) x + scale • fderiv ℝ (fderiv ℝ edge) x := by
  ext v w
  change fderiv ℝ (fderiv ℝ (fun z => Q z + scale * edge z - seed z)) x v w = _
  rw [hessian_sub _ _ (hQ.add (contDiff_const.mul he)) seed.contDiff,
    hessian_add _ _ hQ (contDiff_const.mul he), hessian_const_mul _ he,
    hessian_linear]
  simp only [ContinuousLinearMap.zero_apply, sub_zero, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul]

theorem packet_strongConvex (Q edge : X → ℝ) (scale nu : ℝ) (seed : X →L[ℝ] ℝ)
    (hscale : 0 ≤ scale) (hQ : ContDiff ℝ 2 Q) (he : ContDiff ℝ 2 edge)
    (hQs : StrongConvexOn (Set.univ : Set X) nu Q)
    (hec : ConvexOn ℝ (Set.univ : Set X) edge) :
    StrongConvexOn (Set.univ : Set X) nu (packet Q edge scale seed) := by
  apply strongConvex_of_hessian_lower _ nu (packet_contDiff Q edge scale seed hQ he)
  intro x v
  rw [packet_hessian Q edge scale seed hQ he]
  have h1 := hessian_lower_of_strongConvex Q nu hQ hQs x v
  have h2 := hessian_lower_of_strongConvex edge 0 he (strongConvexOn_zero.mpr hec) x v
  simp only [zero_mul] at h2
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  nlinarith only [h1, mul_nonneg hscale h2]

theorem packet_second_jet (Q edge : X → ℝ) (scale : ℝ) (seed : X →L[ℝ] ℝ)
    (hQ : ContDiff ℝ 2 Q) (he : ContDiff ℝ 2 edge) (x : X) :
    iteratedFDeriv ℝ 2 (packet Q edge scale seed) x =
      iteratedFDeriv ℝ 2 Q x + scale • iteratedFDeriv ℝ 2 edge x := by
  have hs : iteratedFDeriv ℝ 2 (seed : X → ℝ) x = 0 := by
    apply norm_eq_zero.mp
    rw [← hessian_norm_eq_second_jet, hessian_linear]
    exact ContinuousLinearMap.opNorm_zero
  change iteratedFDeriv ℝ 2 (fun z => Q z + scale * edge z - seed z) x = _
  rw [fun_iteratedFDeriv_sub_apply (hQ.add (contDiff_const.mul he)).contDiffAt seed.contDiff.contDiffAt,
    fun_iteratedFDeriv_add_apply hQ.contDiffAt (contDiff_const.mul he).contDiffAt]
  have hsm := iteratedFDeriv_const_smul_apply' (a := scale) he.contDiffAt (x := x)
  change iteratedFDeriv ℝ 2 (fun x => scale * edge x) x = _ at hsm
  rw [hsm, hs, sub_zero]

theorem packet_second_jet_bound (Q edge : X → ℝ) (scale LQ Le : ℝ) (seed : X →L[ℝ] ℝ)
    (hscale : 0 ≤ scale) (hQ : ContDiff ℝ 2 Q) (he : ContDiff ℝ 2 edge)
    (hQbound : ∀ z, ‖iteratedFDeriv ℝ 2 Q z‖ ≤ LQ)
    (hebound : ∀ z, ‖iteratedFDeriv ℝ 2 edge z‖ ≤ Le) (z : X) :
    ‖iteratedFDeriv ℝ 2 (packet Q edge scale seed) z‖ ≤ LQ + scale * Le := by
  rw [packet_second_jet Q edge scale seed hQ he]
  have hb := norm_add_le (iteratedFDeriv ℝ 2 Q z) (scale • iteratedFDeriv ℝ 2 edge z)
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hscale] at hb
  exact hb.trans (add_le_add (hQbound z) (mul_le_mul_of_nonneg_left (hebound z) hscale))

theorem packet_hessian_lipschitz (Q edge : X → ℝ) (scale rho : ℝ) (seed : X →L[ℝ] ℝ)
    (hscale : 0 ≤ scale) (hQ : ContDiff ℝ 2 Q) (he : ContDiff ℝ 2 edge)
    (hQconstant : ∀ x y, fderiv ℝ (fderiv ℝ Q) x = fderiv ℝ (fderiv ℝ Q) y)
    (heLip : ∀ x y, ‖iteratedFDeriv ℝ 2 edge x - iteratedFDeriv ℝ 2 edge y‖ ≤ rho * ‖x - y‖)
    (x y : X) :
    ‖fderiv ℝ (fderiv ℝ (packet Q edge scale seed)) x -
      fderiv ℝ (fderiv ℝ (packet Q edge scale seed)) y‖ ≤ scale * rho * ‖x - y‖ := by
  apply (hessian_difference_norm_le_second_jet _ x y).trans
  have hQt : iteratedFDeriv ℝ 2 Q x = iteratedFDeriv ℝ 2 Q y := by
    ext v
    simp only [iteratedFDeriv_two_apply]
    rw [hQconstant x y]
  rw [packet_second_jet Q edge scale seed hQ he, packet_second_jet Q edge scale seed hQ he,
    hQt, add_sub_add_left_eq_sub, ← smul_sub, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg hscale]
  convert! mul_le_mul_of_nonneg_left (heLip x y) hscale using 1 <;> try ring

end
end FangqingUnlocalizedPacketRegularity


open scoped ContDiff

namespace FangqingPrivatePacketAnalytic

open FangqingAmplifier FangqingAmplifierRegularity FangqingPathEdgeRegularity
  FangqingUnlocalizedPacketRegularity

noncomputable section

universe u

/- This is the genuine unlocalized packet.  The arbitrary linear seed has
   identically zero Hessian, so it needs no size assumption for item (i). -/
def linearPacket {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (Q edge : X → ℝ) (scale seedSize : ℝ) (handle : X) : X → ℝ :=
  packet Q edge scale (seedSize • innerSL ℝ handle)

def GradientRate {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
    (H : X → ℝ) (L : ℝ) : Prop :=
  ∀ x y, ‖gradient H x - gradient H y‖ ≤ L * ‖x - y‖

def HessianRate {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (H : X → ℝ) (rho : ℝ) : Prop :=
  ∀ x y, ‖fderiv ℝ (fderiv ℝ H) x - fderiv ℝ (fderiv ℝ H) y‖ ≤ rho * ‖x - y‖

theorem actual_private_packet_regularity (P : FlatCubic.Profile) :
    ∃ Cedge : ℝ≥0, ∀ (A B W : Type u)
      [NormedAddCommGroup A] [InnerProductSpace ℝ A] [CompleteSpace A]
      [NormedAddCommGroup B] [InnerProductSpace ℝ B] [CompleteSpace B]
      [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W],
      ∀ (q nu scale seedSize delta omega : ℝ) (C : A ≃ₗᵢ[ℝ] B)
      (n : ℕ) (v : Fin (n + 1) → PhysicalSpace A B W) (handle : PhysicalSpace A B W),
      0 ≤ q → 0 ≤ nu → 0 ≤ scale → 0 < delta → delta ≤ omega → Orthonormal ℝ v →
      let H := linearPacket (QPhysical q nu C) (pathEdge P delta omega n v) scale seedSize handle
      ContDiff ℝ 2 H ∧ StrongConvexOn (Set.univ : Set (PhysicalSpace A B W)) nu H ∧
      (∀ z, ‖iteratedFDeriv ℝ 2 H z‖ ≤ nu * (q + 2) + (4 * Cedge : ℝ) * scale * omega) ∧
      GradientRate H (nu * (q + 2) + (4 * Cedge : ℝ) * scale * omega) ∧
      HessianRate H ((8 * Cedge : ℝ) * scale) := by
  obtain ⟨Ce, hCe⟩ := FangqingPathEdgeRegularity.actual_pathEdge_regularity.{u} P
  refine ⟨Ce, ?_⟩
  intro A B W inst inst' inst'' instB instB' instB'' instW instW' instW''
    q nu scale seedSize delta omega C n v handle hq hnu hscale hd hdD hv H
  obtain ⟨he, hec, he2, heLip, heHLip⟩ := hCe (PhysicalSpace A B W) delta omega hd hdD n v hv
  have hQ := physical_quadratic_contDiff (W := W) q nu C
  have hQs := physical_quadratic_strongConvex (W := W) q nu hq hnu C
  have hs := packet_contDiff (QPhysical q nu C) (pathEdge P delta omega n v) scale
    (seedSize • innerSL ℝ handle) hQ he
  have hsecond : ∀ z, ‖iteratedFDeriv ℝ 2 H z‖ ≤
      nu * (q + 2) + (4 * Ce : ℝ) * scale * omega := by
    intro z
    have hb := packet_second_jet_bound (QPhysical q nu C) (pathEdge P delta omega n v) scale
      (nu * (q + 2)) ((4 * Ce : ℝ) * omega) (seedSize • innerSL ℝ handle) hscale hQ he
      (physical_quadratic_second_jet_bound q nu hq hnu C) he2 z
    convert! hb using 1 <;> try ring
  refine ⟨hs, packet_strongConvex _ _ scale nu _ hscale hQ he hQs hec, hsecond, ?_, ?_⟩
  · have homega : 0 < omega := hd.trans_le hdD
    let M : ℝ≥0 := ⟨nu * (q + 2) + (4 * Ce : ℝ) * scale * omega, by positivity⟩
    have hgrad := FangqingJetToRegularity.gradient_lipschitz_from_second_jet H hs M hsecond
    exact fun x y => hgrad.norm_sub_le x y
  · intro x y
    have hc : ∀ x y : PhysicalSpace A B W,
        fderiv ℝ (fderiv ℝ (QPhysical q nu C)) x = fderiv ℝ (fderiv ℝ (QPhysical q nu C)) y := by
      intro x y
      rw [physical_quadratic_hessian_constant, physical_quadratic_hessian_constant]
    have hb := packet_hessian_lipschitz (QPhysical q nu C) (pathEdge P delta omega n v)
      scale (8 * Ce : ℝ) (seedSize • innerSL ℝ handle) hscale hQ he hc heLip x y
    convert! hb using 1 <;> try ring

theorem literal_packet_eq
    {A B W : Type*} [NormedAddCommGroup A] [InnerProductSpace ℝ A]
    [NormedAddCommGroup B] [InnerProductSpace ℝ B]
    [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    (P : FlatCubic.Profile) (q cg rho barLam eta delta omega : ℝ) (C : A ≃ₗᵢ[ℝ] B)
    (n : ℕ) (v : Fin (n + 1) → PhysicalSpace A B W) (h : A) (z : PhysicalSpace A B W) :
    linearPacket (QPhysical q (cg * rho * barLam) C) (pathEdge P delta omega n v)
      (cg * rho) (cg * rho * eta) (mkPhysical h 0 0) z =
    cg * rho * (pathEdge P delta omega n v z + barLam / 2 *
      (2 * ‖z.fst.fst‖ ^ 2 + (q + 1) * ‖z.fst.snd‖ ^ 2 -
       2 * Real.sqrt q * inner ℝ (C z.fst.fst) z.fst.snd + ‖z.snd‖ ^ 2) -
       eta * inner ℝ h z.fst.fst) := by
  have hi : inner ℝ (mkPhysical h (0 : B) (0 : W)) z = inner ℝ h z.fst.fst := by
    change (inner ℝ h z.fst.fst + inner ℝ (0 : B) z.fst.snd) + inner ℝ (0 : W) z.snd = _
    simp only [inner_zero_left, add_zero]
  dsimp [linearPacket, packet, QPhysical]
  simp only [ContinuousLinearMap.smul_apply, innerSL_apply_apply, smul_eq_mul, hi]
  ring

theorem original_smoothness_scalar_budget (Ce Cw q nu scale omega : ℝ)
    (hCe : 0 ≤ Ce) (hCw : 0 ≤ Cw) (hq : 1 ≤ q) (hnu : 0 ≤ nu)
    (hscale : scale * omega = Cw * nu * q ^ 2) :
    nu * (q + 2) + 4 * Ce * scale * omega ≤ (3 + 4 * Ce * Cw) * nu * q ^ 2 := by
  have hq2 : q + 2 ≤ 3 * q ^ 2 := by nlinarith only [hq, sq_nonneg (q - 1)]
  have hfirst := mul_le_mul_of_nonneg_left hq2 hnu
  have heq : 4 * Ce * scale * omega = 4 * Ce * Cw * nu * q ^ 2 := by
    calc
      _ = 4 * Ce * (scale * omega) := by ring
      _ = _ := by rw [hscale]; ring
  rw [heq]
  nlinarith only [hfirst]

theorem universal_edge_scale_choice (Ce : ℝ) (hCe : 0 ≤ Ce) :
    ∃ cg : ℝ, 0 < cg ∧ 8 * Ce * cg ≤ 1 ∧
      ∀ rho : ℝ, 0 ≤ rho → (8 * Ce) * (cg * rho) ≤ rho := by
  refine ⟨1 / (8 * (Ce + 1)), by positivity, ?_, ?_⟩
  · rw [mul_one_div]
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 8 * (Ce + 1))).mpr
    nlinarith only [hCe]
  · intro rho hrho
    have hh : 8 * Ce * (1 / (8 * (Ce + 1))) ≤ 1 := by
      rw [mul_one_div]
      apply (div_le_iff₀ (by positivity : (0 : ℝ) < 8 * (Ce + 1))).mpr
      nlinarith only [hCe]
    have hm := mul_le_mul_of_nonneg_right hh hrho
    convert! hm using 1 <;> try ring

end
end FangqingPrivatePacketAnalytic


open scoped BigOperators Topology ContDiff

namespace FangqingRadialGateBounds

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/- All constants below are independent of the dimension of E. -/
theorem identity_iterated_bound (B : ℝ) (hB : 1 ≤ B) (x : E) (hx : ‖x‖ ≤ B) (n : ℕ) :
    ‖iteratedFDeriv ℝ n (id : E → E) x‖ ≤ B := by
  cases n with
  | zero => simpa only [norm_iteratedFDeriv_zero, id_eq] using hx
  | succ n =>
    rw [← norm_iteratedFDeriv_fderiv]
    have hid : fderiv ℝ (id : E → E) = fun _ => ContinuousLinearMap.id ℝ E := by
      funext z
      exact fderiv_id
    rw [hid]
    cases n with
    | zero => simpa only [norm_iteratedFDeriv_zero] using ContinuousLinearMap.norm_id_le.trans hB
    | succ n =>
      rw [iteratedFDeriv_succ_const]
      simp only [Pi.zero_apply, norm_zero]
      linarith only [hB]

theorem normsq_iterated_bound (B : ℝ) (hB : 1 ≤ B) (x : E) (hx : ‖x‖ ≤ B) (n : ℕ) :
    ‖iteratedFDeriv ℝ n (fun z : E => ‖z‖ ^ 2) x‖ ≤ (2 : ℝ) ^ n * B ^ 2 := by
  have hb := (innerSL ℝ (E := E)).norm_iteratedFDeriv_le_of_bilinear_of_le_one
    (contDiff_id : ContDiff ℝ ⊤ (id : E → E)) contDiff_id x
    (by simp : (n : ℕ∞ω) ≤ ⊤) (norm_innerSL_le ℝ)
  have hs : (∑ k ∈ Finset.range (n + 1),
      (n.choose k : ℝ) * ‖iteratedFDeriv ℝ k (id : E → E) x‖ *
        ‖iteratedFDeriv ℝ (n - k) (id : E → E) x‖) ≤ (2 : ℝ) ^ n * B ^ 2 := by
    calc
      _ ≤ ∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ) * B ^ 2 := by
        apply Finset.sum_le_sum
        intro k hk
        have h1 := identity_iterated_bound B hB x hx k
        have h2 := identity_iterated_bound B hB x hx (n - k)
        have hh := mul_le_mul (mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg (n.choose k)))
          h2 (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (by linarith only [hB]))
        nlinarith only [hh]
      _ = (2 : ℝ) ^ n * B ^ 2 := by
        rw [← Finset.sum_mul]
        congr 1
        exact_mod_cast Nat.sum_range_choose n
  have hb' : ‖iteratedFDeriv ℝ n (fun z : E => ‖z‖ ^ 2) x‖ ≤
      ∑ k ∈ Finset.range (n + 1),
        (n.choose k : ℝ) * ‖iteratedFDeriv ℝ k (id : E → E) x‖ *
          ‖iteratedFDeriv ℝ (n - k) (id : E → E) x‖ := by
    have hfun : (fun z : E => (innerSL ℝ z) z) = (fun z : E => ‖z‖ ^ 2) := by
      funext z
      exact real_inner_self_eq_norm_sq z
    simp only [id_eq] at hb
    rw [hfun] at hb
    exact hb
  exact hb'.trans hs

def baseGate (theta : ℝ → ℝ) (z : E) : ℝ := theta (‖z‖ ^ 2)

theorem baseGate_contDiff (theta : ℝ → ℝ) (n : ℕ∞ω) (htheta : ContDiff ℝ n theta) :
    ContDiff ℝ n (baseGate (E := E) theta) :=
  htheta.comp (contDiff_id.norm_sq ℝ)

theorem baseGate_iterated_bound (theta : ℝ → ℝ) (n : ℕ)
    (htheta : ContDiff ℝ n theta) (hn : n ≠ 0) (B C : ℝ) (hB : 1 ≤ B) (hC : 0 ≤ C)
    (hderiv : ∀ j, j ≤ n → ∀ u : ℝ, ‖iteratedFDeriv ℝ j theta u‖ ≤ C)
    (hzero : ∀ u : ℝ, B ^ 2 < u → theta u = 0) (x : E) :
    ‖iteratedFDeriv ℝ n (baseGate theta) x‖ ≤ n.factorial * C * (2 * B ^ 2) ^ n := by
  by_cases hx : ‖x‖ ≤ B
  · have hD : ∀ i : ℕ, 1 ≤ i → i ≤ n →
        ‖iteratedFDeriv ℝ i (fun z : E => ‖z‖ ^ 2) x‖ ≤ (2 * B ^ 2) ^ i := by
      intro i hi hin
      have hsq : 1 ≤ B ^ 2 := by nlinarith [sq_nonneg (B - 1)]
      have hpow : B ^ 2 ≤ (B ^ 2) ^ i := le_self_pow₀ hsq (by omega)
      calc
        _ ≤ (2 : ℝ) ^ i * B ^ 2 := normsq_iterated_bound B hB x hx i
        _ ≤ (2 : ℝ) ^ i * (B ^ 2) ^ i :=
          mul_le_mul_of_nonneg_left hpow (by positivity)
        _ = _ := by rw [mul_pow]
    have hh := norm_iteratedFDeriv_comp_le htheta
      (contDiff_id.norm_sq ℝ : ContDiff ℝ n (fun z : E => ‖z‖ ^ 2)) le_rfl x
      (fun j hj => hderiv j hj _) hD
    simpa only [baseGate, Function.comp_def, id_eq] using! hh
  · have hx' : B < ‖x‖ := lt_of_not_ge hx
    have heq : baseGate (E := E) theta =ᶠ[𝓝 x] (fun _ => 0) := by
      have hopen : {z : E | B < ‖z‖} ∈ 𝓝 x :=
        (isOpen_lt continuous_const continuous_norm).mem_nhds hx'
      filter_upwards [hopen] with z hz
      apply hzero
      have hn0 := norm_nonneg z
      have hB0 : 0 < B := by linarith only [hB]
      nlinarith only [hz, hn0, hB0]
    have hd := (heq.iteratedFDeriv ℝ n).eq_of_nhds
    rw [hd, iteratedFDeriv_const_of_ne hn]
    simp only [Pi.zero_apply, norm_zero]
    positivity

/- Scaling and translation retain the exact R^{-j} derivative scale. -/
def scaledGate (theta : ℝ → ℝ) (R : ℝ) (center z : E) : ℝ :=
  theta (‖z - center‖ ^ 2 / R ^ 2)

theorem scaledGate_eq (theta : ℝ → ℝ) (R : ℝ) (center z : E) (hR : 0 < R) :
    scaledGate theta R center z = baseGate theta (R⁻¹ • (z - center)) := by
  dsimp [scaledGate, baseGate]
  congr 1
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hR), mul_pow]
  field_simp

theorem scaledGate_iterated_bound (theta : ℝ → ℝ) (n : ℕ)
    (htheta : ContDiff ℝ n theta) (hn : n ≠ 0) (B C R : ℝ) (hB : 1 ≤ B) (hC : 0 ≤ C)
    (hR : 0 < R)
    (hderiv : ∀ j, j ≤ n → ∀ u : ℝ, ‖iteratedFDeriv ℝ j theta u‖ ≤ C)
    (hzero : ∀ u : ℝ, B ^ 2 < u → theta u = 0) (center x : E) :
    ‖iteratedFDeriv ℝ n (scaledGate theta R center) x‖ ≤
      (n.factorial * C * (2 * B ^ 2) ^ n) / R ^ n := by
  have hfun : scaledGate theta R center =
      (fun z => baseGate theta (R⁻¹ • (z - center))) := by
    funext z
    exact scaledGate_eq theta R center z hR
  rw [hfun, iteratedFDeriv_comp_sub (f := fun z : E => baseGate theta (R⁻¹ • z)) n center x]
  have hh := congrFun (iteratedFDeriv_comp_const_smul R⁻¹ (baseGate_contDiff theta n htheta))
    (x - center)
  rw [hh, norm_smul, Real.norm_eq_abs, abs_pow, abs_of_pos (inv_pos.mpr hR)]
  have hb := baseGate_iterated_bound theta n htheta hn B C hB hC hderiv hzero
    (R⁻¹ • (x - center))
  have hm := mul_le_mul_of_nonneg_left hb (by positivity : 0 ≤ R⁻¹ ^ n)
  convert! hm using 1 <;> simp only [div_eq_mul_inv, inv_pow] <;> ring


/- A fixed smooth scalar profile supplies its own finite constants.
   These constants are chosen on a compact interval in R, never on a
   dimension-dependent ball in E. -/
theorem scalar_profile_derivatives_bounded (theta : ℝ → ℝ) (n : ℕ) (B : ℝ)
    (htheta : ContDiff ℝ n theta)
    (hleft : ∀ u : ℝ, u < 0 → theta u = 1)
    (hright : ∀ u : ℝ, B ^ 2 < u → theta u = 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ j, j ≤ n → ∀ u : ℝ, ‖iteratedFDeriv ℝ j theta u‖ ≤ C := by
  classical
  have h_each : ∀ j : Fin (n + 1), ∃ C : ℝ, 0 ≤ C ∧
      ∀ u : ℝ, ‖iteratedFDeriv ℝ j.val theta u‖ ≤ C := by
    intro j
    have hc : Continuous (iteratedFDeriv ℝ j.val theta) :=
      htheta.continuous_iteratedFDeriv (by exact_mod_cast (by omega : j.val ≤ n))
    obtain ⟨C0, hC0⟩ := (isCompact_Icc : IsCompact (Set.Icc (0 : ℝ) (B ^ 2))).exists_bound_of_continuousOn
      hc.continuousOn
    refine ⟨max C0 1, (by positivity), ?_⟩
    intro u
    by_cases hu : u < 0
    · have heq : theta =ᶠ[𝓝 u] (fun _ => (1 : ℝ)) := by
        filter_upwards [Iio_mem_nhds hu] with v hv
        exact hleft v hv
      rw [(heq.iteratedFDeriv ℝ j.val).eq_of_nhds]
      by_cases hj : j.val = 0
      · change ‖iteratedFDeriv ℝ j.val (fun _ : ℝ => (1 : ℝ)) u‖ ≤ max C0 1
        rw [hj, norm_iteratedFDeriv_zero, norm_one]
        exact le_max_right C0 1
      · rw [iteratedFDeriv_const_of_ne hj]
        simp only [Pi.zero_apply, norm_zero]
        positivity
    · by_cases hr : B ^ 2 < u
      · have heq : theta =ᶠ[𝓝 u] (fun _ => (0 : ℝ)) := by
          filter_upwards [Ioi_mem_nhds hr] with v hv
          exact hright v hv
        rw [(heq.iteratedFDeriv ℝ j.val).eq_of_nhds]
        by_cases hj : j.val = 0
        · change ‖iteratedFDeriv ℝ j.val (fun _ : ℝ => (0 : ℝ)) u‖ ≤ max C0 1
          rw [hj, norm_iteratedFDeriv_zero, norm_zero]
          positivity
        · rw [iteratedFDeriv_const_of_ne hj]
          simp only [Pi.zero_apply, norm_zero]
          positivity
      · exact (hC0 u ⟨le_of_not_gt hu, le_of_not_gt hr⟩).trans (le_max_left _ _)
  choose Cs hCs using h_each
  refine ⟨∑ j, Cs j, Finset.sum_nonneg (fun j _ => (hCs j).1), ?_⟩
  intro j hj u
  let jj : Fin (n + 1) := ⟨j, by omega⟩
  have hbound := (hCs jj).2 u
  exact hbound.trans (Finset.single_le_sum (fun k _ => (hCs k).1) (Finset.mem_univ jj))

universe u

/- The order of quantifiers records the dimension-free statement:
   one numerical K works for every real Hilbert-space dimension. -/
theorem universal_three_gate_bounds (theta : ℝ → ℝ) (B : ℝ) (hB : 1 ≤ B)
    (htheta : ContDiff ℝ 3 theta)
    (hleft : ∀ u : ℝ, u < 0 → theta u = 1)
    (hright : ∀ u : ℝ, B ^ 2 < u → theta u = 0) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (F : Type u) [NormedAddCommGroup F] [InnerProductSpace ℝ F],
      ∀ (R : ℝ), 0 < R → ∀ (center x : F) (j : ℕ), 1 ≤ j → j ≤ 3 →
        ‖iteratedFDeriv ℝ j (scaledGate theta R center) x‖ ≤ K / R ^ j := by
  obtain ⟨C, hC, hderiv⟩ := scalar_profile_derivatives_bounded theta 3 B htheta hleft hright
  let D := 2 * B ^ 2
  have hD : 1 ≤ D := by dsimp [D]; nlinarith [sq_nonneg (B - 1)]
  refine ⟨6 * C * D ^ 3, (by positivity), ?_⟩
  intro F inst inst' R hR center x j hj hj3
  have hb := scaledGate_iterated_bound theta j (htheta.of_le (by exact_mod_cast hj3))
    (by omega) B C R hB hC hR (fun i hi => hderiv i (hi.trans hj3)) hright center x
  refine hb.trans ?_
  apply (div_le_div_iff_of_pos_right (pow_pos hR j)).mpr
  have hfac : (j.factorial : ℝ) ≤ 6 := by
    have hh := Nat.factorial_le hj3
    norm_num at hh ⊢
    exact_mod_cast hh
  have hpow : D ^ j ≤ D ^ 3 := pow_le_pow_right₀ hD hj3
  exact mul_le_mul (mul_le_mul_of_nonneg_right hfac hC) hpow
    (by positivity) (by positivity)

end
end FangqingRadialGateBounds


open scoped ContDiff

namespace FangqingGateBudgetBridge

open FangqingRadialGateBounds

noncomputable section

universe u

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem scaledGate_contDiff (theta : ℝ → ℝ) (R : ℝ) (center : E) (hR : 0 < R)
    (htheta : ContDiff ℝ 3 theta) : ContDiff ℝ 3 (scaledGate theta R center) := by
  have hb := baseGate_contDiff (E := E) theta 3 htheta
  have hsub : ContDiff ℝ 3 (fun z : E => z - center) := contDiff_id.sub contDiff_const
  have ha : ContDiff ℝ 3 (fun z : E => R⁻¹ • (z - center)) := hsub.const_smul _
  have hc := hb.comp ha
  have heq : scaledGate (E := E) theta R center =
      (fun z : E => baseGate theta (R⁻¹ • (z - center))) := by
    funext z
    exact scaledGate_eq theta R center z hR
  rw [heq]
  exact hc

theorem first_scalar_bound (f : E → ℝ) (P : ℝ) (x v : E)
    (hjet : ‖iteratedFDeriv ℝ 1 f x‖ ≤ P) : |fderiv ℝ f x v| ≤ P * ‖v‖ := by
  have hh := (iteratedFDeriv ℝ 1 f x).le_opNorm ![v]
  simp only [iteratedFDeriv_one_apply, Matrix.cons_val_zero, Fin.prod_univ_one,
    Real.norm_eq_abs] at hh
  exact hh.trans (mul_le_mul_of_nonneg_right hjet (norm_nonneg v))

theorem second_scalar_bound (f : E → ℝ) (H : ℝ) (x v : E)
    (hjet : ‖iteratedFDeriv ℝ 2 f x‖ ≤ H) :
    |fderiv ℝ (fderiv ℝ f) x v v| ≤ H * ‖v‖ ^ 2 := by
  have hh := (iteratedFDeriv ℝ 2 f x).le_opNorm ![v, v]
  simp only [iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Fin.prod_univ_two, Real.norm_eq_abs] at hh
  have hm := mul_le_mul_of_nonneg_right hjet (sq_nonneg ‖v‖)
  nlinarith only [hh, hm]

theorem universal_gate_scalar_budgets (theta : ℝ → ℝ) (B : ℝ) (hB : 1 ≤ B)
    (htheta : ContDiff ℝ 3 theta)
    (hleft : ∀ u : ℝ, u < 0 → theta u = 1)
    (hright : ∀ u : ℝ, B ^ 2 < u → theta u = 0) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (F : Type u) [NormedAddCommGroup F] [InnerProductSpace ℝ F],
      ∀ (R : ℝ), 0 < R → ∀ (center : F),
        ContDiff ℝ 3 (scaledGate theta R center) ∧
        (∀ s v : F, |fderiv ℝ (scaledGate theta R center) s v| ≤ K / R * ‖v‖) ∧
        (∀ s v : F, |fderiv ℝ (fderiv ℝ (scaledGate theta R center)) s v v| ≤ K / R ^ 2 * ‖v‖ ^ 2) := by
  obtain ⟨K, hK, hbound⟩ := universal_three_gate_bounds.{u} theta B hB htheta hleft hright
  refine ⟨K, hK, ?_⟩
  intro F inst inst' R hR center
  refine ⟨scaledGate_contDiff theta R center hR htheta, ?_, ?_⟩
  · intro s v
    apply first_scalar_bound (scaledGate theta R center) (K / R) s v
    simpa only [pow_one] using hbound F R hR center s 1 le_rfl (by norm_num)
  · intro s v
    exact second_scalar_bound (scaledGate theta R center) (K / R ^ 2) s v
      (hbound F R hR center s 2 (by norm_num) (by norm_num))

end
end FangqingGateBudgetBridge


open scoped BigOperators ContDiff Topology

namespace FangqingSaturatedProfileBounds

noncomputable section

theorem scalar_saturation_derivatives_bounded (phi : ℝ → ℝ) (n : ℕ) (B left right : ℝ)
    (hphi : ContDiff ℝ n phi) (hleft : ∀ u, u < -B → phi u = left)
    (hright : ∀ u, B < u → phi u = right) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ j, j ≤ n → ∀ u : ℝ, ‖iteratedFDeriv ℝ j phi u‖ ≤ C := by
  classical
  have h_each : ∀ j : Fin (n + 1), ∃ C : ℝ, 0 ≤ C ∧
      ∀ u : ℝ, ‖iteratedFDeriv ℝ j.val phi u‖ ≤ C := by
    intro j
    have hc : Continuous (iteratedFDeriv ℝ j.val phi) :=
      hphi.continuous_iteratedFDeriv (by exact_mod_cast (by omega : j.val ≤ n))
    obtain ⟨C0, hC0⟩ := (isCompact_Icc : IsCompact (Set.Icc (-B) B)).exists_bound_of_continuousOn
      hc.continuousOn
    let M := max C0 (max |left| |right|)
    have hM : 0 ≤ M := (abs_nonneg left).trans ((le_max_left _ _).trans (le_max_right _ _))
    refine ⟨M, hM, ?_⟩
    intro u
    by_cases hl : u < -B
    · have heq : phi =ᶠ[𝓝 u] (fun _ => left) := by
        filter_upwards [Iio_mem_nhds hl] with v hv
        exact hleft v hv
      rw [(heq.iteratedFDeriv ℝ j.val).eq_of_nhds]
      by_cases hj : j.val = 0
      · change ‖iteratedFDeriv ℝ j.val (fun _ : ℝ => left) u‖ ≤ M
        rw [hj, norm_iteratedFDeriv_zero, Real.norm_eq_abs]
        exact (le_max_left _ _).trans (le_max_right _ _)
      · rw [iteratedFDeriv_const_of_ne hj]
        simpa only [Pi.zero_apply, norm_zero] using hM
    · by_cases hr : B < u
      · have heq : phi =ᶠ[𝓝 u] (fun _ => right) := by
          filter_upwards [Ioi_mem_nhds hr] with v hv
          exact hright v hv
        rw [(heq.iteratedFDeriv ℝ j.val).eq_of_nhds]
        by_cases hj : j.val = 0
        · change ‖iteratedFDeriv ℝ j.val (fun _ : ℝ => right) u‖ ≤ M
          rw [hj, norm_iteratedFDeriv_zero, Real.norm_eq_abs]
          exact (le_max_right _ _).trans (le_max_right _ _)
        · rw [iteratedFDeriv_const_of_ne hj]
          simpa only [Pi.zero_apply, norm_zero] using hM
      · exact (hC0 u ⟨le_of_not_gt hl, le_of_not_gt hr⟩).trans (le_max_left _ _)
  choose Cs hCs using h_each
  refine ⟨∑ j, Cs j, Finset.sum_nonneg (fun j _ => (hCs j).1), ?_⟩
  intro j hj u
  let jj : Fin (n + 1) := ⟨j, by omega⟩
  exact ((hCs jj).2 u).trans
    (Finset.single_le_sum (fun k _ => (hCs k).1) (Finset.mem_univ jj))

theorem monotone_cutoff_range (theta : ℝ → ℝ) (B : ℝ) (hanti : Antitone theta)
    (hleft : ∀ u : ℝ, u < 0 → theta u = 1)
    (hright : ∀ u : ℝ, B ^ 2 < u → theta u = 0) (u : ℝ) :
    0 ≤ theta u ∧ theta u ≤ 1 := by
  have hr := hanti (le_max_left u (B ^ 2 + 1))
  have hhi : B ^ 2 < max u (B ^ 2 + 1) := lt_of_lt_of_le (by linarith) (le_max_right _ _)
  rw [hright _ hhi] at hr
  have hl := hanti (min_le_right (-1) u)
  have hlo : min (-1) u < (0 : ℝ) := lt_of_le_of_lt (min_le_left _ _) (by norm_num)
  rw [hleft _ hlo] at hl
  exact ⟨hr, hl⟩

end
end FangqingSaturatedProfileBounds


open scoped BigOperators ContDiff

namespace FangqingLinearProfileJetBounds

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def linearProfile (phi : ℝ → ℝ) (A : ℝ) (h : E) (z : E) : ℝ :=
  phi (inner ℝ h z / A)

def coordinate (A : ℝ) (h : E) : E →L[ℝ] ℝ := A⁻¹ • innerSL ℝ h

theorem linearProfile_eq_comp (phi : ℝ → ℝ) (A : ℝ) (h : E) :
    linearProfile phi A h = phi ∘ coordinate A h := by
  funext z
  dsimp [linearProfile, coordinate]
  rw [ContinuousLinearMap.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]
  rfl

theorem coordinate_norm_le (A : ℝ) (h : E) (hA : 0 < A) (hh : ‖h‖ ≤ 1) :
    ‖coordinate A h‖ ≤ A⁻¹ := by
  rw [coordinate, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hA), innerSL_apply_norm]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hh (inv_nonneg.mpr hA.le)

theorem linearProfile_contDiff (phi : ℝ → ℝ) (A : ℝ) (h : E) (hphi : ContDiff ℝ 3 phi) :
    ContDiff ℝ 3 (linearProfile phi A h) := by
  rw [linearProfile_eq_comp]
  exact hphi.comp_continuousLinearMap

theorem linearProfile_jet_bound (phi : ℝ → ℝ) (A C : ℝ) (h x : E)
    (hA : 0 < A) (hC : 0 ≤ C) (hh : ‖h‖ ≤ 1) (hphi : ContDiff ℝ 3 phi)
    (hderiv : ∀ j, j ≤ 3 → ∀ u : ℝ, ‖iteratedFDeriv ℝ j phi u‖ ≤ C)
    (j : ℕ) (hj : j ≤ 3) :
    ‖iteratedFDeriv ℝ j (linearProfile phi A h) x‖ ≤ C / A ^ j := by
  rw [linearProfile_eq_comp, (coordinate A h).iteratedFDeriv_comp_right hphi x (by exact_mod_cast hj)]
  have hop := (iteratedFDeriv ℝ j phi (coordinate A h x)).norm_compContinuousLinearMap_le
    (fun _ => coordinate A h)
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hop
  have hp := pow_le_pow_left₀ (norm_nonneg (coordinate A h)) (coordinate_norm_le A h hA hh) j
  have hb := hderiv j hj (coordinate A h x)
  have hm := mul_le_mul hb hp (by positivity : 0 ≤ ‖coordinate A h‖ ^ j) hC
  calc
    _ ≤ C * A⁻¹ ^ j := hop.trans hm
    _ = C / A ^ j := by rw [inv_pow, div_eq_mul_inv]

end
end FangqingLinearProfileJetBounds


open scoped BigOperators ContDiff

namespace FangqingRelayProductBounds

noncomputable section

variable {X E : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem norm_iterated_comp_contraction (f : E → ℝ) (P : X →L[ℝ] E)
    (N : ℕ∞ω) (hf : ContDiff ℝ N f) (hP : ‖P‖ ≤ 1) (x : X)
    (j : ℕ) (hj : (j : ℕ∞ω) ≤ N) :
    ‖iteratedFDeriv ℝ j (f ∘ P) x‖ ≤ ‖iteratedFDeriv ℝ j f (P x)‖ := by
  rw [P.iteratedFDeriv_comp_right hf x hj]
  have hbound := (iteratedFDeriv ℝ j f (P x)).norm_compContinuousLinearMap_le (fun _ => P)
  have hp : ‖P‖ ^ j ≤ 1 := pow_le_one₀ (norm_nonneg P) hP
  have hm := mul_le_mul_of_nonneg_left hp (norm_nonneg (iteratedFDeriv ℝ j f (P x)))
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, mul_one] at hbound hm
  exact hbound.trans hm

theorem product_iterated_bound (f g : X → ℝ) (N : ℕ∞ω)
    (hf : ContDiff ℝ N f) (hg : ContDiff ℝ N g) (x : X) (j : ℕ)
    (hj : (j : ℕ∞ω) ≤ N) (A B : ℕ → ℝ)
    (hA : ∀ i, i ≤ j → ‖iteratedFDeriv ℝ i f x‖ ≤ A i)
    (hB : ∀ i, i ≤ j → ‖iteratedFDeriv ℝ i g x‖ ≤ B i) :
    ‖iteratedFDeriv ℝ j (fun z => f z * g z) x‖ ≤
      ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * A i * B (j - i) := by
  refine (norm_iteratedFDeriv_mul_le hf hg x hj).trans ?_
  apply Finset.sum_le_sum
  intro i hi
  have hi' : i ≤ j := by have hh := Finset.mem_range.mp hi; omega
  have hAi := hA i hi'
  have hBi := hB (j - i) (Nat.sub_le _ _)
  exact mul_le_mul (mul_le_mul_of_nonneg_left hAi (Nat.cast_nonneg _)) hBi
    (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) ((norm_nonneg _).trans hAi))

def budget (a0 a1 a2 a3 : ℝ) : ℕ → ℝ
  | 0 => a0
  | 1 => a1
  | 2 => a2
  | _ => a3

theorem product_second_bound (f g : X → ℝ) (hf : ContDiff ℝ 3 f) (hg : ContDiff ℝ 3 g)
    (x : X) (a0 a1 a2 b0 b1 b2 : ℝ)
    (hA0 : ‖f x‖ ≤ a0) (hA1 : ‖iteratedFDeriv ℝ 1 f x‖ ≤ a1)
    (hA2 : ‖iteratedFDeriv ℝ 2 f x‖ ≤ a2)
    (hB0 : ‖g x‖ ≤ b0) (hB1 : ‖iteratedFDeriv ℝ 1 g x‖ ≤ b1)
    (hB2 : ‖iteratedFDeriv ℝ 2 g x‖ ≤ b2) :
    ‖iteratedFDeriv ℝ 2 (fun z => f z * g z) x‖ ≤ a0 * b2 + 2 * a1 * b1 + a2 * b0 := by
  have hA : ∀ i, i ≤ 2 → ‖iteratedFDeriv ℝ i f x‖ ≤ budget a0 a1 a2 0 i := by
    intro i hi
    interval_cases i
    · simpa only [budget, norm_iteratedFDeriv_zero] using hA0
    · simpa only [budget] using hA1
    · simpa only [budget] using hA2
  have hB : ∀ i, i ≤ 2 → ‖iteratedFDeriv ℝ i g x‖ ≤ budget b0 b1 b2 0 i := by
    intro i hi
    interval_cases i
    · simpa only [budget, norm_iteratedFDeriv_zero] using hB0
    · simpa only [budget] using hB1
    · simpa only [budget] using hB2
  have hh := product_iterated_bound f g 3 hf hg x 2 (by norm_num)
    (budget a0 a1 a2 0) (budget b0 b1 b2 0) hA hB
  norm_num [Finset.sum_range_succ, budget] at hh
  nlinarith only [hh]

theorem product_third_bound (f g : X → ℝ) (hf : ContDiff ℝ 3 f) (hg : ContDiff ℝ 3 g)
    (x : X) (a0 a1 a2 a3 b0 b1 b2 b3 : ℝ)
    (hA0 : ‖f x‖ ≤ a0) (hA1 : ‖iteratedFDeriv ℝ 1 f x‖ ≤ a1)
    (hA2 : ‖iteratedFDeriv ℝ 2 f x‖ ≤ a2) (hA3 : ‖iteratedFDeriv ℝ 3 f x‖ ≤ a3)
    (hB0 : ‖g x‖ ≤ b0) (hB1 : ‖iteratedFDeriv ℝ 1 g x‖ ≤ b1)
    (hB2 : ‖iteratedFDeriv ℝ 2 g x‖ ≤ b2) (hB3 : ‖iteratedFDeriv ℝ 3 g x‖ ≤ b3) :
    ‖iteratedFDeriv ℝ 3 (fun z => f z * g z) x‖ ≤
      a0 * b3 + 3 * a1 * b2 + 3 * a2 * b1 + a3 * b0 := by
  have hA : ∀ i, i ≤ 3 → ‖iteratedFDeriv ℝ i f x‖ ≤ budget a0 a1 a2 a3 i := by
    intro i hi
    interval_cases i
    · simpa only [budget, norm_iteratedFDeriv_zero] using hA0
    · simpa only [budget] using hA1
    · simpa only [budget] using hA2
    · simpa only [budget] using hA3
  have hB : ∀ i, i ≤ 3 → ‖iteratedFDeriv ℝ i g x‖ ≤ budget b0 b1 b2 b3 i := by
    intro i hi
    interval_cases i
    · simpa only [budget, norm_iteratedFDeriv_zero] using hB0
    · simpa only [budget] using hB1
    · simpa only [budget] using hB2
    · simpa only [budget] using hB3
  have hh := product_iterated_bound f g 3 hf hg x 3 (by norm_num)
    (budget a0 a1 a2 a3) (budget b0 b1 b2 b3) hA hB
  norm_num [Finset.sum_range_succ, budget] at hh
  nlinarith only [hh]

end
end FangqingRelayProductBounds


namespace FangqingNormalizedEndpointDifference

variable {E : Type*}

theorem minima_difference_bound (H0 H1 : E → ℝ) (z0 z1 : E) (M : ℝ)
    (hmin0 : ∀ z, H0 z0 ≤ H0 z) (hmin1 : ∀ z, H1 z1 ≤ H1 z)
    (hdiff : ∀ z, |H1 z - H0 z| ≤ M) : |H1 z1 - H0 z0| ≤ M := by
  have h0 := abs_le.mp (hdiff z0)
  have h1 := abs_le.mp (hdiff z1)
  apply abs_le.mpr
  constructor <;> linarith only [h0.1, h0.2, h1.1, h1.2, hmin0 z1, hmin1 z0]

theorem normalized_difference_bound (H0 H1 : E → ℝ) (z0 z1 : E) (M : ℝ)
    (hmin0 : ∀ z, H0 z0 ≤ H0 z) (hmin1 : ∀ z, H1 z1 ≤ H1 z)
    (hdiff : ∀ z, |H1 z - H0 z| ≤ M) (z : E) :
    |H0 z - H1 z + H1 z1 - H0 z0| ≤ 2 * M := by
  have hn := minima_difference_bound H0 H1 z0 z1 M hmin0 hmin1 hdiff
  have hd : |H0 z - H1 z| ≤ M := by simpa only [abs_sub_comm] using hdiff z
  have hh := abs_add_le (H0 z - H1 z) (H1 z1 - H0 z0)
  have heq : H0 z - H1 z + H1 z1 - H0 z0 =
      (H0 z - H1 z) + (H1 z1 - H0 z0) := by ring
  rw [heq]
  linarith only [hh, hn, hd]

def inactive (Q base cutoff collar : E → ℝ) (z : E) : ℝ :=
  Q z + cutoff z * base z + collar z

def active (Q base cutoff collar coordinate : E → ℝ) (phi : ℝ → ℝ) (amplitude : ℝ) (z : E) : ℝ :=
  Q z + cutoff z * (base z - amplitude * phi (coordinate z)) + collar z

theorem actual_endpoint_difference (Q base cutoff collar coordinate : E → ℝ)
    (phi : ℝ → ℝ) (amplitude : ℝ) (z : E) :
    inactive Q base cutoff collar z - active Q base cutoff collar coordinate phi amplitude z =
      amplitude * cutoff z * phi (coordinate z) := by
  dsimp [inactive, active]
  ring

theorem actual_normalized_difference_bound (Q base cutoff collar coordinate : E → ℝ)
    (phi : ℝ → ℝ) (amplitude C : ℝ) (ha : 0 ≤ amplitude) (hC : 0 ≤ C)
    (hcutoff : ∀ z, 0 ≤ cutoff z ∧ cutoff z ≤ 1)
    (hphi : ∀ u, |phi u| ≤ C) (z0 z1 : E)
    (hmin0 : ∀ z, inactive Q base cutoff collar z0 ≤ inactive Q base cutoff collar z)
    (hmin1 : ∀ z, active Q base cutoff collar coordinate phi amplitude z1 ≤
      active Q base cutoff collar coordinate phi amplitude z) (z : E) :
    |inactive Q base cutoff collar z - active Q base cutoff collar coordinate phi amplitude z +
      active Q base cutoff collar coordinate phi amplitude z1 - inactive Q base cutoff collar z0| ≤
      2 * amplitude * C := by
  have hdiff : ∀ z, |active Q base cutoff collar coordinate phi amplitude z -
      inactive Q base cutoff collar z| ≤ amplitude * C := by
    intro w
    rw [abs_sub_comm, actual_endpoint_difference, abs_mul, abs_mul,
      abs_of_nonneg ha, abs_of_nonneg (hcutoff w).1]
    have hh := mul_le_mul (hcutoff w).2 (hphi (coordinate w)) (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
    have hm := mul_le_mul_of_nonneg_left hh ha
    simpa only [one_mul, mul_assoc] using hm
  have hh := normalized_difference_bound (inactive Q base cutoff collar)
    (active Q base cutoff collar coordinate phi amplitude) z0 z1 (amplitude * C) hmin0 hmin1 hdiff z
  nlinarith only [hh]

end FangqingNormalizedEndpointDifference


open scoped BigOperators ContDiff

namespace FangqingLocalizedSeedJets

open FangqingRadialGateBounds FangqingGateBudgetBridge FangqingLinearProfileJetBounds
  FangqingRelayProductBounds FangqingNormalizedEndpointDifference

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def localizedSeed (theta phi : ℝ → ℝ) (R A amplitude : ℝ) (handle z : E) : ℝ :=
  amplitude * (scaledGate theta R 0 z * linearProfile phi A handle z)

def normalizedDifference (H0 H1 : E → ℝ) (z0 z1 z : E) : ℝ :=
  H0 z - H1 z + H1 z1 - H0 z0

theorem product_geometric_jet_bound (f g : E → ℝ) (hf : ContDiff ℝ 3 f) (hg : ContDiff ℝ 3 g)
    (D Kf Kg : ℝ) (hD : 0 < D) (hKf : 0 ≤ Kf) (hKg : 0 ≤ Kg) (x : E)
    (hF : ∀ i, i ≤ 3 → ‖iteratedFDeriv ℝ i f x‖ ≤ Kf / D ^ i)
    (hG : ∀ i, i ≤ 3 → ‖iteratedFDeriv ℝ i g x‖ ≤ Kg / D ^ i)
    (j : ℕ) (hj : j ≤ 3) :
    ‖iteratedFDeriv ℝ j (fun z => f z * g z) x‖ ≤ (2 : ℝ) ^ j * Kf * Kg / D ^ j := by
  have hh := product_iterated_bound f g 3 hf hg x j (by exact_mod_cast hj)
    (fun i => Kf / D ^ i) (fun i => Kg / D ^ i)
    (fun i hi => hF i (hi.trans hj)) (fun i hi => hG i (hi.trans hj))
  have heq : (∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * (Kf / D ^ i) * (Kg / D ^ (j - i))) =
      (2 : ℝ) ^ j * Kf * Kg / D ^ j := by
    calc
      _ = ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * (Kf * Kg / D ^ j) := by
        apply Finset.sum_congr rfl
        intro i hi
        have hij : i ≤ j := by have hh := Finset.mem_range.mp hi; omega
        have hterm : (Kf / D ^ i) * (Kg / D ^ (j - i)) = Kf * Kg / D ^ j := by
          rw [div_mul_div_comm, ← pow_add, show i + (j - i) = j by omega]
        calc
          _ = (j.choose i : ℝ) * ((Kf / D ^ i) * (Kg / D ^ (j - i))) := by ring
          _ = _ := by rw [hterm]
      _ = _ := by
        rw [← Finset.sum_mul]
        have hchoose : (∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ)) = (2 : ℝ) ^ j := by
          exact_mod_cast Nat.sum_range_choose j
        rw [hchoose]
        ring
  exact heq ▸ hh

theorem localizedSeed_contDiff (theta phi : ℝ → ℝ) (R A amplitude : ℝ) (handle : E)
    (hR : 0 < R) (htheta : ContDiff ℝ 3 theta) (hphi : ContDiff ℝ 3 phi) :
    ContDiff ℝ 3 (localizedSeed theta phi R A amplitude handle) := by
  have hf := scaledGate_contDiff (E := E) theta R 0 hR htheta
  have hg := linearProfile_contDiff phi A handle hphi
  exact contDiff_const.mul (hf.mul hg)

theorem localizedSeed_jet_bound (theta phi : ℝ → ℝ) (R A amplitude D Ktheta Cphi : ℝ) (handle x : E)
    (hD : 0 < D) (hR : D ≤ R) (hA : D ≤ A) (hamp : 0 ≤ amplitude)
    (hKt : 0 ≤ Ktheta) (hCp : 0 ≤ Cphi) (hh : ‖handle‖ ≤ 1)
    (htheta : ContDiff ℝ 3 theta) (hphi : ContDiff ℝ 3 phi)
    (hgate : ∀ i, i ≤ 3 → ∀ z : E, ‖iteratedFDeriv ℝ i (scaledGate theta R 0) z‖ ≤ Ktheta / R ^ i)
    (hscalar : ∀ i, i ≤ 3 → ∀ u : ℝ, ‖iteratedFDeriv ℝ i phi u‖ ≤ Cphi)
    (j : ℕ) (hj : j ≤ 3) :
    ‖iteratedFDeriv ℝ j (localizedSeed theta phi R A amplitude handle) x‖ ≤
      (8 * Ktheta * Cphi) * amplitude / D ^ j := by
  have hRpos : 0 < R := hD.trans_le hR
  have hApos : 0 < A := hD.trans_le hA
  let f : E → ℝ := scaledGate theta R 0
  let g : E → ℝ := linearProfile phi A handle
  have hf := scaledGate_contDiff (E := E) theta R 0 hRpos htheta
  have hg := linearProfile_contDiff phi A handle hphi
  have hF : ∀ i, i ≤ 3 → ‖iteratedFDeriv ℝ i f x‖ ≤ Ktheta / D ^ i := by
    intro i hi
    exact (hgate i hi x).trans
      (div_le_div_of_nonneg_left hKt (pow_pos hD i) (pow_le_pow_left₀ hD.le hR i))
  have hG : ∀ i, i ≤ 3 → ‖iteratedFDeriv ℝ i g x‖ ≤ Cphi / D ^ i := by
    intro i hi
    exact (linearProfile_jet_bound phi A Cphi handle x hApos hCp hh hphi hscalar i hi).trans
      (div_le_div_of_nonneg_left hCp (pow_pos hD i) (pow_le_pow_left₀ hD.le hA i))
  have hp := product_geometric_jet_bound f g hf hg D Ktheta Cphi hD hKt hCp x hF hG j hj
  have hpow : (2 : ℝ) ^ j ≤ 8 := by
    have hp := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hj
    norm_num at hp ⊢
    exact hp
  have hcoeff := mul_le_mul_of_nonneg_right hpow (by positivity : 0 ≤ Ktheta * Cphi / D ^ j)
  have hprod : ‖iteratedFDeriv ℝ j (fun z => f z * g z) x‖ ≤ 8 * Ktheta * Cphi / D ^ j := by
    exact hp.trans (by convert! hcoeff using 1 <;> try ring)
  have hfun : localizedSeed theta phi R A amplitude handle = fun z => amplitude • (f z * g z) := rfl
  rw [hfun, iteratedFDeriv_const_smul_apply' (a := amplitude)
      ((hf.mul hg).of_le (by exact_mod_cast hj)).contDiffAt,
    norm_smul, Real.norm_eq_abs, abs_of_nonneg hamp]
  have hm := mul_le_mul_of_nonneg_left hprod hamp
  convert! hm using 1 <;> try ring

theorem actual_normalized_difference_jets (theta phi : ℝ → ℝ)
    (R A amplitude D Ktheta Cphi : ℝ) (handle : E)
    (hD : 0 < D) (hR : D ≤ R) (hA : D ≤ A) (hamp : 0 ≤ amplitude)
    (hKt : 0 ≤ Ktheta) (hCp : 0 ≤ Cphi) (hh : ‖handle‖ ≤ 1)
    (htheta : ContDiff ℝ 3 theta) (hphi : ContDiff ℝ 3 phi)
    (hgate : ∀ i, i ≤ 3 → ∀ z : E, ‖iteratedFDeriv ℝ i (scaledGate theta R 0) z‖ ≤ Ktheta / R ^ i)
    (hscalar : ∀ i, i ≤ 3 → ∀ u : ℝ, ‖iteratedFDeriv ℝ i phi u‖ ≤ Cphi)
    (H0 H1 : E → ℝ) (z0 z1 : E)
    (hH : ∀ z, H1 z = H0 z - localizedSeed theta phi R A amplitude handle z)
    (hmin0 : ∀ z, H0 z0 ≤ H0 z) (hmin1 : ∀ z, H1 z1 ≤ H1 z) :
    ContDiff ℝ 3 (normalizedDifference H0 H1 z0 z1) ∧
      (∀ z, |normalizedDifference H0 H1 z0 z1 z| ≤ (16 * Ktheta * Cphi) * amplitude) ∧
      (∀ j, 1 ≤ j → j ≤ 3 → ∀ z,
        ‖iteratedFDeriv ℝ j (normalizedDifference H0 H1 z0 z1) z‖ ≤
          (8 * Ktheta * Cphi) * amplitude / D ^ j) := by
  let seed := localizedSeed theta phi R A amplitude handle
  let M := (8 * Ktheta * Cphi) * amplitude
  have hseedc : ContDiff ℝ 3 seed := localizedSeed_contDiff theta phi R A amplitude handle
    (hD.trans_le hR) htheta hphi
  have hseedbound : ∀ z, |seed z| ≤ M := by
    intro z
    have hb := localizedSeed_jet_bound theta phi R A amplitude D Ktheta Cphi handle z
      hD hR hA hamp hKt hCp hh htheta hphi hgate hscalar 0 (by norm_num)
    simpa only [norm_iteratedFDeriv_zero, Real.norm_eq_abs, pow_zero, div_one] using hb
  have hraw : ∀ z, |H1 z - H0 z| ≤ M := by
    intro z
    rw [hH]
    have heq : H0 z - seed z - H0 z = -seed z := by ring
    rw [heq, abs_neg]
    exact hseedbound z
  have hshift := minima_difference_bound H0 H1 z0 z1 M hmin0 hmin1 hraw
  have heq : normalizedDifference H0 H1 z0 z1 = fun z => seed z + (H1 z1 - H0 z0) := by
    funext z
    dsimp [normalizedDifference]
    rw [hH z]
    ring
  have hc : ContDiff ℝ 3 (normalizedDifference H0 H1 z0 z1) := by
    rw [heq]
    exact hseedc.add contDiff_const
  refine ⟨hc, ?_, ?_⟩
  · intro z
    have hb := normalized_difference_bound H0 H1 z0 z1 M hmin0 hmin1 hraw z
    change |normalizedDifference H0 H1 z0 z1 z| ≤ _ at hb
    dsimp [M] at hb
    nlinarith only [hb]
  · intro j hj hj3 z
    rw [heq, fun_iteratedFDeriv_add_apply ((hseedc.of_le (by exact_mod_cast hj3)).contDiffAt)
      contDiffAt_const, iteratedFDeriv_const_of_ne (by omega)]
    simp only [Pi.zero_apply, add_zero]
    exact localizedSeed_jet_bound theta phi R A amplitude D Ktheta Cphi handle z
      hD hR hA hamp hKt hCp hh htheta hphi hgate hscalar j hj3

end
end FangqingLocalizedSeedJets


open scoped BigOperators ContDiff

namespace FangqingActualLocalizedSeedBounds

open FangqingRadialGateBounds FangqingSaturatedProfileBounds FangqingLocalizedSeedJets

noncomputable section

universe u

/- A fixed pair of scalar profiles supplies one constant before the ambient
   Hilbert space is chosen.  No derivative bound for the vector seed is an input. -/
theorem universal_normalized_seed_bounds
    (theta phi : ℝ → ℝ) (Btheta Bphi left right : ℝ) (hB : 1 ≤ Btheta)
    (htheta : ContDiff ℝ 3 theta) (hphi : ContDiff ℝ 3 phi)
    (htleft : ∀ u : ℝ, u < 0 → theta u = 1)
    (htright : ∀ u : ℝ, Btheta ^ 2 < u → theta u = 0)
    (hpleft : ∀ u : ℝ, u < -Bphi → phi u = left)
    (hpright : ∀ u : ℝ, Bphi < u → phi u = right) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (F : Type u) [NormedAddCommGroup F] [InnerProductSpace ℝ F],
      ∀ (R A amplitude D : ℝ) (handle : F),
      0 < D → D ≤ R → D ≤ A → 0 ≤ amplitude → ‖handle‖ ≤ 1 →
      ∀ (H0 H1 : F → ℝ) (z0 z1 : F),
      (∀ z, H1 z = H0 z - localizedSeed theta phi R A amplitude handle z) →
      (∀ z, H0 z0 ≤ H0 z) → (∀ z, H1 z1 ≤ H1 z) →
      ContDiff ℝ 3 (normalizedDifference H0 H1 z0 z1) ∧
      (∀ z, |normalizedDifference H0 H1 z0 z1 z| ≤ K * amplitude) ∧
      (∀ j, 1 ≤ j → j ≤ 3 → ∀ z,
        ‖iteratedFDeriv ℝ j (normalizedDifference H0 H1 z0 z1) z‖ ≤
          K * amplitude / D ^ j) := by
  obtain ⟨Ct, hCt, ht⟩ := scalar_profile_derivatives_bounded theta 3 Btheta htheta htleft htright
  obtain ⟨Kr, hKr, hr⟩ := universal_three_gate_bounds.{u} theta Btheta hB htheta htleft htright
  obtain ⟨Cp, hCp, hp⟩ := scalar_saturation_derivatives_bounded phi 3 Bphi left right hphi hpleft hpright
  let Kt := Ct + Kr
  have hKt : 0 ≤ Kt := add_nonneg hCt hKr
  refine ⟨16 * Kt * Cp, (by positivity), ?_⟩
  intro F inst inst' R A amplitude D handle hD hR hA hamp hh H0 H1 z0 z1 hH hm0 hm1
  have hgate : ∀ i, i ≤ 3 → ∀ z : F,
      ‖iteratedFDeriv ℝ i (scaledGate theta R 0) z‖ ≤ Kt / R ^ i := by
    intro i hi z
    by_cases hiz : i = 0
    · subst i
      simp only [norm_iteratedFDeriv_zero, pow_zero, div_one]
      have hz := (ht 0 (by norm_num) (‖z - 0‖ ^ 2 / R ^ 2)).trans (le_add_of_nonneg_right hKr)
      simpa only [norm_iteratedFDeriv_zero, scaledGate, Kt] using hz
    · exact (hr F R (hD.trans_le hR) 0 z i (by omega) hi).trans
        (div_le_div_of_nonneg_right (le_add_of_nonneg_left hCt) (pow_nonneg (hD.trans_le hR).le i))
  obtain ⟨hc, hb, hj⟩ := actual_normalized_difference_jets theta phi R A amplitude D Kt Cp handle
    hD hR hA hamp hKt hCp hh htheta hphi hgate hp H0 H1 z0 z1 hH hm0 hm1
  refine ⟨hc, hb, ?_⟩
  intro j hj1 hj3 z
  apply (hj j hj1 hj3 z).trans
  apply div_le_div_of_nonneg_right _ (pow_nonneg hD.le j)
  nlinarith only [mul_nonneg hKt hCp, hamp]

/- The radial cutoff used in the paper is chi(norm/R), not an unannounced
   squared-norm replacement.  This equation records the admissible choice
   chi(t)=theta(t^2) exactly. -/
theorem literal_radial_cutoff_eq
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (theta : ℝ → ℝ) (R : ℝ) (z : F) :
    (fun t : ℝ => theta (t ^ 2)) (‖z‖ / R) = scaledGate theta R 0 z := by
  simp only [scaledGate, sub_zero, div_pow]

/- The four refined rates follow from the actual amplitude s*A <= C*nu*D^2.
   The normalizing minima were already handled by the preceding theorem. -/
theorem refined_normalized_rates
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (Delta : F → ℝ) (K C nu D amplitude : ℝ)
    (hD : 0 < D) (hK : 0 ≤ K) (hamp : amplitude ≤ C * nu * D ^ 2)
    (hzero : ∀ z, |Delta z| ≤ K * amplitude)
    (hjets : ∀ j, 1 ≤ j → j ≤ 3 → ∀ z,
      ‖iteratedFDeriv ℝ j Delta z‖ ≤ K * amplitude / D ^ j) :
    (∀ z, |Delta z| ≤ K * C * nu * D ^ 2) ∧
    (∀ z, ‖iteratedFDeriv ℝ 1 Delta z‖ ≤ K * C * nu * D) ∧
    (∀ z, ‖iteratedFDeriv ℝ 2 Delta z‖ ≤ K * C * nu) ∧
    (∀ z, ‖iteratedFDeriv ℝ 3 Delta z‖ ≤ K * C * nu / D) := by
  have hscale : K * amplitude ≤ K * C * nu * D ^ 2 := by
    convert! mul_le_mul_of_nonneg_left hamp hK using 1 <;> try ring
  refine ⟨fun z => (hzero z).trans hscale, ?_, ?_, ?_⟩
  · intro z
    have h := (hjets 1 (by norm_num) (by norm_num) z).trans
      (div_le_div_of_nonneg_right hscale (pow_nonneg hD.le 1))
    convert! h using 1 <;> try field_simp [ne_of_gt hD] <;> try ring
  · intro z
    have h := (hjets 2 (by norm_num) (by norm_num) z).trans
      (div_le_div_of_nonneg_right hscale (pow_nonneg hD.le 2))
    convert! h using 1 <;> try field_simp [ne_of_gt hD] <;> try ring
  · intro z
    have h := (hjets 3 (by norm_num) (by norm_num) z).trans
      (div_le_div_of_nonneg_right hscale (pow_nonneg hD.le 3))
    convert! h using 1 <;> try field_simp [ne_of_gt hD] <;> try ring

end
end FangqingActualLocalizedSeedBounds


open scoped ContDiff

namespace FangqingLocalizedPacketEndpoints

open FangqingPacketLeakage FangqingRadialGateBounds FangqingLocalizedSeedJets
  FangqingActualLocalizedSeedBounds

noncomputable section

variable {E I : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [Fintype I]

def inactiveEndpoint (theta collar : ℝ → ℝ) (R : ℝ) (Q : E → ℝ)
    (g : ℝ → ℝ) (d : I → E) (scale : ℝ) : E → ℝ :=
  localized (fun t => theta (t ^ 2)) collar R Q (fun z => scale * edgeSum g d z)

def activeEndpointSquared (theta collar phi : ℝ → ℝ) (R : ℝ) (Q : E → ℝ)
    (g : ℝ → ℝ) (d : I → E) (scale s A : ℝ) (handle : E) : E → ℝ :=
  activeEndpoint (fun t => theta (t ^ 2)) collar phi R Q g d scale s A handle

theorem actual_shell_seed_cancellation (theta collar phi : ℝ → ℝ) (R : ℝ) (Q : E → ℝ)
    (g : ℝ → ℝ) (d : I → E) (scale s A : ℝ) (handle z : E) :
    activeEndpointSquared theta collar phi R Q g d scale s A handle z =
      inactiveEndpoint theta collar R Q g d scale z -
        localizedSeed theta phi R A (s * A) handle z := by
  dsimp [activeEndpointSquared, activeEndpoint, inactiveEndpoint, localized, boundedSeed,
    localizedSeed, FangqingLinearProfileJetBounds.linearProfile]
  simp only [scaledGate, sub_zero, div_pow]
  ring

universe u

/- Actual edge/collar/amplifier expressions are retained without imposing C3
   on their common capped edge.  Their cancellation is proved above. -/
theorem actual_packet_normalized_difference_bounds
    (theta phi : ℝ → ℝ) (Bt Bp left right : ℝ) (hBt : 1 ≤ Bt)
    (htheta : ContDiff ℝ 3 theta) (hphi : ContDiff ℝ 3 phi)
    (htleft : ∀ t : ℝ, t < 0 → theta t = 1)
    (htright : ∀ t : ℝ, Bt ^ 2 < t → theta t = 0)
    (hpleft : ∀ t : ℝ, t < -Bp → phi t = left)
    (hpright : ∀ t : ℝ, Bp < t → phi t = right) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (F : Type u) [NormedAddCommGroup F] [InnerProductSpace ℝ F],
      ∀ (J : Type) [Fintype J] (collar : ℝ → ℝ) (R A s D : ℝ) (Q : F → ℝ)
      (g : ℝ → ℝ) (d : J → F) (scale : ℝ) (handle z0 z1 : F),
      0 < D → D ≤ R → D ≤ A → 0 ≤ s * A → ‖handle‖ ≤ 1 →
      let H0 := inactiveEndpoint theta collar R Q g d scale
      let H1 := activeEndpointSquared theta collar phi R Q g d scale s A handle
      (∀ z, H0 z0 ≤ H0 z) → (∀ z, H1 z1 ≤ H1 z) →
      ContDiff ℝ 3 (normalizedDifference H0 H1 z0 z1) ∧
      (∀ z, |normalizedDifference H0 H1 z0 z1 z| ≤ K * (s * A)) ∧
      (∀ j, 1 ≤ j → j ≤ 3 → ∀ z,
        ‖iteratedFDeriv ℝ j (normalizedDifference H0 H1 z0 z1) z‖ ≤
          K * (s * A) / D ^ j) := by
  obtain ⟨K, hK, hb⟩ := universal_normalized_seed_bounds.{u} theta phi Bt Bp left right hBt
    htheta hphi htleft htright hpleft hpright
  refine ⟨K, hK, ?_⟩
  intro F inst inst' J instJ collar R A s D Q g d scale handle z0 z1 hD hR hA hs hh H0 H1 hm0 hm1
  exact hb F R A (s * A) D handle hD hR hA hs hh H0 H1 z0 z1
    (actual_shell_seed_cancellation theta collar phi R Q g d scale s A handle) hm0 hm1

end
end FangqingLocalizedPacketEndpoints


open scoped ContDiff NNReal

namespace FangqingSeedJetRegularity

open FangqingJetToRegularity

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem first_jet_norm_eq_gradient (f : E → ℝ) (z : E) :
    ‖iteratedFDeriv ℝ 1 f z‖ = ‖gradient f z‖ := by
  rw [norm_iteratedFDeriv_one]
  simp only [gradient, LinearIsometryEquiv.norm_map]

theorem actual_seed_regularities (Delta : E → ℝ) (hc : ContDiff ℝ 3 Delta)
    (G H rho : ℝ≥0)
    (hg : ∀ z, ‖iteratedFDeriv ℝ 1 Delta z‖ ≤ G)
    (hh : ∀ z, ‖iteratedFDeriv ℝ 2 Delta z‖ ≤ H)
    (ht : ∀ z, ‖iteratedFDeriv ℝ 3 Delta z‖ ≤ rho) :
    (∀ z, ‖gradient Delta z‖ ≤ G) ∧
    (∀ z, ‖fderiv ℝ (fderiv ℝ Delta) z‖ ≤ H) ∧
    LipschitzWith H (gradient Delta) ∧
    LipschitzWith rho (fderiv ℝ (fderiv ℝ Delta)) := by
  refine ⟨?_, ?_, gradient_lipschitz_from_second_jet Delta
    (hc.of_le (by norm_num)) H hh, hessian_lipschitz_from_third_jet Delta hc rho ht⟩
  · intro z
    rw [← first_jet_norm_eq_gradient]
    exact hg z
  · intro z
    rw [hessian_norm_eq_second_jet]
    exact hh z

end FangqingSeedJetRegularity


/- Paired A/B rotations and independent W rotations preserve the actual
   public amplifier and rotate the actual localized packet.  Minimum
   values are proved invariant; they are not assumed public constants. -/

open scoped BigOperators

namespace OriginalPacketOrientationNormalization

open FangqingAmplifier FangqingPacketLeakage FangqingLocalizedPacketEndpoints

variable {A B W : Type*}
  [NormedAddCommGroup A] [InnerProductSpace ℝ A]
  [NormedAddCommGroup B] [InnerProductSpace ℝ B]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W]

noncomputable def pairedB (C : A ≃ₗᵢ[ℝ] B) (U : A ≃ₗᵢ[ℝ] A) : B ≃ₗᵢ[ℝ] B :=
  (C.symm.trans U).trans C

noncomputable def rotation (C : A ≃ₗᵢ[ℝ] B) (U : A ≃ₗᵢ[ℝ] A) (V : W ≃ₗᵢ[ℝ] W) :
    PhysicalSpace A B W ≃ₗᵢ[ℝ] PhysicalSpace A B W :=
  LinearIsometryEquiv.withLpProdCongr 2
    (LinearIsometryEquiv.withLpProdCongr 2 U (pairedB C U)) V

theorem rotation_mk (C : A ≃ₗᵢ[ℝ] B) (U : A ≃ₗᵢ[ℝ] A) (V : W ≃ₗᵢ[ℝ] W)
    (a : A) (b : B) (w : W) :
    rotation C U V (mkPhysical a b w) = mkPhysical (U a) (C (U (C.symm b))) (V w) := by
  rfl

theorem rotation_intertwines_public_pair (C : A ≃ₗᵢ[ℝ] B) (U : A ≃ₗᵢ[ℝ] A)
    (a : A) (b : B) :
    inner ℝ (C (U a)) (C (U (C.symm b))) = inner ℝ (C a) b := by
  rw [C.inner_map_map, U.inner_map_map]
  rw [← C.inner_map_map a (C.symm b), C.apply_symm_apply]

theorem actual_public_amplifier_invariant
    (C : A ≃ₗᵢ[ℝ] B) (U : A ≃ₗᵢ[ℝ] A) (V : W ≃ₗᵢ[ℝ] W)
    (q nu : ℝ) (z : PhysicalSpace A B W) :
    QPhysical q nu C (rotation C U V z) = QPhysical q nu C z := by
  have hz : mkPhysical z.fst.fst z.fst.snd z.snd = z := by
    apply (WithLp.ext_iff 2).mpr
    apply Prod.ext
    · apply (WithLp.ext_iff 2).mpr
      exact Prod.ext rfl rfl
    · rfl
  conv_lhs => rw [← hz]
  conv_rhs => rw [← hz]
  rw [rotation_mk]
  change nu / 2 * (2 * ‖U z.fst.fst‖ ^ 2 +
      (q + 1) * ‖C (U (C.symm z.fst.snd))‖ ^ 2 -
      2 * Real.sqrt q * inner ℝ (C (U z.fst.fst)) (C (U (C.symm z.fst.snd))) +
      ‖V z.snd‖ ^ 2) =
    nu / 2 * (2 * ‖z.fst.fst‖ ^ 2 + (q + 1) * ‖z.fst.snd‖ ^ 2 -
      2 * Real.sqrt q * inner ℝ (C z.fst.fst) z.fst.snd + ‖z.snd‖ ^ 2)
  simp only [LinearIsometryEquiv.norm_map, rotation_intertwines_public_pair]

noncomputable def physicalFrame (C : A ≃ₗᵢ[ℝ] B) (h : A) (n : ℕ)
    (tail : Fin (n + 2) → W) : Fin (n + 3) → PhysicalSpace A B W :=
  Fin.cons (mkPhysical 0 (C h) 0) (fun i => mkPhysical 0 0 (tail i))

theorem physicalFrame_rotates
    (C : A ≃ₗᵢ[ℝ] B) (U : A ≃ₗᵢ[ℝ] A) (V : W ≃ₗᵢ[ℝ] W)
    (h : A) (n : ℕ) (tail : Fin (n + 2) → W) (i : Fin (n + 3)) :
    physicalFrame C (U h) n (fun j => V (tail j)) i =
      rotation C U V (physicalFrame C h n tail i) := by
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [physicalFrame, rotation_mk]
  · simp [physicalFrame, rotation_mk]

theorem physicalPath_rotates
    (C : A ≃ₗᵢ[ℝ] B) (U : A ≃ₗᵢ[ℝ] A) (V : W ≃ₗᵢ[ℝ] W)
    (h : A) (n : ℕ) (tail : Fin (n + 2) → W) (i : Fin (n + 2)) :
    pathDirection n (physicalFrame C (U h) n (fun j => V (tail j))) i =
      rotation C U V (pathDirection n (physicalFrame C h n tail) i) := by
  simp only [pathDirection, physicalFrame_rotates, map_sub]

section GeneralRotation

variable {E I : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [Fintype I]

theorem actual_edgeSum_equivariant (T : E ≃ₗᵢ[ℝ] E) (g : ℝ → ℝ)
    (d : I → E) (z : E) :
    edgeSum g (fun i => T (d i)) (T z) = edgeSum g d z := by
  unfold edgeSum
  apply Finset.sum_congr rfl
  intro i _
  rw [T.inner_map_map]

theorem actual_active_endpoint_equivariant
    (T : E ≃ₗᵢ[ℝ] E) (chi collar phi : ℝ → ℝ) (R scale s a : ℝ)
    (Q : E → ℝ) (hQ : ∀ z, Q (T z) = Q z) (g : ℝ → ℝ)
    (d : I → E) (handle z : E) :
    activeEndpoint chi collar phi R Q g (fun i => T (d i)) scale s a (T handle) (T z) =
      activeEndpoint chi collar phi R Q g d scale s a handle z := by
  simp only [activeEndpoint, localized, T.norm_map, hQ, actual_edgeSum_equivariant,
    boundedSeed, T.inner_map_map]

theorem actual_inactive_endpoint_equivariant
    (T : E ≃ₗᵢ[ℝ] E) (theta collar : ℝ → ℝ) (R scale : ℝ)
    (Q : E → ℝ) (hQ : ∀ z, Q (T z) = Q z) (g : ℝ → ℝ)
    (d : I → E) (z : E) :
    inactiveEndpoint theta collar R Q g (fun i => T (d i)) scale (T z) =
      inactiveEndpoint theta collar R Q g d scale z := by
  simp only [inactiveEndpoint, localized, T.norm_map, hQ, actual_edgeSum_equivariant]

theorem range_of_rotation (T : E ≃ₗᵢ[ℝ] E) (f g : E → ℝ)
    (heq : ∀ z, g (T z) = f z) : Set.range g = Set.range f := by
  ext v
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨T.symm z, by rw [← heq, T.apply_symm_apply]⟩
  · rintro ⟨z, rfl⟩
    exact ⟨T z, heq z⟩

theorem actual_minimum_value_rotation_invariant
    (T : E ≃ₗᵢ[ℝ] E) (f g : E → ℝ) (heq : ∀ z, g (T z) = f z)
    (zf zg : E) (hf : ∀ z, f zf ≤ f z) (hg : ∀ z, g zg ≤ g z) :
    f zf = g zg := by
  have ha := hf (T.symm zg)
  have hb := hg (T zf)
  rw [← heq (T.symm zg), T.apply_symm_apply] at ha
  rw [heq] at hb
  exact le_antisymm ha hb

end GeneralRotation

theorem actual_physical_endpoint_equivariance
    (C : A ≃ₗᵢ[ℝ] B) (U : A ≃ₗᵢ[ℝ] A) (V : W ≃ₗᵢ[ℝ] W)
    (h : A) (n : ℕ) (tail : Fin (n + 2) → W)
    (theta collar phi : ℝ → ℝ) (R scale s a q nu : ℝ) (g : ℝ → ℝ)
    (z : PhysicalSpace A B W) :
    let T := rotation C U V
    let d := pathDirection n (physicalFrame C h n tail)
    let d' := pathDirection n (physicalFrame C (U h) n (fun j => V (tail j)))
    inactiveEndpoint theta collar R (QPhysical q nu C) g d' scale (T z) =
      inactiveEndpoint theta collar R (QPhysical q nu C) g d scale z ∧
    activeEndpointSquared theta collar phi R (QPhysical q nu C) g d' scale s a
      (mkPhysical (U h) 0 0) (T z) =
      activeEndpointSquared theta collar phi R (QPhysical q nu C) g d scale s a
        (mkPhysical h 0 0) z := by
  dsimp only
  have hd : pathDirection n (physicalFrame C (U h) n (fun j => V (tail j))) =
      fun i => rotation C U V (pathDirection n (physicalFrame C h n tail) i) :=
    funext (physicalPath_rotates C U V h n tail)
  have hh : mkPhysical (U h) (0 : B) (0 : W) = rotation C U V (mkPhysical h 0 0) := by
    simp [rotation_mk]
  rw [hd, hh]
  exact ⟨actual_inactive_endpoint_equivariant (rotation C U V) theta collar R scale
      (QPhysical q nu C) (actual_public_amplifier_invariant C U V q nu) g _ z,
    actual_active_endpoint_equivariant (rotation C U V) (fun t => theta (t ^ 2)) collar phi
      R scale s a (QPhysical q nu C) (actual_public_amplifier_invariant C U V q nu) g _ _ z⟩

theorem actual_physical_normalizers_orientation_independent
    (C : A ≃ₗᵢ[ℝ] B) (U : A ≃ₗᵢ[ℝ] A) (V : W ≃ₗᵢ[ℝ] W)
    (h : A) (n : ℕ) (tail : Fin (n + 2) → W)
    (theta collar phi : ℝ → ℝ) (R scale s a q nu : ℝ) (g : ℝ → ℝ) :
    let d := pathDirection n (physicalFrame C h n tail)
    let d' := pathDirection n (physicalFrame C (U h) n (fun j => V (tail j)))
    sInf (Set.range (inactiveEndpoint theta collar R (QPhysical q nu C) g d' scale)) =
      sInf (Set.range (inactiveEndpoint theta collar R (QPhysical q nu C) g d scale)) ∧
    sInf (Set.range (activeEndpointSquared theta collar phi R (QPhysical q nu C) g d' scale s a
      (mkPhysical (U h) 0 0))) =
      sInf (Set.range (activeEndpointSquared theta collar phi R (QPhysical q nu C) g d scale s a
        (mkPhysical h 0 0))) := by
  dsimp only
  have he := actual_physical_endpoint_equivariance C U V h n tail theta collar phi R scale s a q nu g
  exact ⟨congrArg sInf (range_of_rotation (rotation C U V) _ _ (fun z => (he z).1)),
    congrArg sInf (range_of_rotation (rotation C U V) _ _ (fun z => (he z).2))⟩

noncomputable def H0
    (C : A ≃ₗᵢ[ℝ] B) (h : A) (n : ℕ) (tail : Fin (n + 2) → W)
    (theta collar : ℝ → ℝ) (R scale q nu : ℝ) (g : ℝ → ℝ) :
    PhysicalSpace A B W → ℝ :=
  inactiveEndpoint theta collar R (QPhysical q nu C) g
    (pathDirection n (physicalFrame C h n tail)) scale

noncomputable def H1
    (C : A ≃ₗᵢ[ℝ] B) (h : A) (n : ℕ) (tail : Fin (n + 2) → W)
    (theta collar phi : ℝ → ℝ) (R scale s a q nu : ℝ) (g : ℝ → ℝ) :
    PhysicalSpace A B W → ℝ :=
  activeEndpointSquared theta collar phi R (QPhysical q nu C) g
    (pathDirection n (physicalFrame C h n tail)) scale s a (mkPhysical h 0 0)

noncomputable def normalizedEndpointDifference
    (C : A ≃ₗᵢ[ℝ] B) (h : A) (n : ℕ) (tail : Fin (n + 2) → W)
    (theta collar phi : ℝ → ℝ) (R scale s a q nu : ℝ) (g : ℝ → ℝ)
    (z : PhysicalSpace A B W) : ℝ :=
  H0 C h n tail theta collar R scale q nu g z -
    H1 C h n tail theta collar phi R scale s a q nu g z +
    sInf (Set.range (H1 C h n tail theta collar phi R scale s a q nu g)) -
    sInf (Set.range (H0 C h n tail theta collar R scale q nu g))

theorem actual_normalized_difference_tail_blind
    (C : A ≃ₗᵢ[ℝ] B) (U : A ≃ₗᵢ[ℝ] A) (V0 V1 : W ≃ₗᵢ[ℝ] W)
    (h : A) (n : ℕ) (tail : Fin (n + 2) → W)
    (theta collar phi : ℝ → ℝ) (R scale s a q nu : ℝ) (g : ℝ → ℝ) :
    normalizedEndpointDifference C (U h) n (fun j => V0 (tail j))
      theta collar phi R scale s a q nu g =
    normalizedEndpointDifference C (U h) n (fun j => V1 (tail j))
      theta collar phi R scale s a q nu g := by
  funext z
  have hm0 := actual_physical_normalizers_orientation_independent C U V0 h n tail
    theta collar phi R scale s a q nu g
  have hm1 := actual_physical_normalizers_orientation_independent C U V1 h n tail
    theta collar phi R scale s a q nu g
  have hc0 := actual_shell_seed_cancellation theta collar phi R (QPhysical q nu C) g
    (pathDirection n (physicalFrame C (U h) n (fun j => V0 (tail j)))) scale s a (mkPhysical (U h) 0 0) z
  have hc1 := actual_shell_seed_cancellation theta collar phi R (QPhysical q nu C) g
    (pathDirection n (physicalFrame C (U h) n (fun j => V1 (tail j)))) scale s a (mkPhysical (U h) 0 0) z
  unfold normalizedEndpointDifference H0 H1
  rw [hm0.1, hm0.2, hm1.1, hm1.2, hc0, hc1]
  ring

theorem actual_minimizers_rotate
    (C : A ≃ₗᵢ[ℝ] B) (U : A ≃ₗᵢ[ℝ] A) (V : W ≃ₗᵢ[ℝ] W)
    (h : A) (n : ℕ) (tail : Fin (n + 2) → W)
    (theta collar phi : ℝ → ℝ) (R scale s a q nu : ℝ) (g : ℝ → ℝ)
    (z0 z1 : PhysicalSpace A B W)
    (h0 : ∀ z, H0 C h n tail theta collar R scale q nu g z0 ≤
      H0 C h n tail theta collar R scale q nu g z)
    (h1 : ∀ z, H1 C h n tail theta collar phi R scale s a q nu g z1 ≤
      H1 C h n tail theta collar phi R scale s a q nu g z) :
    (∀ z, H0 C (U h) n (fun j => V (tail j)) theta collar R scale q nu g
        (rotation C U V z0) ≤
      H0 C (U h) n (fun j => V (tail j)) theta collar R scale q nu g z) ∧
    (∀ z, H1 C (U h) n (fun j => V (tail j)) theta collar phi R scale s a q nu g
        (rotation C U V z1) ≤
      H1 C (U h) n (fun j => V (tail j)) theta collar phi R scale s a q nu g z) := by
  have he := actual_physical_endpoint_equivariance C U V h n tail theta collar phi R scale s a q nu g
  constructor
  · intro z
    obtain ⟨z, rfl⟩ := (rotation C U V).surjective z
    exact (he z0).1.le.trans ((h0 z).trans (he z).1.symm.le)
  · intro z
    obtain ⟨z, rfl⟩ := (rotation C U V).surjective z
    exact (he z1).2.le.trans ((h1 z).trans (he z).2.symm.le)

end OriginalPacketOrientationNormalization


/- Genuine reduced private-packet objective. Flux identities below are
   derived from directional derivatives at its actual global minimizer,
   rather than supplied as a premise. -/

open scoped BigOperators Topology

namespace OriginalScalarPacketMinimizer

noncomputable section

def weight (S lam : ℝ) {n : ℕ} (i : Fin (n + 1)) : ℝ := if i = 0 then S else lam

def chainObjective (g : ℝ → ℝ) (n : ℕ) (S lam Gamma : ℝ) (z : Fin (n + 1) → ℝ) : ℝ :=
  (∑ i : Fin n, g (z i.castSucc - z i.succ)) +
    (1 / 2 : ℝ) * (∑ i : Fin (n + 1), weight S lam i * (z i) ^ 2) - Gamma * z 0

def positivePart {n : ℕ} (z : Fin (n + 1) → ℝ) : Fin (n + 1) → ℝ := fun i => max (z i) 0

theorem positivePart_square_le (x : ℝ) : (max x 0) ^ 2 ≤ x ^ 2 := by
  by_cases hx : 0 ≤ x
  · rw [max_eq_left hx]
  · rw [max_eq_right (le_of_not_ge hx)]
    simpa only [zero_pow (by omega : 2 ≠ 0)] using sq_nonneg x

theorem actual_edge_monotone_in_abs
    (P : FlatCubic.Profile) (delta omega : ℝ) (hd : 0 < delta) (hdw : delta ≤ omega)
    (a b : ℝ) (hab : |a| ≤ |b|) :
    FlatCubic.edge P delta omega a ≤ FlatCubic.edge P delta omega b := by
  have hm : MonotoneOn (FlatCubic.primitive P delta omega) (Set.Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
      (FlatCubic.primitive_contDiff_two P delta omega hd hdw).continuous.continuousOn
    · intro x _
      exact (FlatCubic.primitive_hasDerivAt P delta omega x hd hdw).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [(FlatCubic.primitive_hasDerivAt P delta omega x hd hdw).deriv]
      exact FlatCubic.rawp_nonneg P delta omega x (hd.trans_le hdw).le (interior_subset hx)
  exact hm (abs_nonneg a) (abs_nonneg b) hab

theorem actual_minimizer_coordinates_nonnegative
    (P : FlatCubic.Profile) (delta omega : ℝ) (hd : 0 < delta) (hdw : delta ≤ omega)
    (n : ℕ) (S lam Gamma : ℝ) (hS : 0 < S) (hlam : 0 < lam) (hGamma : 0 ≤ Gamma)
    (z : Fin (n + 1) → ℝ)
    (hmin : ∀ w, chainObjective (FlatCubic.edge P delta omega) n S lam Gamma z ≤
      chainObjective (FlatCubic.edge P delta omega) n S lam Gamma w) :
    ∀ i, 0 ≤ z i := by
  intro j
  by_contra hj
  have hjneg : z j < 0 := lt_of_not_ge hj
  have hw : ∀ i : Fin (n + 1), 0 < weight S lam i := by
    intro i
    unfold weight
    split_ifs <;> assumption
  have he : (∑ i : Fin n, FlatCubic.edge P delta omega
      (positivePart z i.castSucc - positivePart z i.succ)) ≤
      ∑ i : Fin n, FlatCubic.edge P delta omega (z i.castSucc - z i.succ) := by
    apply Finset.sum_le_sum
    intro i _
    exact actual_edge_monotone_in_abs P delta omega hd hdw _ _
      (abs_max_sub_max_le_abs (z i.castSucc) (z i.succ) 0)
  have hquad : (∑ i : Fin (n + 1), weight S lam i * (positivePart z i) ^ 2) <
      ∑ i : Fin (n + 1), weight S lam i * (z i) ^ 2 := by
    apply Finset.sum_lt_sum
    · intro i _
      exact mul_le_mul_of_nonneg_left (positivePart_square_le (z i)) (hw i).le
    · refine ⟨j, Finset.mem_univ _, ?_⟩
      unfold positivePart
      rw [max_eq_right hjneg.le]
      have hsq : 0 < (z j) ^ 2 := sq_pos_of_ne_zero (ne_of_lt hjneg)
      simpa only [zero_pow (by omega : 2 ≠ 0)] using mul_lt_mul_of_pos_left hsq (hw j)
  have hs : Gamma * z 0 ≤ Gamma * positivePart z 0 :=
    mul_le_mul_of_nonneg_left (le_max_left _ _) hGamma
  have hm := hmin (positivePart z)
  unfold chainObjective at hm
  linarith only [he, hquad, hs, hm]

theorem chain_directional_derivative
    (g p : ℝ → ℝ) (hg : ∀ x, HasDerivAt g (p x) x)
    (n : ℕ) (S lam Gamma : ℝ) (z v : Fin (n + 1) → ℝ) :
    HasDerivAt (fun t : ℝ => chainObjective g n S lam Gamma (fun i => z i + t * v i))
      ((∑ i : Fin n, p (z i.castSucc - z i.succ) * (v i.castSucc - v i.succ)) +
        (∑ i : Fin (n + 1), weight S lam i * z i * v i) - Gamma * v 0) 0 := by
  have hlin (i : Fin (n + 1)) : HasDerivAt (fun t : ℝ => z i + t * v i) (v i) 0 := by
    convert! ((hasDerivAt_id (0 : ℝ)).mul_const (v i)).const_add (z i) using 1 <;> simp
  have he (i : Fin n) : HasDerivAt
      (fun t : ℝ => g ((z i.castSucc + t * v i.castSucc) - (z i.succ + t * v i.succ)))
      (p (z i.castSucc - z i.succ) * (v i.castSucc - v i.succ)) 0 := by
    have hgp : HasDerivAt g (p (z i.castSucc - z i.succ))
        (((fun t : ℝ => z i.castSucc + t * v i.castSucc) -
          (fun t : ℝ => z i.succ + t * v i.succ)) 0) := by
      simpa using hg (z i.castSucc - z i.succ)
    convert! hgp.comp 0 ((hlin i.castSucc).sub (hlin i.succ)) using 1 <;> simp
  have hq (i : Fin (n + 1)) : HasDerivAt
      (fun t : ℝ => weight S lam i * (z i + t * v i) ^ 2)
      (2 * (weight S lam i * z i * v i)) 0 := by
    convert! ((hlin i).pow 2).const_mul (weight S lam i) using 1 <;> simp <;> ring
  have hd := ((HasDerivAt.sum (u := Finset.univ) (fun i _ => he i)).add
    ((HasDerivAt.sum (u := Finset.univ) (fun i _ => hq i)).const_mul (1 / 2 : ℝ))).sub
      ((hlin 0).const_mul Gamma)
  convert! hd using 1
  · funext t
    simp [chainObjective, Finset.sum_apply]
  · rw [← Finset.mul_sum]
    ring

theorem actual_minimizer_directional_stationarity
    (g p : ℝ → ℝ) (hg : ∀ x, HasDerivAt g (p x) x)
    (n : ℕ) (S lam Gamma : ℝ) (z : Fin (n + 1) → ℝ)
    (hmin : ∀ w, chainObjective g n S lam Gamma z ≤ chainObjective g n S lam Gamma w)
    (v : Fin (n + 1) → ℝ) :
    (∑ i : Fin n, p (z i.castSucc - z i.succ) * (v i.castSucc - v i.succ)) +
      (∑ i : Fin (n + 1), weight S lam i * z i * v i) - Gamma * v 0 = 0 := by
  have hl : IsLocalMin
      (fun t : ℝ => chainObjective g n S lam Gamma (fun i => z i + t * v i)) 0 := by
    apply Filter.Eventually.of_forall
    intro t
    simpa only [zero_mul, add_zero] using hmin (fun i => z i + t * v i)
  exact hl.hasDerivAt_eq_zero (chain_directional_derivative g p hg n S lam Gamma z v)

def suffixDirection {n : ℕ} (k : Fin n) (j : Fin (n + 1)) : ℝ :=
  if k.val < j.val then 1 else 0

def tailSum {n : ℕ} (z : Fin (n + 1) → ℝ) (k : Fin n) : ℝ :=
  ∑ j : Fin (n + 1), if k.val < j.val then z j else 0

theorem suffix_edge_difference {n : ℕ} (k i : Fin n) :
    suffixDirection k i.castSucc - suffixDirection k i.succ = if i = k then -1 else 0 := by
  by_cases hik : i = k
  · subst i
    simp [suffixDirection]
  · have hv : i.val ≠ k.val := fun h => hik (Fin.ext h)
    by_cases hlt : i.val < k.val
    · simp only [suffixDirection, Fin.val_castSucc, Fin.val_succ,
        if_neg (by omega : ¬ k.val < i.val), if_neg (by omega : ¬ k.val < i.val + 1),
        if_neg hik, sub_self]
    · simp only [suffixDirection, Fin.val_castSucc, Fin.val_succ,
        if_pos (by omega : k.val < i.val), if_pos (by omega : k.val < i.val + 1),
        if_neg hik, sub_self]

theorem weighted_suffix_sum {n : ℕ} (S lam : ℝ) (z : Fin (n + 1) → ℝ) (k : Fin n) :
    (∑ j : Fin (n + 1), weight S lam j * z j * suffixDirection k j) = lam * tailSum z k := by
  rw [tailSum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : k.val < j.val
  · have hj0 : j ≠ 0 := by
      intro hz
      subst j
      simp at hj
    simp only [suffixDirection, if_pos hj, weight, if_neg hj0, mul_one]
  · simp only [suffixDirection, if_neg hj, mul_zero]

theorem weighted_sum (n : ℕ) (S lam : ℝ) (z : Fin (n + 1) → ℝ) :
    (∑ j : Fin (n + 1), weight S lam j * z j) = S * z 0 + lam * ∑ j : Fin n, z j.succ := by
  rw [Fin.sum_univ_succ]
  simp only [weight, Fin.succ_ne_zero, if_false, if_true]
  rw [Finset.mul_sum]

theorem minimizer_flux_from_actual_directional_derivatives
    (g p : ℝ → ℝ) (hg : ∀ x, HasDerivAt g (p x) x)
    (n : ℕ) (S lam Gamma : ℝ) (z : Fin (n + 1) → ℝ)
    (hmin : ∀ w, chainObjective g n S lam Gamma z ≤ chainObjective g n S lam Gamma w) :
    (∀ k : Fin n, p (z k.castSucc - z k.succ) = lam * tailSum z k) ∧
    Gamma = S * z 0 + lam * ∑ j : Fin n, z j.succ := by
  constructor
  · intro k
    have h := actual_minimizer_directional_stationarity g p hg n S lam Gamma z hmin (suffixDirection k)
    have he : (∑ i : Fin n, p (z i.castSucc - z i.succ) *
        (suffixDirection k i.castSucc - suffixDirection k i.succ)) =
        -p (z k.castSucc - z k.succ) := by
      simp only [suffix_edge_difference, mul_ite, mul_neg_one, mul_zero]
      simp
    rw [he, weighted_suffix_sum] at h
    have h0 : suffixDirection k (0 : Fin (n + 1)) = 0 := by simp [suffixDirection]
    rw [h0, mul_zero, sub_zero] at h
    linarith only [h]
  · have h := actual_minimizer_directional_stationarity g p hg n S lam Gamma z hmin (fun _ => 1)
    simp only [sub_self, mul_zero, Finset.sum_const_zero, zero_add, mul_one] at h
    rw [weighted_sum] at h
    linarith only [h]

theorem actual_flat_packet_minimizer_flux
    (P : FlatCubic.Profile) (delta omega : ℝ) (hd : 0 < delta) (hdw : delta ≤ omega)
    (n : ℕ) (S lam Gamma : ℝ) (hS : 0 < S) (hlam : 0 < lam) (hGamma : 0 ≤ Gamma)
    (z : Fin (n + 1) → ℝ)
    (hmin : ∀ w, chainObjective (FlatCubic.edge P delta omega) n S lam Gamma z ≤
      chainObjective (FlatCubic.edge P delta omega) n S lam Gamma w) :
    (∀ i, 0 ≤ z i) ∧
    (∀ k : Fin n, FlatCubic.signedp P delta omega (z k.castSucc - z k.succ) = lam * tailSum z k) ∧
    Gamma = S * z 0 + lam * ∑ j : Fin n, z j.succ := by
  exact ⟨actual_minimizer_coordinates_nonnegative P delta omega hd hdw n S lam Gamma hS hlam hGamma z hmin,
    minimizer_flux_from_actual_directional_derivatives _ _ (FlatCubic.edge_hasDerivAt P delta omega hd hdw)
      n S lam Gamma z hmin⟩

theorem tailSum_nonnegative {n : ℕ} (z : Fin (n + 1) → ℝ)
    (hz : ∀ j, 0 ≤ z j) (k : Fin n) : 0 ≤ tailSum z k := by
  apply Finset.sum_nonneg
  intro j _
  split_ifs
  · exact hz j
  · rfl

theorem tailSum_ge_successor {n : ℕ} (z : Fin (n + 1) → ℝ)
    (hz : ∀ j, 0 ≤ z j) (k : Fin n) : z k.succ ≤ tailSum z k := by
  have hh := Finset.single_le_sum (s := Finset.univ)
    (f := fun j : Fin (n + 1) => if k.val < j.val then z j else 0)
    (fun j _ => by split_ifs; exact hz j; rfl) (Finset.mem_univ k.succ)
  simpa only [tailSum, Fin.val_succ, Nat.lt_succ_self, if_true] using hh

theorem tailSum_le_all_tail {n : ℕ} (z : Fin (n + 1) → ℝ)
    (hz : ∀ j, 0 ≤ z j) (k : Fin n) : tailSum z k ≤ ∑ j : Fin n, z j.succ := by
  have hh : tailSum z k ≤ ∑ j : Fin (n + 1), if j = 0 then 0 else z j := by
    apply Finset.sum_le_sum
    intro j _
    by_cases hj : k.val < j.val
    · have hj0 : j ≠ 0 := by intro h; subst j; simp at hj
      simp only [if_pos hj, if_neg hj0]
      exact le_rfl
    · simp only [if_neg hj]
      split_ifs
      · rfl
      · exact hz j
  simpa only [Fin.sum_univ_succ, if_pos rfl, Fin.succ_ne_zero, if_false, if_true, zero_add] using hh

theorem actual_flat_packet_edge_steps
    (P : FlatCubic.Profile) (delta omega : ℝ) (hd : 0 < delta) (hdw : delta ≤ omega)
    (n : ℕ) (S lam : ℝ) (hS : 0 < S) (hlam : 0 < lam)
    (z : Fin (n + 1) → ℝ)
    (hmin : ∀ w, chainObjective (FlatCubic.edge P delta omega) n S lam (omega ^ 2) z ≤
      chainObjective (FlatCubic.edge P delta omega) n S lam (omega ^ 2) w) :
    ∀ k : Fin n, 0 ≤ z k.castSucc - z k.succ ∧ z k.castSucc - z k.succ ≤ omega := by
  obtain ⟨hz, hp, hGamma⟩ := actual_flat_packet_minimizer_flux P delta omega hd hdw
    n S lam (omega ^ 2) hS hlam (sq_nonneg omega) z hmin
  have homega : 0 < omega := hd.trans_le hdw
  intro k
  constructor
  · by_contra hk
    have hneg : z k.castSucc - z k.succ < 0 := lt_of_not_ge hk
    have hzpos : 0 < z k.succ := by linarith [hz k.castSucc]
    have htpos : 0 < tailSum z k := hzpos.trans_le (tailSum_ge_successor z hz k)
    have hppos : 0 < FlatCubic.signedp P delta omega (z k.castSucc - z k.succ) := by
      rw [hp k]
      exact mul_pos hlam htpos
    have hraw : 0 ≤ FlatCubic.rawp P delta omega (-(z k.castSucc - z k.succ)) :=
      FlatCubic.rawp_nonneg P delta omega _ homega.le (by linarith)
    simp only [FlatCubic.signedp, if_neg (not_le_of_gt hneg)] at hppos
    linarith only [hppos, hraw]
  · have hpupper : FlatCubic.signedp P delta omega (z k.castSucc - z k.succ) ≤ omega ^ 2 := by
      rw [hp k]
      have ht := mul_le_mul_of_nonneg_left (tailSum_le_all_tail z hz k) hlam.le
      have hs : 0 ≤ S * z 0 := mul_nonneg hS.le (hz 0)
      linarith only [ht, hGamma, hs]
    by_contra hk
    have hlarge : omega < z k.castSucc - z k.succ := lt_of_not_ge hk
    have hpos : 0 ≤ z k.castSucc - z k.succ := homega.le.trans hlarge.le
    simp only [FlatCubic.signedp, if_pos hpos, FlatCubic.rawp,
      if_neg (not_le_of_gt hlarge)] at hpupper
    nlinarith only [hpupper, homega, hlarge]

theorem coordinate_bounds_from_actual_steps
    (n : ℕ) (omega : ℝ) (z : Fin (n + 1) → ℝ)
    (hsteps : ∀ k : Fin n, 0 ≤ z k.castSucc - z k.succ ∧ z k.castSucc - z k.succ ≤ omega) :
    ∀ j : Fin (n + 1), z j ≤ z 0 ∧ z 0 - (j.val : ℝ) * omega ≤ z j := by
  intro j
  induction j using Fin.induction with
  | zero => simp
  | succ i ih =>
      obtain ⟨hn, hu⟩ := hsteps i
      have hv : (i.succ.val : ℝ) = (i.castSucc.val : ℝ) + 1 := by
        simp only [Fin.val_succ, Fin.val_castSucc, Nat.cast_add, Nat.cast_one]
      constructor
      · linarith only [ih.1, hn]
      · rw [hv]
        linarith only [ih.2, hu]

theorem actual_flat_packet_coordinate_bounds
    (P : FlatCubic.Profile) (delta omega : ℝ) (hd : 0 < delta) (hdw : delta ≤ omega)
    (n : ℕ) (S lam : ℝ) (hS : 0 < S) (hlam : 0 < lam)
    (z : Fin (n + 1) → ℝ)
    (hmin : ∀ w, chainObjective (FlatCubic.edge P delta omega) n S lam (omega ^ 2) z ≤
      chainObjective (FlatCubic.edge P delta omega) n S lam (omega ^ 2) w) :
    omega ^ 2 / (S + lam * n) ≤ z 0 ∧ z 0 ≤ omega ^ 2 / S ∧
    ∀ j : Fin (n + 1), z j ≤ z 0 ∧ omega ^ 2 / (S + lam * n) - (j.val : ℝ) * omega ≤ z j := by
  obtain ⟨hz, hp, hGamma⟩ := actual_flat_packet_minimizer_flux P delta omega hd hdw n S lam
    (omega ^ 2) hS hlam (sq_nonneg omega) z hmin
  have hb := coordinate_bounds_from_actual_steps n omega z
    (actual_flat_packet_edge_steps P delta omega hd hdw n S lam hS hlam z hmin)
  have hsum : (∑ j : Fin n, z j.succ) ≤ (n : ℝ) * z 0 := by
    have hh := Finset.sum_le_sum (s := Finset.univ) (fun (j : Fin n) _ => (hb j.succ).1)
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using hh
  have hden : 0 < S + lam * n := by positivity
  have hlower : omega ^ 2 / (S + lam * n) ≤ z 0 := by
    apply (div_le_iff₀ hden).mpr
    have hh := mul_le_mul_of_nonneg_left hsum hlam.le
    nlinarith only [hh, hGamma]
  have hupper : z 0 ≤ omega ^ 2 / S := by
    apply (le_div_iff₀ hS).mpr
    have hh : 0 ≤ lam * ∑ j : Fin n, z j.succ :=
      mul_nonneg hlam.le (Finset.sum_nonneg (fun j _ => hz j.succ))
    nlinarith only [hh, hGamma]
  refine ⟨hlower, hupper, ?_⟩
  intro j
  exact ⟨(hb j).1, (sub_le_sub_right hlower _).trans (hb j).2⟩

theorem actual_flat_packet_bulk_coordinates
    (P : FlatCubic.Profile) (delta omega q Cm Cw lam : ℝ)
    (hd : 0 < delta) (hdw : delta ≤ omega) (hq : 1 ≤ q)
    (hCm : 0 ≤ Cm) (hCw : 4 * (Cm + 2) ≤ Cw) (hlam : 0 < lam)
    (homega : omega = Cw * lam * q ^ 2)
    (n : ℕ) (hn : (n : ℝ) ≤ Cm * q) (z : Fin (n + 1) → ℝ)
    (hmin : ∀ w, chainObjective (FlatCubic.edge P delta omega) n
      (lam * (q + 2) / 2) lam (omega ^ 2) z ≤
      chainObjective (FlatCubic.edge P delta omega) n (lam * (q + 2) / 2) lam (omega ^ 2) w) :
    4 * q * omega ≤ z 0 ∧
      ∀ j : Fin (n + 1), (j.val : ℝ) ≤ q → 3 * q * omega ≤ z j := by
  have hqpos : 0 < q := by linarith
  have hwpos : 0 < omega := hd.trans_le hdw
  have hS : 0 < lam * (q + 2) / 2 := by positivity
  obtain ⟨hbase, hu, hb⟩ := actual_flat_packet_coordinate_bounds P delta omega hd hdw n
    (lam * (q + 2) / 2) lam hS hlam z hmin
  let den : ℝ := lam * (q + 2) / 2 + lam * n
  have hden : 0 < den := by dsimp only [den]; positivity
  have hdenupper : den ≤ lam * (Cm + 2) * q := by
    have hh := mul_le_mul_of_nonneg_left hn hlam.le
    dsimp only [den]
    nlinarith only [hh, hq, hlam]
  have hratio : 4 * q * den ≤ omega := by
    have hh := mul_le_mul_of_nonneg_left hdenupper (by positivity : 0 ≤ 4 * q)
    have hc := mul_le_mul_of_nonneg_right hCw (by positivity : 0 ≤ lam * q ^ 2)
    rw [homega]
    nlinarith only [hh, hc]
  have hbulk : 4 * q * omega ≤ z 0 := by
    have hh := mul_le_mul_of_nonneg_right hratio hwpos.le
    have hdv : 4 * q * omega ≤ omega ^ 2 / den := by
      apply (le_div_iff₀ hden).mpr
      nlinarith only [hh]
    exact hdv.trans hbase
  refine ⟨hbulk, ?_⟩
  intro j hj
  have hji := mul_le_mul_of_nonneg_right hj hwpos.le
  have hlower := (hb j).2
  have hbase4 : 4 * q * omega ≤ omega ^ 2 / den := by
    apply (le_div_iff₀ hden).mpr
    have hh := mul_le_mul_of_nonneg_right hratio hwpos.le
    nlinarith only [hh]
  change omega ^ 2 / den - (j.val : ℝ) * omega ≤ z j at hlower
  nlinarith only [hji, hlower, hbase4]

def alphaStar (q lam eta : ℝ) {n : ℕ} (z : Fin (n + 1) → ℝ) : ℝ :=
  (Real.sqrt q * z 0 + eta / lam) / 2

def scalarObjective (g : ℝ → ℝ) (n : ℕ) (q lam eta alpha : ℝ) (z : Fin (n + 1) → ℝ) : ℝ :=
  (∑ i : Fin n, g (z i.castSucc - z i.succ)) +
    lam / 2 * (2 * alpha ^ 2 + (q + 1) * (z 0) ^ 2 -
      2 * Real.sqrt q * alpha * z 0 + ∑ j : Fin n, (z j.succ) ^ 2) - eta * alpha

theorem actual_alpha_completion_of_square
    (g : ℝ → ℝ) (n : ℕ) (q lam eta alpha : ℝ) (hq : 0 ≤ q) (hlam : lam ≠ 0)
    (z : Fin (n + 1) → ℝ) :
    scalarObjective g n q lam eta alpha z =
      chainObjective g n (lam * (q + 2) / 2) lam (eta * Real.sqrt q / 2) z +
        lam * (alpha - alphaStar q lam eta z) ^ 2 - eta ^ 2 / (4 * lam) := by
  unfold scalarObjective chainObjective alphaStar
  rw [weighted_sum n (lam * (q + 2) / 2) lam (fun i => (z i) ^ 2)]
  field_simp
  ring_nf
  rw [Real.sq_sqrt hq]
  ring

theorem actual_scalar_minimizer_alpha_and_reduction
    (g : ℝ → ℝ) (n : ℕ) (q lam eta alpha : ℝ) (hq : 0 ≤ q) (hlam : 0 < lam)
    (z : Fin (n + 1) → ℝ)
    (hmin : ∀ a w, scalarObjective g n q lam eta alpha z ≤ scalarObjective g n q lam eta a w) :
    alpha = alphaStar q lam eta z ∧
      ∀ w, chainObjective g n (lam * (q + 2) / 2) lam (eta * Real.sqrt q / 2) z ≤
        chainObjective g n (lam * (q + 2) / 2) lam (eta * Real.sqrt q / 2) w := by
  have ha := hmin (alphaStar q lam eta z) z
  rw [actual_alpha_completion_of_square g n q lam eta alpha hq hlam.ne' z,
    actual_alpha_completion_of_square g n q lam eta (alphaStar q lam eta z) hq hlam.ne' z] at ha
  simp only [sub_self, zero_pow (by omega : 2 ≠ 0), mul_zero, add_zero] at ha
  have hs : (alpha - alphaStar q lam eta z) ^ 2 = 0 := by
    nlinarith only [ha, hlam, sq_nonneg (alpha - alphaStar q lam eta z)]
  have heq : alpha = alphaStar q lam eta z := by nlinarith only [hs]
  refine ⟨heq, ?_⟩
  intro w
  have hm := hmin (alphaStar q lam eta w) w
  rw [actual_alpha_completion_of_square g n q lam eta alpha hq hlam.ne' z,
    actual_alpha_completion_of_square g n q lam eta (alphaStar q lam eta w) hq hlam.ne' w] at hm
  rw [heq] at hm
  simpa only [sub_self, zero_pow (by omega : 2 ≠ 0), mul_zero, add_zero,
    sub_le_sub_iff_right] using hm

theorem actual_scalar_minimizer_bulk
    (P : FlatCubic.Profile) (delta omega q Cm Cw lam alpha : ℝ)
    (hd : 0 < delta) (hdw : delta ≤ omega) (hq : 1 ≤ q)
    (hCm : 0 ≤ Cm) (hCw : 4 * (Cm + 2) ≤ Cw) (hlam : 0 < lam)
    (homega : omega = Cw * lam * q ^ 2)
    (n : ℕ) (hn : (n : ℝ) ≤ Cm * q) (z : Fin (n + 1) → ℝ)
    (hmin : ∀ a w, scalarObjective (FlatCubic.edge P delta omega) n q lam
      (2 * omega ^ 2 / Real.sqrt q) alpha z ≤
      scalarObjective (FlatCubic.edge P delta omega) n q lam (2 * omega ^ 2 / Real.sqrt q) a w) :
    alpha = alphaStar q lam (2 * omega ^ 2 / Real.sqrt q) z ∧
    (∀ i, 0 ≤ z i) ∧ (∀ k : Fin n, 0 ≤ z k.castSucc - z k.succ ∧ z k.castSucc - z k.succ ≤ omega) ∧
    4 * q * omega ≤ z 0 ∧
      ∀ j : Fin (n + 1), (j.val : ℝ) ≤ q → 3 * q * omega ≤ z j := by
  have hqpos : 0 < q := by linarith
  obtain ⟨ha, hred⟩ := actual_scalar_minimizer_alpha_and_reduction
    (FlatCubic.edge P delta omega) n q lam (2 * omega ^ 2 / Real.sqrt q) alpha hqpos.le hlam z hmin
  have hGamma : (2 * omega ^ 2 / Real.sqrt q) * Real.sqrt q / 2 = omega ^ 2 := by
    field_simp [(Real.sqrt_pos.mpr hqpos).ne']
  rw [hGamma] at hred
  have hS : 0 < lam * (q + 2) / 2 := by positivity
  obtain ⟨hz, _, _⟩ := actual_flat_packet_minimizer_flux P delta omega hd hdw n
    (lam * (q + 2) / 2) lam (omega ^ 2) hS hlam (sq_nonneg omega) z hred
  obtain ⟨hbulk, hcoords⟩ := actual_flat_packet_bulk_coordinates P delta omega q Cm Cw lam hd hdw hq
    hCm hCw hlam homega n hn z hred
  exact ⟨ha, hz, actual_flat_packet_edge_steps P delta omega hd hdw n (lam * (q + 2) / 2) lam
    hS hlam z hred, hbulk, hcoords⟩

end
end OriginalScalarPacketMinimizer


/- Actual physical packet minimizer -> the literal scalar minimizer.
   Orthogonal components are removed by exact paired-reflection symmetry
   and strict-convex minimizer uniqueness, not assumed absent. -/

open scoped BigOperators

namespace OriginalPhysicalPacketMinimizer

open FangqingAmplifier FangqingPacketLeakage FangqingLocalizedPacketEndpoints
  OriginalPacketOrientationNormalization OriginalScalarPacketMinimizer

noncomputable section

variable {A B W : Type*}
  [NormedAddCommGroup A] [InnerProductSpace ℝ A] [FiniteDimensional ℝ A]
  [NormedAddCommGroup B] [InnerProductSpace ℝ B] [FiniteDimensional ℝ B]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]

def rawPacket (C : A ≃ₗᵢ[ℝ] B) (h : A) (n : ℕ) (tail : Fin (n + 2) → W)
    (g : ℝ → ℝ) (q nu scale seed : ℝ) : PhysicalSpace A B W → ℝ :=
  H1 C h n tail (fun _ => 1) (fun _ => 0) id 1 scale seed 1 q nu g

theorem rawPacket_literal (C : A ≃ₗᵢ[ℝ] B) (h : A) (n : ℕ) (tail : Fin (n + 2) → W)
    (g : ℝ → ℝ) (q nu scale seed : ℝ) (z : PhysicalSpace A B W) :
    rawPacket C h n tail g q nu scale seed z = QPhysical q nu C z +
      scale * edgeSum g (pathDirection n (physicalFrame C h n tail)) z -
        seed * inner ℝ h z.fst.fst := by
  have hi : inner ℝ (mkPhysical h (0 : B) (0 : W)) z = inner ℝ h z.fst.fst := by
    change (inner ℝ h z.fst.fst + inner ℝ (0 : B) z.fst.snd) + inner ℝ (0 : W) z.snd = _
    simp only [inner_zero_left, add_zero]
  unfold rawPacket H1 activeEndpointSquared activeEndpoint localized boundedSeed
  simp only [id_eq, div_one, one_mul, zero_add, add_zero, hi]
  ring

theorem actual_raw_packet_reflection_invariant
    (C : A ≃ₗᵢ[ℝ] B) (h : A) (n : ℕ) (tail : Fin (n + 2) → W)
    (g : ℝ → ℝ) (q nu scale seed : ℝ) (z : PhysicalSpace A B W) :
    let U := (Submodule.span ℝ ({h} : Set A)).reflection
    let V := (Submodule.span ℝ (Set.range tail)).reflection
    rawPacket C h n tail g q nu scale seed (rotation C U V z) =
      rawPacket C h n tail g q nu scale seed z := by
  let U := (Submodule.span ℝ ({h} : Set A)).reflection
  let V := (Submodule.span ℝ (Set.range tail)).reflection
  have hh : U h = h := Submodule.reflection_mem_subspace_eq_self (Submodule.subset_span (Set.mem_singleton h))
  have ht : (fun j => V (tail j)) = tail := by
    funext j
    exact Submodule.reflection_mem_subspace_eq_self (Submodule.subset_span ⟨j, rfl⟩)
  have he := (actual_physical_endpoint_equivariance C U V h n tail
    (fun _ => 1) (fun _ => 0) id 1 scale seed 1 q nu g z).2
  change H1 C h n tail (fun _ => 1) (fun _ => 0) id 1 scale seed 1 q nu g (rotation C U V z) = _
  simpa only [rawPacket, H1, hh, ht] using he

def coordinatePoint (C : A ≃ₗᵢ[ℝ] B) (h : A) (n : ℕ) (tail : Fin (n + 2) → W)
    (alpha : ℝ) (z : Fin (n + 3) → ℝ) : PhysicalSpace A B W :=
  mkPhysical (alpha • h) (z 0 • C h) (∑ j : Fin (n + 2), z j.succ • tail j)

theorem physicalFrame_orthonormal
    (C : A ≃ₗᵢ[ℝ] B) (h : A) (hh : ‖h‖ = 1)
    (n : ℕ) (tail : Fin (n + 2) → W) (ht : Orthonormal ℝ tail) :
    Orthonormal ℝ (physicalFrame C h n tail) := by
  rw [orthonormal_iff_ite]
  intro i j
  refine Fin.cases ?_ (fun i' => ?_) i
  · refine Fin.cases ?_ (fun j' => ?_) j
    · change (inner ℝ (0 : A) (0 : A) + inner ℝ (C h) (C h)) + inner ℝ (0 : W) (0 : W) = _
      simp only [inner_zero_left, zero_add, add_zero, real_inner_self_eq_norm_sq, C.norm_map, hh]
      norm_num
    · change (inner ℝ (0 : A) (0 : A) + inner ℝ (C h) (0 : B)) + inner ℝ (0 : W) (tail j') = _
      simp only [inner_zero_left, inner_zero_right, zero_add]
      simp
      exact (Fin.succ_ne_zero j').symm
  · refine Fin.cases ?_ (fun j' => ?_) j
    · change (inner ℝ (0 : A) (0 : A) + inner ℝ (0 : B) (C h)) + inner ℝ (tail i') (0 : W) = _
      simp only [inner_zero_left, inner_zero_right, zero_add]
      simp
    · change (inner ℝ (0 : A) (0 : A) + inner ℝ (0 : B) (0 : B)) + inner ℝ (tail i') (tail j') = _
      simp only [inner_zero_left, zero_add, orthonormal_iff_ite.mp ht]
      simp

theorem actual_minimizer_has_coordinate_form
    (C : A ≃ₗᵢ[ℝ] B) (h : A) (n : ℕ) (tail : Fin (n + 2) → W)
    (g : ℝ → ℝ) (q nu scale seed : ℝ)
    (hstrict : StrictConvexOn ℝ (Set.univ : Set (PhysicalSpace A B W))
      (rawPacket C h n tail g q nu scale seed))
    (Z : PhysicalSpace A B W)
    (hmin : ∀ Y, rawPacket C h n tail g q nu scale seed Z ≤ rawPacket C h n tail g q nu scale seed Y) :
    ∃ alpha : ℝ, ∃ z : Fin (n + 3) → ℝ, Z = coordinatePoint C h n tail alpha z := by
  let U := (Submodule.span ℝ ({h} : Set A)).reflection
  let V := (Submodule.span ℝ (Set.range tail)).reflection
  let T := rotation C U V
  have hinv (Y : PhysicalSpace A B W) : rawPacket C h n tail g q nu scale seed (T Y) =
      rawPacket C h n tail g q nu scale seed Y := actual_raw_packet_reflection_invariant C h n tail g q nu scale seed Y
  have hmT : ∀ Y, rawPacket C h n tail g q nu scale seed (T Z) ≤
      rawPacket C h n tail g q nu scale seed Y := by
    intro Y
    obtain ⟨Y, rfl⟩ := T.surjective Y
    rw [hinv, hinv]
    exact hmin Y
  have hfix : T Z = Z := hstrict.eq_of_isMinOn
    (fun Y _ => hmT Y) (fun Y _ => hmin Y) (Set.mem_univ _) (Set.mem_univ _)
  have ha : U Z.fst.fst = Z.fst.fst := congrArg (fun Y : PhysicalSpace A B W => Y.fst.fst) hfix
  have hb : C (U (C.symm Z.fst.snd)) = Z.fst.snd := congrArg (fun Y : PhysicalSpace A B W => Y.fst.snd) hfix
  have hw : V Z.snd = Z.snd := congrArg (fun Y : PhysicalSpace A B W => Y.snd) hfix
  have hb' : U (C.symm Z.fst.snd) = C.symm Z.fst.snd := by
    simpa only [C.symm_apply_apply] using congrArg C.symm hb
  obtain ⟨alpha, halpha⟩ := Submodule.mem_span_singleton.mp (Submodule.reflection_eq_self_iff _ |>.mp ha)
  obtain ⟨first, hfirst⟩ := Submodule.mem_span_singleton.mp (Submodule.reflection_eq_self_iff _ |>.mp hb')
  obtain ⟨coeff, hcoeff⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp
    (Submodule.reflection_eq_self_iff _ |>.mp hw)
  refine ⟨alpha, Fin.cons first coeff, ?_⟩
  apply (WithLp.ext_iff 2).mpr
  apply Prod.ext
  · apply (WithLp.ext_iff 2).mpr
    apply Prod.ext
    · exact halpha.symm
    · change Z.fst.snd = first • C h
      have he := congrArg C hfirst
      simpa only [map_smul, C.apply_symm_apply] using he.symm
  · exact hcoeff.symm

theorem coordinatePoint_frame_inner
    (C : A ≃ₗᵢ[ℝ] B) (h : A) (hh : ‖h‖ = 1)
    (n : ℕ) (tail : Fin (n + 2) → W) (ht : Orthonormal ℝ tail)
    (alpha : ℝ) (z : Fin (n + 3) → ℝ) (i : Fin (n + 3)) :
    inner ℝ (physicalFrame C h n tail i) (coordinatePoint C h n tail alpha z) = z i := by
  have hinner : inner ℝ (C h) (C h) = 1 := by rw [real_inner_self_eq_norm_sq, C.norm_map, hh]; norm_num
  refine Fin.cases ?_ (fun j => ?_) i
  · change (inner ℝ (0 : A) (alpha • h) + inner ℝ (C h) (z 0 • C h)) +
      inner ℝ (0 : W) (∑ j : Fin (n + 2), z j.succ • tail j) = z 0
    simp only [inner_zero_left, inner_smul_right, hinner, mul_one, mul_zero, zero_add, add_zero]
  · change (inner ℝ (0 : A) (alpha • h) + inner ℝ (0 : B) (z 0 • C h)) +
      inner ℝ (tail j) (∑ j : Fin (n + 2), z j.succ • tail j) = z j.succ
    simp only [inner_zero_left, zero_add]
    exact ht.inner_right_fintype (fun j => z j.succ) j

theorem orthonormal_tail_sum_norm_sq
    {n : ℕ} (tail : Fin n → W) (ht : Orthonormal ℝ tail) (c : Fin n → ℝ) :
    ‖∑ j, c j • tail j‖ ^ 2 = ∑ j, (c j) ^ 2 := by
  have hh := ht.inner_sum c c Finset.univ
  simpa only [real_inner_self_eq_norm_sq, RCLike.conj_to_real, pow_two] using hh

theorem actual_physical_scalar_value_identity
    (C : A ≃ₗᵢ[ℝ] B) (h : A) (hh : ‖h‖ = 1)
    (n : ℕ) (tail : Fin (n + 2) → W) (ht : Orthonormal ℝ tail)
    (g : ℝ → ℝ) (q scale lam eta alpha : ℝ) (z : Fin (n + 3) → ℝ) :
    rawPacket C h n tail g q (scale * lam) scale (scale * eta) (coordinatePoint C h n tail alpha z) =
      scale * scalarObjective g (n + 2) q lam eta alpha z := by
  have hpath (i : Fin (n + 2)) : inner ℝ (pathDirection n (physicalFrame C h n tail) i)
      (coordinatePoint C h n tail alpha z) = z i.castSucc - z i.succ := by
    simp only [pathDirection, inner_sub_left, coordinatePoint_frame_inner C h hh n tail ht alpha z]
  have hhandle : inner ℝ h (alpha • h) = alpha := by
    rw [inner_smul_right, real_inner_self_eq_norm_sq, hh]
    ring
  have hcross : inner ℝ (C (alpha • h)) (z 0 • C h) = alpha * z 0 := by
    simp only [map_smul, inner_smul_left, inner_smul_right, RCLike.conj_to_real,
      real_inner_self_eq_norm_sq, C.norm_map, hh]
    ring
  rw [rawPacket_literal]
  unfold edgeSum
  simp only [hpath]
  change QPhysical q (scale * lam) C (coordinatePoint C h n tail alpha z) +
    scale * (∑ i : Fin (n + 2), g (z i.castSucc - z i.succ)) -
    scale * eta * inner ℝ h (alpha • h) = _
  rw [hhandle]
  unfold QPhysical
  change scale * lam / 2 * (2 * ‖alpha • h‖ ^ 2 + (q + 1) * ‖z 0 • C h‖ ^ 2 -
    2 * Real.sqrt q * inner ℝ (C (alpha • h)) (z 0 • C h) +
    ‖∑ j : Fin (n + 2), z j.succ • tail j‖ ^ 2) +
    scale * (∑ i : Fin (n + 2), g (z i.castSucc - z i.succ)) - scale * eta * alpha = _
  rw [hcross, orthonormal_tail_sum_norm_sq tail ht]
  simp only [norm_smul, Real.norm_eq_abs, C.norm_map, hh, mul_one, sq_abs]
  unfold scalarObjective
  ring

theorem actual_physical_minimizer_reduces_to_scalar_minimizer
    (C : A ≃ₗᵢ[ℝ] B) (h : A) (hh : ‖h‖ = 1)
    (n : ℕ) (tail : Fin (n + 2) → W) (ht : Orthonormal ℝ tail)
    (g : ℝ → ℝ) (q scale lam eta : ℝ) (hscale : 0 < scale)
    (hstrict : StrictConvexOn ℝ (Set.univ : Set (PhysicalSpace A B W))
      (rawPacket C h n tail g q (scale * lam) scale (scale * eta)))
    (Z : PhysicalSpace A B W)
    (hmin : ∀ Y, rawPacket C h n tail g q (scale * lam) scale (scale * eta) Z ≤
      rawPacket C h n tail g q (scale * lam) scale (scale * eta) Y) :
    ∃ alpha : ℝ, ∃ z : Fin (n + 3) → ℝ, Z = coordinatePoint C h n tail alpha z ∧
      ∀ a w, scalarObjective g (n + 2) q lam eta alpha z ≤ scalarObjective g (n + 2) q lam eta a w := by
  obtain ⟨alpha, z, hZ⟩ := actual_minimizer_has_coordinate_form C h n tail g q
    (scale * lam) scale (scale * eta) hstrict Z hmin
  refine ⟨alpha, z, hZ, ?_⟩
  intro a w
  have hm := hmin (coordinatePoint C h n tail a w)
  rw [hZ, actual_physical_scalar_value_identity C h hh n tail ht,
    actual_physical_scalar_value_identity C h hh n tail ht] at hm
  by_contra hc
  have hh := mul_lt_mul_of_pos_left (lt_of_not_ge hc) hscale
  exact (not_lt_of_ge hm) hh

theorem actual_physical_minimizer_bulk_coordinates
    (P : FlatCubic.Profile) (C : A ≃ₗᵢ[ℝ] B) (h : A) (hh : ‖h‖ = 1)
    (n : ℕ) (tail : Fin (n + 2) → W) (ht : Orthonormal ℝ tail)
    (delta omega q Cm Cw scale lam : ℝ)
    (hd : 0 < delta) (hdw : delta ≤ omega) (hq : 1 ≤ q)
    (hCm : 0 ≤ Cm) (hCw : 4 * (Cm + 2) ≤ Cw) (hscale : 0 < scale) (hlam : 0 < lam)
    (homega : omega = Cw * lam * q ^ 2) (hn : ((n + 2 : ℕ) : ℝ) ≤ Cm * q)
    (hstrict : StrictConvexOn ℝ (Set.univ : Set (PhysicalSpace A B W))
      (rawPacket C h n tail (FlatCubic.edge P delta omega) q (scale * lam) scale
        (scale * (2 * omega ^ 2 / Real.sqrt q))))
    (Z : PhysicalSpace A B W)
    (hmin : ∀ Y, rawPacket C h n tail (FlatCubic.edge P delta omega) q (scale * lam) scale
        (scale * (2 * omega ^ 2 / Real.sqrt q)) Z ≤
      rawPacket C h n tail (FlatCubic.edge P delta omega) q (scale * lam) scale
        (scale * (2 * omega ^ 2 / Real.sqrt q)) Y) :
    ∃ alpha : ℝ, ∃ z : Fin (n + 3) → ℝ,
      Z = coordinatePoint C h n tail alpha z ∧
      alpha = alphaStar q lam (2 * omega ^ 2 / Real.sqrt q) z ∧
      (∀ i, 0 ≤ z i) ∧ (∀ k : Fin (n + 2), 0 ≤ z k.castSucc - z k.succ ∧ z k.castSucc - z k.succ ≤ omega) ∧
      ∀ j : Fin (n + 3), (j.val : ℝ) ≤ q →
        3 * q * omega ≤ inner ℝ (physicalFrame C h n tail j) Z := by
  obtain ⟨alpha, z, hZ, hm⟩ := actual_physical_minimizer_reduces_to_scalar_minimizer C h hh n tail ht
    (FlatCubic.edge P delta omega) q scale lam (2 * omega ^ 2 / Real.sqrt q) hscale hstrict Z hmin
  obtain ⟨ha, hz, hsteps, _, hbulk⟩ := actual_scalar_minimizer_bulk P delta omega q Cm Cw lam alpha
    hd hdw hq hCm hCw hlam homega (n + 2) hn z hm
  refine ⟨alpha, z, hZ, ha, hz, hsteps, ?_⟩
  intro j hj
  rw [hZ, coordinatePoint_frame_inner C h hh n tail ht]
  exact hbulk j hj

end
end OriginalPhysicalPacketMinimizer


namespace PacketCore

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E]

def EpsilonSubgradient (g : E → ℝ) (y v : E) (ε : ℝ) : Prop :=
  0 ≤ ε ∧ ∀ w : E, g y + inner ℝ v (w - y) - ε ≤ g w

theorem strongConvex_support
    (g : E → ℝ) (μ : ℝ)
    (hsc : StrongConvexOn (Set.univ : Set E) μ g)
    (hdiff : Differentiable ℝ g) (y w : E) :
    g y + inner ℝ (gradient g y) (w - y) +
      μ / 2 * ‖w - y‖ ^ 2 ≤ g w := by
  let h : E → ℝ := fun z => g z - μ / 2 * ‖z‖ ^ 2
  have hc : ConvexOn ℝ (Set.univ : Set E) h :=
    strongConvexOn_iff_convex.mp hsc
  let a : ℝ → E := fun t => y + t • (w - y)
  have ha0 : a 0 = y := by simp [a]
  have ha1 : a 1 = w := by
    dsimp [a]
    simp only [one_smul]
    abel
  have hline : ConvexOn ℝ (Set.univ : Set ℝ)
      (fun t : ℝ => h (a t)) := by
    refine ⟨convex_univ, ?_⟩
    intro s hs t ht p q hp hq hpq
    have haff : a (p * s + q * t) = p • a s + q • a t := by
      calc
        a (p * s + q * t) =
            (p + q) • y + (p * s + q * t) • (w - y) := by
          simp only [a, hpq, one_smul]
        _ = p • a s + q • a t := by
          simp only [a, smul_add, add_smul, mul_smul]
          abel
    have hh := hc.2 (Set.mem_univ (a s)) (Set.mem_univ (a t)) hp hq hpq
    simpa only [smul_eq_mul, ← haff] using hh
  have hcurve : HasDerivAt a (w - y) (0 : ℝ) := by
    simpa only [a, one_smul, id_eq] using
      (((hasDerivAt_id (0 : ℝ)).smul_const (w - y)).const_add y)
  have hgy : HasFDerivAt g (fderiv ℝ g y) (a 0) := by
    rw [ha0]
    exact (hdiff y).hasFDerivAt
  have hgcurve : HasDerivAt (fun t : ℝ => g (a t))
      (inner ℝ (gradient g y) (w - y)) 0 := by
    simpa only [Function.comp_def, inner_gradient_left] using
      (hgy.comp_hasDerivAt (0 : ℝ) hcurve)
  have hnormcurve : HasDerivAt (fun t : ℝ => ‖a t‖ ^ 2)
      (2 * inner ℝ y (w - y)) 0 := by
    simpa only [ha0] using hcurve.norm_sq
  have hder : HasDerivAt (fun t : ℝ => h (a t))
      (inner ℝ (gradient g y) (w - y) -
        μ / 2 * (2 * inner ℝ y (w - y))) 0 := by
    simpa only [h, Pi.sub_def] using
      (hgcurve.sub (hnormcurve.const_mul (μ / 2)))
  have htangent := hline.le_slope_of_hasDerivAt
    (Set.mem_univ (0 : ℝ)) (Set.mem_univ (1 : ℝ))
    (by norm_num : (0 : ℝ) < 1) hder
  have ht : inner ℝ (gradient g y) (w - y) -
      μ / 2 * (2 * inner ℝ y (w - y)) ≤
      (g w - μ / 2 * ‖w‖ ^ 2) -
        (g y - μ / 2 * ‖y‖ ^ 2) := by
    simpa only [slope_def_field, ha0, ha1, h, sub_zero, div_one]
      using htangent
  rw [inner_sub_right (𝕜 := ℝ) y w y,
    real_inner_self_eq_norm_sq] at ht
  rw [norm_sub_sq_real, real_inner_comm y w]
  nlinarith only [ht]


theorem gradient_eq_zero_at_global_min
    (H : E → ℝ) (z : E) (hmin : ∀ y : E, H z ≤ H y) :
    gradient H z = 0 := by
  have hloc : IsLocalMin H z := Filter.Eventually.of_forall hmin
  have hf := hloc.fderiv_eq_zero
  have hi : inner ℝ (gradient H z) (gradient H z) = 0 := by
    rw [inner_gradient_left, hf]
    simp
  rw [real_inner_self_eq_norm_sq] at hi
  apply norm_eq_zero.mp
  nlinarith [norm_nonneg (gradient H z)]

theorem gradient_strong_monotone
    (H : E → ℝ) (k : ℝ)
    (hsc : StrongConvexOn (Set.univ : Set E) k H)
    (hdiff : Differentiable ℝ H) (y z : E) :
    k * ‖y - z‖ ^ 2 ≤
      inner ℝ (gradient H y - gradient H z) (y - z) := by
  have h1 := strongConvex_support H k hsc hdiff y z
  have h2 := strongConvex_support H k hsc hdiff z y
  have hneg : z - y = -(y - z) := by abel
  rw [norm_sub_rev z y] at h1
  rw [hneg, inner_neg_right] at h1
  rw [inner_sub_left]
  nlinarith only [h1, h2]

theorem strongConvex_gradient_distance
    (H : E → ℝ) (k : ℝ) (hk : 0 < k)
    (hsc : StrongConvexOn (Set.univ : Set E) k H)
    (hdiff : Differentiable ℝ H) (z : E)
    (hmin : ∀ y : E, H z ≤ H y) (y : E) :
    k * ‖y - z‖ ≤ ‖gradient H y‖ := by
  have hz := gradient_eq_zero_at_global_min H z hmin
  have h1 := gradient_strong_monotone H k hsc hdiff y z
  rw [hz, sub_zero] at h1
  have h2 := real_inner_le_norm (gradient H y) (y - z)
  by_cases ht : ‖y - z‖ = 0
  · simpa [ht] using norm_nonneg (gradient H y)
  · have htpos : 0 < ‖y - z‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm ht)
    nlinarith only [h1, h2, htpos]


noncomputable def saddleValue (H : E → ℝ) (β c lam m : ℝ) (x y : E) : ℝ :=
  β / 2 * ‖x‖ ^ 2 + lam * inner ℝ x y - (H y - c / 2 * ‖y‖ ^ 2) + m

theorem inner_maximizer_first_order
    (H : E → ℝ) (β c lam m : ℝ) (x y : E)
    (hdiff : Differentiable ℝ H)
    (hmax : ∀ z : E, saddleValue H β c lam m x z ≤ saddleValue H β c lam m x y) :
    gradient H y = lam • x + c • y := by
  apply ext_inner_right ℝ
  intro v
  let a : ℝ → E := fun t => y + t • v
  have ha0 : a 0 = y := by simp [a]
  have hcurve : HasDerivAt a v (0 : ℝ) := by
    simpa only [a, one_smul, id_eq] using
      (((hasDerivAt_id (0 : ℝ)).smul_const v).const_add y)
  have hH : HasDerivAt (fun t : ℝ => H (a t))
      (inner ℝ (gradient H y) v) 0 := by
    have hHy : HasFDerivAt H (fderiv ℝ H y) (a 0) := by
      rw [ha0]
      exact (hdiff y).hasFDerivAt
    simpa only [Function.comp_def, inner_gradient_left] using
      (hHy.comp_hasDerivAt (0 : ℝ) hcurve)
  have hi : HasDerivAt (fun t : ℝ => inner ℝ x (a t))
      (inner ℝ x v) 0 := by
    simpa only [inner_zero_left, zero_add, add_zero] using
      (HasDerivAt.inner ℝ (hasDerivAt_const (0 : ℝ) x) hcurve)
  have hn : HasDerivAt (fun t : ℝ => ‖a t‖ ^ 2)
      (2 * inner ℝ y v) 0 := by
    simpa only [ha0] using hcurve.norm_sq
  have hp : HasDerivAt
      (fun t : ℝ => lam * inner ℝ x (a t) - (H (a t) - c / 2 * ‖a t‖ ^ 2))
      (lam * inner ℝ x v - (inner ℝ (gradient H y) v -
        c / 2 * (2 * inner ℝ y v))) 0 :=
    (hi.const_mul lam).sub (hH.sub (hn.const_mul (c / 2)))
  have hpmax : IsLocalMax
      (fun t : ℝ => lam * inner ℝ x (a t) - (H (a t) - c / 2 * ‖a t‖ ^ 2)) 0 := by
    apply Filter.Eventually.of_forall
    intro t
    have hh := hmax (a t)
    dsimp [saddleValue] at hh
    dsimp only
    rw [ha0]
    linarith only [hh]
  have hz := hpmax.hasDerivAt_eq_zero hp
  rw [inner_add_left, real_inner_smul_left, real_inner_smul_left]
  nlinarith only [hz]

theorem fenchel_first_order_identity
    (H : E → ℝ) (β c lam m : ℝ) (x y : E)
    (hβ : 0 < β) (hc : 0 < c) (hrel : lam ^ 2 = β * c)
    (hdiff : Differentiable ℝ H)
    (hmax : ∀ z : E, saddleValue H β c lam m x z ≤ saddleValue H β c lam m x y) :
    gradient H y = c • (y - (-β / lam) • x) := by
  have hlam : lam ≠ 0 := by
    intro hzero
    rw [hzero] at hrel
    nlinarith [mul_pos hβ hc]
  have hcoef : c * (-β / lam) = -lam := by
    field_simp
    nlinarith only [hrel]
  rw [inner_maximizer_first_order H β c lam m x y hdiff hmax,
    smul_sub, smul_smul, hcoef, neg_smul]
  abel

theorem fenchel_candidate_identity
    (β lam : ℝ) (hlam : lam ≠ 0) (x y : E) :
    β • x + lam • y = lam • (y - (-β / lam) • x) := by
  have hcoef : lam * (-β / lam) = -β := by field_simp
  rw [smul_sub, smul_smul, hcoef, neg_smul]
  abel

theorem fenchel_stationarity_distance_core
    (H : E → ℝ) (μ β c lam m : ℝ) (x y z : E)
    (hμ : 0 < μ) (hβ : 0 < β) (hc : 0 < c)
    (hrel : lam ^ 2 = β * c)
    (hsc : StrongConvexOn (Set.univ : Set E) (μ + c) H)
    (hdiff : Differentiable ℝ H) (hmin : ∀ w : E, H z ≤ H w)
    (hmax : ∀ w : E, saddleValue H β c lam m x w ≤ saddleValue H β c lam m x y) :
    lam / (1 + c / (μ + c)) * ‖(-β / lam) • x - z‖ ≤
      ‖β • x + lam • y‖ := by
  have hk : 0 < μ + c := by positivity
  have hlam : lam ≠ 0 := by
    intro hzero
    rw [hzero] at hrel
    nlinarith [mul_pos hβ hc]
  let w : E := (-β / lam) • x
  have hg := fenchel_first_order_identity H β c lam m x y hβ hc hrel hdiff hmax
  change gradient H y = c • (y - w) at hg
  have hd := strongConvex_gradient_distance H (μ + c) hk hsc hdiff z hmin y
  rw [hg, norm_smul, Real.norm_eq_abs, abs_of_pos hc] at hd
  have ht : ‖w - z‖ ≤ ‖y - w‖ + ‖y - z‖ := by
    calc
      ‖w - z‖ ≤ ‖w - y‖ + ‖y - z‖ := norm_sub_le_norm_sub_add_norm_sub w y z
      _ = ‖y - w‖ + ‖y - z‖ := by rw [norm_sub_rev w y]
  have hraw : (μ + c) * ‖w - z‖ ≤ (μ + c + c) * ‖y - w‖ := by
    have ht' := mul_le_mul_of_nonneg_left ht (le_of_lt hk)
    nlinarith only [ht', hd]
  have hv := fenchel_candidate_identity β lam hlam x y
  change β • x + lam • y = lam • (y - w) at hv
  rw [hv, norm_smul, Real.norm_eq_abs]
  change lam / (1 + c / (μ + c)) * ‖w - z‖ ≤ |lam| * ‖y - w‖
  have hden : 0 < 1 + c / (μ + c) := by positivity
  by_cases hsign : 0 < lam
  · rw [abs_of_pos hsign]
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hden).mpr
    have hmul := mul_le_mul_of_nonneg_left hraw (le_of_lt hsign)
    apply (mul_le_mul_iff_left₀ hk).mp
    have hscaled : lam * ‖y - w‖ * (1 + c / (μ + c)) * (μ + c) =
        lam * (μ + c + c) * ‖y - w‖ := by
      field_simp
      <;> ring
    rw [hscaled]
    nlinarith only [hmul]
  · have hlamle : lam ≤ 0 := le_of_not_gt hsign
    have hleft : lam / (1 + c / (μ + c)) * ‖w - z‖ ≤ 0 := by
      exact mul_nonpos_of_nonpos_of_nonneg (div_nonpos_of_nonpos_of_nonneg hlamle (le_of_lt hden)) (norm_nonneg _)
    exact le_trans hleft (mul_nonneg (abs_nonneg _) (norm_nonneg _))


noncomputable def valueFromMaximizers (H : E → ℝ) (β c lam m : ℝ) (Y : E → E) (x : E) : ℝ :=
  saddleValue H β c lam m x (Y x)

theorem value_strongConvex_from_actual_maximizers
    (H : E → ℝ) (β c lam m : ℝ) (Y : E → E)
    (hY : ∀ x z : E, saddleValue H β c lam m x z ≤ saddleValue H β c lam m x (Y x)) :
    StrongConvexOn (Set.univ : Set E) β (valueFromMaximizers H β c lam m Y) := by
  rw [strongConvexOn_iff_convex]
  refine ⟨convex_univ, ?_⟩
  intro x hx z hz a b ha hb hab
  let t : E := a • x + b • z
  let y : E := Y t
  have h1 := mul_le_mul_of_nonneg_left (hY x y) ha
  have h2 := mul_le_mul_of_nonneg_left (hY z y) hb
  have hlin : saddleValue H β c lam m t y - β / 2 * ‖t‖ ^ 2 =
      a * (saddleValue H β c lam m x y - β / 2 * ‖x‖ ^ 2) +
      b * (saddleValue H β c lam m z y - β / 2 * ‖z‖ ^ 2) := by
    dsimp [saddleValue, t]
    rw [inner_add_left, real_inner_smul_left, real_inner_smul_left]
    have hbeq : b = 1 - a := by linarith only [hab]
    rw [hbeq]
    ring
  change saddleValue H β c lam m t y - β / 2 * ‖t‖ ^ 2 ≤
    a * (saddleValue H β c lam m x (Y x) - β / 2 * ‖x‖ ^ 2) +
    b * (saddleValue H β c lam m z (Y z) - β / 2 * ‖z‖ ^ 2)
  nlinarith only [hlin, h1, h2]

theorem saddle_complete_square
    (H : E → ℝ) (β c lam m : ℝ) (hβ : 0 < β)
    (hrel : lam ^ 2 = β * c) (x y : E) :
    saddleValue H β c lam m x y =
      β / 2 * ‖x + (lam / β) • y‖ ^ 2 - H y + m := by
  have hβne : β ≠ 0 := ne_of_gt hβ
  have hcformula : c = lam ^ 2 / β := by
    apply (eq_div_iff hβne).mpr
    nlinarith only [hrel]
  dsimp [saddleValue]
  rw [hcformula, norm_add_sq_real, inner_smul_right, norm_smul,
    Real.norm_eq_abs, mul_pow, sq_abs]
  field_simp
  <;> ring

theorem saddle_at_candidate_minimum
    (H : E → ℝ) (β c lam m : ℝ) (hβ : 0 < β)
    (hrel : lam ^ 2 = β * c) (z y : E) :
    saddleValue H β c lam m ((-lam / β) • z) y =
      c / 2 * ‖y - z‖ ^ 2 - H y + m := by
  rw [saddle_complete_square H β c lam m hβ hrel]
  have hvec : (-lam / β) • z + (lam / β) • y = (lam / β) • (y - z) := by
    rw [smul_sub, neg_div, neg_smul]
    abel
  rw [hvec, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  have hcoef : β / 2 * (lam / β) ^ 2 = c / 2 := by
    field_simp
    nlinarith only [hrel]
  calc
    β / 2 * ((lam / β) ^ 2 * ‖y - z‖ ^ 2) - H y + m =
        (β / 2 * (lam / β) ^ 2) * ‖y - z‖ ^ 2 - H y + m := by ring
    _ = c / 2 * ‖y - z‖ ^ 2 - H y + m := by rw [hcoef]

theorem value_minimum_zero_from_actual_maximizers
    (H : E → ℝ) (μ β c lam : ℝ) (z : E) (Y : E → E)
    (hμ : 0 < μ) (hβ : 0 < β) (hrel : lam ^ 2 = β * c)
    (hsc : StrongConvexOn (Set.univ : Set E) (μ + c) H)
    (hdiff : Differentiable ℝ H) (hmin : ∀ w : E, H z ≤ H w)
    (hY : ∀ x w : E, saddleValue H β c lam (H z) x w ≤
      saddleValue H β c lam (H z) x (Y x)) :
    (∀ x : E, 0 ≤ valueFromMaximizers H β c lam (H z) Y x) ∧
    valueFromMaximizers H β c lam (H z) Y ((-lam / β) • z) = 0 ∧
    (∀ x : E, valueFromMaximizers H β c lam (H z) Y ((-lam / β) • z) ≤
      valueFromMaximizers H β c lam (H z) Y x) := by
  have hnonneg : ∀ x : E, 0 ≤ valueFromMaximizers H β c lam (H z) Y x := by
    intro x
    have hs := hY x z
    have hp : 0 ≤ saddleValue H β c lam (H z) x z := by
      rw [saddle_complete_square H β c lam (H z) hβ hrel]
      have hq : 0 ≤ β / 2 * ‖x + (lam / β) • z‖ ^ 2 := by positivity
      linarith only [hq]
    exact le_trans hp hs
  have hg : gradient H z = 0 := gradient_eq_zero_at_global_min H z hmin
  have hupper : ∀ y : E, saddleValue H β c lam (H z) ((-lam / β) • z) y ≤ 0 := by
    intro y
    have hs := strongConvex_support H (μ + c) hsc hdiff z y
    rw [hg, inner_zero_left] at hs
    rw [saddle_at_candidate_minimum H β c lam (H z) hβ hrel]
    nlinarith only [hs, mul_nonneg (le_of_lt hμ) (sq_nonneg ‖y - z‖)]
  have hzero : valueFromMaximizers H β c lam (H z) Y ((-lam / β) • z) = 0 := by
    apply le_antisymm
    · exact hupper (Y ((-lam / β) • z))
    · exact hnonneg _
  exact ⟨hnonneg, hzero, fun x => by rw [hzero]; exact hnonneg x⟩


theorem saddle_inner_quadratic_gap
    (H : E → ℝ) (μ β c lam m : ℝ) (x y : E)
    (hsc : StrongConvexOn (Set.univ : Set E) (μ + c) H)
    (hdiff : Differentiable ℝ H)
    (hmax : ∀ z : E, saddleValue H β c lam m x z ≤ saddleValue H β c lam m x y)
    (z : E) :
    saddleValue H β c lam m x z ≤
      saddleValue H β c lam m x y - μ / 2 * ‖z - y‖ ^ 2 := by
  have hs := strongConvex_support H (μ + c) hsc hdiff y z
  rw [inner_maximizer_first_order H β c lam m x y hdiff hmax,
    inner_add_left, real_inner_smul_left, real_inner_smul_left,
    inner_sub_right, inner_sub_right, real_inner_self_eq_norm_sq] at hs
  rw [norm_sub_sq_real, real_inner_comm z y] at hs
  dsimp [saddleValue]
  rw [norm_sub_sq_real]
  nlinarith only [hs]

theorem saddle_change_center
    (H : E → ℝ) (β c lam m : ℝ) (x x' y z : E) :
    saddleValue H β c lam m x' z - saddleValue H β c lam m x' y =
      saddleValue H β c lam m x z - saddleValue H β c lam m x y +
        lam * inner ℝ (x' - x) (z - y) := by
  dsimp [saddleValue]
  rw [inner_sub_left, inner_sub_right, inner_sub_right]
  ring

theorem scalar_young (μ A t : ℝ) (hμ : 0 < μ) :
    A * t ≤ μ / 2 * t ^ 2 + A ^ 2 / (2 * μ) := by
  have hden : 0 < 2 * μ := by positivity
  have hcancel : A ^ 2 / (2 * μ) * (2 * μ) = A ^ 2 :=
    div_mul_cancel₀ _ (ne_of_gt hden)
  apply (mul_le_mul_iff_right₀ hμ).mp
  nlinarith only [hcancel, sq_nonneg (μ * t - A)]

theorem value_maximization_gap
    (H : E → ℝ) (μ β c lam m : ℝ) (hμ : 0 < μ)
    (hsc : StrongConvexOn (Set.univ : Set E) (μ + c) H)
    (hdiff : Differentiable ℝ H) (Y : E → E)
    (hY : ∀ x z : E, saddleValue H β c lam m x z ≤ saddleValue H β c lam m x (Y x))
    (x x' : E) :
    0 ≤ valueFromMaximizers H β c lam m Y x' - saddleValue H β c lam m x' (Y x) ∧
    valueFromMaximizers H β c lam m Y x' - saddleValue H β c lam m x' (Y x) ≤
      lam ^ 2 / (2 * μ) * ‖x' - x‖ ^ 2 := by
  constructor
  · exact sub_nonneg.mpr (hY x' (Y x))
  · have hs := saddle_inner_quadratic_gap H μ β c lam m x (Y x) hsc hdiff
        (hY x) (Y x')
    have hid := saddle_change_center H β c lam m x x' (Y x) (Y x')
    have hi : lam * inner ℝ (x' - x) (Y x' - Y x) ≤
        (|lam| * ‖x' - x‖) * ‖Y x' - Y x‖ := by
      have ht := real_inner_le_norm (lam • (x' - x)) (Y x' - Y x)
      simpa only [real_inner_smul_left, norm_smul, Real.norm_eq_abs, mul_assoc] using ht
    have hy := scalar_young μ (|lam| * ‖x' - x‖) ‖Y x' - Y x‖ hμ
    have hcoeff : (|lam| * ‖x' - x‖) ^ 2 / (2 * μ) =
        lam ^ 2 / (2 * μ) * ‖x' - x‖ ^ 2 := by
      rw [mul_pow, sq_abs]
      ring
    rw [hcoeff] at hy
    change saddleValue H β c lam m x' (Y x') - saddleValue H β c lam m x' (Y x) ≤ _
    nlinarith only [hs, hid, hi, hy]

theorem saddle_outer_remainder
    (H : E → ℝ) (β c lam m : ℝ) (x x' y : E) :
    saddleValue H β c lam m x' y - saddleValue H β c lam m x y -
      inner ℝ (β • x + lam • y) (x' - x) = β / 2 * ‖x' - x‖ ^ 2 := by
  dsimp [saddleValue]
  rw [inner_add_left, real_inner_smul_left, real_inner_smul_left,
    inner_sub_right, inner_sub_right, real_inner_self_eq_norm_sq,
    norm_sub_sq_real, real_inner_comm x' x, real_inner_comm y x', real_inner_comm y x]
  ring

theorem value_quadratic_remainder
    (H : E → ℝ) (μ β c lam m : ℝ) (hμ : 0 < μ) (hβ : 0 < β)
    (hsc : StrongConvexOn (Set.univ : Set E) (μ + c) H)
    (hdiff : Differentiable ℝ H) (Y : E → E)
    (hY : ∀ x z : E, saddleValue H β c lam m x z ≤ saddleValue H β c lam m x (Y x))
    (x x' : E) :
    ‖valueFromMaximizers H β c lam m Y x' - valueFromMaximizers H β c lam m Y x -
      inner ℝ (β • x + lam • Y x) (x' - x)‖ ≤
      (β / 2 + lam ^ 2 / (2 * μ)) * ‖x' - x‖ ^ 2 := by
  obtain ⟨hlo, hup⟩ := value_maximization_gap H μ β c lam m hμ hsc hdiff Y hY x x'
  have hid := saddle_outer_remainder H β c lam m x x' (Y x)
  have hq : 0 ≤ β / 2 * ‖x' - x‖ ^ 2 := by positivity
  have hnonneg : 0 ≤ valueFromMaximizers H β c lam m Y x' -
      valueFromMaximizers H β c lam m Y x -
      inner ℝ (β • x + lam • Y x) (x' - x) := by
    dsimp [valueFromMaximizers] at *
    linarith only [hlo, hid, hq]
  rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
  dsimp [valueFromMaximizers] at *
  nlinarith only [hup, hid]

theorem hasGradientAt_of_quadratic_remainder
    (F : E → ℝ) (v x : E) (C : ℝ)
    (hbound : ∀ z : E, ‖F z - F x - inner ℝ v (z - x)‖ ≤ C * ‖z - x‖ ^ 2) :
    HasGradientAt F v x := by
  rw [hasGradientAt_iff_hasFDerivAt, hasFDerivAt_iff_isLittleO_nhds_zero]
  have hbig : (fun h : E => F (x + h) - F x - (InnerProductSpace.toDual ℝ E v) h)
      =O[nhds 0] (fun h : E => ‖h‖ ^ 2) := by
    apply Asymptotics.IsBigO.of_bound C
    apply Filter.Eventually.of_forall
    intro h
    simpa using hbound (x + h)
  exact hbig.trans_isLittleO (Asymptotics.isLittleO_norm_pow_id (by norm_num : 1 < 2))

theorem value_hasGradientAt_from_actual_maximizers
    (H : E → ℝ) (μ β c lam m : ℝ) (hμ : 0 < μ) (hβ : 0 < β)
    (hsc : StrongConvexOn (Set.univ : Set E) (μ + c) H)
    (hdiff : Differentiable ℝ H) (Y : E → E)
    (hY : ∀ x z : E, saddleValue H β c lam m x z ≤ saddleValue H β c lam m x (Y x))
    (x : E) :
    HasGradientAt (valueFromMaximizers H β c lam m Y) (β • x + lam • Y x) x := by
  exact hasGradientAt_of_quadratic_remainder _ _ _ _
    (value_quadratic_remainder H μ β c lam m hμ hβ hsc hdiff Y hY x)

theorem value_gradient_identity_from_actual_maximizers
    (H : E → ℝ) (μ β c lam m : ℝ) (hμ : 0 < μ) (hβ : 0 < β)
    (hsc : StrongConvexOn (Set.univ : Set E) (μ + c) H)
    (hdiff : Differentiable ℝ H) (Y : E → E)
    (hY : ∀ x z : E, saddleValue H β c lam m x z ≤ saddleValue H β c lam m x (Y x))
    (x : E) :
    gradient (valueFromMaximizers H β c lam m Y) x = β • x + lam • Y x := by
  have hd := value_hasGradientAt_from_actual_maximizers H μ β c lam m hμ hβ hsc hdiff Y hY x
  exact (hd.differentiableAt.hasGradientAt.unique hd)


theorem saddle_upper_quadratic_from_zero
    (H : E → ℝ) (μ β c lam m : ℝ)
    (hsc : StrongConvexOn (Set.univ : Set E) (μ + c) H)
    (hdiff : Differentiable ℝ H) (x y : E) :
    saddleValue H β c lam m x y - saddleValue H β c lam m x 0 ≤
      (|lam| * ‖x‖ + ‖gradient H 0‖) * ‖y‖ - μ / 2 * ‖y‖ ^ 2 := by
  have hs := strongConvex_support H (μ + c) hsc hdiff 0 y
  simp only [sub_zero] at hs
  have h1 := real_inner_le_norm (lam • x) y
  have h2 := real_inner_le_norm (-gradient H 0) y
  simp only [real_inner_smul_left, norm_smul, Real.norm_eq_abs] at h1
  simp only [inner_neg_left, norm_neg] at h2
  dsimp [saddleValue]
  simp only [inner_zero_right, norm_zero, zero_pow (by norm_num : 2 ≠ 0),
    mul_zero, sub_zero]
  nlinarith only [hs, h1, h2]

theorem exists_inner_maximizer_finiteDimensional
    [FiniteDimensional ℝ E]
    (H : E → ℝ) (μ β c lam m : ℝ) (hμ : 0 < μ)
    (hsc : StrongConvexOn (Set.univ : Set E) (μ + c) H)
    (hdiff : Differentiable ℝ H) (x : E) :
    ∃ y : E, ∀ z : E, saddleValue H β c lam m x z ≤ saddleValue H β c lam m x y := by
  let B : ℝ := |lam| * ‖x‖ + ‖gradient H 0‖
  let R : ℝ := (2 * B + 1) / μ
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hR : 0 < R := by dsimp [R]; positivity
  have hzero : (0 : E) ∈ Metric.closedBall 0 R := by
    simp only [Metric.mem_closedBall, dist_self]
    exact le_of_lt hR
  have hHcont : Continuous H := hdiff.continuous
  have hcont : Continuous (fun y : E => saddleValue H β c lam m x y) := by
    dsimp [saddleValue]
    fun_prop
  obtain ⟨y, hy, hmax⟩ :=
    (isCompact_closedBall (0 : E) R).exists_isMaxOn ⟨0, hzero⟩ hcont.continuousOn
  refine ⟨y, ?_⟩
  intro z
  by_cases hz : z ∈ Metric.closedBall 0 R
  · exact hmax hz
  · have hzR : R < ‖z‖ := by
      simpa only [Metric.mem_closedBall, dist_zero_right, not_le] using hz
    have hzpos : 0 < ‖z‖ := lt_trans hR hzR
    have hμz : 2 * B + 1 < ‖z‖ * μ := (div_lt_iff₀ hμ).mp hzR
    have hneg : B * ‖z‖ - μ / 2 * ‖z‖ ^ 2 < 0 := by
      have hcoef : 0 < μ / 2 * ‖z‖ - B := by nlinarith only [hμz]
      have hp := mul_pos hcoef hzpos
      nlinarith only [hp]
    have hub := saddle_upper_quadratic_from_zero H μ β c lam m hsc hdiff x z
    change saddleValue H β c lam m x z - saddleValue H β c lam m x 0 ≤
      B * ‖z‖ - μ / 2 * ‖z‖ ^ 2 at hub
    have h0 : saddleValue H β c lam m x 0 ≤ saddleValue H β c lam m x y := hmax hzero
    linarith only [hub, hneg, h0]

theorem fenchel_transfer_with_actual_maximizers
    (H : E → ℝ) (μ β c lam : ℝ) (z : E) (Y : E → E)
    (hμ : 0 < μ) (hβ : 0 < β) (hc : 0 < c)
    (hrel : lam ^ 2 = β * c)
    (hsc : StrongConvexOn (Set.univ : Set E) (μ + c) H)
    (hdiff : Differentiable ℝ H) (hmin : ∀ w : E, H z ≤ H w)
    (hY : ∀ x w : E, saddleValue H β c lam (H z) x w ≤
      saddleValue H β c lam (H z) x (Y x)) :
    (∀ x : E, gradient (valueFromMaximizers H β c lam (H z) Y) x =
      lam • (Y x - (-β / lam) • x)) ∧
    (∀ x : E, gradient H (Y x) = c • (Y x - (-β / lam) • x)) ∧
    (∀ x : E, lam / (1 + c / (μ + c)) * ‖(-β / lam) • x - z‖ ≤
      ‖gradient (valueFromMaximizers H β c lam (H z) Y) x‖) ∧
    StrongConvexOn (Set.univ : Set E) β (valueFromMaximizers H β c lam (H z) Y) ∧
    valueFromMaximizers H β c lam (H z) Y ((-lam / β) • z) = 0 ∧
    (∀ x : E, valueFromMaximizers H β c lam (H z) Y ((-lam / β) • z) ≤
      valueFromMaximizers H β c lam (H z) Y x) := by
  have hlam : lam ≠ 0 := by
    intro hzero
    rw [hzero] at hrel
    nlinarith [mul_pos hβ hc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    rw [value_gradient_identity_from_actual_maximizers H μ β c lam (H z) hμ hβ hsc hdiff Y hY x]
    exact fenchel_candidate_identity β lam hlam x (Y x)
  · intro x
    exact fenchel_first_order_identity H β c lam (H z) x (Y x) hβ hc hrel hdiff (hY x)
  · intro x
    rw [value_gradient_identity_from_actual_maximizers H μ β c lam (H z) hμ hβ hsc hdiff Y hY x]
    exact fenchel_stationarity_distance_core H μ β c lam (H z) x (Y x) z hμ hβ hc hrel hsc hdiff hmin (hY x)
  · exact value_strongConvex_from_actual_maximizers H β c lam (H z) Y hY
  · exact (value_minimum_zero_from_actual_maximizers H μ β c lam z Y hμ hβ hrel hsc hdiff hmin hY).2.1
  · exact (value_minimum_zero_from_actual_maximizers H μ β c lam z Y hμ hβ hrel hsc hdiff hmin hY).2.2

theorem fenchel_transfer_finiteDimensional_smooth
    [FiniteDimensional ℝ E]
    (H : E → ℝ) (μ β c lam : ℝ) (z : E)
    (hμ : 0 < μ) (hβ : 0 < β) (hc : 0 < c)
    (hrel : lam ^ 2 = β * c)
    (hsc : StrongConvexOn (Set.univ : Set E) (μ + c) H)
    (hdiff : Differentiable ℝ H) (hmin : ∀ w : E, H z ≤ H w) :
    ∃ Y : E → E,
      (∀ x w : E, saddleValue H β c lam (H z) x w ≤
        saddleValue H β c lam (H z) x (Y x)) ∧
      (∀ x : E, gradient (valueFromMaximizers H β c lam (H z) Y) x =
        lam • (Y x - (-β / lam) • x)) ∧
      (∀ x : E, gradient H (Y x) = c • (Y x - (-β / lam) • x)) ∧
      (∀ x : E, lam / (1 + c / (μ + c)) * ‖(-β / lam) • x - z‖ ≤
        ‖gradient (valueFromMaximizers H β c lam (H z) Y) x‖) ∧
      StrongConvexOn (Set.univ : Set E) β (valueFromMaximizers H β c lam (H z) Y) ∧
      valueFromMaximizers H β c lam (H z) Y ((-lam / β) • z) = 0 ∧
      (∀ x : E, valueFromMaximizers H β c lam (H z) Y ((-lam / β) • z) ≤
        valueFromMaximizers H β c lam (H z) Y x) := by
  classical
  let Y : E → E := fun x => Classical.choose
    (exists_inner_maximizer_finiteDimensional H μ β c lam (H z) hμ hsc hdiff x)
  have hY : ∀ x w : E, saddleValue H β c lam (H z) x w ≤
      saddleValue H β c lam (H z) x (Y x) := by
    intro x
    exact Classical.choose_spec
      (exists_inner_maximizer_finiteDimensional H μ β c lam (H z) hμ hsc hdiff x)
  exact ⟨Y, hY, fenchel_transfer_with_actual_maximizers H μ β c lam z Y hμ hβ hc hrel hsc hdiff hmin hY⟩


theorem value_independent_of_maximizer_selection
    (H : E → ℝ) (β c lam m : ℝ) (Y Z : E → E)
    (hY : ∀ x w : E, saddleValue H β c lam m x w ≤ saddleValue H β c lam m x (Y x))
    (hZ : ∀ x w : E, saddleValue H β c lam m x w ≤ saddleValue H β c lam m x (Z x)) :
    valueFromMaximizers H β c lam m Y = valueFromMaximizers H β c lam m Z := by
  funext x
  apply le_antisymm
  · exact hZ x (Y x)
  · exact hY x (Z x)

theorem unique_inner_maximizer
    (H : E → ℝ) (μ β c lam m : ℝ) (hμ : 0 < μ)
    (hsc : StrongConvexOn (Set.univ : Set E) (μ + c) H)
    (hdiff : Differentiable ℝ H) (x y z : E)
    (hy : ∀ w : E, saddleValue H β c lam m x w ≤ saddleValue H β c lam m x y)
    (hz : ∀ w : E, saddleValue H β c lam m x w ≤ saddleValue H β c lam m x z) :
    y = z := by
  have hgap := saddle_inner_quadratic_gap H μ β c lam m x y hsc hdiff hy z
  have hrev := hz y
  have hsq : ‖z - y‖ ^ 2 = 0 := by
    have hn := sq_nonneg ‖z - y‖
    nlinarith only [hgap, hrev, hn, hμ]
  have hn : ‖z - y‖ = 0 := by nlinarith only [hsq, norm_nonneg (z - y)]
  exact (sub_eq_zero.mp (norm_eq_zero.mp hn)).symm

end PacketCore


/- Actual physical packet: checked analytic class -> true finite-
   dimensional minimizer existence -> exact coordinate reduction/bulk.
   No minimizer, scalar flux, coordinate form or bulk bound is an input. -/

open scoped BigOperators

namespace OriginalPhysicalPacketExistence

open FangqingAmplifier FangqingPacketLeakage FangqingPathEdgeRegularity
  FangqingUnlocalizedPacketRegularity FangqingPrivatePacketAnalytic
  OriginalPacketOrientationNormalization OriginalScalarPacketMinimizer OriginalPhysicalPacketMinimizer

noncomputable section

universe u

variable {A B W : Type u}
  [NormedAddCommGroup A] [InnerProductSpace ℝ A] [FiniteDimensional ℝ A]
  [NormedAddCommGroup B] [InnerProductSpace ℝ B] [FiniteDimensional ℝ B]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]

theorem rawPacket_eq_actual_linearPacket
    (P : FlatCubic.Profile) (C : A ≃ₗᵢ[ℝ] B) (h : A)
    (n : ℕ) (tail : Fin (n + 2) → W) (delta omega q nu scale seed : ℝ) :
    rawPacket C h n tail (FlatCubic.edge P delta omega) q nu scale seed =
      linearPacket (QPhysical q nu C)
        (pathEdge P delta omega (n + 2) (physicalFrame C h n tail)) scale seed (mkPhysical h 0 0) := by
  funext Z
  rw [rawPacket_literal]
  have hi : inner ℝ (mkPhysical h (0 : B) (0 : W)) Z = inner ℝ h Z.fst.fst := by
    change (inner ℝ h Z.fst.fst + inner ℝ (0 : B) Z.fst.snd) + inner ℝ (0 : W) Z.snd = _
    simp only [inner_zero_left, add_zero]
  unfold linearPacket packet pathEdge
  simp only [ContinuousLinearMap.smul_apply, innerSL_apply_apply, smul_eq_mul, hi]
  rfl

theorem actual_raw_packet_contDiff_strongConvex
    (P : FlatCubic.Profile) (C : A ≃ₗᵢ[ℝ] B) (h : A) (hh : ‖h‖ = 1)
    (n : ℕ) (tail : Fin (n + 2) → W) (ht : Orthonormal ℝ tail)
    (delta omega q nu scale seed : ℝ)
    (hd : 0 < delta) (hdw : delta ≤ omega) (hq : 0 ≤ q) (hnu : 0 ≤ nu) (hscale : 0 ≤ scale) :
    ContDiff ℝ 2 (rawPacket C h n tail (FlatCubic.edge P delta omega) q nu scale seed) ∧
      StrongConvexOn (Set.univ : Set (PhysicalSpace A B W)) nu
        (rawPacket C h n tail (FlatCubic.edge P delta omega) q nu scale seed) := by
  obtain ⟨Ce, hCe⟩ := actual_private_packet_regularity.{u} P
  have he := hCe A B W q nu scale seed delta omega C (n + 2) (physicalFrame C h n tail)
    (mkPhysical h 0 0) hq hnu hscale hd hdw (physicalFrame_orthonormal C h hh n tail ht)
  rw [← rawPacket_eq_actual_linearPacket] at he
  exact ⟨he.1, he.2.1⟩

theorem actual_physical_minimizer_exists_with_bulk
    (P : FlatCubic.Profile) (C : A ≃ₗᵢ[ℝ] B) (h : A) (hh : ‖h‖ = 1)
    (n : ℕ) (tail : Fin (n + 2) → W) (ht : Orthonormal ℝ tail)
    (delta omega q Cm Cw scale lam : ℝ)
    (hd : 0 < delta) (hdw : delta ≤ omega) (hq : 1 ≤ q)
    (hCm : 0 ≤ Cm) (hCw : 4 * (Cm + 2) ≤ Cw) (hscale : 0 < scale) (hlam : 0 < lam)
    (homega : omega = Cw * lam * q ^ 2) (hn : ((n + 2 : ℕ) : ℝ) ≤ Cm * q) :
    ∃ Z : PhysicalSpace A B W, ∃ alpha : ℝ, ∃ z : Fin (n + 3) → ℝ,
      (∀ Y, rawPacket C h n tail (FlatCubic.edge P delta omega) q (scale * lam) scale
          (scale * (2 * omega ^ 2 / Real.sqrt q)) Z ≤
        rawPacket C h n tail (FlatCubic.edge P delta omega) q (scale * lam) scale
          (scale * (2 * omega ^ 2 / Real.sqrt q)) Y) ∧
      Z = coordinatePoint C h n tail alpha z ∧
      alpha = alphaStar q lam (2 * omega ^ 2 / Real.sqrt q) z ∧
      (∀ i, 0 ≤ z i) ∧ (∀ k : Fin (n + 2), 0 ≤ z k.castSucc - z k.succ ∧ z k.castSucc - z k.succ ≤ omega) ∧
      ∀ j : Fin (n + 3), (j.val : ℝ) ≤ q →
        3 * q * omega ≤ inner ℝ (physicalFrame C h n tail j) Z := by
  let F := rawPacket C h n tail (FlatCubic.edge P delta omega) q (scale * lam) scale
    (scale * (2 * omega ^ 2 / Real.sqrt q))
  have hnu : 0 < scale * lam := mul_pos hscale hlam
  obtain ⟨hC2, hsc⟩ := actual_raw_packet_contDiff_strongConvex P C h hh n tail ht delta omega q
    (scale * lam) scale (scale * (2 * omega ^ 2 / Real.sqrt q)) hd hdw (by linarith) hnu.le hscale.le
  obtain ⟨Z, hZ⟩ := PacketCore.exists_inner_maximizer_finiteDimensional F (scale * lam) 0 0 0 0
    hnu (by simpa only [add_zero] using hsc) (hC2.differentiable (by norm_num)) 0
  have hm : ∀ Y, F Z ≤ F Y := by
    intro Y
    simpa [PacketCore.saddleValue] using hZ Y
  obtain ⟨alpha, z, hcoord, ha, hz, hstep, hbulk⟩ := actual_physical_minimizer_bulk_coordinates P C h hh n tail ht
    delta omega q Cm Cw scale lam hd hdw hq hCm hCw hscale hlam homega hn
    (hsc.strictConvexOn hnu) Z hm
  exact ⟨Z, alpha, z, hm, hcoord, ha, hz, hstep, hbulk⟩

end
end OriginalPhysicalPacketExistence


/- Quantitative size and value-gap bounds for the actual packet
   minimizer, following the checked alpha/flux reduction. -/

open scoped BigOperators

namespace OriginalPacketDistanceGapBounds

open FangqingAmplifier FangqingPacketLeakage OriginalPacketOrientationNormalization
  OriginalScalarPacketMinimizer OriginalPhysicalPacketMinimizer OriginalPhysicalPacketExistence

noncomputable section

def distanceScale (q omega : ℝ) : ℝ := q * Real.sqrt q * omega

theorem distanceScale_sq (q omega : ℝ) (hq : 0 ≤ q) :
    (distanceScale q omega) ^ 2 = q ^ 3 * omega ^ 2 := by
  unfold distanceScale
  rw [mul_pow, mul_pow, Real.sq_sqrt hq]
  ring

theorem actual_scalar_minimizer_size_bounds
    (P : FlatCubic.Profile) (delta omega q Cm Cw lam alpha : ℝ)
    (hd : 0 < delta) (hdw : delta ≤ omega) (hq : 1 ≤ q)
    (hCm : 0 ≤ Cm) (hCw : 4 * (Cm + 2) ≤ Cw) (hlam : 0 < lam)
    (homega : omega = Cw * lam * q ^ 2)
    (n : ℕ) (hn : (n : ℝ) ≤ Cm * q) (z : Fin (n + 1) → ℝ)
    (hmin : ∀ a w, scalarObjective (FlatCubic.edge P delta omega) n q lam
      (2 * omega ^ 2 / Real.sqrt q) alpha z ≤
      scalarObjective (FlatCubic.edge P delta omega) n q lam (2 * omega ^ 2 / Real.sqrt q) a w) :
    (∀ j, 0 ≤ z j ∧ z j ≤ 2 * Cw * q * omega) ∧
    0 ≤ alpha ∧ alpha ≤ 2 * Cw * distanceScale q omega ∧
      (∑ j : Fin (n + 1), (z j) ^ 2) ≤
        4 * Cw ^ 2 * (Cm + 1) * (distanceScale q omega) ^ 2 := by
  have hqpos : 0 < q := by linarith
  have hsqrt : 0 < Real.sqrt q := Real.sqrt_pos.mpr hqpos
  have hwpos : 0 < omega := hd.trans_le hdw
  have hCwpos : 0 < Cw := by linarith
  have hDpos : 0 < distanceScale q omega := by unfold distanceScale; positivity
  obtain ⟨ha, hred⟩ := actual_scalar_minimizer_alpha_and_reduction
    (FlatCubic.edge P delta omega) n q lam (2 * omega ^ 2 / Real.sqrt q) alpha hqpos.le hlam z hmin
  have hGamma : (2 * omega ^ 2 / Real.sqrt q) * Real.sqrt q / 2 = omega ^ 2 := by
    field_simp [hsqrt.ne']
  rw [hGamma] at hred
  have hS : 0 < lam * (q + 2) / 2 := by positivity
  obtain ⟨hz, _, _⟩ := actual_flat_packet_minimizer_flux P delta omega hd hdw n
    (lam * (q + 2) / 2) lam (omega ^ 2) hS hlam (sq_nonneg omega) z hred
  obtain ⟨_, hz0, hcoords⟩ := actual_flat_packet_coordinate_bounds P delta omega hd hdw n
    (lam * (q + 2) / 2) lam hS hlam z hred
  have hupper0 : z 0 ≤ 2 * Cw * q * omega := by
    have hm : omega ^ 2 = Cw * lam * q ^ 2 * omega := by
      calc
        _ = omega * omega := by ring
        _ = _ := congrArg (fun x : ℝ => x * omega) homega
    have hquad : omega ^ 2 / (lam * (q + 2) / 2) ≤ 2 * Cw * q * omega := by
      apply (div_le_iff₀ hS).mpr
      have hp : 0 ≤ Cw * lam * q * omega := by positivity
      nlinarith only [hm, hp]
    exact hz0.trans hquad
  have hall : ∀ j, 0 ≤ z j ∧ z j ≤ 2 * Cw * q * omega :=
    fun j => ⟨hz j, (hcoords j).1.trans hupper0⟩
  have hseed : (2 * omega ^ 2 / Real.sqrt q) / lam / 2 = Cw * distanceScale q omega := by
    unfold distanceScale
    field_simp [hsqrt.ne', hlam.ne']
    rw [Real.sq_sqrt hqpos.le]
    nlinarith only [homega]
  have halpha : alpha = Real.sqrt q / 2 * z 0 + Cw * distanceScale q omega := by
    rw [ha]
    unfold alphaStar
    linarith only [hseed]
  have hapos : 0 ≤ alpha := by
    rw [halpha]
    exact add_nonneg (mul_nonneg (by positivity) (hz 0)) (mul_nonneg hCwpos.le hDpos.le)
  have haupper : alpha ≤ 2 * Cw * distanceScale q omega := by
    have hh := mul_le_mul_of_nonneg_left hupper0 (by positivity : 0 ≤ Real.sqrt q / 2)
    rw [halpha]
    unfold distanceScale at *
    nlinarith only [hh]
  have hcount : ((n + 1 : ℕ) : ℝ) ≤ (Cm + 1) * q := by
    push_cast
    nlinarith only [hn, hq]
  have hsum : (∑ j : Fin (n + 1), (z j) ^ 2) ≤
      ((n + 1 : ℕ) : ℝ) * (2 * Cw * q * omega) ^ 2 := by
    have hh := Finset.sum_le_sum (s := Finset.univ) (fun (j : Fin (n + 1)) _ =>
      sq_le_sq₀ (hall j).1 (by positivity : 0 ≤ 2 * Cw * q * omega) |>.mpr (hall j).2)
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using hh
  refine ⟨hall, hapos, haupper, ?_⟩
  calc
    _ ≤ ((n + 1 : ℕ) : ℝ) * (2 * Cw * q * omega) ^ 2 := hsum
    _ ≤ ((Cm + 1) * q) * (2 * Cw * q * omega) ^ 2 :=
      mul_le_mul_of_nonneg_right hcount (sq_nonneg _)
    _ = _ := by rw [distanceScale_sq q omega hqpos.le]; ring

variable {A B W : Type*}
  [NormedAddCommGroup A] [InnerProductSpace ℝ A] [FiniteDimensional ℝ A]
  [NormedAddCommGroup B] [InnerProductSpace ℝ B] [FiniteDimensional ℝ B]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]

theorem coordinatePoint_norm_sq
    (C : A ≃ₗᵢ[ℝ] B) (h : A) (hh : ‖h‖ = 1)
    (n : ℕ) (tail : Fin (n + 2) → W) (ht : Orthonormal ℝ tail)
    (alpha : ℝ) (z : Fin (n + 3) → ℝ) :
    ‖coordinatePoint C h n tail alpha z‖ ^ 2 = alpha ^ 2 + ∑ j : Fin (n + 3), (z j) ^ 2 := by
  have he (Z : PhysicalSpace A B W) : ‖Z‖ ^ 2 = ‖Z.fst.fst‖ ^ 2 + ‖Z.fst.snd‖ ^ 2 + ‖Z.snd‖ ^ 2 := by
    simp [WithLp.prod_norm_sq_eq_of_L2]
  rw [he]
  change ‖alpha • h‖ ^ 2 + ‖z 0 • C h‖ ^ 2 + ‖∑ j : Fin (n + 2), z j.succ • tail j‖ ^ 2 = _
  have hsum := Fin.sum_univ_succ (fun j : Fin (n + 3) => (z j) ^ 2)
  rw [orthonormal_tail_sum_norm_sq tail ht, hsum]
  simp only [norm_smul, Real.norm_eq_abs, C.norm_map, hh, mul_one, sq_abs]
  ring

theorem actual_coordinate_minimizer_norm_bound
    (P : FlatCubic.Profile) (C : A ≃ₗᵢ[ℝ] B) (h : A) (hh : ‖h‖ = 1)
    (n : ℕ) (tail : Fin (n + 2) → W) (ht : Orthonormal ℝ tail)
    (delta omega q Cm Cw lam alpha : ℝ)
    (hd : 0 < delta) (hdw : delta ≤ omega) (hq : 1 ≤ q)
    (hCm : 0 ≤ Cm) (hCw : 4 * (Cm + 2) ≤ Cw) (hlam : 0 < lam)
    (homega : omega = Cw * lam * q ^ 2) (hn : ((n + 2 : ℕ) : ℝ) ≤ Cm * q)
    (z : Fin (n + 3) → ℝ)
    (hmin : ∀ a w, scalarObjective (FlatCubic.edge P delta omega) (n + 2) q lam
      (2 * omega ^ 2 / Real.sqrt q) alpha z ≤
      scalarObjective (FlatCubic.edge P delta omega) (n + 2) q lam
        (2 * omega ^ 2 / Real.sqrt q) a w) :
    ‖coordinatePoint C h n tail alpha z‖ ≤ 2 * Cw * (Cm + 2) * distanceScale q omega := by
  obtain ⟨hz, ha0, hau, hsum⟩ := actual_scalar_minimizer_size_bounds P delta omega q Cm Cw lam alpha
    hd hdw hq hCm hCw hlam homega (n + 2) hn z hmin
  have hCw0 : 0 ≤ Cw := by linarith
  have hq0 : 0 ≤ q := by linarith
  have hw0 : 0 ≤ omega := (hd.trans_le hdw).le
  have hD0 : 0 ≤ distanceScale q omega := by unfold distanceScale; positivity
  have halphasq : alpha ^ 2 ≤ (2 * Cw * distanceScale q omega) ^ 2 :=
    (sq_le_sq₀ ha0 (by positivity)).mpr hau
  have hnorm : ‖coordinatePoint C h n tail alpha z‖ ^ 2 ≤
      4 * Cw ^ 2 * (Cm + 2) * (distanceScale q omega) ^ 2 := by
    rw [coordinatePoint_norm_sq C h hh n tail ht]
    nlinarith only [halphasq, hsum]
  have hscalar : Cm + 2 ≤ (Cm + 2) ^ 2 := by nlinarith only [hCm, sq_nonneg Cm]
  have hscale := mul_le_mul_of_nonneg_left hscalar
    (by positivity : 0 ≤ 4 * Cw ^ 2 * (distanceScale q omega) ^ 2)
  have hbound0 : 0 ≤ 2 * Cw * (Cm + 2) * distanceScale q omega := by positivity
  nlinarith only [hnorm, hscale, norm_nonneg (coordinatePoint C h n tail alpha z), hbound0]

theorem actual_edge_nonnegative
    (P : FlatCubic.Profile) (delta omega : ℝ) (hd : 0 < delta) (hdw : delta ≤ omega) (t : ℝ) :
    0 ≤ FlatCubic.edge P delta omega t := by
  have hh := actual_edge_monotone_in_abs P delta omega hd hdw 0 t (by simpa using abs_nonneg t)
  rw [FlatCubic.edge_flat_value P delta omega 0 hd hdw (by simpa using (half_pos hd).le)] at hh
  exact hh

theorem actual_raw_packet_gap_le_seed
    (P : FlatCubic.Profile) (C : A ≃ₗᵢ[ℝ] B) (h : A) (hh : ‖h‖ = 1)
    (n : ℕ) (tail : Fin (n + 2) → W)
    (delta omega q nu scale seed alpha : ℝ) (z : Fin (n + 3) → ℝ)
    (hd : 0 < delta) (hdw : delta ≤ omega) (hq : 0 ≤ q) (hnu : 0 ≤ nu) (hscale : 0 ≤ scale) :
    rawPacket C h n tail (FlatCubic.edge P delta omega) q nu scale seed 0 -
      rawPacket C h n tail (FlatCubic.edge P delta omega) q nu scale seed
        (coordinatePoint C h n tail alpha z) ≤ seed * alpha := by
  let Z := coordinatePoint C h n tail alpha z
  have hg0 : FlatCubic.edge P delta omega 0 = 0 :=
    FlatCubic.edge_flat_value P delta omega 0 hd hdw (by simpa using (half_pos hd).le)
  have h0 : rawPacket C h n tail (FlatCubic.edge P delta omega) q nu scale seed 0 = 0 := by
    rw [rawPacket_literal]
    simp [QPhysical, edgeSum, hg0]
  have hQ : 0 ≤ QPhysical q nu C Z := by
    have hr := (physical_rayleigh_bounds q nu hq hnu C Z).1
    have hi : 0 ≤ inner ℝ (HPhysical q nu C Z) Z := (mul_nonneg hnu (sq_nonneg _)).trans hr
    rw [QPhysical_eq_half_inner]
    exact mul_nonneg (by norm_num) hi
  have he : 0 ≤ scale * edgeSum (FlatCubic.edge P delta omega)
      (pathDirection n (physicalFrame C h n tail)) Z := by
    apply mul_nonneg hscale
    exact Finset.sum_nonneg (fun i _ => actual_edge_nonnegative P delta omega hd hdw _)
  have hhandle : inner ℝ h Z.fst.fst = alpha := by
    change inner ℝ h (alpha • h) = alpha
    rw [inner_smul_right, real_inner_self_eq_norm_sq, hh]
    ring
  rw [h0, rawPacket_literal]
  change 0 - (QPhysical q nu C Z + scale * edgeSum (FlatCubic.edge P delta omega)
      (pathDirection n (physicalFrame C h n tail)) Z - seed * inner ℝ h Z.fst.fst) ≤ seed * alpha
  rw [hhandle]
  linarith only [hQ, he]

theorem actual_seed_ratio
    (q omega Cw lam scale : ℝ) (hq : 0 < q) (homega : omega = Cw * lam * q ^ 2) :
    scale * (2 * omega ^ 2 / Real.sqrt q) =
      2 * Cw * (scale * lam) * distanceScale q omega := by
  unfold distanceScale
  field_simp [(Real.sqrt_pos.mpr hq).ne']
  rw [Real.sq_sqrt hq.le]
  have hm := congrArg (fun x : ℝ => 2 * scale * x * omega) homega
  nlinarith only [hm]

universe u

theorem actual_physical_minimizer_norm_gap_bulk
    {A B W : Type u}
    [NormedAddCommGroup A] [InnerProductSpace ℝ A] [FiniteDimensional ℝ A]
    [NormedAddCommGroup B] [InnerProductSpace ℝ B] [FiniteDimensional ℝ B]
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
    (P : FlatCubic.Profile) (C : A ≃ₗᵢ[ℝ] B) (h : A) (hh : ‖h‖ = 1)
    (n : ℕ) (tail : Fin (n + 2) → W) (ht : Orthonormal ℝ tail)
    (delta omega q Cm Cw scale lam : ℝ)
    (hd : 0 < delta) (hdw : delta ≤ omega) (hq : 1 ≤ q)
    (hCm : 0 ≤ Cm) (hCw : 4 * (Cm + 2) ≤ Cw) (hscale : 0 < scale) (hlam : 0 < lam)
    (homega : omega = Cw * lam * q ^ 2) (hn : ((n + 2 : ℕ) : ℝ) ≤ Cm * q) :
    ∃ Z : PhysicalSpace A B W,
      (∀ Y, rawPacket C h n tail (FlatCubic.edge P delta omega) q (scale * lam) scale
          (scale * (2 * omega ^ 2 / Real.sqrt q)) Z ≤
        rawPacket C h n tail (FlatCubic.edge P delta omega) q (scale * lam) scale
          (scale * (2 * omega ^ 2 / Real.sqrt q)) Y) ∧
      (∀ Y, (∀ X, rawPacket C h n tail (FlatCubic.edge P delta omega) q (scale * lam) scale
          (scale * (2 * omega ^ 2 / Real.sqrt q)) Y ≤
        rawPacket C h n tail (FlatCubic.edge P delta omega) q (scale * lam) scale
          (scale * (2 * omega ^ 2 / Real.sqrt q)) X) → Y = Z) ∧
      ‖Z‖ ≤ 2 * Cw * (Cm + 2) * distanceScale q omega ∧
      rawPacket C h n tail (FlatCubic.edge P delta omega) q (scale * lam) scale
          (scale * (2 * omega ^ 2 / Real.sqrt q)) 0 -
        rawPacket C h n tail (FlatCubic.edge P delta omega) q (scale * lam) scale
          (scale * (2 * omega ^ 2 / Real.sqrt q)) Z ≤
        4 * Cw ^ 2 * (scale * lam) * (distanceScale q omega) ^ 2 ∧
      ∀ j : Fin (n + 3), (j.val : ℝ) ≤ q →
        3 * q * omega ≤ inner ℝ (physicalFrame C h n tail j) Z := by
  have hqpos : 0 < q := by linarith
  have hCw0 : 0 ≤ Cw := by linarith
  have hwpos : 0 < omega := hd.trans_le hdw
  have hD0 : 0 ≤ distanceScale q omega := by unfold distanceScale; positivity
  obtain ⟨Z, alpha, z, hm, hcoord, ha, hz, hsteps, hbulk⟩ :=
    actual_physical_minimizer_exists_with_bulk P C h hh n tail ht delta omega q Cm Cw scale lam
      hd hdw hq hCm hCw hscale hlam homega hn
  have hscalar : ∀ a w, scalarObjective (FlatCubic.edge P delta omega) (n + 2) q lam
      (2 * omega ^ 2 / Real.sqrt q) alpha z ≤
      scalarObjective (FlatCubic.edge P delta omega) (n + 2) q lam
        (2 * omega ^ 2 / Real.sqrt q) a w := by
    intro a w
    have hv := hm (coordinatePoint C h n tail a w)
    rw [hcoord, actual_physical_scalar_value_identity C h hh n tail ht,
      actual_physical_scalar_value_identity C h hh n tail ht] at hv
    by_contra hc
    exact (not_lt_of_ge hv) (mul_lt_mul_of_pos_left (lt_of_not_ge hc) hscale)
  have hnorm : ‖Z‖ ≤ 2 * Cw * (Cm + 2) * distanceScale q omega := by
    rw [hcoord]
    exact actual_coordinate_minimizer_norm_bound P C h hh n tail ht delta omega q Cm Cw lam alpha
      hd hdw hq hCm hCw hlam homega hn z hscalar
  have hgap := actual_raw_packet_gap_le_seed P C h hh n tail delta omega q (scale * lam) scale
    (scale * (2 * omega ^ 2 / Real.sqrt q)) alpha z hd hdw hqpos.le (mul_pos hscale hlam).le hscale.le
  rw [← hcoord] at hgap
  have hau := (actual_scalar_minimizer_size_bounds P delta omega q Cm Cw lam alpha hd hdw hq
    hCm hCw hlam homega (n + 2) hn z hscalar).2.2.1
  have hseed0 : 0 ≤ scale * (2 * omega ^ 2 / Real.sqrt q) := by positivity
  have hgapfinal := hgap.trans (mul_le_mul_of_nonneg_left hau hseed0)
  have hclass := actual_raw_packet_contDiff_strongConvex P C h hh n tail ht delta omega q
    (scale * lam) scale (scale * (2 * omega ^ 2 / Real.sqrt q)) hd hdw hqpos.le
    (mul_pos hscale hlam).le hscale.le
  refine ⟨Z, hm, ?_, hnorm, ?_, hbulk⟩
  · intro Y hY
    exact (hclass.2.strictConvexOn (mul_pos hscale hlam)).eq_of_isMinOn
      (fun X _ => hY X) (fun X _ => hm X) (Set.mem_univ _) (Set.mem_univ _)
  · calc
      _ ≤ scale * (2 * omega ^ 2 / Real.sqrt q) * (2 * Cw * distanceScale q omega) := hgapfinal
      _ = _ := by rw [actual_seed_ratio q omega Cw lam scale hqpos homega]; ring

end
end OriginalPacketDistanceGapBounds


open scoped ContDiff NNReal

namespace FangqingC2GrowthBounds

open FangqingJetToRegularity

noncomputable section

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]

theorem growth_from_actual_second_jet (g : X → ℝ) (hc : ContDiff ℝ 2 g) (M : ℝ≥0)
    (h2 : ∀ z, ‖iteratedFDeriv ℝ 2 g z‖ ≤ M)
    (hzero : g 0 = 0) (hfirst : fderiv ℝ g 0 = 0) :
    (∀ z, ‖fderiv ℝ g z‖ ≤ (M : ℝ) * ‖z‖) ∧
    (∀ z, |g z| ≤ (M : ℝ) * ‖z‖ ^ 2) ∧
    (∀ R : ℝ, 0 ≤ R → ∀ x y : X, ‖x‖ ≤ R → ‖y‖ ≤ R →
      |g x - g y| ≤ (M : ℝ) * R * ‖x - y‖) := by
  have hl := derivative_lipschitz_from_second_jet g hc M h2
  have hD : ∀ z, ‖fderiv ℝ g z‖ ≤ (M : ℝ) * ‖z‖ := by
    intro z
    simpa only [hfirst, sub_zero] using hl.norm_sub_le z 0
  have hlocal : ∀ R : ℝ, 0 ≤ R → ∀ x y : X, ‖x‖ ≤ R → ‖y‖ ≤ R →
      |g x - g y| ≤ (M : ℝ) * R * ‖x - y‖ := by
    intro R hR x y hx hy
    have hh := Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ)
      (s := Metric.closedBall (0 : X) R) (C := (M : ℝ) * R)
      (fun z _ => (hc.differentiable (by norm_num) z))
      (fun z hz => (hD z).trans (mul_le_mul_of_nonneg_left (by simpa using hz) M.coe_nonneg))
      (convex_closedBall (0 : X) R) (by simpa using hy) (by simpa using hx)
    simpa only [Real.norm_eq_abs] using hh
  refine ⟨hD, ?_, hlocal⟩
  intro z
  have hh := hlocal ‖z‖ (norm_nonneg z) z 0 le_rfl (by simpa using norm_nonneg z)
  simpa only [hzero, sub_zero, pow_two, mul_assoc] using hh

end
end FangqingC2GrowthBounds


open scoped ContDiff

namespace FangqingC2ProductHessianBounds

open FangqingC2HessianAlgebra

set_option maxHeartbeats 1200000

noncomputable section

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem first_eval_bound (T : X →L[ℝ] ℝ) (C : ℝ) (hb : ‖T‖ ≤ C) (v : X) :
    |T v| ≤ C * ‖v‖ := by
  exact (T.le_opNorm v).trans (mul_le_mul_of_nonneg_right hb (norm_nonneg v))

theorem second_eval_bound (T : X →L[ℝ] (X →L[ℝ] ℝ)) (C : ℝ) (hb : ‖T‖ ≤ C) (v w : X) :
    |T v w| ≤ C * ‖v‖ * ‖w‖ := by
  have h1 := T.le_opNorm v
  have h2 := (T v).le_opNorm w
  exact h2.trans ((mul_le_mul_of_nonneg_right h1 (norm_nonneg w)).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hb (norm_nonneg v)) (norm_nonneg w)))

theorem first_difference_eval_bound (A B : X →L[ℝ] ℝ) (C : ℝ) (hb : ‖A - B‖ ≤ C) (v : X) :
    |A v - B v| ≤ C * ‖v‖ := by
  simpa only [ContinuousLinearMap.sub_apply] using first_eval_bound (A - B) C hb v

theorem second_difference_eval_bound (A B : X →L[ℝ] (X →L[ℝ] ℝ)) (C : ℝ) (hb : ‖A - B‖ ≤ C) (v w : X) :
    |A v w - B v w| ≤ C * ‖v‖ * ‖w‖ := by
  simpa only [ContinuousLinearMap.sub_apply] using second_eval_bound (A - B) C hb v w

theorem scalar_product_difference_bound (a a' b b' Da A Db B : ℝ)
    (hDa : 0 ≤ Da) (hA : 0 ≤ A) (hDb : 0 ≤ Db) (hB : 0 ≤ B)
    (ha : |a - a'| ≤ Da) (ha' : |a'| ≤ A) (hb : |b| ≤ B) (hb' : |b - b'| ≤ Db) :
    |a * b - a' * b'| ≤ Da * B + A * Db := by
  have heq : a * b - a' * b' = (a - a') * b + a' * (b - b') := by ring
  rw [heq]
  calc
    _ ≤ |(a - a') * b| + |a' * (b - b')| := abs_add_le _ _
    _ = |a - a'| * |b| + |a'| * |b - b'| := by rw [abs_mul, abs_mul]
    _ ≤ _ := add_le_add (mul_le_mul ha hb (abs_nonneg _) hDa)
      (mul_le_mul ha' hb' (abs_nonneg _) hA)

theorem abs_four_difference_bound (a b c d a' b' c' d' A B C D : ℝ)
    (ha : |a - a'| ≤ A) (hb : |b - b'| ≤ B) (hc : |c - c'| ≤ C) (hd : |d - d'| ≤ D) :
    |(a + b + c + d) - (a' + b' + c' + d')| ≤ A + B + C + D := by
  have heq : (a + b + c + d) - (a' + b' + c' + d') =
      (a - a') + (b - b') + (c - c') + (d - d') := by ring
  rw [heq]
  exact (abs_add_le _ _).trans (add_le_add
    ((abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add ha hb)) hc)) hd)

theorem product_hessian_norm_bound (f g : X → ℝ) (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (x : X) (F0 F1 F2 G0 G1 G2 : ℝ)
    (hF0 : 0 ≤ F0) (hF1 : 0 ≤ F1) (hF2 : 0 ≤ F2)
    (hG0 : 0 ≤ G0) (hG1 : 0 ≤ G1) (hG2 : 0 ≤ G2)
    (hfv : |f x| ≤ F0) (hfd : ‖fderiv ℝ f x‖ ≤ F1)
    (hfh : ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ F2)
    (hgv : |g x| ≤ G0) (hgd : ‖fderiv ℝ g x‖ ≤ G1)
    (hgh : ‖fderiv ℝ (fderiv ℝ g) x‖ ≤ G2) :
    ‖fderiv ℝ (fderiv ℝ (fun z => f z * g z)) x‖ ≤ F0 * G2 + 2 * F1 * G1 + F2 * G0 := by
  have hcoef : 0 ≤ F0 * G2 + 2 * F1 * G1 + F2 * G0 := by positivity
  refine (fderiv ℝ (fderiv ℝ (fun z => f z * g z)) x).opNorm_le_bound hcoef ?_
  intro v
  refine ((fderiv ℝ (fderiv ℝ (fun z => f z * g z)) x) v).opNorm_le_bound (by positivity) ?_
  intro w
  rw [hessian_mul f g hf hg]
  simp only [Real.norm_eq_abs]
  have h1 := mul_le_mul hfv (second_eval_bound _ G2 hgh v w) (abs_nonneg _) hF0
  have h2 := mul_le_mul (first_eval_bound _ F1 hfd v) (first_eval_bound _ G1 hgd w)
    (abs_nonneg _) (by positivity : 0 ≤ F1 * ‖v‖)
  have h3 := mul_le_mul (first_eval_bound _ F1 hfd w) (first_eval_bound _ G1 hgd v)
    (abs_nonneg _) (by positivity : 0 ≤ F1 * ‖w‖)
  have h4 := mul_le_mul hgv (second_eval_bound _ F2 hfh v w) (abs_nonneg _) hG0
  have hh := abs_four_difference_bound
    (f x * fderiv ℝ (fderiv ℝ g) x v w)
    (fderiv ℝ f x v * fderiv ℝ g x w)
    (fderiv ℝ f x w * fderiv ℝ g x v)
    (g x * fderiv ℝ (fderiv ℝ f) x v w) 0 0 0 0
    (F0 * (G2 * ‖v‖ * ‖w‖)) (F1 * ‖v‖ * (G1 * ‖w‖))
    (F1 * ‖w‖ * (G1 * ‖v‖)) (G0 * (F2 * ‖v‖ * ‖w‖))
    (by simpa only [sub_zero, abs_mul] using h1)
    (by simpa only [sub_zero, abs_mul] using h2)
    (by simpa only [sub_zero, abs_mul] using h3)
    (by simpa only [sub_zero, abs_mul] using h4)
  simp only [zero_add, sub_zero] at hh
  convert! hh using 1 <;> try ring

/- Local budgets are actual derivatives and derivative differences, not a
   presumed bound for the product.  The nonsmooth third derivative of a C2
   capped edge never appears: its Hessian difference is the last input. -/
theorem product_hessian_difference_bound (f g : X → ℝ) (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (x y : X) (F0 F1 F2 F3 G0 G1 G2 G3 : ℝ)
    (hF0 : 0 ≤ F0) (hF1 : 0 ≤ F1) (hF2 : 0 ≤ F2) (hF3 : 0 ≤ F3)
    (hG0 : 0 ≤ G0) (hG1 : 0 ≤ G1) (hG2 : 0 ≤ G2) (hG3 : 0 ≤ G3)
    (hfv : |f y| ≤ F0) (hfd : ‖fderiv ℝ f y‖ ≤ F1)
    (hfh : ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ F2)
    (hgv : |g y| ≤ G0) (hgd : ‖fderiv ℝ g x‖ ≤ G1)
    (hgh : ‖fderiv ℝ (fderiv ℝ g) x‖ ≤ G2)
    (hfvl : |f x - f y| ≤ F1 * ‖x - y‖)
    (hfdl : ‖fderiv ℝ f x - fderiv ℝ f y‖ ≤ F2 * ‖x - y‖)
    (hfhl : ‖fderiv ℝ (fderiv ℝ f) x - fderiv ℝ (fderiv ℝ f) y‖ ≤ F3 * ‖x - y‖)
    (hgvl : |g x - g y| ≤ G1 * ‖x - y‖)
    (hgdl : ‖fderiv ℝ g x - fderiv ℝ g y‖ ≤ G2 * ‖x - y‖)
    (hghl : ‖fderiv ℝ (fderiv ℝ g) x - fderiv ℝ (fderiv ℝ g) y‖ ≤ G3 * ‖x - y‖) :
    ‖fderiv ℝ (fderiv ℝ (fun z => f z * g z)) x -
      fderiv ℝ (fderiv ℝ (fun z => f z * g z)) y‖ ≤
      (F0 * G3 + 3 * F1 * G2 + 3 * F2 * G1 + F3 * G0) * ‖x - y‖ := by
  have hcoef : 0 ≤ F0 * G3 + 3 * F1 * G2 + 3 * F2 * G1 + F3 * G0 := by positivity
  refine (fderiv ℝ (fderiv ℝ (fun z => f z * g z)) x -
    fderiv ℝ (fderiv ℝ (fun z => f z * g z)) y).opNorm_le_bound
      (mul_nonneg hcoef (norm_nonneg _)) ?_
  intro v
  refine ((fderiv ℝ (fderiv ℝ (fun z => f z * g z)) x -
    fderiv ℝ (fderiv ℝ (fun z => f z * g z)) y) v).opNorm_le_bound (by positivity) ?_
  intro w
  simp only [ContinuousLinearMap.sub_apply]
  rw [hessian_mul f g hf hg, hessian_mul f g hf hg]
  have hterm1 := scalar_product_difference_bound (f x) (f y)
    (fderiv ℝ (fderiv ℝ g) x v w) (fderiv ℝ (fderiv ℝ g) y v w)
    (F1 * ‖x - y‖) F0 (G3 * ‖x - y‖ * ‖v‖ * ‖w‖) (G2 * ‖v‖ * ‖w‖)
    (by positivity) hF0 (by positivity) (by positivity) hfvl hfv
    (second_eval_bound _ G2 hgh v w) (second_difference_eval_bound _ _ _ hghl v w)
  have hterm2 := scalar_product_difference_bound
    (fderiv ℝ f x v) (fderiv ℝ f y v) (fderiv ℝ g x w) (fderiv ℝ g y w)
    (F2 * ‖x - y‖ * ‖v‖) (F1 * ‖v‖) (G2 * ‖x - y‖ * ‖w‖) (G1 * ‖w‖)
    (by positivity) (by positivity) (by positivity) (by positivity)
    (first_difference_eval_bound _ _ _ hfdl v) (first_eval_bound _ F1 hfd v)
    (first_eval_bound _ G1 hgd w) (first_difference_eval_bound _ _ _ hgdl w)
  have hterm3 := scalar_product_difference_bound
    (fderiv ℝ f x w) (fderiv ℝ f y w) (fderiv ℝ g x v) (fderiv ℝ g y v)
    (F2 * ‖x - y‖ * ‖w‖) (F1 * ‖w‖) (G2 * ‖x - y‖ * ‖v‖) (G1 * ‖v‖)
    (by positivity) (by positivity) (by positivity) (by positivity)
    (first_difference_eval_bound _ _ _ hfdl w) (first_eval_bound _ F1 hfd w)
    (first_eval_bound _ G1 hgd v) (first_difference_eval_bound _ _ _ hgdl v)
  have hterm4 := scalar_product_difference_bound (g x) (g y)
    (fderiv ℝ (fderiv ℝ f) x v w) (fderiv ℝ (fderiv ℝ f) y v w)
    (G1 * ‖x - y‖) G0 (F3 * ‖x - y‖ * ‖v‖ * ‖w‖) (F2 * ‖v‖ * ‖w‖)
    (by positivity) hG0 (by positivity) (by positivity) hgvl hgv
    (second_eval_bound _ F2 hfh v w) (second_difference_eval_bound _ _ _ hfhl v w)
  have hh := abs_four_difference_bound _ _ _ _ _ _ _ _ _ _ _ _ hterm1 hterm2 hterm3 hterm4
  simp only [Real.norm_eq_abs]
  convert! hh using 1 <;> try ring

end
end FangqingC2ProductHessianBounds


open scoped ContDiff NNReal Topology

namespace FangqingCutoffProductRegularity

open FangqingJetToRegularity FangqingC2GrowthBounds FangqingC2ProductHessianBounds

set_option maxHeartbeats 1500000

noncomputable section

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]

theorem hessian_zero_outside_support (f g : X → ℝ) (R : ℝ)
    (hzero : ∀ z, R < ‖z‖ → f z = 0) (x : X) (hx : R < ‖x‖) :
    fderiv ℝ (fderiv ℝ (fun z => f z * g z)) x = 0 := by
  have he : (fun z => f z * g z) =ᶠ[𝓝 x] (fun _ => (0 : ℝ)) := by
    have hopen := (isOpen_lt continuous_const continuous_norm).mem_nhds hx
    filter_upwards [hopen] with z hz
    rw [hzero z hz, zero_mul]
  have hfirst : fderiv ℝ (fun z => f z * g z) =ᶠ[𝓝 x] fderiv ℝ (fun _ : X => (0 : ℝ)) := he.fderiv
  have hh : fderiv ℝ (fderiv ℝ (fun z => f z * g z)) x =
      fderiv ℝ (fderiv ℝ (fun _ : X => (0 : ℝ))) x := hfirst.fderiv_eq
  rw [hh]
  have hc : fderiv ℝ (fun _ : X => (0 : ℝ)) = fun _ => 0 :=
    funext (fun z => (hasFDerivAt_const (0 : ℝ) z).fderiv)
  rw [hc]
  exact (hasFDerivAt_const (0 : X →L[ℝ] ℝ) x).fderiv

theorem cutoff_product_regularity (f g : X → ℝ) (hf : ContDiff ℝ 3 f) (hg : ContDiff ℝ 2 g)
    (R K : ℝ) (M rho : ℝ≥0) (hR : 0 < R) (hK : 0 ≤ K)
    (hfj : ∀ j, j ≤ 3 → ∀ z, ‖iteratedFDeriv ℝ j f z‖ ≤ K / R ^ j)
    (hfzero : ∀ z, 2 * R < ‖z‖ → f z = 0)
    (hg2 : ∀ z, ‖iteratedFDeriv ℝ 2 g z‖ ≤ M)
    (hg0 : g 0 = 0) (hgd0 : fderiv ℝ g 0 = 0)
    (hglip : ∀ x y, ‖fderiv ℝ (fderiv ℝ g) x - fderiv ℝ (fderiv ℝ g) y‖ ≤ (rho : ℝ) * ‖x - y‖) :
    ContDiff ℝ 2 (fun z => f z * g z) ∧
    (∀ z, ‖fderiv ℝ (fderiv ℝ (fun z => f z * g z)) z‖ ≤ 16 * K * M) ∧
    (∀ x y, ‖fderiv ℝ (fderiv ℝ (fun z => f z * g z)) x -
      fderiv ℝ (fderiv ℝ (fun z => f z * g z)) y‖ ≤
        (K * rho + 21 * K * M / R) * ‖x - y‖) := by
  have hf2 : ContDiff ℝ 2 f := hf.of_le (by norm_num)
  have hf0 : ∀ z, |f z| ≤ K := by
    intro z
    simpa only [norm_iteratedFDeriv_zero, Real.norm_eq_abs, pow_zero, div_one] using hfj 0 (by norm_num) z
  have hf1 : ∀ z, ‖fderiv ℝ f z‖ ≤ K / R := by
    intro z
    simpa only [norm_iteratedFDeriv_one, pow_one] using hfj 1 (by norm_num) z
  have hf2b : ∀ z, ‖fderiv ℝ (fderiv ℝ f) z‖ ≤ K / R ^ 2 := by
    intro z
    rw [hessian_norm_eq_second_jet]
    exact hfj 2 (by norm_num) z
  let F1 : ℝ≥0 := ⟨K / R, by positivity⟩
  let F2 : ℝ≥0 := ⟨K / R ^ 2, by positivity⟩
  let F3 : ℝ≥0 := ⟨K / R ^ 3, by positivity⟩
  have hfvlip : ∀ x y, |f x - f y| ≤ K / R * ‖x - y‖ := by
    have hl := lipschitzWith_of_nnnorm_fderiv_le (hf2.differentiable (by norm_num))
      (C := F1) (fun z => by exact_mod_cast hf1 z)
    exact fun x y => hl.norm_sub_le x y
  have hfdlip := derivative_lipschitz_from_second_jet f hf2 F2 (hfj 2 (by norm_num))
  have hfhlip := hessian_lipschitz_from_third_jet f hf F3 (hfj 3 (by norm_num))
  have hg2b : ∀ z, ‖fderiv ℝ (fderiv ℝ g) z‖ ≤ M := by
    intro z
    rw [hessian_norm_eq_second_jet]
    exact hg2 z
  have hgdlip := derivative_lipschitz_from_second_jet g hg M hg2
  obtain ⟨hg1, hgv, hgvLip⟩ := growth_from_actual_second_jet g hg M hg2 hg0 hgd0
  have hg1local : ∀ z, ‖z‖ ≤ 3 * R → ‖fderiv ℝ g z‖ ≤ 3 * M * R := by
    intro z hz
    have hh := (hg1 z).trans (mul_le_mul_of_nonneg_left hz M.coe_nonneg)
    convert! hh using 1 <;> try ring
  have hgvlocal : ∀ z, ‖z‖ ≤ 3 * R → |g z| ≤ 9 * M * R ^ 2 := by
    intro z hz
    have hsq := pow_le_pow_left₀ (norm_nonneg z) hz 2
    have hh := (hgv z).trans (mul_le_mul_of_nonneg_left hsq M.coe_nonneg)
    convert! hh using 1 <;> try ring
  have hlocalnorm : ∀ z, ‖z‖ ≤ 3 * R →
      ‖fderiv ℝ (fderiv ℝ (fun z => f z * g z)) z‖ ≤ 16 * K * M := by
    intro z hz
    have hh := product_hessian_norm_bound f g hf2 hg z K (K / R) (K / R ^ 2)
      (9 * M * R ^ 2) (3 * M * R) M hK (by positivity) (by positivity)
      (by positivity) (by positivity) M.coe_nonneg (hf0 z) (hf1 z) (hf2b z)
      (hgvlocal z hz) (hg1local z hz) (hg2b z)
    convert! hh using 1 <;> try field_simp [ne_of_gt hR] <;> try ring
  have hnorm : ∀ z, ‖fderiv ℝ (fderiv ℝ (fun z => f z * g z)) z‖ ≤ 16 * K * M := by
    intro z
    by_cases hz : ‖z‖ ≤ 2 * R
    · exact hlocalnorm z (by linarith only [hz, hR])
    · rw [hessian_zero_outside_support f g (2 * R) hfzero z (lt_of_not_ge hz)]
      have hh : ‖(0 : X →L[ℝ] (X →L[ℝ] ℝ))‖ = 0 := ContinuousLinearMap.opNorm_zero
      rw [hh]
      positivity
  let C := K * rho + 21 * K * M / R
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hlocal : ∀ x y : X, ‖x‖ ≤ 3 * R → ‖y‖ ≤ 3 * R →
      ‖fderiv ℝ (fderiv ℝ (fun z => f z * g z)) x -
        fderiv ℝ (fderiv ℝ (fun z => f z * g z)) y‖ ≤ C * ‖x - y‖ := by
    intro x y hx hy
    have hgvxy := hgvLip (3 * R) (by positivity) x y hx hy
    have hh := product_hessian_difference_bound f g hf2 hg x y
      K (K / R) (K / R ^ 2) (K / R ^ 3) (9 * M * R ^ 2) (3 * M * R) M rho
      hK (by positivity) (by positivity) (by positivity)
      (by positivity) (by positivity) M.coe_nonneg rho.coe_nonneg
      (hf0 y) (hf1 y) (hf2b x) (hgvlocal y hy) (hg1local x hx) (hg2b x)
      (hfvlip x y) (hfdlip.norm_sub_le x y) (hfhlip.norm_sub_le x y)
      (by convert! hgvxy using 1 <;> try ring) (hgdlip.norm_sub_le x y) (hglip x y)
    convert! hh using 1 <;> dsimp [C] <;> try field_simp [ne_of_gt hR] <;> try ring
  have hfar : ∀ x y : X, 3 * R < ‖y‖ →
      ‖fderiv ℝ (fderiv ℝ (fun z => f z * g z)) x -
        fderiv ℝ (fderiv ℝ (fun z => f z * g z)) y‖ ≤ C * ‖x - y‖ := by
    intro x y hy
    rw [hessian_zero_outside_support f g (2 * R) hfzero y (by linarith only [hy, hR]), sub_zero]
    by_cases hx : ‖x‖ ≤ 2 * R
    · have hd : R ≤ ‖x - y‖ := by
        have hh := norm_sub_norm_le y x
        rw [norm_sub_rev y x] at hh
        linarith only [hh, hx, hy]
      have hCR : 16 * K * M ≤ C * R := by
        dsimp [C]
        have heq : (K * rho + 21 * K * M / R) * R = K * rho * R + 21 * K * M := by
          field_simp [ne_of_gt hR]
        rw [heq]
        nlinarith only [mul_nonneg hK M.coe_nonneg, mul_nonneg (mul_nonneg hK rho.coe_nonneg) hR.le]
      exact (hnorm x).trans (hCR.trans (mul_le_mul_of_nonneg_left hd hC))
    · rw [hessian_zero_outside_support f g (2 * R) hfzero x (lt_of_not_ge hx)]
      have hh : ‖(0 : X →L[ℝ] (X →L[ℝ] ℝ))‖ = 0 := ContinuousLinearMap.opNorm_zero
      rw [hh]
      positivity
  refine ⟨hf2.mul hg, hnorm, ?_⟩
  intro x y
  by_cases hy : ‖y‖ ≤ 3 * R
  · by_cases hx : ‖x‖ ≤ 3 * R
    · exact hlocal x y hx hy
    · have hh := hfar y x (lt_of_not_ge hx)
      rw [norm_sub_rev (fderiv ℝ (fderiv ℝ (fun z => f z * g z)) y)
        (fderiv ℝ (fderiv ℝ (fun z => f z * g z)) x)] at hh
      simpa only [norm_sub_rev y x, C] using hh
  · exact hfar x y (lt_of_not_ge hy)

end
end FangqingCutoffProductRegularity


open scoped ContDiff Topology

namespace FangqingRadialCollar

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def primitive (psi : ℝ → ℝ) (t : ℝ) : ℝ := ∫ u in (1 : ℝ)..t, psi u

def collar (psi : ℝ → ℝ) (R : ℝ) (z : E) : ℝ :=
  R ^ 2 / 2 * primitive psi (‖z‖ ^ 2 / R ^ 2)

def radiusJet (R : ℝ) (z : E) : E →L[ℝ] ℝ := (2 / R ^ 2 : ℝ) • innerSL ℝ z

theorem primitive_hasDerivAt (psi : ℝ → ℝ) (hc : Continuous psi) (t : ℝ) :
    HasDerivAt (primitive psi) (psi t) t :=
  intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 1 t)
    hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt

theorem primitive_contDiff_three (psi : ℝ → ℝ) (hc : ContDiff ℝ 2 psi) :
    ContDiff ℝ 3 (primitive psi) := by
  change ContDiff ℝ (2 + 1) (primitive psi)
  rw [contDiff_succ_iff_deriv]
  have heq : deriv (primitive psi) = psi := funext (fun t => (primitive_hasDerivAt psi hc.continuous t).deriv)
  refine ⟨fun t => (primitive_hasDerivAt psi hc.continuous t).differentiableAt, by simp, ?_⟩
  rw [heq]
  exact hc

theorem collar_contDiff_three (psi : ℝ → ℝ) (hc : ContDiff ℝ 2 psi) (R : ℝ) :
    ContDiff ℝ 3 (collar (E := E) psi R) := by
  have hn : ContDiff ℝ 3 (fun z : E => ‖z‖ ^ 2 / R ^ 2) := (contDiff_id.norm_sq ℝ).div_const _
  exact contDiff_const.mul ((primitive_contDiff_three psi hc).comp hn)

theorem radius_hasFDerivAt (R : ℝ) (z : E) :
    HasFDerivAt (fun y : E => ‖y‖ ^ 2 / R ^ 2) (radiusJet R z) z := by
  have hh := (hasStrictFDerivAt_norm_sq z).hasFDerivAt.const_mul ((R ^ 2)⁻¹)
  convert! hh using 1
  · funext y
    simp only [div_eq_mul_inv, mul_comm]
  · ext v
    simp only [radiusJet, ContinuousLinearMap.smul_apply, smul_eq_mul, two_smul,
      ContinuousLinearMap.add_apply, div_eq_mul_inv]
    ring

theorem collar_hasFDerivAt (psi : ℝ → ℝ) (hc : Continuous psi) (R : ℝ) (hR : 0 < R) (z : E) :
    HasFDerivAt (collar psi R) (psi (‖z‖ ^ 2 / R ^ 2) • innerSL ℝ z) z := by
  have hh := ((primitive_hasDerivAt psi hc (‖z‖ ^ 2 / R ^ 2)).comp_hasFDerivAt z
    (radius_hasFDerivAt R z)).const_mul (R ^ 2 / 2)
  convert! hh using 1
  ext v
  simp only [radiusJet, ContinuousLinearMap.smul_apply, smul_eq_mul]
  field_simp [ne_of_gt hR]
  <;> try ring

theorem collar_hessian_apply (psi : ℝ → ℝ) (hc : ContDiff ℝ 2 psi) (R : ℝ) (hR : 0 < R)
    (z v w : E) :
    fderiv ℝ (fderiv ℝ (collar psi R)) z v w =
      psi (‖z‖ ^ 2 / R ^ 2) * inner ℝ v w +
      (2 / R ^ 2) * deriv psi (‖z‖ ^ 2 / R ^ 2) * inner ℝ z v * inner ℝ z w := by
  have heq : fderiv ℝ (collar (E := E) psi R) =
      fun z => psi (‖z‖ ^ 2 / R ^ 2) • innerSL ℝ z :=
    funext (fun z => (collar_hasFDerivAt psi hc.continuous R hR z).fderiv)
  rw [heq]
  have hpsi := ((hc.differentiable (by norm_num) (‖z‖ ^ 2 / R ^ 2)).hasDerivAt).comp_hasFDerivAt z
    (radius_hasFDerivAt R z)
  have hh := hpsi.smul (innerSL ℝ (E := E)).hasFDerivAt
  change HasFDerivAt (fun y : E => psi (‖y‖ ^ 2 / R ^ 2) • innerSL ℝ y) _ z at hh
  rw [hh.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.smul_apply, radiusJet, innerSL_apply_apply, smul_eq_mul, Function.comp_apply]
  change psi (‖z‖ ^ 2 / R ^ 2) * inner ℝ v w +
    (deriv psi (‖z‖ ^ 2 / R ^ 2) * ((2 / R ^ 2) * inner ℝ z v)) * inner ℝ z w = _
  ring

theorem collar_hessian_nonneg (psi : ℝ → ℝ) (hc : ContDiff ℝ 2 psi) (hm : Monotone psi)
    (hpsi : ∀ t, 0 ≤ psi t) (R : ℝ) (hR : 0 < R) (z v : E) :
    0 ≤ fderiv ℝ (fderiv ℝ (collar psi R)) z v v := by
  rw [collar_hessian_apply psi hc R hR, real_inner_self_eq_norm_sq]
  have hd : 0 ≤ deriv psi (‖z‖ ^ 2 / R ^ 2) := hm.deriv_nonneg
  have hprod : 0 ≤ (2 / R ^ 2) * deriv psi (‖z‖ ^ 2 / R ^ 2) * (inner ℝ z v) ^ 2 := by positivity
  have hf := mul_nonneg (hpsi (‖z‖ ^ 2 / R ^ 2)) (sq_nonneg ‖v‖)
  nlinarith only [hprod, hf]

theorem collar_hessian_outer_lower (psi : ℝ → ℝ) (hc : ContDiff ℝ 2 psi) (hm : Monotone psi)
    (B R : ℝ) (hB : 0 ≤ B) (hR : 0 < R) (hpsi : ∀ t, B ^ 2 ≤ t → psi t = 1)
    (z v : E) (hz : B * R ≤ ‖z‖) :
    ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ (collar psi R)) z v v := by
  have harg : B ^ 2 ≤ ‖z‖ ^ 2 / R ^ 2 := by
    apply (le_div_iff₀ (pow_pos hR 2)).mpr
    have hs := pow_le_pow_left₀ (mul_nonneg hB hR.le) hz 2
    simpa only [mul_pow] using hs
  rw [collar_hessian_apply psi hc R hR, hpsi _ harg, one_mul, real_inner_self_eq_norm_sq]
  have hd : 0 ≤ deriv psi (‖z‖ ^ 2 / R ^ 2) := hm.deriv_nonneg
  have hprod : 0 ≤ (2 / R ^ 2) * deriv psi (‖z‖ ^ 2 / R ^ 2) * (inner ℝ z v) ^ 2 := by positivity
  nlinarith only [hprod]

end
end FangqingRadialCollar


open scoped ContDiff Topology BigOperators

namespace FangqingRadialCollarBounds

open FangqingRadialCollar FangqingRadialGateBounds FangqingJetToRegularity

set_option maxHeartbeats 1500000

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def baseCollar (psi : ℝ → ℝ) (z : E) : ℝ := (1 / 2 : ℝ) * primitive psi (‖z‖ ^ 2)

theorem primitive_compact_derivative_bounds (psi : ℝ → ℝ) (hc : ContDiff ℝ 2 psi) (B : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ j, j ≤ 3 → ∀ u ∈ Set.Icc (0 : ℝ) (B ^ 2),
      ‖iteratedFDeriv ℝ j (primitive psi) u‖ ≤ C := by
  classical
  have hpc := primitive_contDiff_three psi hc
  have h_each : ∀ j : Fin 4, ∃ C : ℝ, 0 ≤ C ∧
      ∀ u ∈ Set.Icc (0 : ℝ) (B ^ 2), ‖iteratedFDeriv ℝ j.val (primitive psi) u‖ ≤ C := by
    intro j
    have hj : (j.val : ℕ∞ω) ≤ 3 := by exact_mod_cast (by omega : j.val ≤ 3)
    obtain ⟨C, hC⟩ := (isCompact_Icc : IsCompact (Set.Icc (0 : ℝ) (B ^ 2))).exists_bound_of_continuousOn
      (hpc.continuous_iteratedFDeriv hj).continuousOn
    exact ⟨max C 0, le_max_right _ _, fun u hu => (hC u hu).trans (le_max_left _ _)⟩
  choose Cs hCs using h_each
  refine ⟨∑ j, Cs j, Finset.sum_nonneg (fun j _ => (hCs j).1), ?_⟩
  intro j hj u hu
  let jj : Fin 4 := ⟨j, by omega⟩
  exact ((hCs jj).2 u hu).trans (Finset.single_le_sum (fun k _ => (hCs k).1) (Finset.mem_univ jj))

theorem baseCollar_contDiff (psi : ℝ → ℝ) (hc : ContDiff ℝ 2 psi) :
    ContDiff ℝ 3 (baseCollar (E := E) psi) :=
  contDiff_const.mul ((primitive_contDiff_three psi hc).comp (contDiff_id.norm_sq ℝ))

theorem baseCollar_local_jet_bound (psi : ℝ → ℝ) (hc : ContDiff ℝ 2 psi)
    (B C : ℝ) (hB : 1 ≤ B) (hC : 0 ≤ C)
    (hscalar : ∀ j, j ≤ 3 → ∀ u ∈ Set.Icc (0 : ℝ) (B ^ 2), ‖iteratedFDeriv ℝ j (primitive psi) u‖ ≤ C)
    (x : E) (hx : ‖x‖ ≤ B) (j : ℕ) (hj1 : 1 ≤ j) (hj3 : j ≤ 3) :
    ‖iteratedFDeriv ℝ j (baseCollar psi) x‖ ≤ (j.factorial : ℝ) * C * (2 * B ^ 2) ^ j := by
  have hpc := primitive_contDiff_three psi hc
  have hD : ∀ i : ℕ, 1 ≤ i → i ≤ j →
      ‖iteratedFDeriv ℝ i (fun z : E => ‖z‖ ^ 2) x‖ ≤ (2 * B ^ 2) ^ i := by
    intro i hi hij
    have hBsq : 1 ≤ B ^ 2 := by nlinarith [sq_nonneg (B - 1)]
    have hp := le_self_pow₀ hBsq (by omega : i ≠ 0)
    calc
      _ ≤ (2 : ℝ) ^ i * B ^ 2 := normsq_iterated_bound B hB x hx i
      _ ≤ (2 : ℝ) ^ i * (B ^ 2) ^ i := mul_le_mul_of_nonneg_left hp (by positivity)
      _ = _ := by rw [mul_pow]
  have harg : ‖x‖ ^ 2 ∈ Set.Icc (0 : ℝ) (B ^ 2) :=
    ⟨sq_nonneg _, pow_le_pow_left₀ (norm_nonneg x) hx 2⟩
  have hh := norm_iteratedFDeriv_comp_le (hpc.of_le (by exact_mod_cast hj3))
    (contDiff_id.norm_sq ℝ : ContDiff ℝ j (fun z : E => ‖z‖ ^ 2)) le_rfl x
    (fun i hi => hscalar i (hi.trans hj3) _ harg) hD
  have hfun : baseCollar (E := E) psi = fun z => (1 / 2 : ℝ) • primitive psi (‖z‖ ^ 2) := rfl
  have hcomp : ContDiff ℝ j (fun z : E => primitive psi (‖z‖ ^ 2)) := by
    exact (hpc.comp (contDiff_id.norm_sq ℝ)).of_le (by exact_mod_cast hj3)
  rw [hfun, iteratedFDeriv_const_smul_apply' (a := (1 / 2 : ℝ)) hcomp.contDiffAt, norm_smul]
  have hnorm : ‖(1 / 2 : ℝ)‖ ≤ 1 := by norm_num
  calc
    _ ≤ 1 * ‖iteratedFDeriv ℝ j (fun z : E => primitive psi (‖z‖ ^ 2)) x‖ :=
      mul_le_mul_of_nonneg_right hnorm (norm_nonneg _)
    _ ≤ _ := by simpa only [one_mul, Function.comp_def, id_eq] using! hh

theorem second_jet_linear_zero {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] (L : X →L[ℝ] Y) (x : X) :
    iteratedFDeriv ℝ 2 (L : X → Y) x = 0 := by
  apply norm_eq_zero.mp
  rw [← norm_iteratedFDeriv_fderiv]
  have heq : fderiv ℝ (L : X → Y) = fun _ => L := funext (fun x => L.fderiv)
  rw [heq, iteratedFDeriv_succ_const]
  simp only [Pi.zero_apply, norm_zero]

theorem baseCollar_first (psi : ℝ → ℝ) (hc : ContDiff ℝ 2 psi) (z : E) :
    fderiv ℝ (baseCollar psi) z = psi (‖z‖ ^ 2) • innerSL ℝ z := by
  have heq : baseCollar (E := E) psi = collar psi 1 := by
    funext z
    simp only [baseCollar, collar, one_pow, div_one]
  rw [heq]
  simpa only [one_pow, div_one] using (collar_hasFDerivAt psi hc.continuous 1 (by norm_num) z).fderiv

theorem baseCollar_outer_jets (psi : ℝ → ℝ) (hc : ContDiff ℝ 2 psi) (B : ℝ) (hB : 1 ≤ B)
    (hright : ∀ u, B ^ 2 < u → psi u = 1) (x : E) (hx : B < ‖x‖) :
    ‖iteratedFDeriv ℝ 2 (baseCollar psi) x‖ ≤ 1 ∧
      iteratedFDeriv ℝ 3 (baseCollar psi) x = 0 := by
  have he : fderiv ℝ (baseCollar (E := E) psi) =ᶠ[𝓝 x] (innerSL ℝ : E → (E →L[ℝ] ℝ)) := by
    have hopen := (isOpen_lt continuous_const continuous_norm).mem_nhds hx
    filter_upwards [hopen] with z hz
    rw [baseCollar_first psi hc]
    have harg : B ^ 2 < ‖z‖ ^ 2 := by nlinarith only [hz, hB, norm_nonneg z]
    rw [hright _ harg, one_smul]
  have hh : fderiv ℝ (fderiv ℝ (baseCollar psi)) x = innerSL ℝ := by
    rw [he.fderiv_eq]
    exact (innerSL ℝ (E := E)).fderiv
  refine ⟨?_, ?_⟩
  · rw [← norm_iteratedFDeriv_fderiv, norm_iteratedFDeriv_one, hh]
    exact norm_innerSL_le ℝ
  · apply norm_eq_zero.mp
    rw [← norm_iteratedFDeriv_fderiv]
    rw [(he.iteratedFDeriv ℝ 2).eq_of_nhds, second_jet_linear_zero]
    simp only [norm_zero]

universe u

theorem universal_baseCollar_jets (psi : ℝ → ℝ) (hc : ContDiff ℝ 2 psi) (B : ℝ) (hB : 1 ≤ B)
    (hright : ∀ t, B ^ 2 < t → psi t = 1) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (F : Type u) [NormedAddCommGroup F] [InnerProductSpace ℝ F],
      ∀ x : F, ‖iteratedFDeriv ℝ 2 (baseCollar psi) x‖ ≤ K ∧
        ‖iteratedFDeriv ℝ 3 (baseCollar psi) x‖ ≤ K := by
  obtain ⟨C, hC, hb⟩ := primitive_compact_derivative_bounds psi hc B
  let K2 := (2 : ℕ).factorial * C * (2 * B ^ 2) ^ 2
  let K3 := (3 : ℕ).factorial * C * (2 * B ^ 2) ^ 3
  let K := max 1 (max K2 K3)
  refine ⟨K, (by positivity), ?_⟩
  intro F inst inst' x
  by_cases hx : ‖x‖ ≤ B
  · exact ⟨(baseCollar_local_jet_bound psi hc B C hB hC hb x hx 2 (by norm_num) (by norm_num)).trans
      ((le_max_left K2 K3).trans (le_max_right 1 _)),
      (baseCollar_local_jet_bound psi hc B C hB hC hb x hx 3 (by norm_num) (by norm_num)).trans
      ((le_max_right K2 K3).trans (le_max_right 1 _))⟩
  · obtain ⟨h2, h3⟩ := baseCollar_outer_jets psi hc B hB hright x (lt_of_not_ge hx)
    refine ⟨h2.trans (le_max_left _ _), ?_⟩
    rw [h3, norm_zero]
    positivity

theorem collar_scaling_eq (psi : ℝ → ℝ) (R : ℝ) (hR : 0 < R) (z : E) :
    collar psi R z = R ^ 2 * baseCollar psi (R⁻¹ • z) := by
  simp only [collar, baseCollar, norm_smul, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr hR), mul_pow, div_eq_mul_inv, inv_pow]
  ring

theorem collar_jet_norm_scaling (psi : ℝ → ℝ) (hc : ContDiff ℝ 2 psi)
    (R : ℝ) (hR : 0 < R) (z : E) (j : ℕ) (hj : j ≤ 3) :
    ‖iteratedFDeriv ℝ j (collar psi R) z‖ =
      R ^ 2 * R⁻¹ ^ j * ‖iteratedFDeriv ℝ j (baseCollar psi) (R⁻¹ • z)‖ := by
  have hb := baseCollar_contDiff (E := E) psi hc
  have hb' : ContDiff ℝ j (baseCollar (E := E) psi) := hb.of_le (by exact_mod_cast hj)
  have hcomp : ContDiff ℝ j (fun z : E => baseCollar psi (R⁻¹ • z)) :=
    hb'.comp (contDiff_id.const_smul _)
  have heq : collar (E := E) psi R = fun z => R ^ 2 • baseCollar psi (R⁻¹ • z) :=
    funext (collar_scaling_eq psi R hR)
  have hscale := congrFun (iteratedFDeriv_comp_const_smul R⁻¹ hb') z
  rw [heq, iteratedFDeriv_const_smul_apply' hcomp.contDiffAt, hscale]
  simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg R),
    abs_pow, abs_of_pos (inv_pos.mpr hR)]
  ring

theorem universal_scaled_collar_jets (psi : ℝ → ℝ) (hc : ContDiff ℝ 2 psi)
    (B : ℝ) (hB : 1 ≤ B) (hright : ∀ t, B ^ 2 < t → psi t = 1) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (F : Type u) [NormedAddCommGroup F] [InnerProductSpace ℝ F],
      ∀ R : ℝ, 0 < R → ∀ z : F,
      ContDiff ℝ 3 (collar (E := F) psi R) ∧
      ‖iteratedFDeriv ℝ 2 (collar psi R) z‖ ≤ K ∧
      ‖iteratedFDeriv ℝ 3 (collar psi R) z‖ ≤ K / R := by
  obtain ⟨K, hK, hb⟩ := universal_baseCollar_jets.{u} psi hc B hB hright
  refine ⟨K, hK, ?_⟩
  intro F inst inst' R hR z
  have h := hb F (R⁻¹ • z)
  refine ⟨collar_contDiff_three psi hc R, ?_, ?_⟩
  · rw [collar_jet_norm_scaling psi hc R hR z 2 (by norm_num)]
    have hh := mul_le_mul_of_nonneg_left h.1 (by positivity : 0 ≤ R ^ 2 * R⁻¹ ^ 2)
    convert! hh using 1 <;> try field_simp [ne_of_gt hR] <;> try ring
  · rw [collar_jet_norm_scaling psi hc R hR z 3 (by norm_num)]
    have hh := mul_le_mul_of_nonneg_left h.2 (by positivity : 0 ≤ R ^ 2 * R⁻¹ ^ 3)
    convert! hh using 1 <;> try field_simp [ne_of_gt hR] <;> try ring


end
end FangqingRadialCollarBounds


namespace FangqingRadialCollarEtaBridge

open FangqingRadialCollar

noncomputable section

def eta (psi : ℝ → ℝ) (r : ℝ) : ℝ :=
  if r ≤ 1 then 0 else ∫ u in (1 : ℝ)..r, u * psi (u ^ 2)

theorem half_primitive_square_hasDerivAt (psi : ℝ → ℝ) (hc : Continuous psi) (r : ℝ) :
    HasDerivAt (fun u : ℝ => (1 / 2 : ℝ) * primitive psi (u ^ 2)) (r * psi (r ^ 2)) r := by
  have hh := ((primitive_hasDerivAt psi hc (r ^ 2)).comp r ((hasDerivAt_id r).pow 2)).const_mul (1 / 2 : ℝ)
  convert! hh using 1 <;> simp only [Nat.cast_ofNat, pow_one, id_eq] <;> try ring

theorem eta_eq_half_primitive (psi : ℝ → ℝ) (hc : Continuous psi)
    (hzero : ∀ t, t ≤ 1 → psi t = 0) (r : ℝ) (hr : 0 ≤ r) :
    eta psi r = (1 / 2 : ℝ) * primitive psi (r ^ 2) := by
  by_cases hr1 : r ≤ 1
  · rw [eta, if_pos hr1]
    have hs : r ^ 2 ≤ 1 := by nlinarith only [hr, hr1]
    have heq : Set.EqOn psi (fun _ : ℝ => 0) (Set.uIcc 1 (r ^ 2)) := by
      intro u hu
      rw [Set.uIcc_of_ge hs] at hu
      exact hzero u hu.2
    unfold primitive
    rw [intervalIntegral.integral_congr heq]
    simp
  · rw [eta, if_neg hr1]
    have hh := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x _ => half_primitive_square_hasDerivAt psi hc x)
      ((continuous_id.mul (hc.comp (continuous_id.pow 2))).intervalIntegrable 1 r)
    simpa only [one_pow, primitive, intervalIntegral.integral_same, mul_zero, sub_zero] using hh

theorem literal_paper_collar_eq
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (psi : ℝ → ℝ) (hc : Continuous psi) (hzero : ∀ t, t ≤ 1 → psi t = 0)
    (R : ℝ) (hR : 0 < R) (z : E) :
    R ^ 2 * eta psi (‖z‖ / R) = collar psi R z := by
  rw [eta_eq_half_primitive psi hc hzero _ (div_nonneg (norm_nonneg _) hR.le)]
  simp only [collar, div_pow]
  ring

end
end FangqingRadialCollarEtaBridge


open scoped ContDiff

namespace FangqingPublicShellProfiles

noncomputable section

def psi (t : ℝ) : ℝ := Real.smoothTransition ((4 / 5 : ℝ) * (t - 1))

def theta (t : ℝ) : ℝ := 1 - Real.smoothTransition ((16 / 13 : ℝ) * (t - 9 / 4))

theorem psi_smooth : ContDiff ℝ ∞ psi := by unfold psi; fun_prop

theorem theta_smooth : ContDiff ℝ ∞ theta := by unfold theta; fun_prop

theorem psi_monotone : Monotone psi := by
  intro x y hxy
  apply Real.smoothTransition.monotone
  linarith only [hxy]

theorem theta_antitone : Antitone theta := by
  intro x y hxy
  have hh := Real.smoothTransition.monotone (show (16 / 13 : ℝ) * (x - 9 / 4) ≤ (16 / 13 : ℝ) * (y - 9 / 4) by linarith only [hxy])
  dsimp [theta]
  linarith only [hh]

theorem psi_range (t : ℝ) : 0 ≤ psi t ∧ psi t ≤ 1 :=
  ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩

theorem theta_range (t : ℝ) : 0 ≤ theta t ∧ theta t ≤ 1 := by
  have h0 := Real.smoothTransition.nonneg ((16 / 13 : ℝ) * (t - 9 / 4))
  have h1 := Real.smoothTransition.le_one ((16 / 13 : ℝ) * (t - 9 / 4))
  constructor <;> dsimp [theta] <;> linarith only [h0, h1]

theorem psi_zero (t : ℝ) (ht : t ≤ 1) : psi t = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith only [ht])

theorem psi_one (t : ℝ) (ht : 9 / 4 ≤ t) : psi t = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith only [ht])

theorem theta_one (t : ℝ) (ht : t ≤ 9 / 4) : theta t = 1 := by
  rw [theta, Real.smoothTransition.zero_of_nonpos (by linarith only [ht]), sub_zero]

theorem theta_zero (t : ℝ) (ht : 49 / 16 ≤ t) : theta t = 0 := by
  rw [theta, Real.smoothTransition.one_of_one_le (by linarith only [ht]), sub_self]

universe u

theorem universal_actual_cutoff_jets :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (F : Type u) [NormedAddCommGroup F] [InnerProductSpace ℝ F],
      ∀ R : ℝ, 0 < R → ∀ z : F, ∀ j : ℕ, j ≤ 3 →
      ‖iteratedFDeriv ℝ j (FangqingRadialGateBounds.scaledGate theta R 0) z‖ ≤ K / R ^ j := by
  obtain ⟨K, hK, hb⟩ := FangqingRadialGateBounds.universal_three_gate_bounds.{u} theta (7 / 4)
    (by norm_num) (theta_smooth.of_le (by decide))
    (fun t ht => theta_one t (by linarith only [ht]))
    (fun t ht => theta_zero t (by nlinarith only [ht]))
  refine ⟨max 1 K, (by positivity), ?_⟩
  intro F inst inst' R hR z j hj
  by_cases hj0 : j = 0
  · subst j
    simp only [norm_iteratedFDeriv_zero, pow_zero, div_one,
      FangqingRadialGateBounds.scaledGate, Real.norm_eq_abs]
    rw [abs_of_nonneg (theta_range _).1]
    exact (theta_range _).2.trans (le_max_left _ _)
  · exact (hb F R hR 0 z j (by omega) hj).trans
      (div_le_div_of_nonneg_right (le_max_right _ _) (pow_nonneg hR.le j))

theorem actual_cutoff_zero_outside
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (R : ℝ) (hR : 0 < R) (z : F) (hz : 2 * R < ‖z‖) :
    FangqingRadialGateBounds.scaledGate theta R 0 z = 0 := by
  apply theta_zero
  simp only [sub_zero]
  apply (le_div_iff₀ (pow_pos hR 2)).mpr
  nlinarith only [hz, hR, norm_nonneg z, sq_nonneg (‖z‖ - 2 * R)]

theorem actual_cutoff_one_inside
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (R : ℝ) (hR : 0 < R) (z : F) (hz : ‖z‖ ≤ (3 / 2 : ℝ) * R) :
    FangqingRadialGateBounds.scaledGate theta R 0 z = 1 := by
  apply theta_one
  simp only [sub_zero]
  apply (div_le_iff₀ (pow_pos hR 2)).mpr
  have hh := pow_le_pow_left₀ (norm_nonneg z) hz 2
  nlinarith only [hh]

end
end FangqingPublicShellProfiles


namespace FangqingHessianTensorIsometry

noncomputable section

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem second_jet_difference_le_hessian (f : X → ℝ) (x y : X) :
    ‖iteratedFDeriv ℝ 2 f x - iteratedFDeriv ℝ 2 f y‖ ≤
      ‖fderiv ℝ (fderiv ℝ f) x - fderiv ℝ (fderiv ℝ f) y‖ := by
  refine (iteratedFDeriv ℝ 2 f x - iteratedFDeriv ℝ 2 f y).opNorm_le_bound
    (ContinuousLinearMap.opNorm_nonneg _) ?_
  intro v
  simp only [ContinuousMultilinearMap.sub_apply, iteratedFDeriv_two_apply, Fin.prod_univ_two]
  have h1 := (fderiv ℝ (fderiv ℝ f) x - fderiv ℝ (fderiv ℝ f) y).le_opNorm (v 0)
  have h2 := ((fderiv ℝ (fderiv ℝ f) x - fderiv ℝ (fderiv ℝ f) y) (v 0)).le_opNorm (v 1)
  simp only [ContinuousLinearMap.sub_apply] at h2
  have hh := h2.trans (mul_le_mul_of_nonneg_right h1 (norm_nonneg (v 1)))
  convert! hh using 1 <;> try ring

theorem second_jet_difference_eq_hessian (f : X → ℝ) (x y : X) :
    ‖iteratedFDeriv ℝ 2 f x - iteratedFDeriv ℝ 2 f y‖ =
      ‖fderiv ℝ (fderiv ℝ f) x - fderiv ℝ (fderiv ℝ f) y‖ :=
  le_antisymm (second_jet_difference_le_hessian f x y)
    (FangqingC2BlockRegularity.hessian_difference_norm_le_second_jet f x y)

end
end FangqingHessianTensorIsometry


open scoped ContDiff NNReal Topology

namespace FangqingInactiveShellClass

open FangqingRadialGateBounds FangqingGateBudgetBridge FangqingCutoffProductRegularity
  FangqingRadialCollar FangqingRadialCollarBounds FangqingPublicShellProfiles
  FangqingHessianStrongConvexity FangqingC2HessianAlgebra FangqingJetToRegularity
  FangqingHessianTensorIsometry FangqingC2ProductHessianBounds

set_option maxHeartbeats 2000000

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

def inactiveShell (Q g : E → ℝ) (R gain : ℝ) (z : E) : ℝ :=
  Q z + scaledGate theta R 0 z * g z + gain * collar psi R z

universe u

theorem universal_inactive_shell_class :
    ∃ K : ℝ, 0 ≤ K ∧ ∃ Kc : ℝ, 0 ≤ Kc ∧
    ∀ (F : Type u) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F],
      ∀ (Q g : F → ℝ) (R nu LQ : ℝ) (M rho : ℝ≥0),
      0 < R → 0 ≤ LQ → ContDiff ℝ 2 Q → ContDiff ℝ 2 g →
      StrongConvexOn (Set.univ : Set F) nu Q → ConvexOn ℝ (Set.univ : Set F) g →
      (∀ z, ‖iteratedFDeriv ℝ 2 Q z‖ ≤ LQ) →
      (∀ x y, fderiv ℝ (fderiv ℝ Q) x = fderiv ℝ (fderiv ℝ Q) y) →
      (∀ z, ‖iteratedFDeriv ℝ 2 g z‖ ≤ M) → g 0 = 0 → fderiv ℝ g 0 = 0 →
      (∀ x y, ‖fderiv ℝ (fderiv ℝ g) x - fderiv ℝ (fderiv ℝ g) y‖ ≤ (rho : ℝ) * ‖x - y‖) →
      let gain := (16 * K + 1) * (M : ℝ)
      let H := inactiveShell Q g R gain
      ContDiff ℝ 2 H ∧ StrongConvexOn (Set.univ : Set F) nu H ∧
      (∀ z, ‖iteratedFDeriv ℝ 2 H z‖ ≤ LQ + 16 * K * M + gain * Kc) ∧
      (∀ x y, ‖iteratedFDeriv ℝ 2 H x - iteratedFDeriv ℝ 2 H y‖ ≤
        (K * rho + 21 * K * M / R + gain * (Kc / R)) * ‖x - y‖) := by
  obtain ⟨K, hK, hcut⟩ := universal_actual_cutoff_jets.{u}
  have hpsi : ContDiff ℝ 2 psi := psi_smooth.of_le (by decide)
  obtain ⟨Kc, hKc, hcol⟩ := universal_scaled_collar_jets.{u} psi hpsi (3 / 2) (by norm_num)
    (fun t ht => psi_one t (by nlinarith only [ht]))
  refine ⟨K, hK, Kc, hKc, ?_⟩
  intro F inst inst' inst'' Q g R nu LQ M rho hR hLQ hQ hg hQs hgc hQ2 hQconst hg2 hg0 hgd0 hglip gain H
  let f : F → ℝ := scaledGate theta R 0
  have hf : ContDiff ℝ 3 f := scaledGate_contDiff theta R 0 hR (theta_smooth.of_le (by decide))
  obtain ⟨hprod, hprod2, hprodLip⟩ := cutoff_product_regularity f g hf hg R K M rho hR hK
    (fun j hj z => hcut F R hR z j hj) (actual_cutoff_zero_outside R hR) hg2 hg0 hgd0 hglip
  have hc3 : ContDiff ℝ 3 (collar (E := F) psi R) := collar_contDiff_three psi hpsi R
  have hc2 : ContDiff ℝ 2 (collar (E := F) psi R) := hc3.of_le (by norm_num)
  have hgain : 0 ≤ gain := by dsimp [gain]; positivity
  have hH : ContDiff ℝ 2 H := (hQ.add hprod).add (contDiff_const.mul hc2)
  have hform : ∀ z v : F, fderiv ℝ (fderiv ℝ H) z v v =
      fderiv ℝ (fderiv ℝ Q) z v v + fderiv ℝ (fderiv ℝ (fun z => f z * g z)) z v v +
      gain * fderiv ℝ (fderiv ℝ (collar psi R)) z v v := by
    intro z v
    change fderiv ℝ (fderiv ℝ (fun z => Q z + f z * g z + gain * collar psi R z)) z v v = _
    rw [hessian_add _ _ (hQ.add hprod) (contDiff_const.mul hc2),
      hessian_add _ _ hQ hprod, hessian_const_mul _ hc2]
  have hSC : StrongConvexOn (Set.univ : Set F) nu H := by
    apply strongConvex_of_hessian_lower H nu hH
    intro z v
    rw [hform]
    have hq := hessian_lower_of_strongConvex Q nu hQ hQs z v
    have hcolpos := collar_hessian_nonneg psi hpsi psi_monotone (fun t => (psi_range t).1) R hR z v
    by_cases hz : ‖z‖ < (3 / 2 : ℝ) * R
    · have heq : (fun z => f z * g z) =ᶠ[𝓝 z] g := by
        have hopen := (isOpen_lt continuous_norm continuous_const).mem_nhds hz
        filter_upwards [hopen] with y hy
        rw [show f y = 1 from actual_cutoff_one_inside R hR y hy.le, one_mul]
      have hfirst : fderiv ℝ (fun z => f z * g z) =ᶠ[𝓝 z] fderiv ℝ g := heq.fderiv
      have heq2 : fderiv ℝ (fderiv ℝ (fun z => f z * g z)) z = fderiv ℝ (fderiv ℝ g) z := hfirst.fderiv_eq
      rw [heq2]
      have hgpos := hessian_lower_of_strongConvex g 0 hg (strongConvexOn_zero.mpr hgc) z v
      simp only [zero_mul] at hgpos
      nlinarith only [hq, hgpos, mul_nonneg hgain hcolpos]
    · have hc := collar_hessian_outer_lower psi hpsi psi_monotone (3 / 2) R (by norm_num) hR
        (fun t ht => psi_one t (by nlinarith only [ht])) z v (le_of_not_gt hz)
      have hb := second_eval_bound _ (16 * K * M) (hprod2 z) v v
      have hb' := (abs_le.mp hb).1
      have hm := mul_le_mul_of_nonneg_left hc hgain
      dsimp [gain] at hm
      nlinarith only [hq, hb', hm, mul_nonneg M.coe_nonneg (sq_nonneg ‖v‖)]
  have hjet : ∀ z, iteratedFDeriv ℝ 2 H z =
      iteratedFDeriv ℝ 2 Q z + iteratedFDeriv ℝ 2 (fun z => f z * g z) z +
      gain • iteratedFDeriv ℝ 2 (collar psi R) z := by
    intro z
    change iteratedFDeriv ℝ 2 (fun z => Q z + f z * g z + gain * collar psi R z) z = _
    rw [fun_iteratedFDeriv_add_apply (hQ.add hprod).contDiffAt (contDiff_const.mul hc2).contDiffAt,
      fun_iteratedFDeriv_add_apply hQ.contDiffAt hprod.contDiffAt]
    have hh := iteratedFDeriv_const_smul_apply' (a := gain) hc2.contDiffAt (x := z)
    change iteratedFDeriv ℝ 2 (fun z => gain * collar psi R z) z = _ at hh
    rw [hh]
  have hH2 : ∀ z, ‖iteratedFDeriv ℝ 2 H z‖ ≤ LQ + 16 * K * M + gain * Kc := by
    intro z
    rw [hjet]
    have hp2 : ‖iteratedFDeriv ℝ 2 (fun z => f z * g z) z‖ ≤ 16 * K * M := by
      rw [← hessian_norm_eq_second_jet]
      exact hprod2 z
    have hh := norm_add_le
      (iteratedFDeriv ℝ 2 Q z + iteratedFDeriv ℝ 2 (fun z => f z * g z) z)
      (gain • iteratedFDeriv ℝ 2 (collar psi R) z)
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hgain] at hh
    have hh1 := norm_add_le (iteratedFDeriv ℝ 2 Q z) (iteratedFDeriv ℝ 2 (fun z => f z * g z) z)
    exact hh.trans (add_le_add (hh1.trans (add_le_add (hQ2 z) hp2))
      (mul_le_mul_of_nonneg_left (hcol F R hR z).2.1 hgain))
  refine ⟨hH, hSC, hH2, ?_⟩
  intro x y
  have hQjet : iteratedFDeriv ℝ 2 Q x = iteratedFDeriv ℝ 2 Q y := by
    apply sub_eq_zero.mp
    apply norm_eq_zero.mp
    rw [second_jet_difference_eq_hessian, hQconst x y, sub_self]
    exact ContinuousLinearMap.opNorm_zero
  have hprodjet : ‖iteratedFDeriv ℝ 2 (fun z => f z * g z) x -
      iteratedFDeriv ℝ 2 (fun z => f z * g z) y‖ ≤ (K * rho + 21 * K * M / R) * ‖x - y‖ := by
    rw [second_jet_difference_eq_hessian]
    exact hprodLip x y
  let Rc : ℝ≥0 := ⟨Kc / R, by positivity⟩
  have hcolLip := second_jet_lipschitz_from_third_jet (collar (E := F) psi R) hc3 Rc
    (fun z => (hcol F R hR z).2.2)
  have heq : iteratedFDeriv ℝ 2 H x - iteratedFDeriv ℝ 2 H y =
      (iteratedFDeriv ℝ 2 (fun z => f z * g z) x - iteratedFDeriv ℝ 2 (fun z => f z * g z) y) +
      gain • (iteratedFDeriv ℝ 2 (collar psi R) x - iteratedFDeriv ℝ 2 (collar psi R) y) := by
    rw [hjet x, hjet y, hQjet, smul_sub]
    abel
  rw [heq]
  have hh := norm_add_le
    (iteratedFDeriv ℝ 2 (fun z => f z * g z) x - iteratedFDeriv ℝ 2 (fun z => f z * g z) y)
    (gain • (iteratedFDeriv ℝ 2 (collar psi R) x - iteratedFDeriv ℝ 2 (collar psi R) y))
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hgain] at hh
  have hcpoint : ‖iteratedFDeriv ℝ 2 (collar psi R) x - iteratedFDeriv ℝ 2 (collar psi R) y‖ ≤
      (Kc / R) * ‖x - y‖ := hcolLip.norm_sub_le x y
  have hc := mul_le_mul_of_nonneg_left hcpoint hgain
  have hb := hh.trans (add_le_add hprodjet hc)
  convert! hb using 1 <;> try ring

end
end FangqingInactiveShellClass


open scoped ContDiff NNReal

namespace FangqingActualInactivePacket

open FangqingAmplifier FangqingAmplifierRegularity FangqingPacketLeakage
  FangqingPathIncidenceBounds FangqingPathEdgeRegularity FangqingInactiveShellClass
  FangqingHessianTensorIsometry FangqingJetToRegularity

set_option maxHeartbeats 2000000

noncomputable section

universe v

variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

def AnalyticClass (H : E → ℝ) (nu L rho : ℝ) : Prop :=
  ContDiff ℝ 2 H ∧ StrongConvexOn (Set.univ : Set E) nu H ∧
  (∀ x y, ‖gradient H x - gradient H y‖ ≤ L * ‖x - y‖) ∧
  (∀ x y, ‖fderiv ℝ (fderiv ℝ H) x - fderiv ℝ (fderiv ℝ H) y‖ ≤ rho * ‖x - y‖)

theorem class_of_actual_jets (H : E → ℝ) (nu L rho : ℝ) (hL : 0 ≤ L)
    (hc : ContDiff ℝ 2 H) (hs : StrongConvexOn (Set.univ : Set E) nu H)
    (h2 : ∀ z, ‖iteratedFDeriv ℝ 2 H z‖ ≤ L)
    (hlip : ∀ x y, ‖iteratedFDeriv ℝ 2 H x - iteratedFDeriv ℝ 2 H y‖ ≤ rho * ‖x - y‖) :
    AnalyticClass H nu L rho := by
  let Ln : ℝ≥0 := ⟨L, hL⟩
  have hg := gradient_lipschitz_from_second_jet H hc Ln h2
  refine ⟨hc, hs, fun x y => hg.norm_sub_le x y, ?_⟩
  intro x y
  rw [← second_jet_difference_eq_hessian]
  exact hlip x y

theorem actual_scaled_path_data (P : FlatCubic.Profile) (Ce : ℝ≥0)
    (hb : ∀ (F : Type v) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F],
      ∀ delta omega : ℝ, 0 < delta → delta ≤ omega → ∀ n (v : Fin (n + 1) → F), Orthonormal ℝ v →
      ContDiff ℝ 2 (pathEdge P delta omega n v) ∧ ConvexOn ℝ (Set.univ : Set F) (pathEdge P delta omega n v) ∧
      (∀ z, ‖iteratedFDeriv ℝ 2 (pathEdge P delta omega n v) z‖ ≤ (4 * Ce : ℝ) * omega) ∧
      (∀ x y, ‖iteratedFDeriv ℝ 2 (pathEdge P delta omega n v) x - iteratedFDeriv ℝ 2 (pathEdge P delta omega n v) y‖ ≤ (8 * Ce : ℝ) * ‖x - y‖) ∧
      (∀ x y, ‖fderiv ℝ (fderiv ℝ (pathEdge P delta omega n v)) x - fderiv ℝ (fderiv ℝ (pathEdge P delta omega n v)) y‖ ≤ (8 * Ce : ℝ) * ‖x - y‖))
    (delta omega scale : ℝ) (hd : 0 < delta) (hdD : delta ≤ omega) (hscale : 0 ≤ scale)
    (n : ℕ) (v : Fin (n + 1) → E) (hv : Orthonormal ℝ v) :
    let g := fun z => scale * pathEdge P delta omega n v z
    ContDiff ℝ 2 g ∧ ConvexOn ℝ (Set.univ : Set E) g ∧
    (∀ z, ‖iteratedFDeriv ℝ 2 g z‖ ≤ (4 * Ce : ℝ) * scale * omega) ∧
    g 0 = 0 ∧ fderiv ℝ g 0 = 0 ∧
    (∀ x y, ‖fderiv ℝ (fderiv ℝ g) x - fderiv ℝ (fderiv ℝ g) y‖ ≤ (8 * Ce : ℝ) * scale * ‖x - y‖) := by
  intro g
  obtain ⟨hc, hconv, h2, h2lip, hhlip⟩ := hb E delta omega hd hdD n v hv
  have hgc : ContDiff ℝ 2 g := contDiff_const.mul hc
  have hj0 := FlatCubic.edge_flat_jets_closed P delta omega 0 hd hdD (by simp only [abs_zero]; linarith only [hd])
  have he0 : pathEdge P delta omega n v 0 = 0 := by
    simp only [pathEdge, edgeSum, inner_zero_right, hj0.1, Finset.sum_const_zero]
  have hed0 : fderiv ℝ (pathEdge P delta omega n v) 0 = 0 := by
    change fderiv ℝ (edgeSum (FlatCubic.edge P delta omega) (FangqingPathIncidenceBounds.pathDirection n v)) 0 = 0
    rw [(hasFDerivAt_edgeSum (FlatCubic.edge P delta omega) ((FlatCubic.edge_contDiff_two P delta omega hd hdD).differentiable (by norm_num))
      (FangqingPathIncidenceBounds.pathDirection n v) 0).fderiv]
    simp only [edgeGradient, inner_zero_right, hj0.2.1, zero_smul, Finset.sum_const_zero]
  refine ⟨hgc, ?_, ?_, ?_, ?_, ?_⟩
  · exact ConvexOn.smul hscale hconv
  · intro z
    have hh := iteratedFDeriv_const_smul_apply' (a := scale) hc.contDiffAt (x := z)
    change iteratedFDeriv ℝ 2 g z = _ at hh
    rw [hh, norm_smul, Real.norm_eq_abs, abs_of_nonneg hscale]
    convert! mul_le_mul_of_nonneg_left (h2 z) hscale using 1 <;> try ring
  · simp only [g, he0, mul_zero]
  · have hh := ((hc.differentiable (by norm_num) 0).hasFDerivAt.const_mul scale).fderiv
    change fderiv ℝ g 0 = _ at hh
    rw [hh, hed0, smul_zero]
  · intro x y
    apply (FangqingJetToRegularity.hessian_difference_norm_le_second_jet g x y).trans
    have hhx := iteratedFDeriv_const_smul_apply' (a := scale) hc.contDiffAt (x := x)
    have hhy := iteratedFDeriv_const_smul_apply' (a := scale) hc.contDiffAt (x := y)
    change iteratedFDeriv ℝ 2 g x = _ at hhx
    change iteratedFDeriv ℝ 2 g y = _ at hhy
    rw [hhx, hhy, ← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_nonneg hscale]
    convert! mul_le_mul_of_nonneg_left (h2lip x y) hscale using 1 <;> try ring

universe u

theorem actual_inactive_packet_class (P : FlatCubic.Profile) :
    ∃ Ce : ℝ≥0, ∃ K : ℝ, 0 ≤ K ∧ ∃ Kc : ℝ, 0 ≤ Kc ∧
    ∀ (A B W : Type u)
      [NormedAddCommGroup A] [InnerProductSpace ℝ A] [CompleteSpace A]
      [NormedAddCommGroup B] [InnerProductSpace ℝ B] [CompleteSpace B]
      [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W],
      ∀ (q nu scale delta omega R : ℝ) (C : A ≃ₗᵢ[ℝ] B)
      (n : ℕ) (v : Fin (n + 1) → PhysicalSpace A B W),
      0 ≤ q → 0 ≤ nu → 0 ≤ scale → 0 < delta → delta ≤ omega → 0 < R → Orthonormal ℝ v →
      let M : ℝ := (4 * Ce : ℝ) * scale * omega
      let gain := (16 * K + 1) * M
      let H0 := inactiveShell (QPhysical q nu C) (fun z => scale * pathEdge P delta omega n v z) R gain
      AnalyticClass H0 nu (nu * (q + 2) + 16 * K * M + gain * Kc)
        (K * ((8 * Ce : ℝ) * scale) + 21 * K * M / R + gain * (Kc / R)) ∧
      (∀ z, ‖iteratedFDeriv ℝ 2 H0 z‖ ≤ nu * (q + 2) + 16 * K * M + gain * Kc) ∧
      (∀ x y, ‖iteratedFDeriv ℝ 2 H0 x - iteratedFDeriv ℝ 2 H0 y‖ ≤
        (K * ((8 * Ce : ℝ) * scale) + 21 * K * M / R + gain * (Kc / R)) * ‖x - y‖) := by
  obtain ⟨Ce, hCe⟩ := actual_pathEdge_regularity.{u} P
  obtain ⟨K, hK, Kc, hKc, hShell⟩ := universal_inactive_shell_class.{u}
  refine ⟨Ce, K, hK, Kc, hKc, ?_⟩
  intro A B W inst inst' inst'' instB instB' instB'' instW instW' instW''
    q nu scale delta omega R C n v hq hnu hscale hd hdD hR hv M gain H0
  have homega : 0 < omega := hd.trans_le hdD
  obtain ⟨hgc, hgv, hg2, hg0, hgd0, hgLip⟩ := actual_scaled_path_data P Ce hCe
    delta omega scale hd hdD hscale n v hv
  let Mn : ℝ≥0 := ⟨M, by dsimp [M]; positivity⟩
  let rn : ℝ≥0 := ⟨(8 * Ce : ℝ) * scale, by positivity⟩
  have hQc := physical_quadratic_contDiff (W := W) q nu C
  have hQs := physical_quadratic_strongConvex (W := W) q nu hq hnu C
  have hQconst : ∀ x y : PhysicalSpace A B W,
      fderiv ℝ (fderiv ℝ (QPhysical q nu C)) x = fderiv ℝ (fderiv ℝ (QPhysical q nu C)) y := by
    intro x y
    rw [physical_quadratic_hessian_constant, physical_quadratic_hessian_constant]
  obtain ⟨hHc, hHs, hH2, hHLip⟩ := hShell (PhysicalSpace A B W)
    (QPhysical q nu C) (fun z => scale * pathEdge P delta omega n v z) R nu (nu * (q + 2)) Mn rn
    hR (by positivity) hQc hgc hQs hgv (physical_quadratic_second_jet_bound q nu hq hnu C)
    hQconst hg2 hg0 hgd0 hgLip
  exact ⟨class_of_actual_jets H0 nu _ _ (by dsimp [M, gain]; positivity) hHc hHs hH2 hHLip, hH2, hHLip⟩


end
end FangqingActualInactivePacket


open scoped ContDiff NNReal

namespace FangqingC2SmallPerturbation

open FangqingHessianStrongConvexity FangqingC2HessianAlgebra FangqingJetToRegularity
  FangqingHessianTensorIsometry FangqingC2ProductHessianBounds

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem actual_small_perturbation (H seed : E → ℝ) (nu L rho S P : ℝ)
    (hH : ContDiff ℝ 2 H) (hs : ContDiff ℝ 3 seed)
    (hSC : StrongConvexOn (Set.univ : Set E) nu H)
    (hS : 0 ≤ S) (hP : 0 ≤ P)
    (hH2 : ∀ z, ‖iteratedFDeriv ℝ 2 H z‖ ≤ L)
    (hHLip : ∀ x y, ‖iteratedFDeriv ℝ 2 H x - iteratedFDeriv ℝ 2 H y‖ ≤ rho * ‖x - y‖)
    (hs2 : ∀ z, ‖iteratedFDeriv ℝ 2 seed z‖ ≤ S)
    (hs3 : ∀ z, ‖iteratedFDeriv ℝ 3 seed z‖ ≤ P) :
    ContDiff ℝ 2 (fun z => H z - seed z) ∧
    StrongConvexOn (Set.univ : Set E) (nu - S) (fun z => H z - seed z) ∧
    (∀ z, ‖iteratedFDeriv ℝ 2 (fun z => H z - seed z) z‖ ≤ L + S) ∧
    (∀ x y, ‖iteratedFDeriv ℝ 2 (fun z => H z - seed z) x -
      iteratedFDeriv ℝ 2 (fun z => H z - seed z) y‖ ≤ (rho + P) * ‖x - y‖) := by
  have hsC2 : ContDiff ℝ 2 seed := hs.of_le (by norm_num)
  have hdiff := hH.sub hsC2
  have hsc : StrongConvexOn (Set.univ : Set E) (nu - S) (fun z => H z - seed z) := by
    apply strongConvex_of_hessian_lower _ _ hdiff
    intro z v
    rw [hessian_sub _ _ hH hsC2]
    have h1 := hessian_lower_of_strongConvex H nu hH hSC z v
    have h2b : ‖fderiv ℝ (fderiv ℝ seed) z‖ ≤ S := by
      rw [hessian_norm_eq_second_jet]
      exact hs2 z
    have h2 := (abs_le.mp (second_eval_bound _ S h2b v v)).2
    nlinarith only [h1, h2]
  let Pn : ℝ≥0 := ⟨P, hP⟩
  have hseedLip := second_jet_lipschitz_from_third_jet seed hs Pn hs3
  have heq : ∀ z, iteratedFDeriv ℝ 2 (fun z => H z - seed z) z =
      iteratedFDeriv ℝ 2 H z - iteratedFDeriv ℝ 2 seed z := by
    intro z
    exact fun_iteratedFDeriv_sub_apply hH.contDiffAt hsC2.contDiffAt
  refine ⟨hdiff, hsc, ?_, ?_⟩
  · intro z
    rw [heq]
    exact (norm_sub_le _ _).trans (add_le_add (hH2 z) (hs2 z))
  · intro x y
    rw [heq x, heq y]
    have halg : iteratedFDeriv ℝ 2 H x - iteratedFDeriv ℝ 2 seed x -
        (iteratedFDeriv ℝ 2 H y - iteratedFDeriv ℝ 2 seed y) =
        (iteratedFDeriv ℝ 2 H x - iteratedFDeriv ℝ 2 H y) -
        (iteratedFDeriv ℝ 2 seed x - iteratedFDeriv ℝ 2 seed y) := by abel
    rw [halg]
    have hp : ‖iteratedFDeriv ℝ 2 seed x - iteratedFDeriv ℝ 2 seed y‖ ≤ P * ‖x - y‖ :=
      hseedLip.norm_sub_le x y
    have hb := (norm_sub_le _ _).trans (add_le_add (hHLip x y) hp)
    convert! hb using 1 <;> try ring

end
end FangqingC2SmallPerturbation


open scoped ContDiff

namespace FangqingActiveShellClass

open FangqingActualInactivePacket FangqingInactiveShellClass FangqingAmplifier
  FangqingPathEdgeRegularity FangqingLocalizedSeedJets FangqingSaturatedProfileBounds
  FangqingPublicShellProfiles FangqingC2SmallPerturbation

set_option maxHeartbeats 2200000

noncomputable section

universe u

theorem universal_actual_seed_jets (phi : ℝ → ℝ) (B left right : ℝ)
    (hp : ContDiff ℝ 3 phi) (hl : ∀ t, t < -B → phi t = left) (hr : ∀ t, B < t → phi t = right) :
    ∃ Ks : ℝ, 0 ≤ Ks ∧ ∀ (F : Type u) [NormedAddCommGroup F] [InnerProductSpace ℝ F],
      ∀ (R A amp : ℝ) (handle : F), 0 < A → A ≤ R → 0 ≤ amp → ‖handle‖ ≤ 1 →
      ContDiff ℝ 3 (localizedSeed theta phi R A amp handle) ∧
      ∀ j, j ≤ 3 → ∀ z,
        ‖iteratedFDeriv ℝ j (localizedSeed theta phi R A amp handle) z‖ ≤ Ks * amp / A ^ j := by
  obtain ⟨Kt, hKt, ht⟩ := universal_actual_cutoff_jets.{u}
  obtain ⟨Cp, hCp, hphi⟩ := scalar_saturation_derivatives_bounded phi 3 B left right hp hl hr
  refine ⟨8 * Kt * Cp, (by positivity), ?_⟩
  intro F inst inst' R A amp handle hA hAR hamp hh
  refine ⟨localizedSeed_contDiff theta phi R A amp handle (hA.trans_le hAR)
    (theta_smooth.of_le (by decide)) hp, ?_⟩
  intro j hj z
  exact localizedSeed_jet_bound theta phi R A amp A Kt Cp handle z hA hAR le_rfl hamp hKt hCp hh
    (theta_smooth.of_le (by decide)) hp (fun j hj z => ht F R (hA.trans_le hAR) z j hj) hphi j hj

theorem actual_width_curvature_reserve (Ks Cs nu D : ℝ)
    (hKs : 0 ≤ Ks) (hCs : 0 ≤ Cs) (hnu : 0 ≤ nu) (hD : 0 < D) :
    let CA := 1 + 2 * Ks * Cs
    let A := CA * D
    Ks * ((Cs * nu * D) * A) / A ^ 2 ≤ nu / 2 := by
  intro CA A
  have hCA : 0 < CA := by dsimp [CA]; positivity
  have heq : Ks * ((Cs * nu * D) * A) / A ^ 2 = Ks * Cs * nu / CA := by
    dsimp [A]
    field_simp [ne_of_gt hCA, ne_of_gt hD]
    <;> try ring
  rw [heq]
  apply (div_le_iff₀ hCA).mpr
  dsimp [CA]
  nlinarith only [hnu]

theorem actual_paired_shell_class (P : FlatCubic.Profile)
    (phi : ℝ → ℝ) (B left right Cs : ℝ) (hCs : 0 ≤ Cs)
    (hp : ContDiff ℝ 3 phi) (hl : ∀ t, t < -B → phi t = left) (hr : ∀ t, B < t → phi t = right) :
    ∃ Ce : ℝ≥0, ∃ K : ℝ, 0 ≤ K ∧ ∃ Kc : ℝ, 0 ≤ Kc ∧ ∃ Ks : ℝ, 0 ≤ Ks ∧
    ∀ (A0 B0 W : Type u)
      [NormedAddCommGroup A0] [InnerProductSpace ℝ A0] [CompleteSpace A0]
      [NormedAddCommGroup B0] [InnerProductSpace ℝ B0] [CompleteSpace B0]
      [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W],
      ∀ (q nu scale delta omega R D : ℝ) (C : A0 ≃ₗᵢ[ℝ] B0)
      (n : ℕ) (v : Fin (n + 1) → PhysicalSpace A0 B0 W) (handle : PhysicalSpace A0 B0 W),
      0 ≤ q → 0 ≤ nu → 0 ≤ scale → 0 < delta → delta ≤ omega → 0 < D →
      (1 + 2 * Ks * Cs) * D ≤ R → Orthonormal ℝ v → ‖handle‖ ≤ 1 →
      let A := (1 + 2 * Ks * Cs) * D
      let s := Cs * nu * D
      let M : ℝ := (4 * Ce : ℝ) * scale * omega
      let gain := (16 * K + 1) * M
      let H0 := inactiveShell (QPhysical q nu C) (fun z => scale * pathEdge P delta omega n v z) R gain
      let H1 := fun z => H0 z - localizedSeed theta phi R A (s * A) handle z
      let L0 := nu * (q + 2) + 16 * K * M + gain * Kc
      let rho0 := K * ((8 * Ce : ℝ) * scale) + 21 * K * M / R + gain * (Kc / R)
      AnalyticClass H0 nu L0 rho0 ∧
      AnalyticClass H1 (nu / 2) (L0 + Ks * (s * A) / A ^ 2) (rho0 + Ks * (s * A) / A ^ 3) := by
  obtain ⟨Ce, K, hK, Kc, hKc, hInactive⟩ := actual_inactive_packet_class.{u} P
  obtain ⟨Ks, hKs, hSeed⟩ := universal_actual_seed_jets.{u} phi B left right hp hl hr
  refine ⟨Ce, K, hK, Kc, hKc, Ks, hKs, ?_⟩
  intro A0 B0 W inst inst' inst'' instB instB' instB'' instW instW' instW''
    q nu scale delta omega R D C n v handle hq hnu hscale hd hdD hD hRA hv hh A s M gain H0 H1 L0 rho0
  have hA : 0 < A := by dsimp [A]; positivity
  have hR : 0 < R := hA.trans_le hRA
  have hs : 0 ≤ s := by dsimp [s]; positivity
  have hamp : 0 ≤ s * A := mul_nonneg hs hA.le
  obtain ⟨hH0, hH02, hH0Lip⟩ := hInactive A0 B0 W q nu scale delta omega R C n v hq hnu hscale hd hdD hR hv
  obtain ⟨hSeedC, hSeedJ⟩ := hSeed (PhysicalSpace A0 B0 W) R A (s * A) handle hA hRA hamp hh
  let S := Ks * (s * A) / A ^ 2
  let T := Ks * (s * A) / A ^ 3
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have hT : 0 ≤ T := by dsimp [T]; positivity
  obtain ⟨hH1c, hH1s, hH12, hH1Lip⟩ := actual_small_perturbation H0
    (localizedSeed theta phi R A (s * A) handle) nu L0 rho0 S T hH0.1 hSeedC hH0.2.1 hS hT
    hH02 hH0Lip (hSeedJ 2 (by norm_num)) (hSeedJ 3 (by norm_num))
  have hSmall : S ≤ nu / 2 := actual_width_curvature_reserve Ks Cs nu D hKs hCs hnu hD
  have hmod : nu / 2 ≤ nu - S := by linarith only [hSmall]
  have homega : 0 < omega := hd.trans_le hdD
  have hL : 0 ≤ L0 + S := by dsimp [L0, M, gain]; positivity
  exact ⟨hH0, class_of_actual_jets H1 (nu / 2) (L0 + S) (rho0 + T) hL hH1c (hH1s.mono hmod) hH12 hH1Lip⟩

theorem actual_active_shell_literal_eq
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (Q g : F → ℝ) (phi : ℝ → ℝ) (R A s gain : ℝ) (hR : 0 < R) (handle z : F) :
    inactiveShell Q g R gain z - localizedSeed theta phi R A (s * A) handle z =
      Q z + theta ((‖z‖ / R) ^ 2) * (g z - s * A * phi (inner ℝ handle z / A)) +
        gain * R ^ 2 * FangqingRadialCollarEtaBridge.eta psi (‖z‖ / R) := by
  have hc := FangqingRadialCollarEtaBridge.literal_paper_collar_eq psi psi_smooth.continuous psi_zero R hR z
  dsimp [inactiveShell, localizedSeed, FangqingLinearProfileJetBounds.linearProfile]
  rw [← hc]
  simp only [FangqingRadialGateBounds.scaledGate, sub_zero, div_pow]
  ring


end
end FangqingActiveShellClass


open scoped ContDiff

namespace FangqingFenchelEndpointClass

set_option maxHeartbeats 1500000

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

abbrev Joint (E : Type*) := WithLp 2 (E × E)

def mk (x y : E) : Joint E := WithLp.toLp 2 (x, y)

def xL : Joint E →L[ℝ] E := WithLp.fstL 2 ℝ E E

def yL : Joint E →L[ℝ] E := WithLp.sndL 2 ℝ E E

def pairL (f g : Joint E →L[ℝ] E) : Joint E →L[ℝ] Joint E :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ E E).symm.toContinuousLinearMap.comp (f.prod g)

def K (beta c lam : ℝ) : Joint E →L[ℝ] Joint E :=
  pairL (beta • xL + lam • yL) (lam • xL + c • yL)

def quadratic (beta c lam : ℝ) (z : Joint E) : ℝ :=
  beta / 2 * ‖z.fst‖ ^ 2 + lam * inner ℝ z.fst z.snd + c / 2 * ‖z.snd‖ ^ 2

def jointEndpoint (H : E → ℝ) (beta c lam m : ℝ) (z : Joint E) : ℝ :=
  quadratic beta c lam z - H z.snd + m

theorem jointEndpoint_eq_original (H : E → ℝ) (beta c lam m : ℝ) (z : Joint E) :
    jointEndpoint H beta c lam m z = PacketCore.saddleValue H beta c lam m z.fst z.snd := by
  dsimp [jointEndpoint, quadratic, PacketCore.saddleValue]
  ring

theorem K_apply (beta c lam : ℝ) (z : Joint E) :
    K beta c lam z = mk (beta • z.fst + lam • z.snd) (lam • z.fst + c • z.snd) := rfl

theorem K_symmetric (beta c lam : ℝ) : (K (E := E) beta c lam).toLinearMap.IsSymmetric := by
  intro z w
  change inner ℝ (K beta c lam z) w = inner ℝ z (K beta c lam w)
  change inner ℝ (beta • z.fst + lam • z.snd) w.fst + inner ℝ (lam • z.fst + c • z.snd) w.snd =
    inner ℝ z.fst (beta • w.fst + lam • w.snd) + inner ℝ z.snd (lam • w.fst + c • w.snd)
  simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right]
  ring

theorem quadratic_eq_half_inner (beta c lam : ℝ) (z : Joint E) :
    quadratic beta c lam z = (1 / 2 : ℝ) * (K beta c lam).reApplyInnerSelf z := by
  change quadratic beta c lam z = (1 / 2 : ℝ) *
    (inner ℝ (beta • z.fst + lam • z.snd) z.fst + inner ℝ (lam • z.fst + c • z.snd) z.snd)
  simp only [quadratic, inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq,
    real_inner_comm z.snd z.fst]
  ring

theorem quadratic_hasFDerivAt (beta c lam : ℝ) (z : Joint E) :
    HasFDerivAt (quadratic beta c lam) (innerSL ℝ (K beta c lam z)) z := by
  have heq : quadratic (E := E) beta c lam = fun z => (1 / 2 : ℝ) * (K beta c lam).reApplyInnerSelf z :=
    funext (quadratic_eq_half_inner beta c lam)
  rw [heq]
  have hh := ((K_symmetric (E := E) beta c lam).hasStrictFDerivAt_reApplyInnerSelf z).hasFDerivAt.const_mul (1 / 2 : ℝ)
  convert! hh using 1
  ext v
  simp only [two_smul, ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply, smul_eq_mul]
  ring

theorem quadratic_contDiff (beta c lam : ℝ) : ContDiff ℝ 2 (quadratic (E := E) beta c lam) := by
  have hx : ContDiff ℝ 2 (fun z : Joint E => ‖z.fst‖ ^ 2) := (xL (E := E)).contDiff.norm_sq ℝ
  have hy : ContDiff ℝ 2 (fun z : Joint E => ‖z.snd‖ ^ 2) := (yL (E := E)).contDiff.norm_sq ℝ
  have hi : ContDiff ℝ 2 (fun z : Joint E => inner ℝ z.fst z.snd) :=
    (xL (E := E)).contDiff.inner ℝ (yL (E := E)).contDiff
  exact ((contDiff_const.mul hx).add (contDiff_const.mul hi)).add (contDiff_const.mul hy)

theorem quadratic_hessian_constant (beta c lam : ℝ) (z : Joint E) :
    fderiv ℝ (fderiv ℝ (quadratic beta c lam)) z = (innerSL ℝ).comp (K beta c lam) := by
  have heq : fderiv ℝ (quadratic (E := E) beta c lam) =
      ((innerSL ℝ).comp (K beta c lam) : Joint E →L[ℝ] (Joint E →L[ℝ] ℝ)) := by
    funext z
    exact (quadratic_hasFDerivAt beta c lam z).fderiv
  rw [heq]
  exact ((innerSL ℝ (E := Joint E)).comp (K (E := E) beta c lam)).fderiv

theorem mk_norm_le (x y : E) : ‖mk x y‖ ≤ ‖x‖ + ‖y‖ := by
  have hh : ‖mk x y‖ ^ 2 = ‖x‖ ^ 2 + ‖y‖ ^ 2 := WithLp.prod_norm_sq_eq_of_L2 _
  nlinarith only [hh, norm_nonneg (mk x y), norm_nonneg x, norm_nonneg y, mul_nonneg (norm_nonneg x) (norm_nonneg y)]

theorem K_apply_norm_bound (beta c lam : ℝ) (hb : 0 ≤ beta) (hc : 0 ≤ c) (z : Joint E) :
    ‖K beta c lam z‖ ≤ (beta + c + 2 * |lam|) * ‖z‖ := by
  rw [K_apply]
  have h1 := norm_add_le (beta • z.fst) (lam • z.snd)
  have h2 := norm_add_le (lam • z.fst) (c • z.snd)
  simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg hb, abs_of_nonneg hc] at h1 h2
  have hm1 := mul_le_mul_of_nonneg_left (WithLp.norm_fst_le E z) hb
  have hm2 := mul_le_mul_of_nonneg_left (WithLp.norm_snd_le E z) (abs_nonneg lam)
  have hm3 := mul_le_mul_of_nonneg_left (WithLp.norm_fst_le E z) (abs_nonneg lam)
  have hm4 := mul_le_mul_of_nonneg_left (WithLp.norm_snd_le E z) hc
  have hh := mk_norm_le (beta • z.fst + lam • z.snd) (lam • z.fst + c • z.snd)
  nlinarith only [hh, h1, h2, hm1, hm2, hm3, hm4]

theorem K_norm_bound (beta c lam : ℝ) (hb : 0 ≤ beta) (hc : 0 ≤ c) :
    ‖K (E := E) beta c lam‖ ≤ beta + c + 2 * |lam| :=
  (K (E := E) beta c lam).opNorm_le_bound (by positivity) (K_apply_norm_bound beta c lam hb hc)

theorem quadratic_second_jet_bound (beta c lam : ℝ) (hb : 0 ≤ beta) (hc : 0 ≤ c) (z : Joint E) :
    ‖iteratedFDeriv ℝ 2 (quadratic beta c lam) z‖ ≤ beta + c + 2 * |lam| := by
  rw [← FangqingJetToRegularity.hessian_norm_eq_second_jet, quadratic_hessian_constant]
  exact (FangqingAmplifierRegularity.innerSL_comp_norm_le (K (E := E) beta c lam)).trans (K_norm_bound beta c lam hb hc)

theorem yL_norm_le_one : ‖yL (E := E)‖ ≤ 1 :=
  (yL (E := E)).opNorm_le_bound (by norm_num) (fun z => by simpa [yL] using! WithLp.norm_snd_le E z)

theorem second_jet_bound_from_gradient_rate (H : E → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hgrad : ∀ x y, ‖gradient H x - gradient H y‖ ≤ L * ‖x - y‖) (z : E) :
    ‖iteratedFDeriv ℝ 2 H z‖ ≤ L := by
  let Ln : ℝ≥0 := ⟨L, hL⟩
  have hg : LipschitzWith Ln (gradient H) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    change dist (gradient H x) (gradient H y) ≤ L * dist x y
    simpa only [dist_eq_norm] using hgrad x y
  have hdf : LipschitzWith Ln (fderiv ℝ H) := by
    simpa only [one_mul, Function.comp_def, toDual_gradient] using!
      (InnerProductSpace.toDual ℝ E).lipschitz.comp hg
  rw [← FangqingJetToRegularity.hessian_norm_eq_second_jet]
  exact norm_fderiv_le_of_lipschitz ℝ hdf

theorem second_jet_pullback_difference_bound {X Y : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (H : Y → ℝ) (hc : ContDiff ℝ 2 H) (P : X →L[ℝ] Y) (hP : ‖P‖ ≤ 1) (x y : X) :
    ‖iteratedFDeriv ℝ 2 (H ∘ P) x - iteratedFDeriv ℝ 2 (H ∘ P) y‖ ≤
      ‖iteratedFDeriv ℝ 2 H (P x) - iteratedFDeriv ℝ 2 H (P y)‖ := by
  rw [P.iteratedFDeriv_comp_right hc x le_rfl, P.iteratedFDeriv_comp_right hc y le_rfl]
  have heq : (iteratedFDeriv ℝ 2 H (P x)).compContinuousLinearMap (fun _ => P) -
      (iteratedFDeriv ℝ 2 H (P y)).compContinuousLinearMap (fun _ => P) =
      (iteratedFDeriv ℝ 2 H (P x) - iteratedFDeriv ℝ 2 H (P y)).compContinuousLinearMap (fun _ => P) := by
    ext v
    rfl
  rw [heq]
  have hh := (iteratedFDeriv ℝ 2 H (P x) - iteratedFDeriv ℝ 2 H (P y)).norm_compContinuousLinearMap_le (fun _ => P)
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hh
  have hp : ‖P‖ ^ 2 ≤ 1 := pow_le_one₀ (norm_nonneg P) hP
  exact hh.trans (by simpa only [mul_one] using
    mul_le_mul_of_nonneg_left hp (norm_nonneg (iteratedFDeriv ℝ 2 H (P x) - iteratedFDeriv ℝ 2 H (P y))))

theorem convex_add_linear_const (g : E → ℝ) (hc : ConvexOn ℝ (Set.univ : Set E) g)
    (L : E →L[ℝ] ℝ) (C : ℝ) : ConvexOn ℝ (Set.univ : Set E) (fun z => g z + L z + C) := by
  refine ⟨convex_univ, ?_⟩
  intro x hx y hy a b ha hb hab
  have hh := hc.2 hx hy ha hb hab
  have hC := congrArg (fun t : ℝ => t * C) hab
  simp only [smul_eq_mul] at hh
  simp only [map_add, map_smul, smul_eq_mul]
  nlinarith only [hh, hC]

theorem actual_dual_strongConvex (H : E → ℝ) (beta c lam m nu : ℝ)
    (hSC : StrongConvexOn (Set.univ : Set E) nu H) (x : E) :
    StrongConvexOn (Set.univ : Set E) (nu - c) (fun y => -jointEndpoint H beta c lam m (mk x y)) := by
  apply strongConvexOn_iff_convex.mpr
  have hc := strongConvexOn_iff_convex.mp hSC
  have h := convex_add_linear_const (fun y => H y - nu / 2 * ‖y‖ ^ 2) hc
    ((-lam) • innerSL ℝ x) (-beta / 2 * ‖x‖ ^ 2 - m)
  have heq : (fun y => -jointEndpoint H beta c lam m (mk x y) - (nu - c) / 2 * ‖y‖ ^ 2) =
      (fun y => (H y - nu / 2 * ‖y‖ ^ 2) + ((-lam) • innerSL ℝ x) y + (-beta / 2 * ‖x‖ ^ 2 - m)) := by
    funext y
    change -(beta / 2 * ‖x‖ ^ 2 + lam * inner ℝ x y + c / 2 * ‖y‖ ^ 2 - H y + m) -
      (nu - c) / 2 * ‖y‖ ^ 2 =
      (H y - nu / 2 * ‖y‖ ^ 2) + (-lam) * inner ℝ x y + (-beta / 2 * ‖x‖ ^ 2 - m)
    ring
  rw [heq]
  exact h

theorem actual_joint_endpoint_class (H : E → ℝ) (beta c lam m nu LH rho : ℝ)
    (hb : 0 ≤ beta) (hc : 0 ≤ c) (hLH : 0 ≤ LH) (hrho : 0 ≤ rho)
    (hH : ContDiff ℝ 2 H) (hSC : StrongConvexOn (Set.univ : Set E) nu H)
    (hgrad : ∀ x y, ‖gradient H x - gradient H y‖ ≤ LH * ‖x - y‖)
    (hhess : ∀ x y, ‖fderiv ℝ (fderiv ℝ H) x - fderiv ℝ (fderiv ℝ H) y‖ ≤ rho * ‖x - y‖) :
    ContDiff ℝ 2 (jointEndpoint H beta c lam m) ∧
    (∀ x, StrongConvexOn (Set.univ : Set E) (nu - c) (fun y => -jointEndpoint H beta c lam m (mk x y))) ∧
    (∀ x y, ‖gradient (jointEndpoint H beta c lam m) x - gradient (jointEndpoint H beta c lam m) y‖ ≤
      (beta + c + 2 * |lam| + LH) * ‖x - y‖) ∧
    (∀ x y, ‖iteratedFDeriv ℝ 2 (jointEndpoint H beta c lam m) x -
      iteratedFDeriv ℝ 2 (jointEndpoint H beta c lam m) y‖ ≤ rho * ‖x - y‖) := by
  let F := jointEndpoint H beta c lam m
  let Q : Joint E → ℝ := quadratic beta c lam
  let Hc : Joint E → ℝ := H ∘ yL
  have hQ : ContDiff ℝ 2 Q := quadratic_contDiff beta c lam
  have hHc : ContDiff ℝ 2 Hc := hH.comp (yL (E := E)).contDiff
  have hF : ContDiff ℝ 2 F := (hQ.sub hHc).add contDiff_const
  have hjet : ∀ z, iteratedFDeriv ℝ 2 F z = iteratedFDeriv ℝ 2 Q z - iteratedFDeriv ℝ 2 Hc z := by
    intro z
    change iteratedFDeriv ℝ 2 (fun z => Q z - Hc z + m) z = _
    rw [fun_iteratedFDeriv_add_apply (hQ.sub hHc).contDiffAt contDiffAt_const,
      fun_iteratedFDeriv_sub_apply hQ.contDiffAt hHc.contDiffAt, iteratedFDeriv_const_of_ne (by decide)]
    simp only [Pi.zero_apply, add_zero]
  have hH2 : ∀ z, ‖iteratedFDeriv ℝ 2 H z‖ ≤ LH := second_jet_bound_from_gradient_rate H LH hLH hgrad
  have hHc2 : ∀ z, ‖iteratedFDeriv ℝ 2 Hc z‖ ≤ LH := by
    intro z
    exact (FangqingRelayProductBounds.norm_iterated_comp_contraction H (yL (E := E)) 2 hH yL_norm_le_one z 2 le_rfl).trans (hH2 _)
  have hF2 : ∀ z, ‖iteratedFDeriv ℝ 2 F z‖ ≤ beta + c + 2 * |lam| + LH := by
    intro z
    rw [hjet]
    exact (norm_sub_le _ _).trans (add_le_add (quadratic_second_jet_bound beta c lam hb hc z) (hHc2 z))
  have hFgrad := FangqingJetToRegularity.gradient_lipschitz_from_second_jet F hF
    ⟨beta + c + 2 * |lam| + LH, by positivity⟩ hF2
  refine ⟨hF, actual_dual_strongConvex H beta c lam m nu hSC, fun x y => hFgrad.norm_sub_le x y, ?_⟩
  intro x y
  have hQconst : iteratedFDeriv ℝ 2 Q x = iteratedFDeriv ℝ 2 Q y := by
    ext v
    simp only [iteratedFDeriv_two_apply]
    rw [quadratic_hessian_constant, quadratic_hessian_constant]
  have heq : iteratedFDeriv ℝ 2 F x - iteratedFDeriv ℝ 2 F y =
      -(iteratedFDeriv ℝ 2 Hc x - iteratedFDeriv ℝ 2 Hc y) := by
    rw [hjet x, hjet y, hQconst]
    abel
  rw [heq, norm_neg]
  have hh : ‖iteratedFDeriv ℝ 2 H (yL x) - iteratedFDeriv ℝ 2 H (yL y)‖ ≤ rho * ‖yL x - yL y‖ := by
    rw [FangqingHessianTensorIsometry.second_jet_difference_eq_hessian]
    exact hhess _ _
  have hp : ‖yL x - yL y‖ ≤ ‖x - y‖ := by
    rw [← map_sub]
    exact WithLp.norm_snd_le E (x - y)
  exact (second_jet_pullback_difference_bound H hH (yL (E := E)) yL_norm_le_one x y).trans
    (hh.trans (mul_le_mul_of_nonneg_left hp hrho))


def HessianRate {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (F : X → ℝ) (rho : ℝ) : Prop :=
  ∀ x y, ‖fderiv ℝ (fderiv ℝ F) x - fderiv ℝ (fderiv ℝ F) y‖ ≤ rho * ‖x - y‖

theorem actual_joint_endpoint_full_class (H : E → ℝ) (beta c lam m nu LH rho : ℝ)
    (hb : 0 ≤ beta) (hc : 0 ≤ c) (hLH : 0 ≤ LH) (hrho : 0 ≤ rho)
    (hH : ContDiff ℝ 2 H) (hSC : StrongConvexOn (Set.univ : Set E) nu H)
    (hgrad : ∀ x y, ‖gradient H x - gradient H y‖ ≤ LH * ‖x - y‖)
    (hhess : ∀ x y, ‖fderiv ℝ (fderiv ℝ H) x - fderiv ℝ (fderiv ℝ H) y‖ ≤ rho * ‖x - y‖) :
    ContDiff ℝ 2 (jointEndpoint H beta c lam m) ∧
    (∀ x, StrongConvexOn (Set.univ : Set E) (nu - c) (fun y => -jointEndpoint H beta c lam m (mk x y))) ∧
    (∀ x y, ‖gradient (jointEndpoint H beta c lam m) x - gradient (jointEndpoint H beta c lam m) y‖ ≤
      (beta + c + 2 * |lam| + LH) * ‖x - y‖) ∧
    HessianRate (jointEndpoint H beta c lam m) rho := by
  obtain ⟨hF, hSCF, hGF, h2F⟩ := actual_joint_endpoint_class H beta c lam m nu LH rho hb hc hLH hrho hH hSC hgrad hhess
  exact ⟨hF, hSCF, hGF, fun x y =>
    (FangqingJetToRegularity.hessian_difference_norm_le_second_jet _ x y).trans (h2F x y)⟩


end
end FangqingFenchelEndpointClass


open scoped ContDiff

namespace FangqingActiveShellLargerWidth

open FangqingActualInactivePacket FangqingActiveShellClass FangqingLocalizedSeedJets
  FangqingC2SmallPerturbation FangqingHessianTensorIsometry FangqingPublicShellProfiles

noncomputable section

theorem actual_large_width_curvature (Ks Cs nu D A : ℝ)
    (hKs : 0 ≤ Ks) (hCs : 0 ≤ Cs) (hnu : 0 ≤ nu) (hA : 0 < A)
    (hwidth : 2 * Ks * Cs * D ≤ A) :
    Ks * ((Cs * nu * D) * A) / A ^ 2 ≤ nu / 2 := by
  have heq : Ks * ((Cs * nu * D) * A) / A ^ 2 = Ks * Cs * nu * D / A := by
    field_simp [ne_of_gt hA]
    <;> try ring
  rw [heq]
  apply (div_le_iff₀ hA).mpr
  have hm := mul_le_mul_of_nonneg_left hwidth (by positivity : 0 ≤ nu / 2)
  convert! hm using 1 <;> try ring

theorem larger_width_choice (Ks Cs Cmin D : ℝ)
    (hKs : 0 ≤ Ks) (hCs : 0 ≤ Cs) (hCmin : 0 ≤ Cmin) (hD : 0 < D) :
    let A := (1 + 2 * Ks * Cs + Cmin) * D
    D ≤ A ∧ 2 * Ks * Cs * D ≤ A ∧ Cmin * D < A := by
  intro A
  have hk : 0 ≤ 2 * Ks * Cs := by positivity
  have hkD : 0 ≤ 2 * Ks * Cs * D := by positivity
  have hmD : 0 ≤ Cmin * D := by positivity
  dsimp [A]
  constructor
  · nlinarith only [hkD, hmD]
  constructor
  · nlinarith only [hmD, hD]
  · nlinarith only [hkD, hD]

universe u

theorem actual_seeded_shell_any_larger_width
    (phi : ℝ → ℝ) (B left right Cs : ℝ) (hCs : 0 ≤ Cs)
    (hp : ContDiff ℝ 3 phi) (hl : ∀ t, t < -B → phi t = left) (hr : ∀ t, B < t → phi t = right) :
    ∃ Ks : ℝ, 0 ≤ Ks ∧ ∀ (F : Type u)
      [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F],
      ∀ (H0 : F → ℝ) (nu L0 rho0 D A R : ℝ) (handle : F),
      AnalyticClass H0 nu L0 rho0 → 0 ≤ nu → 0 ≤ L0 →
      0 < D → D ≤ A → 2 * Ks * Cs * D ≤ A → A ≤ R → ‖handle‖ ≤ 1 →
      let s := Cs * nu * D
      let H1 := fun z => H0 z - localizedSeed theta phi R A (s * A) handle z
      AnalyticClass H1 (nu / 2) (L0 + Ks * (s * A) / A ^ 2) (rho0 + Ks * (s * A) / A ^ 3) := by
  obtain ⟨Ks, hKs, hSeed⟩ := universal_actual_seed_jets.{u} phi B left right hp hl hr
  refine ⟨Ks, hKs, ?_⟩
  intro F inst inst' inst'' H0 nu L0 rho0 D A R handle hH0 hnu hL0 hD hDA hwidth hAR hh s H1
  have hA : 0 < A := hD.trans_le hDA
  have hs : 0 ≤ s := by dsimp [s]; positivity
  obtain ⟨hSC, hSJ⟩ := hSeed F R A (s * A) handle hA hAR (mul_nonneg hs hA.le) hh
  have hH02 := FangqingFenchelEndpointClass.second_jet_bound_from_gradient_rate H0 L0 hL0 hH0.2.2.1
  have hH0Lip : ∀ x y, ‖iteratedFDeriv ℝ 2 H0 x - iteratedFDeriv ℝ 2 H0 y‖ ≤ rho0 * ‖x - y‖ := by
    intro x y
    rw [second_jet_difference_eq_hessian]
    exact hH0.2.2.2 x y
  let S := Ks * (s * A) / A ^ 2
  let T := Ks * (s * A) / A ^ 3
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have hT : 0 ≤ T := by dsimp [T]; positivity
  obtain ⟨hc, hsc, h2, hLip⟩ := actual_small_perturbation H0
    (localizedSeed theta phi R A (s * A) handle) nu L0 rho0 S T hH0.1 hSC hH0.2.1 hS hT
    hH02 hH0Lip (hSJ 2 (by norm_num)) (hSJ 3 (by norm_num))
  have hsmall : S ≤ nu / 2 := actual_large_width_curvature Ks Cs nu D A hKs hCs hnu hA hwidth
  have hmod : nu / 2 ≤ nu - S := by linarith only [hsmall]
  exact class_of_actual_jets H1 (nu / 2) (L0 + S) (rho0 + T) (add_nonneg hL0 hS) hc (hsc.mono hmod) h2 hLip

end
end FangqingActiveShellLargerWidth


open scoped Topology ContDiff

namespace FangqingShellMinimizerTransfer

open FangqingInactiveShellClass FangqingLocalizedSeedJets FangqingPublicShellProfiles
  FangqingRadialCollar FangqingRadialCollarEtaBridge

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem actual_collar_zero_inner (R : ℝ) (hR : 0 < R) (z : E) (hz : ‖z‖ ≤ R) : collar psi R z = 0 := by
  have hratio : ‖z‖ / R ≤ 1 := (div_le_one hR).mpr hz
  have hh := literal_paper_collar_eq psi psi_smooth.continuous psi_zero R hR z
  rw [eta, if_pos hratio, mul_zero] at hh
  exact hh.symm

theorem actual_active_shell_inner_eq (Q g : E → ℝ) (phi : ℝ → ℝ)
    (R A s gain : ℝ) (hR : 0 < R) (hA : 0 < A) (handle z : E) (hh : ‖handle‖ ≤ 1)
    (hphi : ∀ t, |t| < 1 → phi t = t) (hzR : ‖z‖ < R) (hzA : ‖z‖ < A) :
    inactiveShell Q g R gain z - localizedSeed theta phi R A (s * A) handle z =
      Q z + g z - s * inner ℝ handle z := by
  have hin : |inner ℝ handle z| < A := by
    have h1 := abs_real_inner_le_norm handle z
    have h2 := mul_le_mul_of_nonneg_right hh (norm_nonneg z)
    rw [one_mul] at h2
    exact (h1.trans h2).trans_lt hzA
  have harg : |inner ℝ handle z / A| < 1 := by
    rw [abs_div, abs_of_pos hA]
    exact (div_lt_one hA).mpr hin
  have ht := actual_cutoff_one_inside R hR z (by linarith only [hzR, hR])
  have hc := actual_collar_zero_inner R hR z hzR.le
  dsimp [inactiveShell, localizedSeed, FangqingLinearProfileJetBounds.linearProfile]
  rw [ht, hc, hphi _ harg]
  simp only [one_mul, mul_zero, add_zero]
  field_simp [ne_of_gt hA]
  <;> try ring

theorem actual_active_shell_eventually_eq_raw (Q g : E → ℝ) (phi : ℝ → ℝ)
    (R A s gain : ℝ) (hR : 0 < R) (hA : 0 < A) (handle z : E) (hh : ‖handle‖ ≤ 1)
    (hphi : ∀ t, |t| < 1 → phi t = t) (hzR : ‖z‖ < R) (hzA : ‖z‖ < A) :
    (fun z => inactiveShell Q g R gain z - localizedSeed theta phi R A (s * A) handle z)
      =ᶠ[𝓝 z] (fun z => Q z + g z - s * inner ℝ handle z) := by
  have hn : {y : E | ‖y‖ < min R A} ∈ 𝓝 z :=
    (isOpen_lt continuous_norm continuous_const).mem_nhds (lt_min hzR hzA)
  filter_upwards [hn] with y hy
  exact actual_active_shell_inner_eq Q g phi R A s gain hR hA handle y hh hphi
    (lt_min_iff.mp hy).1 (lt_min_iff.mp hy).2

theorem global_minimum_of_actual_local_eq (F G : E → ℝ) (nu : ℝ) (hnu : 0 < nu)
    (hc : ContDiff ℝ 2 F) (hs : StrongConvexOn (Set.univ : Set E) nu F) (z : E)
    (hmin : ∀ y, G z ≤ G y) (heq : F =ᶠ[𝓝 z] G) :
    (∀ y, F z ≤ F y) ∧ (∀ y, (∀ w, F y ≤ F w) → y = z) := by
  have hloc : IsLocalMin F z := by
    filter_upwards [heq] with y hy
    rw [heq.eq_of_nhds, hy]
    exact hmin y
  have hgrad : gradient F z = 0 := by
    simp only [gradient, hloc.fderiv_eq_zero, map_zero]
  have hminF : ∀ y, F z ≤ F y := by
    intro y
    have hh := PacketCore.strongConvex_support F nu hs (hc.differentiable (by norm_num)) z y
    rw [hgrad, inner_zero_left] at hh
    have hn : 0 ≤ nu / 2 * ‖y - z‖ ^ 2 := by positivity
    linarith only [hh, hn]
  refine ⟨hminF, ?_⟩
  intro y hy
  have hgy := PacketCore.gradient_eq_zero_at_global_min F y hy
  have hh := PacketCore.strongConvex_gradient_distance F nu hnu hs (hc.differentiable (by norm_num)) z hminF y
  rw [hgy, norm_zero] at hh
  have hn : ‖y - z‖ = 0 := le_antisymm (nonpos_of_mul_nonpos_right hh hnu) (norm_nonneg (y - z))
  exact sub_eq_zero.mp (norm_eq_zero.mp hn)

theorem actual_active_minimizer_preserved (Q g : E → ℝ) (phi : ℝ → ℝ)
    (R A s gain nu : ℝ) (hR : 0 < R) (hA : 0 < A) (hnu : 0 < nu)
    (handle z : E) (hh : ‖handle‖ ≤ 1) (hphi : ∀ t, |t| < 1 → phi t = t)
    (hzR : ‖z‖ < R) (hzA : ‖z‖ < A)
    (hmin : ∀ y, Q z + g z - s * inner ℝ handle z ≤ Q y + g y - s * inner ℝ handle y)
    (hc : ContDiff ℝ 2 (fun y => inactiveShell Q g R gain y - localizedSeed theta phi R A (s * A) handle y))
    (hs : StrongConvexOn (Set.univ : Set E) nu
      (fun y => inactiveShell Q g R gain y - localizedSeed theta phi R A (s * A) handle y)) :
    let H1 := fun y => inactiveShell Q g R gain y - localizedSeed theta phi R A (s * A) handle y
    (∀ y, H1 z ≤ H1 y) ∧ (∀ y, (∀ w, H1 y ≤ H1 w) → y = z) := by
  intro H1
  exact global_minimum_of_actual_local_eq H1 (fun y => Q y + g y - s * inner ℝ handle y) nu hnu hc hs z hmin
    (actual_active_shell_eventually_eq_raw Q g phi R A s gain hR hA handle z hh hphi hzR hzA)

end
end FangqingShellMinimizerTransfer


namespace FangqingInactiveShellMinimum

open FangqingInactiveShellClass FangqingPublicShellProfiles FangqingRadialCollar FangqingRadialCollarEtaBridge

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem actual_collar_nonnegative (R : ℝ) (hR : 0 < R) (z : E) : 0 ≤ collar psi R z := by
  have hh := literal_paper_collar_eq psi psi_smooth.continuous psi_zero R hR z
  rw [← hh]
  have heta : 0 ≤ eta psi (‖z‖ / R) := by
    by_cases hr : ‖z‖ / R ≤ 1
    · rw [eta, if_pos hr]
    · rw [eta, if_neg hr]
      apply intervalIntegral.integral_nonneg (le_of_lt (lt_of_not_ge hr))
      intro t ht
      exact mul_nonneg (le_trans (by norm_num : (0 : ℝ) ≤ 1) ht.1) (psi_range _).1
  exact mul_nonneg (sq_nonneg R) heta

theorem actual_inactive_minimum_zero (Q g : E → ℝ) (R gain : ℝ) (hR : 0 < R) (hgain : 0 ≤ gain)
    (hQ : ∀ z, 0 ≤ Q z) (hg : ∀ z, 0 ≤ g z) (hQ0 : Q 0 = 0) (hg0 : g 0 = 0) :
    ∀ z, inactiveShell Q g R gain 0 ≤ inactiveShell Q g R gain z := by
  have hcol0 := FangqingShellMinimizerTransfer.actual_collar_zero_inner R hR (0 : E) (by simpa using hR.le)
  intro z
  dsimp [inactiveShell]
  rw [hQ0, hg0, mul_zero, hcol0, mul_zero, zero_add, add_zero]
  have hc := mul_nonneg hgain (actual_collar_nonnegative R hR z)
  have hprod : 0 ≤ FangqingRadialGateBounds.scaledGate theta R 0 z * g z :=
    mul_nonneg (theta_range (‖z - (0 : E)‖ ^ 2 / R ^ 2)).1 (hg z)
  linarith only [hQ z, hc, hprod]

end
end FangqingInactiveShellMinimum


open scoped BigOperators ContDiff

namespace FangqingPhysicalPairedShellMinimizers

open FangqingAmplifier FangqingPacketLeakage FangqingPathEdgeRegularity
  FangqingActualInactivePacket FangqingInactiveShellClass FangqingLocalizedSeedJets
  FangqingActiveShellLargerWidth FangqingShellMinimizerTransfer FangqingInactiveShellMinimum
  FangqingPublicShellProfiles OriginalPacketOrientationNormalization
  OriginalPhysicalPacketMinimizer OriginalPacketDistanceGapBounds

set_option maxHeartbeats 3000000

noncomputable section

universe u

theorem actual_physical_paired_shell_same_minimum
    (P : FlatCubic.Profile) (phi : ℝ → ℝ) (Bp left right Cm Cw : ℝ)
    (hCm : 0 ≤ Cm) (hCw : 4 * (Cm + 2) ≤ Cw)
    (hp : ContDiff ℝ 3 phi) (hl : ∀ t, t < -Bp → phi t = left) (hr : ∀ t, Bp < t → phi t = right)
    (hcore : ∀ t, |t| < 1 → phi t = t) :
    ∃ Ce : ℝ≥0, ∃ K : ℝ, 0 ≤ K ∧ ∃ Kc : ℝ, 0 ≤ Kc ∧ ∃ Ks : ℝ, 0 ≤ Ks ∧
    ∀ (A0 B0 W : Type u)
      [NormedAddCommGroup A0] [InnerProductSpace ℝ A0] [FiniteDimensional ℝ A0]
      [NormedAddCommGroup B0] [InnerProductSpace ℝ B0] [FiniteDimensional ℝ B0]
      [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W],
    ∀ (C : A0 ≃ₗᵢ[ℝ] B0) (h : A0) (n : ℕ) (tail : Fin (n + 2) → W)
      (delta omega q scale lam : ℝ),
      ‖h‖ = 1 → Orthonormal ℝ tail → 0 < delta → delta ≤ omega → 1 ≤ q →
      0 < scale → 0 < lam → omega = Cw * lam * q ^ 2 → ((n + 2 : ℕ) : ℝ) ≤ Cm * q →
      let nu := scale * lam
      let D := distanceScale q omega
      let Cs := 2 * Cw
      let Cmin := 2 * Cw * (Cm + 2)
      let A := (1 + 2 * Ks * Cs + Cmin) * D
      let R := 2 * A
      let s := Cs * nu * D
      let Q := QPhysical q nu C
      let g := fun z => scale * pathEdge P delta omega (n + 2) (physicalFrame C h n tail) z
      let M : ℝ := (4 * Ce : ℝ) * scale * omega
      let gain := (16 * K + 1) * M
      let F0 := inactiveShell Q g R gain
      let F1 := fun z => F0 z - localizedSeed theta phi R A (s * A) (mkPhysical h 0 0) z
      let L0 := nu * (q + 2) + 16 * K * M + gain * Kc
      let rho0 := K * ((8 * Ce : ℝ) * scale) + 21 * K * M / R + gain * (Kc / R)
      AnalyticClass F0 nu L0 rho0 ∧
      AnalyticClass F1 (nu / 2) (L0 + Ks * (s * A) / A ^ 2) (rho0 + Ks * (s * A) / A ^ 3) ∧
      (∀ Y, F0 0 ≤ F0 Y) ∧
      ∃ Z : PhysicalSpace A0 B0 W,
        (∀ Y, F1 Z ≤ F1 Y) ∧ (∀ Y, (∀ X, F1 Y ≤ F1 X) → Y = Z) ∧
        ‖Z‖ ≤ Cmin * D ∧
        F1 0 - F1 Z ≤ 4 * Cw ^ 2 * nu * D ^ 2 ∧
        (∀ j : Fin (n + 3), (j.val : ℝ) ≤ q → 3 * q * omega ≤ inner ℝ (physicalFrame C h n tail j) Z) := by
  have hCw0 : 0 ≤ Cw := by linarith only [hCm, hCw]
  have hCs : 0 ≤ 2 * Cw := by positivity
  have hCmin : 0 ≤ 2 * Cw * (Cm + 2) := by positivity
  obtain ⟨Ce, K, hK, Kc, hKc, hInactive⟩ := actual_inactive_packet_class.{u} P
  obtain ⟨Ks, hKs, hWide⟩ := actual_seeded_shell_any_larger_width.{u} phi Bp left right (2 * Cw) hCs hp hl hr
  refine ⟨Ce, K, hK, Kc, hKc, Ks, hKs, ?_⟩
  intro A0 B0 W inst inst' inst'' instB instB' instB'' instW instW' instW'' C h n tail
    delta omega q scale lam hh ht hd hdw hq hscale hlam homega hn nu D Cs Cmin A R s Q g M gain F0 F1 L0 rho0
  have hq0 : 0 < q := by linarith only [hq]
  have hw : 0 < omega := hd.trans_le hdw
  have hnu : 0 < nu := mul_pos hscale hlam
  have hD : 0 < D := by dsimp [D, distanceScale]; positivity
  obtain ⟨hDA, hwidth, hCminA⟩ := larger_width_choice Ks Cs Cmin D hKs hCs hCmin hD
  have hA : 0 < A := hD.trans_le hDA
  have hAR : A ≤ R := by dsimp [R]; linarith only [hA]
  have hR : 0 < R := hA.trans_le hAR
  have hv := physicalFrame_orthonormal C h hh n tail ht
  obtain ⟨hF0, _, _⟩ := hInactive A0 B0 W q nu scale delta omega R C (n + 2) (physicalFrame C h n tail)
    hq0.le hnu.le hscale.le hd hdw hR hv
  have hhandle : ‖mkPhysical h (0 : B0) (0 : W)‖ ≤ 1 := by
    have hn1 := WithLp.prod_norm_sq_eq_of_L2 (mkPhysical h (0 : B0) (0 : W))
    have hn2 := WithLp.prod_norm_sq_eq_of_L2 (WithLp.toLp 2 (h, (0 : B0)))
    change ‖mkPhysical h (0 : B0) (0 : W)‖ ^ 2 = ‖WithLp.toLp 2 (h, (0 : B0))‖ ^ 2 + ‖(0 : W)‖ ^ 2 at hn1
    change ‖WithLp.toLp 2 (h, (0 : B0))‖ ^ 2 = ‖h‖ ^ 2 + ‖(0 : B0)‖ ^ 2 at hn2
    rw [hh, norm_zero] at hn2
    rw [norm_zero] at hn1
    nlinarith only [hn1, hn2, norm_nonneg (mkPhysical h (0 : B0) (0 : W))]
  have hL0 : 0 ≤ L0 := by dsimp [L0, M, gain]; positivity
  have hF1 := hWide (PhysicalSpace A0 B0 W) F0 nu L0 rho0 D A R (mkPhysical h 0 0)
    hF0 hnu.le hL0 hD hDA hwidth hAR hhandle
  have hQnon : ∀ Y : PhysicalSpace A0 B0 W, 0 ≤ Q Y := by
    intro Y
    rw [show Q Y = (1 / 2 : ℝ) * inner ℝ (HPhysical q nu C Y) Y from QPhysical_eq_half_inner q nu C Y]
    exact mul_nonneg (by norm_num) ((mul_nonneg hnu.le (sq_nonneg _)).trans (physical_rayleigh_bounds q nu hq0.le hnu.le C Y).1)
  have hgnon : ∀ Y : PhysicalSpace A0 B0 W, 0 ≤ g Y := by
    intro Y
    apply mul_nonneg hscale.le
    unfold pathEdge edgeSum
    exact Finset.sum_nonneg (fun i _ => actual_edge_nonnegative P delta omega hd hdw _)
  have hg0 : g 0 = 0 := by
    have hj := (FlatCubic.edge_flat_jets_closed P delta omega 0 hd hdw (by simp only [abs_zero]; linarith only [hd])).1
    simp only [g, pathEdge, edgeSum, inner_zero_right, hj, Finset.sum_const_zero, mul_zero]
  have hQ0 : Q 0 = 0 := by simp [Q, QPhysical]
  have hGain : 0 ≤ gain := by dsimp [gain, M]; positivity
  have hMin0 := actual_inactive_minimum_zero Q g R gain hR hGain hQnon hgnon hQ0 hg0
  refine ⟨hF0, hF1, hMin0, ?_⟩
  obtain ⟨Z, hm, hu, hnorm, hgap, hbulk⟩ := actual_physical_minimizer_norm_gap_bulk P C h hh n tail ht
    delta omega q Cm Cw scale lam hd hdw hq hCm hCw hscale hlam homega hn
  have hzA : ‖Z‖ < A := hnorm.trans_lt hCminA
  have hzR : ‖Z‖ < R := hzA.trans_le hAR
  have hseed := actual_seed_ratio q omega Cw lam scale hq0 homega
  have hi : ∀ Y : PhysicalSpace A0 B0 W, inner ℝ (mkPhysical h (0 : B0) (0 : W)) Y = inner ℝ h Y.fst.fst := by
    intro Y
    change (inner ℝ h Y.fst.fst + inner ℝ (0 : B0) Y.fst.snd) + inner ℝ (0 : W) Y.snd = _
    simp only [inner_zero_left, add_zero]
  have hRaw : ∀ Y : PhysicalSpace A0 B0 W,
      rawPacket C h n tail (FlatCubic.edge P delta omega) q nu scale (scale * (2 * omega ^ 2 / Real.sqrt q)) Y =
        Q Y + g Y - s * inner ℝ (mkPhysical h (0 : B0) (0 : W)) Y := by
    intro Y
    rw [rawPacket_literal, hseed, hi]
    rfl
  have hrawmin : ∀ Y, Q Z + g Z - s * inner ℝ (mkPhysical h (0 : B0) (0 : W)) Z ≤
      Q Y + g Y - s * inner ℝ (mkPhysical h (0 : B0) (0 : W)) Y := by
    intro Y
    rw [← hRaw Z, ← hRaw Y]
    exact hm Y
  obtain ⟨hm1, hu1⟩ := actual_active_minimizer_preserved Q g phi R A s gain (nu / 2) hR hA (half_pos hnu)
    (mkPhysical h 0 0) Z hhandle hcore hzR hzA hrawmin hF1.1 hF1.2.1
  have hzval := actual_active_shell_inner_eq Q g phi R A s gain hR hA (mkPhysical h 0 0) Z hhandle hcore hzR hzA
  have h0val := actual_active_shell_inner_eq Q g phi R A s gain hR hA (mkPhysical h 0 0) (0 : PhysicalSpace A0 B0 W)
    hhandle hcore (by simpa using hR) (by simpa using hA)
  refine ⟨Z, hm1, hu1, hnorm, ?_, hbulk⟩
  change (inactiveShell Q g R gain 0 - localizedSeed theta phi R A (s * A) (mkPhysical h 0 0) 0) -
    (inactiveShell Q g R gain Z - localizedSeed theta phi R A (s * A) (mkPhysical h 0 0) Z) ≤ _
  rw [hzval, h0val, ← hRaw Z, ← hRaw 0]
  exact hgap

end
end FangqingPhysicalPairedShellMinimizers


namespace FangqingSeedWidthMonotonic

theorem actual_seed_rates_antitone_width (Ks s A0 A : ℝ)
    (hKs : 0 ≤ Ks) (hs : 0 ≤ s) (hA0 : 0 < A0) (hAA : A0 ≤ A) :
    Ks * (s * A) / A ^ 2 ≤ Ks * (s * A0) / A0 ^ 2 ∧
    Ks * (s * A) / A ^ 3 ≤ Ks * (s * A0) / A0 ^ 3 := by
  have hA : 0 < A := hA0.trans_le hAA
  have heq1 (B : ℝ) (hB : 0 < B) : Ks * (s * B) / B ^ 2 = Ks * s / B := by
    field_simp [ne_of_gt hB]
    <;> try ring
  have heq2 (B : ℝ) (hB : 0 < B) : Ks * (s * B) / B ^ 3 = Ks * s / B ^ 2 := by
    field_simp [ne_of_gt hB]
    <;> try ring
  constructor
  · rw [heq1 A hA, heq1 A0 hA0]
    exact div_le_div_of_nonneg_left (mul_nonneg hKs hs) hA0 hAA
  · rw [heq2 A hA, heq2 A0 hA0]
    exact div_le_div_of_nonneg_left (mul_nonneg hKs hs) (sq_pos_of_pos hA0)
      (pow_le_pow_left₀ hA0.le hAA 2)

end FangqingSeedWidthMonotonic


namespace FangqingPairedShellScaleBudgets

noncomputable section

theorem actual_original_rate_budgets (Ce K Kc Ks Cs Cw q nu scale omega D R : ℝ)
    (hCe : 0 ≤ Ce) (hK : 0 ≤ K) (hKc : 0 ≤ Kc) (hKs : 0 ≤ Ks) (hCs : 0 ≤ Cs)
    (hCw : 1 ≤ Cw) (hq : 1 ≤ q) (hnu : 0 ≤ nu) (hscale : 0 ≤ scale)
    (homega : 0 < omega) (hDomega : omega ≤ D)
    (hscaleomega : scale * omega = Cw * nu * q ^ 2)
    (hRA : (1 + 2 * Ks * Cs) * D ≤ R) :
    let A := (1 + 2 * Ks * Cs) * D
    let s := Cs * nu * D
    let M := 4 * Ce * scale * omega
    let gain := (16 * K + 1) * M
    let S := Ks * (s * A) / A ^ 2
    let T := Ks * (s * A) / A ^ 3
    nu * (q + 2) + 16 * K * M + gain * Kc + S ≤
      (7 / 2 + 4 * Ce * Cw * (16 * K + (16 * K + 1) * Kc)) * nu * q ^ 2 ∧
    K * (8 * Ce * scale) + 21 * K * M / R + gain * (Kc / R) + T ≤
      (8 * K * Ce + 4 * Ce * (21 * K + (16 * K + 1) * Kc) + Ks * Cs) * scale := by
  intro A s M gain S T
  have hD : 0 < D := homega.trans_le hDomega
  have hCA : 1 ≤ 1 + 2 * Ks * Cs := by
    have hm : 0 ≤ 2 * Ks * Cs := by positivity
    linarith only [hm]
  have hDA : D ≤ A := by
    have hh := mul_le_mul_of_nonneg_right hCA hD.le
    simpa only [one_mul] using hh
  have hA : 0 < A := hD.trans_le hDA
  have hR : 0 < R := hA.trans_le hRA
  have hq2 : 1 ≤ q ^ 2 := by nlinarith only [hq, sq_nonneg (q - 1)]
  have hnuq : nu ≤ nu * q ^ 2 := by simpa only [mul_one] using mul_le_mul_of_nonneg_left hq2 hnu
  have hCwq : nu * q ^ 2 ≤ Cw * nu * q ^ 2 := by
    have hh := mul_le_mul_of_nonneg_right hCw (mul_nonneg hnu (sq_nonneg q))
    convert! hh using 1 <;> try ring
  have hnuscale : nu ≤ scale * omega := by rw [hscaleomega]; exact hnuq.trans hCwq
  have hS : S ≤ nu / 2 := FangqingActiveShellClass.actual_width_curvature_reserve Ks Cs nu D hKs hCs hnu hD
  have hqlinear : q + 2 ≤ 3 * q ^ 2 := by nlinarith only [hq, sq_nonneg (q - 1)]
  have hnulinear := mul_le_mul_of_nonneg_left hqlinear hnu
  have hfirst : nu * (q + 2) + S ≤ (7 / 2 : ℝ) * nu * q ^ 2 := by nlinarith only [hnulinear, hS, hnuq]
  have hMpart : 16 * K * M + gain * Kc =
      4 * Ce * Cw * (16 * K + (16 * K + 1) * Kc) * nu * q ^ 2 := by
    dsimp [gain, M]
    calc
      _ = 4 * Ce * (16 * K + (16 * K + 1) * Kc) * (scale * omega) := by ring
      _ = _ := by rw [hscaleomega]; ring
  have hRomega : omega ≤ R := hDomega.trans (hDA.trans hRA)
  have hMR : M / R ≤ 4 * Ce * scale := by
    apply (div_le_iff₀ hR).mpr
    exact mul_le_mul_of_nonneg_left hRomega (by positivity : 0 ≤ 4 * Ce * scale)
  have hmiddle := mul_le_mul_of_nonneg_left hMR
    (by positivity : 0 ≤ 21 * K + (16 * K + 1) * Kc)
  have hmiddle' : 21 * K * M / R + gain * (Kc / R) ≤
      (21 * K + (16 * K + 1) * Kc) * (4 * Ce * scale) := by
    convert! hmiddle using 1 <;> dsimp [gain] <;> try ring
  have hnuD : nu ≤ scale * D := hnuscale.trans (mul_le_mul_of_nonneg_left hDomega hscale)
  have hnuDA : nu * D ≤ scale * A ^ 2 := by
    have hh := mul_le_mul_of_nonneg_right hnuD hD.le
    have hsquare := pow_le_pow_left₀ hD.le hDA 2
    have hl := mul_le_mul_of_nonneg_left hsquare hscale
    nlinarith only [hh, hl]
  have hTeq : T = Ks * Cs * nu * D / A ^ 2 := by
    dsimp [T, s]
    field_simp [ne_of_gt hA]
    <;> try ring
  have hT : T ≤ Ks * Cs * scale := by
    rw [hTeq]
    apply (div_le_iff₀ (sq_pos_of_pos hA)).mpr
    convert! mul_le_mul_of_nonneg_left hnuDA (mul_nonneg hKs hCs) using 1 <;> try ring
  constructor
  · nlinarith only [hfirst, hMpart]
  · nlinarith only [hmiddle', hT]

theorem universal_hessian_scale_choice (C : ℝ) (hC : 0 ≤ C) :
    ∃ cg : ℝ, 0 < cg ∧ ∀ rho : ℝ, 0 ≤ rho → C * (cg * rho) ≤ rho := by
  let cg := 1 / (C + 1)
  have hcg : 0 < cg := by dsimp [cg]; positivity
  have hbudget : C * cg ≤ 1 := by
    dsimp [cg]
    rw [mul_one_div]
    apply (div_le_iff₀ (by positivity : 0 < C + 1)).mpr
    linarith only [hC]
  refine ⟨cg, hcg, ?_⟩
  intro rho hrho
  have hh := mul_le_mul_of_nonneg_right hbudget hrho
  convert! hh using 1 <;> try ring

end
end FangqingPairedShellScaleBudgets


namespace FangqingWidePairedShellRateBudgets

open FangqingPairedShellScaleBudgets FangqingSeedWidthMonotonic

noncomputable section

theorem actual_wider_seed_original_rates (Ce K Kc Ks Cs Cw Cmin q nu scale omega D R : ℝ)
    (hCe : 0 ≤ Ce) (hK : 0 ≤ K) (hKc : 0 ≤ Kc) (hKs : 0 ≤ Ks) (hCs : 0 ≤ Cs)
    (hCmin : 0 ≤ Cmin) (hCw : 1 ≤ Cw) (hq : 1 ≤ q) (hnu : 0 ≤ nu) (hscale : 0 ≤ scale)
    (homega : 0 < omega) (hDomega : omega ≤ D)
    (hscaleomega : scale * omega = Cw * nu * q ^ 2)
    (hRA : (1 + 2 * Ks * Cs + Cmin) * D ≤ R) :
    let A := (1 + 2 * Ks * Cs + Cmin) * D
    let s := Cs * nu * D
    let M := 4 * Ce * scale * omega
    let gain := (16 * K + 1) * M
    nu * (q + 2) + 16 * K * M + gain * Kc + Ks * (s * A) / A ^ 2 ≤
      (7 / 2 + 4 * Ce * Cw * (16 * K + (16 * K + 1) * Kc)) * nu * q ^ 2 ∧
    K * (8 * Ce * scale) + 21 * K * M / R + gain * (Kc / R) + Ks * (s * A) / A ^ 3 ≤
      (8 * K * Ce + 4 * Ce * (21 * K + (16 * K + 1) * Kc) + Ks * Cs) * scale := by
  intro A s M gain
  let A0 := (1 + 2 * Ks * Cs) * D
  have hD : 0 < D := homega.trans_le hDomega
  have hA0 : 0 < A0 := by dsimp [A0]; positivity
  have hAA : A0 ≤ A := by
    dsimp [A0, A]
    nlinarith only [mul_nonneg hCmin hD.le]
  have hs : 0 ≤ s := by dsimp [s]; positivity
  obtain ⟨hS, hT⟩ := actual_seed_rates_antitone_width Ks s A0 A hKs hs hA0 hAA
  obtain ⟨hL, hr⟩ := actual_original_rate_budgets Ce K Kc Ks Cs Cw q nu scale omega D R
    hCe hK hKc hKs hCs hCw hq hnu hscale homega hDomega hscaleomega (hAA.trans hRA)
  constructor
  · exact (add_le_add (le_refl _) hS).trans hL
  · exact (add_le_add (le_refl _) hT).trans hr

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem actual_class_reserve (F : E → ℝ) (nu nu' L L' rho rho' : ℝ)
    (hF : FangqingActualInactivePacket.AnalyticClass F nu L rho)
    (hnu : nu' ≤ nu) (hL : L ≤ L') (hr : rho ≤ rho') :
    FangqingActualInactivePacket.AnalyticClass F nu' L' rho' := by
  refine ⟨hF.1, hF.2.1.mono hnu, ?_, ?_⟩
  · intro x y
    exact (hF.2.2.1 x y).trans (mul_le_mul_of_nonneg_right hL (norm_nonneg _))
  · intro x y
    exact (hF.2.2.2 x y).trans (mul_le_mul_of_nonneg_right hr (norm_nonneg _))

end
end FangqingWidePairedShellRateBudgets


open scoped ContDiff

namespace FangqingRawEndpointDifferenceJets

open FangqingLocalizedSeedJets FangqingActiveShellClass FangqingPublicShellProfiles

noncomputable section

universe u

theorem actual_endpoint_difference_all_jets (phi : ℝ → ℝ) (B left right : ℝ)
    (hp : ContDiff ℝ 3 phi) (hl : ∀ t, t < -B → phi t = left) (hr : ∀ t, B < t → phi t = right) :
    ∃ Kd : ℝ, 0 ≤ Kd ∧ ∀ (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℝ E],
    ∀ (R A D amp : ℝ) (handle : E) (H : E → ℝ),
      0 < D → D ≤ A → A ≤ R → 0 ≤ amp → ‖handle‖ ≤ 1 →
      let difference := fun z => (H z - localizedSeed theta phi R A amp handle z) - H z
      ContDiff ℝ 3 difference ∧
      (∀ j, j ≤ 3 → ∀ z, ‖iteratedFDeriv ℝ j difference z‖ ≤ Kd * amp / D ^ j) ∧
      (∀ z, |difference z| ≤ Kd * amp) := by
  obtain ⟨Kd, hKd, hj⟩ := universal_actual_seed_jets.{u} phi B left right hp hl hr
  refine ⟨Kd, hKd, ?_⟩
  intro E inst inst' R A D amp handle H hD hDA hAR hamp hh difference
  obtain ⟨hc, hb⟩ := hj E R A amp handle (hD.trans_le hDA) hAR hamp hh
  have heq : difference = fun z => -localizedSeed theta phi R A amp handle z := by
    funext z
    dsimp [difference]
    ring
  rw [heq]
  have hall : ∀ j, j ≤ 3 → ∀ z,
      ‖iteratedFDeriv ℝ j (fun z => -localizedSeed theta phi R A amp handle z) z‖ ≤ Kd * amp / D ^ j := by
    intro j hj z
    change ‖iteratedFDeriv ℝ j (-(localizedSeed theta phi R A amp handle)) z‖ ≤ _
    rw [iteratedFDeriv_neg_apply, norm_neg]
    exact (hb j hj z).trans (div_le_div_of_nonneg_left (mul_nonneg hKd hamp)
      (pow_pos hD j) (pow_le_pow_left₀ hD.le hDA j))
  refine ⟨hc.neg, hall, ?_⟩
  intro z
  have hh := hall 0 (by norm_num) z
  simpa only [norm_iteratedFDeriv_zero, Real.norm_eq_abs, pow_zero, div_one] using hh

end
end FangqingRawEndpointDifferenceJets


open scoped ContDiff

namespace FangqingPairedShellAnalyticItems

open FangqingAmplifier FangqingPathEdgeRegularity FangqingActualInactivePacket
  FangqingInactiveShellClass FangqingLocalizedSeedJets FangqingActiveShellLargerWidth
  FangqingPublicShellProfiles OriginalPacketOrientationNormalization
  OriginalPhysicalPacketMinimizer OriginalPacketDistanceGapBounds
  FangqingPhysicalPairedShellMinimizers FangqingRawEndpointDifferenceJets
  FangqingWidePairedShellRateBudgets

noncomputable section

set_option maxHeartbeats 4000000

universe u

theorem actual_paired_shell_analytic_items
    (P : FlatCubic.Profile) (phi : ℝ → ℝ) (Bp left right Cm Cw : ℝ)
    (hCm : 0 ≤ Cm) (hCw : 4 * (Cm + 2) ≤ Cw)
    (hp : ContDiff ℝ 3 phi) (hl : ∀ t, t < -Bp → phi t = left) (hr : ∀ t, Bp < t → phi t = right)
    (hcore : ∀ t, |t| < 1 → phi t = t) :
    ∃ Ce : ℝ≥0, ∃ K : ℝ, 0 ≤ K ∧ ∃ Kc : ℝ, 0 ≤ Kc ∧ ∃ Ks : ℝ, 0 ≤ Ks ∧ ∃ Kd : ℝ, 0 ≤ Kd ∧
    ∀ (A0 B0 W : Type u)
      [NormedAddCommGroup A0] [InnerProductSpace ℝ A0] [FiniteDimensional ℝ A0]
      [NormedAddCommGroup B0] [InnerProductSpace ℝ B0] [FiniteDimensional ℝ B0]
      [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W],
    ∀ (C : A0 ≃ₗᵢ[ℝ] B0) (h : A0) (n : ℕ) (tail : Fin (n + 2) → W)
      (delta omega q scale lam : ℝ),
      ‖h‖ = 1 → Orthonormal ℝ tail → 0 < delta → delta ≤ omega → 1 ≤ q →
      0 < scale → 0 < lam → omega = Cw * lam * q ^ 2 → ((n + 2 : ℕ) : ℝ) ≤ Cm * q →
      let nu := scale * lam
      let D := distanceScale q omega
      let Cs := 2 * Cw
      let Cmin := 2 * Cw * (Cm + 2)
      let A := (1 + 2 * Ks * Cs + Cmin) * D
      let R := 2 * A
      let s := Cs * nu * D
      let Q := QPhysical q nu C
      let g := fun z => scale * pathEdge P delta omega (n + 2) (physicalFrame C h n tail) z
      let M : ℝ := (4 * Ce : ℝ) * scale * omega
      let gain := (16 * K + 1) * M
      let F0 := inactiveShell Q g R gain
      let F1 := fun z => F0 z - localizedSeed theta phi R A (s * A) (mkPhysical h 0 0) z
      let L0 := nu * (q + 2) + 16 * K * M + gain * Kc
      let rho0 := K * ((8 * Ce : ℝ) * scale) + 21 * K * M / R + gain * (Kc / R)
      let CL := 7 / 2 + 4 * (Ce : ℝ) * Cw * (16 * K + (16 * K + 1) * Kc)
      let Crho := 8 * K * (Ce : ℝ) + 4 * (Ce : ℝ) * (21 * K + (16 * K + 1) * Kc) + Ks * Cs
      AnalyticClass F0 (nu / 2) (CL * nu * q ^ 2) (Crho * scale) ∧
      AnalyticClass F1 (nu / 2) (CL * nu * q ^ 2) (Crho * scale) ∧
      ContDiff ℝ 3 (fun z => F1 z - F0 z) ∧
      (∀ j, j ≤ 3 → ∀ z, ‖iteratedFDeriv ℝ j (fun z => F1 z - F0 z) z‖ ≤ Kd * (s * A) / D ^ j) ∧
      (∀ z, |F1 z - F0 z| ≤ Kd * (s * A)) ∧
      (∀ Y, F0 0 ≤ F0 Y) ∧
      ∃ Z : PhysicalSpace A0 B0 W,
        (∀ Y, F1 Z ≤ F1 Y) ∧ (∀ Y, (∀ X, F1 Y ≤ F1 X) → Y = Z) ∧
        ‖Z‖ ≤ Cmin * D ∧
        F1 0 - F1 Z ≤ 4 * Cw ^ 2 * nu * D ^ 2 ∧
        (∀ j : Fin (n + 3), (j.val : ℝ) ≤ q → 3 * q * omega ≤ inner ℝ (physicalFrame C h n tail j) Z) := by
  obtain ⟨Ce, K, hK, Kc, hKc, Ks, hKs, hPhysical⟩ :=
    actual_physical_paired_shell_same_minimum.{u} P phi Bp left right Cm Cw hCm hCw hp hl hr hcore
  obtain ⟨Kd, hKd, hDiff⟩ := actual_endpoint_difference_all_jets.{u} phi Bp left right hp hl hr
  refine ⟨Ce, K, hK, Kc, hKc, Ks, hKs, Kd, hKd, ?_⟩
  intro A0 B0 W inst inst' inst'' instB instB' instB'' instW instW' instW'' C h n tail
    delta omega q scale lam hh ht hd hdw hq hscale hlam homega hn
    nu D Cs Cmin A R s Q g M gain F0 F1 L0 rho0 CL Crho
  obtain ⟨hF0, hF1, hRest⟩ := hPhysical A0 B0 W C h n tail delta omega q scale lam
    hh ht hd hdw hq hscale hlam homega hn
  have hCw1 : 1 ≤ Cw := by linarith only [hCm, hCw]
  have hCs : 0 ≤ Cs := by dsimp [Cs]; positivity
  have hCmin : 0 ≤ Cmin := by dsimp [Cmin]; positivity
  have hq0 : 0 < q := by linarith only [hq]
  have hw : 0 < omega := hd.trans_le hdw
  have hnu : 0 < nu := mul_pos hscale hlam
  have hD : 0 < D := by dsimp [D, distanceScale]; positivity
  obtain ⟨hDA, hWidth, hMinA⟩ := larger_width_choice Ks Cs Cmin D hKs hCs hCmin hD
  have hA : 0 < A := hD.trans_le hDA
  have hAR : A ≤ R := by dsimp [R]; linarith only [hA]
  have hRA : (1 + 2 * Ks * Cs + Cmin) * D ≤ R := hAR
  have hsqrt : 1 ≤ Real.sqrt q := Real.one_le_sqrt.mpr hq
  have hqp : 1 ≤ q * Real.sqrt q := by
    nlinarith only [hq, hsqrt, mul_nonneg (sub_nonneg.mpr hq) (sub_nonneg.mpr hsqrt)]
  have hDomega : omega ≤ D := by
    have hh := mul_le_mul_of_nonneg_right hqp hw.le
    simpa only [one_mul, D, distanceScale] using hh
  have hscaleomega : scale * omega = Cw * nu * q ^ 2 := by rw [homega]; dsimp [nu]; ring
  obtain ⟨hL, hrho⟩ := actual_wider_seed_original_rates (Ce : ℝ) K Kc Ks Cs Cw Cmin q nu scale omega D R
    Ce.coe_nonneg hK hKc hKs hCs hCmin hCw1 hq hnu.le hscale.le hw hDomega hscaleomega hRA
  have hS : 0 ≤ Ks * (s * A) / A ^ 2 := by positivity
  have hT : 0 ≤ Ks * (s * A) / A ^ 3 := by positivity
  have hL0 : L0 ≤ CL * nu * q ^ 2 := (le_add_of_nonneg_right hS).trans hL
  have hr0 : rho0 ≤ Crho * scale := (le_add_of_nonneg_right hT).trans hrho
  have hClass0 := actual_class_reserve F0 nu (nu / 2) L0 (CL * nu * q ^ 2) rho0 (Crho * scale)
    hF0 (by linarith only [hnu]) hL0 hr0
  have hClass1 := actual_class_reserve F1 (nu / 2) (nu / 2)
    (L0 + Ks * (s * A) / A ^ 2) (CL * nu * q ^ 2)
    (rho0 + Ks * (s * A) / A ^ 3) (Crho * scale) hF1 le_rfl hL hrho
  have hhandle : ‖mkPhysical h (0 : B0) (0 : W)‖ ≤ 1 := by
    have hn1 := WithLp.prod_norm_sq_eq_of_L2 (mkPhysical h (0 : B0) (0 : W))
    have hn2 := WithLp.prod_norm_sq_eq_of_L2 (WithLp.toLp 2 (h, (0 : B0)))
    change ‖mkPhysical h (0 : B0) (0 : W)‖ ^ 2 = ‖WithLp.toLp 2 (h, (0 : B0))‖ ^ 2 + ‖(0 : W)‖ ^ 2 at hn1
    change ‖WithLp.toLp 2 (h, (0 : B0))‖ ^ 2 = ‖h‖ ^ 2 + ‖(0 : B0)‖ ^ 2 at hn2
    rw [hh, norm_zero] at hn2
    rw [norm_zero] at hn1
    nlinarith only [hn1, hn2, norm_nonneg (mkPhysical h (0 : B0) (0 : W))]
  obtain ⟨hDC, hDJ, hD0⟩ := hDiff (PhysicalSpace A0 B0 W) R A D (s * A) (mkPhysical h 0 0) F0
    hD hDA hAR (by positivity) hhandle
  exact ⟨hClass0, hClass1, hDC, hDJ, hD0, hRest⟩

end
end FangqingPairedShellAnalyticItems


open scoped Topology BigOperators

namespace FangqingShellPrefixLocality

open FangqingPacketLeakage

variable {E I : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [Fintype I]

noncomputable def selectedEdgeSum (g : ℝ → ℝ) (d : I → E) (selected : Finset I) (y : E) : ℝ :=
  ∑ i ∈ selected, g (inner ℝ (d i) y)

noncomputable def bundle (f : E → ℝ) (y : E) : ℝ × E × (E →L[ℝ] E) :=
  (f y, gradient f y, fderiv ℝ (gradient f) y)

theorem bundle_of_eventuallyEq (f g : E → ℝ) (y : E) (heq : f =ᶠ[𝓝 y] g) :
    bundle f y = bundle g y := by
  unfold bundle
  rw [heq.eq_of_nhds, heq.gradient_eq, heq.gradient.fderiv_eq]

theorem edgeSum_eventually_eq_selected
    (P : FlatCubic.Profile) (delta Delta : ℝ) (hd : 0 < delta) (hdD : delta ≤ Delta)
    (d : I → E) (selected : Finset I) (y : E)
    (hflat : ∀ i ∉ selected, |inner ℝ (d i) y| < delta / 2) :
    edgeSum (FlatCubic.edge P delta Delta) d =ᶠ[𝓝 y]
      selectedEdgeSum (FlatCubic.edge P delta Delta) d selected := by
  classical
  have hi : ∀ i : I, ∀ᶠ z in 𝓝 y,
      i ∉ selected → FlatCubic.edge P delta Delta (inner ℝ (d i) z) = 0 := by
    intro i
    by_cases his : i ∈ selected
    · exact Filter.Eventually.of_forall (fun _ h => False.elim (h his))
    · have hc : Continuous (fun z : E => |inner ℝ (d i) z|) := (innerSL ℝ (d i)).continuous.abs
      have hn : {z : E | |inner ℝ (d i) z| < delta / 2} ∈ 𝓝 y :=
        (isOpen_lt hc continuous_const).mem_nhds (hflat i his)
      filter_upwards [hn] with z hz _
      exact (FlatCubic.edge_flat_jets_closed P delta Delta _ hd hdD hz.le).1
  have hall : ∀ᶠ z in 𝓝 y, ∀ i : I,
      i ∉ selected → FlatCubic.edge P delta Delta (inner ℝ (d i) z) = 0 :=
    Filter.eventually_all.mpr hi
  filter_upwards [hall] with z hz
  unfold edgeSum selectedEdgeSum
  symm
  exact Finset.sum_subset (Finset.subset_univ selected) (fun i _ hin => hz i hin)

theorem localized_eventually_eq_selected
    (P : FlatCubic.Profile) (delta Delta : ℝ) (hd : 0 < delta) (hdD : delta ≤ Delta)
    (d : I → E) (selected : Finset I) (chi collar : ℝ → ℝ) (R scale : ℝ)
    (Q seed : E → ℝ) (y : E)
    (hflat : ∀ i ∉ selected, |inner ℝ (d i) y| < delta / 2) :
    localized chi collar R Q (fun z => scale * edgeSum (FlatCubic.edge P delta Delta) d z + seed z)
      =ᶠ[𝓝 y]
    localized chi collar R Q
      (fun z => scale * selectedEdgeSum (FlatCubic.edge P delta Delta) d selected z + seed z) := by
  filter_upwards [edgeSum_eventually_eq_selected P delta Delta hd hdD d selected y hflat] with z hz
  simp only [localized, hz]

theorem actual_active_endpoint_bundle_selected
    (P : FlatCubic.Profile) (delta Delta : ℝ) (hd : 0 < delta) (hdD : delta ≤ Delta)
    (d : I → E) (selected : Finset I) (chi collar phi : ℝ → ℝ) (R scale s A : ℝ)
    (Q : E → ℝ) (handle y : E)
    (hflat : ∀ i ∉ selected, |inner ℝ (d i) y| < delta / 2) :
    bundle (activeEndpoint chi collar phi R Q (FlatCubic.edge P delta Delta) d scale s A handle) y =
      bundle (localized chi collar R Q
        (fun z => scale * selectedEdgeSum (FlatCubic.edge P delta Delta) d selected z + boundedSeed phi s A handle z)) y := by
  exact bundle_of_eventuallyEq _ _ y
    (localized_eventually_eq_selected P delta Delta hd hdD d selected chi collar R scale Q
      (boundedSeed phi s A handle) y hflat)

noncomputable def prefixEdges (n k : ℕ) : Finset (Fin (n + 2)) :=
  Finset.univ.filter (fun i => i.val < k)

theorem selected_path_prefix_invariant
    (n k : ℕ) (v w : Fin (n + 3) → E)
    (hprefix : ∀ j : Fin (n + 3), j.val < k + 1 → v j = w j)
    (g : ℝ → ℝ) :
    selectedEdgeSum g (pathDirection n v) (prefixEdges n k) =
      selectedEdgeSum g (pathDirection n w) (prefixEdges n k) := by
  classical
  funext z
  unfold selectedEdgeSum
  apply Finset.sum_congr rfl
  intro i hi
  have hik : i.val < k := (Finset.mem_filter.mp hi).2
  have hleft : v i.castSucc = w i.castSucc := hprefix _ (by simp only [Fin.val_castSucc]; omega)
  have hright : v i.succ = w i.succ := hprefix _ (by simp only [Fin.val_succ]; omega)
  simp only [pathDirection, hleft, hright]

theorem actual_path_endpoint_prefix_bundle_invariant
    (P : FlatCubic.Profile) (delta Delta : ℝ) (hd : 0 < delta) (hdD : delta ≤ Delta)
    (n k : ℕ) (v w : Fin (n + 3) → E)
    (hprefix : ∀ j : Fin (n + 3), j.val < k + 1 → v j = w j)
    (chi collar phi : ℝ → ℝ) (R scale s A : ℝ) (Q : E → ℝ) (handle y : E)
    (hflatV : ∀ i : Fin (n + 2), k ≤ i.val → |inner ℝ (pathDirection n v i) y| < delta / 2)
    (hflatW : ∀ i : Fin (n + 2), k ≤ i.val → |inner ℝ (pathDirection n w i) y| < delta / 2) :
    bundle (activeEndpoint chi collar phi R Q (FlatCubic.edge P delta Delta) (pathDirection n v) scale s A handle) y =
      bundle (activeEndpoint chi collar phi R Q (FlatCubic.edge P delta Delta) (pathDirection n w) scale s A handle) y := by
  have hv : ∀ i ∉ prefixEdges n k, |inner ℝ (pathDirection n v i) y| < delta / 2 := by
    intro i hi
    apply hflatV i
    by_contra hn
    exact hi (Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩)
  have hw : ∀ i ∉ prefixEdges n k, |inner ℝ (pathDirection n w i) y| < delta / 2 := by
    intro i hi
    apply hflatW i
    by_contra hn
    exact hi (Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩)
  rw [actual_active_endpoint_bundle_selected P delta Delta hd hdD _ (prefixEdges n k) chi collar phi R scale s A Q handle y hv,
    actual_active_endpoint_bundle_selected P delta Delta hd hdD _ (prefixEdges n k) chi collar phi R scale s A Q handle y hw,
    selected_path_prefix_invariant n k v w hprefix]

noncomputable def maskedPrefix (n k : ℕ) (v : Fin (n + 3) → E) : Fin (n + 3) → E :=
  fun j => if j.val < k + 1 then v j else 0

theorem maskedPrefix_agrees (n k : ℕ) (v : Fin (n + 3) → E) :
    ∀ j : Fin (n + 3), j.val < k + 1 → v j = maskedPrefix n k v j := by
  intro j hj
  simp only [maskedPrefix, if_pos hj]

theorem maskedPrefix_invariant (n k : ℕ) (v w : Fin (n + 3) → E)
    (hprefix : ∀ j : Fin (n + 3), j.val < k + 1 → v j = w j) :
    maskedPrefix n k v = maskedPrefix n k w := by
  funext j
  by_cases hj : j.val < k + 1
  · simp only [maskedPrefix, if_pos hj, hprefix j hj]
  · simp only [maskedPrefix, if_neg hj]

theorem maskedPrefix_measurable [MeasurableSpace E] (n k : ℕ) :
    Measurable (maskedPrefix n k : (Fin (n + 3) → E) → (Fin (n + 3) → E)) := by
  apply measurable_pi_lambda
  intro j
  by_cases hj : j.val < k + 1
  · simpa only [maskedPrefix, if_pos hj] using measurable_pi_apply j
  · simpa only [maskedPrefix, if_neg hj] using (measurable_const : Measurable (fun _ : Fin (n + 3) → E => (0 : E)))

noncomputable def virtualActiveEndpoint
    (P : FlatCubic.Profile) (delta Delta : ℝ) (n k : ℕ) (v : Fin (n + 3) → E)
    (chi collar phi : ℝ → ℝ) (R scale s A : ℝ) (Q : E → ℝ) (handle : E) : E → ℝ :=
  localized chi collar R Q (fun z => scale * selectedEdgeSum (FlatCubic.edge P delta Delta)
    (pathDirection n (maskedPrefix n k v)) (prefixEdges n k) z + boundedSeed phi s A handle z)

theorem virtualActiveEndpoint_prefix_invariant
    (P : FlatCubic.Profile) (delta Delta : ℝ) (n k : ℕ) (v w : Fin (n + 3) → E)
    (hprefix : ∀ j : Fin (n + 3), j.val < k + 1 → v j = w j)
    (chi collar phi : ℝ → ℝ) (R scale s A : ℝ) (Q : E → ℝ) (handle : E) :
    virtualActiveEndpoint P delta Delta n k v chi collar phi R scale s A Q handle =
      virtualActiveEndpoint P delta Delta n k w chi collar phi R scale s A Q handle := by
  unfold virtualActiveEndpoint
  rw [maskedPrefix_invariant n k v w hprefix]

theorem actual_bundle_eq_virtual_on_flat_event
    (P : FlatCubic.Profile) (delta Delta : ℝ) (hd : 0 < delta) (hdD : delta ≤ Delta)
    (n k : ℕ) (v : Fin (n + 3) → E)
    (chi collar phi : ℝ → ℝ) (R scale s A : ℝ) (Q : E → ℝ) (handle y : E)
    (hflat : ∀ i : Fin (n + 2), k ≤ i.val → |inner ℝ (pathDirection n v i) y| < delta / 2) :
    bundle (activeEndpoint chi collar phi R Q (FlatCubic.edge P delta Delta) (pathDirection n v) scale s A handle) y =
      bundle (virtualActiveEndpoint P delta Delta n k v chi collar phi R scale s A Q handle) y := by
  have hv : ∀ i ∉ prefixEdges n k, |inner ℝ (pathDirection n v i) y| < delta / 2 := by
    intro i hi
    apply hflat i
    by_contra hn
    exact hi (Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩)
  rw [actual_active_endpoint_bundle_selected P delta Delta hd hdD _ (prefixEdges n k) chi collar phi R scale s A Q handle y hv]
  unfold virtualActiveEndpoint
  rw [selected_path_prefix_invariant n k v (maskedPrefix n k v) (maskedPrefix_agrees n k v)]

end FangqingShellPrefixLocality

set_option maxHeartbeats 800000
open scoped Topology BigOperators

namespace OriginalPhysicalPairedShellPrefix
open FangqingPacketLeakage FangqingShellPrefixLocality
open FangqingInactiveShellClass FangqingLocalizedSeedJets FangqingPublicShellProfiles
open FangqingAmplifier OriginalPacketOrientationNormalization FangqingPathEdgeRegularity

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

noncomputable def actualInactive (P : FlatCubic.Profile) (delta Delta : ℝ) (n : ℕ)
    (v : Fin (n + 3) → E) (Q : E → ℝ) (scale R gain : ℝ) : E → ℝ :=
  inactiveShell Q (fun z => scale * pathEdge P delta Delta (n + 2) v z) R gain

noncomputable def actualActive (P : FlatCubic.Profile) (delta Delta : ℝ) (n : ℕ)
    (v : Fin (n + 3) → E) (Q : E → ℝ) (phi : ℝ → ℝ) (scale R gain A amplitude : ℝ) (handle : E) : E → ℝ :=
  fun z => actualInactive P delta Delta n v Q scale R gain z - localizedSeed theta phi R A amplitude handle z

noncomputable def publicEndpoint (Q : E → ℝ) (R gain : ℝ) : E → ℝ :=
  fun z => Q z + gain * FangqingRadialCollar.collar psi R z

noncomputable def virtualInactive (P : FlatCubic.Profile) (delta Delta : ℝ) (n k : ℕ)
    (v : Fin (n + 3) → E) (Q : E → ℝ) (scale R gain : ℝ) : E → ℝ :=
  inactiveShell Q (fun z => scale * selectedEdgeSum (FlatCubic.edge P delta Delta)
    (pathDirection n (maskedPrefix n k v)) (prefixEdges n k) z) R gain

noncomputable def virtualActive (P : FlatCubic.Profile) (delta Delta : ℝ) (n k : ℕ)
    (v : Fin (n + 3) → E) (Q : E → ℝ) (phi : ℝ → ℝ) (scale R gain A amplitude : ℝ) (handle : E) : E → ℝ :=
  fun z => virtualInactive P delta Delta n k v Q scale R gain z - localizedSeed theta phi R A amplitude handle z

theorem actualInactive_eventually_virtual
    (P : FlatCubic.Profile) (delta Delta : ℝ) (hd : 0 < delta) (hdD : delta ≤ Delta)
    (n k : ℕ) (v : Fin (n + 3) → E) (Q : E → ℝ) (scale R gain : ℝ) (y : E)
    (hflat : ∀ i : Fin (n + 2), k ≤ i.val → |inner ℝ (pathDirection n v i) y| < delta / 2) :
    actualInactive P delta Delta n v Q scale R gain =ᶠ[𝓝 y]
      virtualInactive P delta Delta n k v Q scale R gain := by
  have hf : ∀ i ∉ prefixEdges n k, |inner ℝ (pathDirection n v i) y| < delta / 2 := by
    intro i hi
    apply hflat i
    by_contra hn
    exact hi (Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩)
  have he := edgeSum_eventually_eq_selected P delta Delta hd hdD (pathDirection n v) (prefixEdges n k) y hf
  rw [selected_path_prefix_invariant n k v (maskedPrefix n k v) (maskedPrefix_agrees n k v)] at he
  filter_upwards [he] with z hz
  change Q z + FangqingRadialGateBounds.scaledGate theta R 0 z * (scale * edgeSum (FlatCubic.edge P delta Delta) (pathDirection n v) z) +
      gain * FangqingRadialCollar.collar psi R z = _
  simp only [hz]
  rfl

theorem actualActive_eventually_virtual
    (P : FlatCubic.Profile) (delta Delta : ℝ) (hd : 0 < delta) (hdD : delta ≤ Delta)
    (n k : ℕ) (v : Fin (n + 3) → E) (Q : E → ℝ) (phi : ℝ → ℝ)
    (scale R gain A amplitude : ℝ) (handle y : E)
    (hflat : ∀ i : Fin (n + 2), k ≤ i.val → |inner ℝ (pathDirection n v i) y| < delta / 2) :
    actualActive P delta Delta n v Q phi scale R gain A amplitude handle =ᶠ[𝓝 y]
      virtualActive P delta Delta n k v Q phi scale R gain A amplitude handle := by
  filter_upwards [actualInactive_eventually_virtual P delta Delta hd hdD n k v Q scale R gain y hflat] with z hz
  exact congrArg (fun value => value - localizedSeed theta phi R A amplitude handle z) hz

theorem actual_inactive_full_bundle_public
    (P : FlatCubic.Profile) (delta Delta : ℝ) (hd : 0 < delta) (hdD : delta ≤ Delta)
    (n : ℕ) (v : Fin (n + 3) → E) (Q : E → ℝ) (scale R gain : ℝ) (y : E)
    (hflat : ∀ i : Fin (n + 2), |inner ℝ (pathDirection n v i) y| < delta / 2) :
    bundle (actualInactive P delta Delta n v Q scale R gain) y = bundle (publicEndpoint Q R gain) y := by
  apply bundle_of_eventuallyEq
  have hh := actualInactive_eventually_virtual P delta Delta hd hdD n 0 v Q scale R gain y (fun i _ => hflat i)
  filter_upwards [hh] with z hz
  rw [hz]
  simp only [virtualInactive, prefixEdges, Nat.not_lt_zero, Finset.filter_false,
    selectedEdgeSum, Finset.sum_empty, mul_zero, inactiveShell, mul_zero, add_zero, publicEndpoint]

theorem actual_paired_full_bundle_factors_through_prefix
    (P : FlatCubic.Profile) (delta Delta : ℝ) (hd : 0 < delta) (hdD : delta ≤ Delta)
    (n k : ℕ) (v : Fin (n + 3) → E) (Q : E → ℝ) (phi : ℝ → ℝ)
    (scale R gain A amplitude : ℝ) (handle y : E)
    (hflat : ∀ i : Fin (n + 2), k ≤ i.val → |inner ℝ (pathDirection n v i) y| < delta / 2) :
    (bundle (actualInactive P delta Delta n v Q scale R gain) y,
      bundle (actualActive P delta Delta n v Q phi scale R gain A amplitude handle) y) =
    (bundle (virtualInactive P delta Delta n k v Q scale R gain) y,
      bundle (virtualActive P delta Delta n k v Q phi scale R gain A amplitude handle) y) := by
  exact Prod.ext (bundle_of_eventuallyEq _ _ y (actualInactive_eventually_virtual P delta Delta hd hdD n k v Q scale R gain y hflat))
    (bundle_of_eventuallyEq _ _ y (actualActive_eventually_virtual P delta Delta hd hdD n k v Q phi scale R gain A amplitude handle y hflat))

theorem virtual_paired_prefix_invariant
    (P : FlatCubic.Profile) (delta Delta : ℝ) (n k : ℕ) (v w : Fin (n + 3) → E)
    (hprefix : ∀ i : Fin (n + 3), i.val < k + 1 → v i = w i)
    (Q : E → ℝ) (phi : ℝ → ℝ) (scale R gain A amplitude : ℝ) (handle : E) :
    virtualInactive P delta Delta n k v Q scale R gain = virtualInactive P delta Delta n k w Q scale R gain ∧
      virtualActive P delta Delta n k v Q phi scale R gain A amplitude handle =
        virtualActive P delta Delta n k w Q phi scale R gain A amplitude handle := by
  constructor
  · unfold virtualInactive
    rw [maskedPrefix_invariant n k v w hprefix]
  · unfold virtualActive virtualInactive
    rw [maskedPrefix_invariant n k v w hprefix]

section Physical
variable {A0 B0 W : Type*}
  [NormedAddCommGroup A0] [InnerProductSpace ℝ A0] [CompleteSpace A0]
  [NormedAddCommGroup B0] [InnerProductSpace ℝ B0] [CompleteSpace B0]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]

theorem actual_physical_inactive_public_no_handle
    (P : FlatCubic.Profile) (delta Delta : ℝ) (hd : 0 < delta) (hdD : delta ≤ Delta)
    (n : ℕ) (C : A0 ≃ₗᵢ[ℝ] B0) (h : A0) (tail : Fin (n + 2) → W)
    (q nu scale R gain : ℝ) (y : PhysicalSpace A0 B0 W)
    (hflat : ∀ i : Fin (n + 2), |inner ℝ (pathDirection n (physicalFrame C h n tail) i) y| < delta / 2) :
    bundle (inactiveShell (QPhysical q nu C)
      (fun z => scale * pathEdge P delta Delta (n + 2) (physicalFrame C h n tail) z) R gain) y =
      bundle (publicEndpoint (QPhysical q nu C) R gain) y :=
  actual_inactive_full_bundle_public P delta Delta hd hdD n (physicalFrame C h n tail) (QPhysical q nu C) scale R gain y hflat

theorem actual_physical_paired_prefix_full_bundle
    (P : FlatCubic.Profile) (delta Delta : ℝ) (hd : 0 < delta) (hdD : delta ≤ Delta)
    (n k : ℕ) (C : A0 ≃ₗᵢ[ℝ] B0) (h : A0) (tail : Fin (n + 2) → W)
    (phi : ℝ → ℝ) (q nu scale R gain A amplitude : ℝ) (y : PhysicalSpace A0 B0 W)
    (hflat : ∀ i : Fin (n + 2), k ≤ i.val → |inner ℝ (pathDirection n (physicalFrame C h n tail) i) y| < delta / 2) :
    let v := physicalFrame C h n tail
    let Q := QPhysical q nu C
    let H0 := inactiveShell Q (fun z => scale * pathEdge P delta Delta (n + 2) v z) R gain
    let H1 := fun z => H0 z - localizedSeed theta phi R A amplitude (mkPhysical h (0 : B0) (0 : W)) z
    (bundle H0 y, bundle H1 y) =
      (bundle (virtualInactive P delta Delta n k v Q scale R gain) y,
       bundle (virtualActive P delta Delta n k v Q phi scale R gain A amplitude (mkPhysical h (0 : B0) (0 : W))) y) :=
  actual_paired_full_bundle_factors_through_prefix P delta Delta hd hdD n k (physicalFrame C h n tail) (QPhysical q nu C)
    phi scale R gain A amplitude (mkPhysical h (0 : B0) (0 : W)) y hflat

end Physical
end OriginalPhysicalPairedShellPrefix

set_option maxHeartbeats 800000
open scoped Topology BigOperators

namespace OriginalPhysicalPairedShellPrefix
open FangqingPacketLeakage FangqingShellPrefixLocality
open FangqingInactiveShellClass FangqingLocalizedSeedJets FangqingPublicShellProfiles
open FangqingAmplifier OriginalPacketOrientationNormalization FangqingPathEdgeRegularity

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem contDiff_gradient_of_contDiff_two (f : E → ℝ) (hf : ContDiff ℝ 2 f) : ContDiff ℝ 1 (gradient f) := by
  have hd : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (by norm_num)
  change ContDiff ℝ 1 (fun z => (InnerProductSpace.toDual ℝ E).symm (fderiv ℝ f z))
  exact (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.contDiff.comp hd

theorem continuous_bundle_of_contDiff_two (f : E → ℝ) (hf : ContDiff ℝ 2 f) : Continuous (bundle f) := by
  have hg := contDiff_gradient_of_contDiff_two f hf
  have hH : ContDiff ℝ 0 (fderiv ℝ (gradient f)) := hg.fderiv_right (by norm_num)
  exact hf.continuous.prodMk (hg.continuous.prodMk hH.continuous)

theorem bundle_eq_of_radial_strict_approximations (f g : E → ℝ)
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) (y : E)
    (heq : ∀ r ∈ Set.Ioo (0 : ℝ) 1, bundle f (r • y) = bundle g (r • y)) : bundle f y = bundle g y := by
  have hc : Continuous (fun r : ℝ => r • y) := continuous_id.smul continuous_const
  have hclosed : IsClosed {r : ℝ | bundle f (r • y) = bundle g (r • y)} :=
    isClosed_eq ((continuous_bundle_of_contDiff_two f hf).comp hc) ((continuous_bundle_of_contDiff_two g hg).comp hc)
  have hsub : Set.Ioo (0 : ℝ) 1 ⊆ {r : ℝ | bundle f (r • y) = bundle g (r • y)} := fun r hr => heq r hr
  have hmem : (1 : ℝ) ∈ closure (Set.Ioo (0 : ℝ) 1) := by
    rw [closure_Ioo (by norm_num : (0 : ℝ) ≠ 1)]
    exact ⟨by norm_num, le_rfl⟩
  simpa only [Set.mem_setOf_eq, one_smul] using (hclosed.closure_subset_iff.mpr hsub) hmem

theorem flat_closed_scales_to_strict (delta : ℝ) (hd : 0 < delta) (d y : E)
    (hflat : |inner ℝ d y| ≤ delta / 2) (r : ℝ) (hr : r ∈ Set.Ioo (0 : ℝ) 1) :
    |inner ℝ d (r • y)| < delta / 2 := by
  rw [inner_smul_right, abs_mul, abs_of_pos hr.1]
  have hh := mul_le_mul_of_nonneg_left hflat hr.1.le
  have hc : r * (delta / 2) < delta / 2 := by nlinarith only [hd, hr.2]
  exact hh.trans_lt hc

theorem inactiveShell_contDiff_two (Q g : E → ℝ) (R gain : ℝ) (hR : 0 < R)
    (hQ : ContDiff ℝ 2 Q) (hg : ContDiff ℝ 2 g) : ContDiff ℝ 2 (inactiveShell Q g R gain) := by
  have ht : ContDiff ℝ 3 (FangqingRadialGateBounds.scaledGate theta R 0 : E → ℝ) :=
    FangqingGateBudgetBridge.scaledGate_contDiff theta R 0 hR (theta_smooth.of_le (by decide))
  have hc : ContDiff ℝ 2 (FangqingRadialCollar.collar psi R : E → ℝ) :=
    (FangqingRadialCollar.collar_contDiff_three psi (psi_smooth.of_le (by decide)) R).of_le (by norm_num)
  exact (hQ.add ((ht.of_le (by norm_num)).mul hg)).add (contDiff_const.mul hc)

theorem actualInactive_contDiff_two (P : FlatCubic.Profile) (delta Delta : ℝ)
    (hd : 0 < delta) (hdD : delta ≤ Delta) (n : ℕ) (v : Fin (n + 3) → E)
    (Q : E → ℝ) (scale R gain : ℝ) (hR : 0 < R) (hQ : ContDiff ℝ 2 Q) :
    ContDiff ℝ 2 (actualInactive P delta Delta n v Q scale R gain) :=
  inactiveShell_contDiff_two Q _ R gain hR hQ (contDiff_const.mul (pathEdge_contDiff P delta Delta hd hdD (n + 2) v))

theorem virtualInactive_contDiff_two (P : FlatCubic.Profile) (delta Delta : ℝ)
    (hd : 0 < delta) (hdD : delta ≤ Delta) (n k : ℕ) (v : Fin (n + 3) → E)
    (Q : E → ℝ) (scale R gain : ℝ) (hR : 0 < R) (hQ : ContDiff ℝ 2 Q) :
    ContDiff ℝ 2 (virtualInactive P delta Delta n k v Q scale R gain) := by
  classical
  apply inactiveShell_contDiff_two Q _ R gain hR hQ
  apply ContDiff.mul contDiff_const
  unfold selectedEdgeSum
  apply ContDiff.sum
  intro i hi
  exact (FlatCubic.edge_contDiff_two P delta Delta hd hdD).comp (innerSL ℝ (pathDirection n (maskedPrefix n k v) i)).contDiff

theorem actualActive_contDiff_two (P : FlatCubic.Profile) (delta Delta : ℝ)
    (hd : 0 < delta) (hdD : delta ≤ Delta) (n : ℕ) (v : Fin (n + 3) → E)
    (Q : E → ℝ) (phi : ℝ → ℝ) (scale R gain A amplitude : ℝ) (handle : E)
    (hR : 0 < R) (hQ : ContDiff ℝ 2 Q) (hphi : ContDiff ℝ 3 phi) :
    ContDiff ℝ 2 (actualActive P delta Delta n v Q phi scale R gain A amplitude handle) := by
  exact (actualInactive_contDiff_two P delta Delta hd hdD n v Q scale R gain hR hQ).sub
    ((localizedSeed_contDiff theta phi R A amplitude handle hR (theta_smooth.of_le (by decide)) hphi).of_le (by norm_num))

theorem virtualActive_contDiff_two (P : FlatCubic.Profile) (delta Delta : ℝ)
    (hd : 0 < delta) (hdD : delta ≤ Delta) (n k : ℕ) (v : Fin (n + 3) → E)
    (Q : E → ℝ) (phi : ℝ → ℝ) (scale R gain A amplitude : ℝ) (handle : E)
    (hR : 0 < R) (hQ : ContDiff ℝ 2 Q) (hphi : ContDiff ℝ 3 phi) :
    ContDiff ℝ 2 (virtualActive P delta Delta n k v Q phi scale R gain A amplitude handle) := by
  exact (virtualInactive_contDiff_two P delta Delta hd hdD n k v Q scale R gain hR hQ).sub
    ((localizedSeed_contDiff theta phi R A amplitude handle hR (theta_smooth.of_le (by decide)) hphi).of_le (by norm_num))

theorem actual_inactive_full_bundle_public_closed
    (P : FlatCubic.Profile) (delta Delta : ℝ) (hd : 0 < delta) (hdD : delta ≤ Delta)
    (n : ℕ) (v : Fin (n + 3) → E) (Q : E → ℝ) (scale R gain : ℝ) (y : E)
    (hR : 0 < R) (hQ : ContDiff ℝ 2 Q)
    (hflat : ∀ i : Fin (n + 2), |inner ℝ (pathDirection n v i) y| ≤ delta / 2) :
    bundle (actualInactive P delta Delta n v Q scale R gain) y = bundle (publicEndpoint Q R gain) y := by
  have hpub : ContDiff ℝ 2 (publicEndpoint Q R gain) := hQ.add
    (contDiff_const.mul ((FangqingRadialCollar.collar_contDiff_three psi (psi_smooth.of_le (by decide)) R).of_le (by norm_num)))
  apply bundle_eq_of_radial_strict_approximations _ _ (actualInactive_contDiff_two P delta Delta hd hdD n v Q scale R gain hR hQ) hpub y
  intro r hr
  exact actual_inactive_full_bundle_public P delta Delta hd hdD n v Q scale R gain (r • y)
    (fun i => flat_closed_scales_to_strict delta hd _ y (hflat i) r hr)

theorem actual_paired_full_bundle_factors_through_prefix_closed
    (P : FlatCubic.Profile) (delta Delta : ℝ) (hd : 0 < delta) (hdD : delta ≤ Delta)
    (n k : ℕ) (v : Fin (n + 3) → E) (Q : E → ℝ) (phi : ℝ → ℝ)
    (scale R gain A amplitude : ℝ) (handle y : E)
    (hR : 0 < R) (hQ : ContDiff ℝ 2 Q) (hphi : ContDiff ℝ 3 phi)
    (hflat : ∀ i : Fin (n + 2), k ≤ i.val → |inner ℝ (pathDirection n v i) y| ≤ delta / 2) :
    (bundle (actualInactive P delta Delta n v Q scale R gain) y,
      bundle (actualActive P delta Delta n v Q phi scale R gain A amplitude handle) y) =
    (bundle (virtualInactive P delta Delta n k v Q scale R gain) y,
      bundle (virtualActive P delta Delta n k v Q phi scale R gain A amplitude handle) y) := by
  have heq : ∀ r ∈ Set.Ioo (0 : ℝ) 1,
      (bundle (actualInactive P delta Delta n v Q scale R gain) (r • y), bundle (actualActive P delta Delta n v Q phi scale R gain A amplitude handle) (r • y)) =
      (bundle (virtualInactive P delta Delta n k v Q scale R gain) (r • y), bundle (virtualActive P delta Delta n k v Q phi scale R gain A amplitude handle) (r • y)) := by
    intro r hr
    exact actual_paired_full_bundle_factors_through_prefix P delta Delta hd hdD n k v Q phi scale R gain A amplitude handle (r • y)
      (fun i hi => flat_closed_scales_to_strict delta hd _ y (hflat i hi) r hr)
  apply Prod.ext
  · apply bundle_eq_of_radial_strict_approximations _ _
      (actualInactive_contDiff_two P delta Delta hd hdD n v Q scale R gain hR hQ)
      (virtualInactive_contDiff_two P delta Delta hd hdD n k v Q scale R gain hR hQ) y
    exact fun r hr => congrArg Prod.fst (heq r hr)
  · apply bundle_eq_of_radial_strict_approximations _ _
      (actualActive_contDiff_two P delta Delta hd hdD n v Q phi scale R gain A amplitude handle hR hQ hphi)
      (virtualActive_contDiff_two P delta Delta hd hdD n k v Q phi scale R gain A amplitude handle hR hQ hphi) y
    exact fun r hr => congrArg Prod.snd (heq r hr)

end OriginalPhysicalPairedShellPrefix

namespace OriginalPhysicalPairedShellPrefix
open FangqingPacketLeakage FangqingShellPrefixLocality
open FangqingInactiveShellClass FangqingLocalizedSeedJets FangqingPublicShellProfiles
open FangqingAmplifier OriginalPacketOrientationNormalization FangqingPathEdgeRegularity

variable {A0 B0 W : Type*}
  [NormedAddCommGroup A0] [InnerProductSpace ℝ A0] [CompleteSpace A0]
  [NormedAddCommGroup B0] [InnerProductSpace ℝ B0] [CompleteSpace B0]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]

theorem actual_physical_inactive_public_closed_no_handle
    (P : FlatCubic.Profile) (delta Delta : ℝ) (hd : 0 < delta) (hdD : delta ≤ Delta)
    (n : ℕ) (C : A0 ≃ₗᵢ[ℝ] B0) (h : A0) (tail : Fin (n + 2) → W)
    (q nu scale R gain : ℝ) (hR : 0 < R) (y : PhysicalSpace A0 B0 W)
    (hflat : ∀ i : Fin (n + 2), |inner ℝ (pathDirection n (physicalFrame C h n tail) i) y| ≤ delta / 2) :
    bundle (inactiveShell (QPhysical q nu C)
      (fun z => scale * pathEdge P delta Delta (n + 2) (physicalFrame C h n tail) z) R gain) y =
      bundle (publicEndpoint (QPhysical q nu C) R gain) y :=
  actual_inactive_full_bundle_public_closed P delta Delta hd hdD n (physicalFrame C h n tail) (QPhysical q nu C) scale R gain y
    hR (FangqingAmplifierRegularity.physical_quadratic_contDiff q nu C) hflat

theorem actual_physical_paired_closed_prefix_full_bundle
    (P : FlatCubic.Profile) (delta Delta : ℝ) (hd : 0 < delta) (hdD : delta ≤ Delta)
    (n k : ℕ) (C : A0 ≃ₗᵢ[ℝ] B0) (h : A0) (tail : Fin (n + 2) → W)
    (phi : ℝ → ℝ) (hphi : ContDiff ℝ 3 phi) (q nu scale R gain A amplitude : ℝ) (hR : 0 < R)
    (y : PhysicalSpace A0 B0 W)
    (hflat : ∀ i : Fin (n + 2), k ≤ i.val → |inner ℝ (pathDirection n (physicalFrame C h n tail) i) y| ≤ delta / 2) :
    let v := physicalFrame C h n tail
    let Q := QPhysical q nu C
    let H0 := inactiveShell Q (fun z => scale * pathEdge P delta Delta (n + 2) v z) R gain
    let H1 := fun z => H0 z - localizedSeed theta phi R A amplitude (mkPhysical h (0 : B0) (0 : W)) z
    (bundle H0 y, bundle H1 y) =
      (bundle (virtualInactive P delta Delta n k v Q scale R gain) y,
       bundle (virtualActive P delta Delta n k v Q phi scale R gain A amplitude (mkPhysical h (0 : B0) (0 : W))) y) :=
  actual_paired_full_bundle_factors_through_prefix_closed P delta Delta hd hdD n k (physicalFrame C h n tail) (QPhysical q nu C)
    phi scale R gain A amplitude (mkPhysical h (0 : B0) (0 : W)) y hR
    (FangqingAmplifierRegularity.physical_quadratic_contDiff q nu C) hphi hflat

end OriginalPhysicalPairedShellPrefix


open scoped ContDiff NNReal

/- A shared actual endpoint pair, all analytic/minimizer claims, and literal
closed-flat value-gradient-Hessian prefix factorization. The post-activation
factorization is explicitly conditional on the later edges being flat. This
source does not assert that arbitrary off-event fixed-frame responses reveal
one direction, nor that a Haar/resisting event has already been generated.
Fresh original-claim correspondence must decide the scope of item (iv). -/


namespace OriginalPairedShellComplete

open FangqingAmplifier FangqingPathEdgeRegularity FangqingActualInactivePacket
  FangqingInactiveShellClass FangqingLocalizedSeedJets FangqingActiveShellLargerWidth
  FangqingPublicShellProfiles OriginalPacketOrientationNormalization
  OriginalPhysicalPacketMinimizer OriginalPacketDistanceGapBounds
  FangqingPhysicalPairedShellMinimizers FangqingRawEndpointDifferenceJets
  FangqingWidePairedShellRateBudgets FangqingPairedShellAnalyticItems
  FangqingShellPrefixLocality OriginalPhysicalPairedShellPrefix FangqingPacketLeakage

noncomputable section

set_option maxHeartbeats 4000000

universe u

theorem actual_shared_paired_shell_with_closed_prefix_locality
    (P : FlatCubic.Profile) (phi : ℝ → ℝ) (Bp left right Cm Cw : ℝ)
    (hCm : 0 ≤ Cm) (hCw : 4 * (Cm + 2) ≤ Cw)
    (hp : ContDiff ℝ 3 phi) (hl : ∀ t, t < -Bp → phi t = left) (hr : ∀ t, Bp < t → phi t = right)
    (hcore : ∀ t, |t| < 1 → phi t = t) :
    ∃ Ce : ℝ≥0, ∃ K : ℝ, 0 ≤ K ∧ ∃ Kc : ℝ, 0 ≤ Kc ∧ ∃ Ks : ℝ, 0 ≤ Ks ∧ ∃ Kd : ℝ, 0 ≤ Kd ∧
    ∀ (A0 B0 W : Type u)
      [NormedAddCommGroup A0] [InnerProductSpace ℝ A0] [FiniteDimensional ℝ A0]
      [NormedAddCommGroup B0] [InnerProductSpace ℝ B0] [FiniteDimensional ℝ B0]
      [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W],
    ∀ (C : A0 ≃ₗᵢ[ℝ] B0) (h : A0) (n : ℕ) (tail : Fin (n + 2) → W)
      (delta omega q scale lam : ℝ),
      ‖h‖ = 1 → Orthonormal ℝ tail → 0 < delta → delta ≤ omega → 1 ≤ q →
      0 < scale → 0 < lam → omega = Cw * lam * q ^ 2 → ((n + 2 : ℕ) : ℝ) ≤ Cm * q →
      let nu := scale * lam
      let D := distanceScale q omega
      let Cs := 2 * Cw
      let Cmin := 2 * Cw * (Cm + 2)
      let A := (1 + 2 * Ks * Cs + Cmin) * D
      let R := 2 * A
      let s := Cs * nu * D
      let Q := QPhysical q nu C
      let g := fun z => scale * pathEdge P delta omega (n + 2) (physicalFrame C h n tail) z
      let M : ℝ := (4 * Ce : ℝ) * scale * omega
      let gain := (16 * K + 1) * M
      let F0 := inactiveShell Q g R gain
      let F1 := fun z => F0 z - localizedSeed theta phi R A (s * A) (mkPhysical h 0 0) z
      let L0 := nu * (q + 2) + 16 * K * M + gain * Kc
      let rho0 := K * ((8 * Ce : ℝ) * scale) + 21 * K * M / R + gain * (Kc / R)
      let CL := 7 / 2 + 4 * (Ce : ℝ) * Cw * (16 * K + (16 * K + 1) * Kc)
      let Crho := 8 * K * (Ce : ℝ) + 4 * (Ce : ℝ) * (21 * K + (16 * K + 1) * Kc) + Ks * Cs
      (AnalyticClass F0 (nu / 2) (CL * nu * q ^ 2) (Crho * scale) ∧
      AnalyticClass F1 (nu / 2) (CL * nu * q ^ 2) (Crho * scale) ∧
      ContDiff ℝ 3 (fun z => F1 z - F0 z) ∧
      (∀ j, j ≤ 3 → ∀ z, ‖iteratedFDeriv ℝ j (fun z => F1 z - F0 z) z‖ ≤ Kd * (s * A) / D ^ j) ∧
      (∀ z, |F1 z - F0 z| ≤ Kd * (s * A)) ∧
      (∀ Y, F0 0 ≤ F0 Y) ∧
      ∃ Z : PhysicalSpace A0 B0 W,
        (∀ Y, F1 Z ≤ F1 Y) ∧ (∀ Y, (∀ X, F1 Y ≤ F1 X) → Y = Z) ∧
        ‖Z‖ ≤ Cmin * D ∧
        F1 0 - F1 Z ≤ 4 * Cw ^ 2 * nu * D ^ 2 ∧
        (∀ j : Fin (n + 3), (j.val : ℝ) ≤ q → 3 * q * omega ≤ inner ℝ (physicalFrame C h n tail j) Z)) ∧
      (∀ Z : PhysicalSpace A0 B0 W, (∀ Y, F1 Z ≤ F1 Y) →
        ∀ Y, rawPacket C h n tail (FlatCubic.edge P delta omega) q nu scale (scale * (2 * omega ^ 2 / Real.sqrt q)) Z ≤
          rawPacket C h n tail (FlatCubic.edge P delta omega) q nu scale (scale * (2 * omega ^ 2 / Real.sqrt q)) Y) ∧
      (∀ y : PhysicalSpace A0 B0 W,
        (∀ i : Fin (n + 2), |inner ℝ (pathDirection n (physicalFrame C h n tail) i) y| ≤ delta / 2) →
        bundle F0 y = bundle (publicEndpoint Q R gain) y) ∧
      (∀ (k : ℕ) (y : PhysicalSpace A0 B0 W),
        (∀ i : Fin (n + 2), k ≤ i.val → |inner ℝ (pathDirection n (physicalFrame C h n tail) i) y| ≤ delta / 2) →
        (bundle F0 y, bundle F1 y) =
          (bundle (virtualInactive P delta omega n k (physicalFrame C h n tail) Q scale R gain) y,
           bundle (virtualActive P delta omega n k (physicalFrame C h n tail) Q phi scale R gain A (s * A) (mkPhysical h 0 0)) y)) ∧
      (∀ (k : ℕ) (w : Fin (n + 3) → PhysicalSpace A0 B0 W),
        (∀ i : Fin (n + 3), i.val < k + 1 → physicalFrame C h n tail i = w i) →
        virtualInactive P delta omega n k (physicalFrame C h n tail) Q scale R gain =
          virtualInactive P delta omega n k w Q scale R gain ∧
        virtualActive P delta omega n k (physicalFrame C h n tail) Q phi scale R gain A (s * A) (mkPhysical h 0 0) =
          virtualActive P delta omega n k w Q phi scale R gain A (s * A) (mkPhysical h 0 0)) := by
  obtain ⟨Ce, K, hK, Kc, hKc, Ks, hKs, Kd, hKd, hAnalytic⟩ :=
    actual_paired_shell_analytic_items.{u} P phi Bp left right Cm Cw hCm hCw hp hl hr hcore
  refine ⟨Ce, K, hK, Kc, hKc, Ks, hKs, Kd, hKd, ?_⟩
  intro A0 B0 W inst inst' inst'' instB instB' instB'' instW instW' instW'' C h n tail
    delta omega q scale lam hh ht hd hdw hq hscale hlam homega hn
    nu D Cs Cmin A R s Q g M gain F0 F1 L0 rho0 CL Crho
  have hA := hAnalytic A0 B0 W C h n tail delta omega q scale lam
    hh ht hd hdw hq hscale hlam homega hn
  have hCw0 : 0 < Cw := by linarith only [hCm, hCw]
  have hw : 0 < omega := hd.trans_le hdw
  have hq0 : 0 < q := by linarith only [hq]
  have hR : 0 < R := by
    dsimp [R, A, D, Cs, Cmin, distanceScale]
    positivity
  have hnu : 0 < nu := mul_pos hscale hlam
  have hD : 0 < D := by dsimp [D, distanceScale]; positivity
  have hCs : 0 ≤ Cs := by dsimp [Cs]; positivity
  have hCmin : 0 ≤ Cmin := by dsimp [Cmin]; positivity
  obtain ⟨hDA, hWidth, hMinA⟩ :=
    FangqingActiveShellLargerWidth.larger_width_choice Ks Cs Cmin D hKs hCs hCmin hD
  have hAp : 0 < A := hD.trans_le hDA
  have hAR : A ≤ R := by dsimp [R]; linarith only [hAp]
  refine ⟨hA, ?_, ?_, ?_, ?_⟩
  · obtain ⟨Zraw, hm, hu, hnorm, hgap, hbulk⟩ := actual_physical_minimizer_norm_gap_bulk P C h hh n tail ht
      delta omega q Cm Cw scale lam hd hdw hq hCm hCw hscale hlam homega hn
    have hzA : ‖Zraw‖ < A := hnorm.trans_lt hMinA
    have hzR : ‖Zraw‖ < R := hzA.trans_le hAR
    have hhandle : ‖mkPhysical h (0 : B0) (0 : W)‖ ≤ 1 := by
      have hn1 := WithLp.prod_norm_sq_eq_of_L2 (mkPhysical h (0 : B0) (0 : W))
      have hn2 := WithLp.prod_norm_sq_eq_of_L2 (WithLp.toLp 2 (h, (0 : B0)))
      change ‖mkPhysical h (0 : B0) (0 : W)‖ ^ 2 = ‖WithLp.toLp 2 (h, (0 : B0))‖ ^ 2 + ‖(0 : W)‖ ^ 2 at hn1
      change ‖WithLp.toLp 2 (h, (0 : B0))‖ ^ 2 = ‖h‖ ^ 2 + ‖(0 : B0)‖ ^ 2 at hn2
      rw [hh, norm_zero] at hn2
      rw [norm_zero] at hn1
      nlinarith only [hn1, hn2, norm_nonneg (mkPhysical h (0 : B0) (0 : W))]
    have hseed := actual_seed_ratio q omega Cw lam scale hq0 homega
    have hi : ∀ Y : PhysicalSpace A0 B0 W, inner ℝ (mkPhysical h (0 : B0) (0 : W)) Y = inner ℝ h Y.fst.fst := by
      intro Y
      change (inner ℝ h Y.fst.fst + inner ℝ (0 : B0) Y.fst.snd) + inner ℝ (0 : W) Y.snd = _
      simp only [inner_zero_left, add_zero]
    have hRaw : ∀ Y : PhysicalSpace A0 B0 W,
        rawPacket C h n tail (FlatCubic.edge P delta omega) q nu scale (scale * (2 * omega ^ 2 / Real.sqrt q)) Y =
          Q Y + g Y - s * inner ℝ (mkPhysical h (0 : B0) (0 : W)) Y := by
      intro Y
      rw [rawPacket_literal, hseed, hi]
      rfl
    have hrawmin : ∀ Y, Q Zraw + g Zraw - s * inner ℝ (mkPhysical h (0 : B0) (0 : W)) Zraw ≤
        Q Y + g Y - s * inner ℝ (mkPhysical h (0 : B0) (0 : W)) Y := by
      intro Y
      rw [← hRaw Zraw, ← hRaw Y]
      exact hm Y
    obtain ⟨hm1, hu1⟩ := FangqingShellMinimizerTransfer.actual_active_minimizer_preserved
      Q g phi R A s gain (nu / 2) hR hAp (half_pos hnu) (mkPhysical h 0 0) Zraw
      hhandle hcore hzR hzA hrawmin hA.2.1.1 hA.2.1.2.1
    intro Z hZ Y
    have hsame : Z = Zraw := hu1 Z hZ
    rw [hsame]
    exact hm Y
  · intro y hy
    exact actual_physical_inactive_public_closed_no_handle P delta omega hd hdw n C h tail
      q nu scale R gain hR y hy
  · intro k y hy
    exact actual_physical_paired_closed_prefix_full_bundle P delta omega hd hdw n k C h tail
      phi hp q nu scale R gain A (s * A) hR y hy
  · intro k w hw
    exact virtual_paired_prefix_invariant P delta omega n k (physicalFrame C h n tail) w hw
      Q phi scale R gain A (s * A) (mkPhysical h 0 0)

end
end OriginalPairedShellComplete
end LegacyAnalyticPrefix

namespace FangqingPrefixAdaptedModel
variable {E : Type*} [Zero E] {m : ℕ}
def mask (k : ℕ) (V : Fin m → E) : Fin m → E := fun i => if i.val < k then V i else 0
end FangqingPrefixAdaptedModel
namespace OriginalActualPairedPacketRun
abbrev Response (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] := ℝ × E × (E →L[ℝ] E)
end OriginalActualPairedPacketRun


/- Actual paired endpoint replies in the executed disclosure protocol.
   All flat cores below are derived from small undisclosed COLUMN projections;
   no target reply equality is assumed. -/

open scoped Topology BigOperators

namespace OriginalActualPairedPacketExecution
open FangqingAmplifier FangqingPacketLeakage FangqingInactiveShellClass
  FangqingLocalizedSeedJets FangqingPublicShellProfiles OriginalPacketOrientationNormalization
  FangqingShellPrefixLocality OriginalPhysicalPairedShellPrefix

noncomputable section
set_option maxHeartbeats 2000000

variable {A B W : Type*}
  [NormedAddCommGroup A] [InnerProductSpace ℝ A] [CompleteSpace A]
  [NormedAddCommGroup B] [InnerProductSpace ℝ B] [CompleteSpace B]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]

theorem physical_first_inner (C : A ≃ₗᵢ[ℝ] B) (h : A) (n : ℕ)
    (tail : Fin (n + 2) → W) (y : PhysicalSpace A B W) :
    inner ℝ (physicalFrame C h n tail 0) y = inner ℝ h (C.symm y.fst.snd) := by
  change (inner ℝ (0 : A) y.fst.fst + inner ℝ (C h) y.fst.snd) + inner ℝ (0 : W) y.snd = _
  rw [inner_zero_left, inner_zero_left, zero_add, add_zero]
  rw [← C.apply_symm_apply y.fst.snd, C.inner_map_map]
  simp only [C.symm_apply_apply]

theorem physical_tail_inner (C : A ≃ₗᵢ[ℝ] B) (h : A) (n : ℕ)
    (tail : Fin (n + 2) → W) (y : PhysicalSpace A B W) (j : Fin (n + 2)) :
    inner ℝ (physicalFrame C h n tail j.succ) y = inner ℝ (tail j) y.snd := by
  change (inner ℝ (0 : A) y.fst.fst + inner ℝ (0 : B) y.fst.snd) + inner ℝ (tail j) y.snd = _
  simp only [inner_zero_left, zero_add]

theorem column_bounds_give_flat_edges
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (n k : ℕ) (v : Fin (n + 3) → E) (y : E) (delta : ℝ) (hd : 0 < delta)
    (hsmall : ∀ j : Fin (n + 3), k ≤ j.val → |inner ℝ (v j) y| ≤ delta / 8) :
    ∀ i : Fin (n + 2), k ≤ i.val → |inner ℝ (pathDirection n v i) y| ≤ delta / 2 := by
  intro i hi
  have hleft := hsmall i.castSucc (by simpa only [Fin.val_castSucc] using hi)
  have hright := hsmall i.succ (by simp only [Fin.val_succ]; omega)
  rw [pathDirection, inner_sub_left]
  have hab := abs_sub (inner ℝ (v i.castSucc) y) (inner ℝ (v i.succ) y)
  linarith only [hab, hleft, hright, hd]

theorem inactive_columns_small
    (C : A ≃ₗᵢ[ℝ] B) (h : A) (n : ℕ) (tail : Fin (n + 2) → W)
    (y : PhysicalSpace A B W) (delta : ℝ)
    (hhandle : |inner ℝ h (C.symm y.fst.snd)| ≤ delta / 8)
    (htail : ∀ j, |inner ℝ (tail j) y.snd| ≤ delta / 8) :
    ∀ j : Fin (n + 3), |inner ℝ (physicalFrame C h n tail j) y| ≤ delta / 8 := by
  intro j
  refine Fin.cases ?_ (fun i => ?_) j
  · rw [physical_first_inner]; exact hhandle
  · rw [physical_tail_inner]; exact htail i

theorem active_later_columns_small
    (C : A ≃ₗᵢ[ℝ] B) (h : A) (n k : ℕ) (tail : Fin (n + 2) → W)
    (y : PhysicalSpace A B W) (delta : ℝ)
    (htail : ∀ j, k ≤ j.val → |inner ℝ (tail j) y.snd| ≤ delta / 8) :
    ∀ j : Fin (n + 3), k + 1 ≤ j.val → |inner ℝ (physicalFrame C h n tail j) y| ≤ delta / 8 := by
  intro j
  refine Fin.cases ?_ (fun i => ?_) j
  · intro hj; simp only [Fin.val_zero] at hj; omega
  · intro hj
    rw [physical_tail_inner]
    exact htail i (by simp only [Fin.val_succ] at hj; omega)

theorem masked_tail_columns_small
    (n k disclosed : ℕ) (tail : Fin (n + 2) → W) (y : W) (delta : ℝ) (hd : 0 < delta)
    (htail : ∀ j, k ≤ j.val → |inner ℝ (tail j) y| ≤ delta / 8) :
    ∀ j, k ≤ j.val → |inner ℝ (FangqingPrefixAdaptedModel.mask disclosed tail j) y| ≤ delta / 8 := by
  intro j hj
  by_cases hdj : j.val < disclosed
  · simpa only [FangqingPrefixAdaptedModel.mask, if_pos hdj] using htail j hj
  · simp only [FangqingPrefixAdaptedModel.mask, if_neg hdj, inner_zero_left, abs_zero]
    positivity

theorem physical_masked_tail_preserves_one_boundary
    (C : A ≃ₗᵢ[ℝ] B) (h : A) (n k : ℕ) (tail : Fin (n + 2) → W) :
    ∀ j : Fin (n + 3), j.val < (k + 1) + 1 →
      physicalFrame C h n tail j =
        physicalFrame C h n (FangqingPrefixAdaptedModel.mask (min (k + 1) (n + 2)) tail) j := by
  intro j
  refine Fin.cases ?_ (fun i => ?_) j
  · intro _; rfl
  · intro hj
    have hik : i.val < min (k + 1) (n + 2) := lt_min (by simp only [Fin.val_succ] at hj; omega) i.isLt
    simp only [physicalFrame, Fin.cons_succ, FangqingPrefixAdaptedModel.mask, if_pos hik]

theorem physical_bundles_equal_of_common_prefix_and_column_bounds
    (P : FlatCubic.Profile) (delta omega : ℝ) (hd : 0 < delta) (hdw : delta ≤ omega)
    (n k : ℕ) (C : A ≃ₗᵢ[ℝ] B) (h : A) (tail tail' : Fin (n + 2) → W)
    (phi : ℝ → ℝ) (hphi : ContDiff ℝ 3 phi) (q nu scale R gain width amplitude : ℝ) (hR : 0 < R)
    (y : PhysicalSpace A B W)
    (hprefix : ∀ j : Fin (n + 3), j.val < k + 1 → physicalFrame C h n tail j = physicalFrame C h n tail' j)
    (hsmall : ∀ j : Fin (n + 3), k ≤ j.val → |inner ℝ (physicalFrame C h n tail j) y| ≤ delta / 8)
    (hsmall' : ∀ j : Fin (n + 3), k ≤ j.val → |inner ℝ (physicalFrame C h n tail' j) y| ≤ delta / 8) :
    (bundle (actualInactive P delta omega n (physicalFrame C h n tail) (QPhysical q nu C) scale R gain) y,
      bundle (actualActive P delta omega n (physicalFrame C h n tail) (QPhysical q nu C) phi scale R gain width amplitude (mkPhysical h 0 0)) y) =
    (bundle (actualInactive P delta omega n (physicalFrame C h n tail') (QPhysical q nu C) scale R gain) y,
      bundle (actualActive P delta omega n (physicalFrame C h n tail') (QPhysical q nu C) phi scale R gain width amplitude (mkPhysical h 0 0)) y) := by
  have hV := actual_physical_paired_closed_prefix_full_bundle P delta omega hd hdw n k C h tail
    phi hphi q nu scale R gain width amplitude hR y (column_bounds_give_flat_edges n k _ y delta hd hsmall)
  have hW := actual_physical_paired_closed_prefix_full_bundle P delta omega hd hdw n k C h tail'
    phi hphi q nu scale R gain width amplitude hR y (column_bounds_give_flat_edges n k _ y delta hd hsmall')
  have hInv := virtual_paired_prefix_invariant P delta omega n k (physicalFrame C h n tail)
    (physicalFrame C h n tail') hprefix (QPhysical q nu C) phi scale R gain width amplitude (mkPhysical h 0 0)
  dsimp only at hV hW
  rw [hInv.1, hInv.2] at hV
  exact hV.trans hW.symm

end
end OriginalActualPairedPacketExecution

open scoped Topology BigOperators
namespace OriginalRawPacketResistingLocality
open FangqingAmplifier FangqingPacketLeakage OriginalPacketOrientationNormalization
  OriginalPhysicalPacketMinimizer FangqingShellPrefixLocality OriginalActualPairedPacketExecution
noncomputable section
set_option maxHeartbeats 1400000
variable {A B W : Type*}
  [NormedAddCommGroup A] [InnerProductSpace ℝ A] [CompleteSpace A] [FiniteDimensional ℝ A]
  [NormedAddCommGroup B] [InnerProductSpace ℝ B] [CompleteSpace B] [FiniteDimensional ℝ B]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W] [FiniteDimensional ℝ W]

theorem raw_packet_bundle_eq_of_strict_flat_common_prefix
    (P : FlatCubic.Profile) (delta omega : ℝ) (hd : 0 < delta) (hdw : delta ≤ omega)
    (C : A ≃ₗᵢ[ℝ] B) (h : A) (n k : ℕ) (tail tail' : Fin (n + 2) → W)
    (q nu scale seed : ℝ) (y : PhysicalSpace A B W)
    (hprefix : ∀ j : Fin (n + 3), j.val < k + 1 → physicalFrame C h n tail j = physicalFrame C h n tail' j)
    (hf : ∀ i : Fin (n + 2), k ≤ i.val → |inner ℝ (pathDirection n (physicalFrame C h n tail) i) y| < delta / 2)
    (hf' : ∀ i : Fin (n + 2), k ≤ i.val → |inner ℝ (pathDirection n (physicalFrame C h n tail') i) y| < delta / 2) :
    bundle (rawPacket C h n tail (FlatCubic.edge P delta omega) q nu scale seed) y =
      bundle (rawPacket C h n tail' (FlatCubic.edge P delta omega) q nu scale seed) y := by
  have hnot (i : Fin (n + 2)) (hi : i ∉ prefixEdges n k) : k ≤ i.val := by
    by_contra hlt
    exact hi (Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩)
  have h1 := edgeSum_eventually_eq_selected P delta omega hd hdw
    (pathDirection n (physicalFrame C h n tail)) (prefixEdges n k) y (fun i hi => hf i (hnot i hi))
  have h2 := edgeSum_eventually_eq_selected P delta omega hd hdw
    (pathDirection n (physicalFrame C h n tail')) (prefixEdges n k) y (fun i hi => hf' i (hnot i hi))
  have hs := selected_path_prefix_invariant n k (physicalFrame C h n tail) (physicalFrame C h n tail') hprefix
  apply bundle_of_eventuallyEq
  filter_upwards [h1, h2] with z hz hz'
  rw [rawPacket_literal, rawPacket_literal, hz, hz', hs]

theorem future_zero_columns_give_strict_flat_edges
    (C : A ≃ₗᵢ[ℝ] B) (h : A) (n k : ℕ) (tail : Fin (n + 2) → W)
    (y : PhysicalSpace A B W) (delta : ℝ) (hd : 0 < delta)
    (hz : ∀ j : Fin (n + 2), k ≤ j.val → inner ℝ (tail j) y.snd = 0) :
    ∀ i : Fin (n + 2), k + 1 ≤ i.val →
      |inner ℝ (pathDirection n (physicalFrame C h n tail) i) y| < delta / 2 := by
  have hc (j : Fin (n + 3)) : k + 1 ≤ j.val → inner ℝ (physicalFrame C h n tail j) y = 0 := by
    refine Fin.cases ?_ (fun a => ?_) j
    · intro hj; simp only [Fin.val_zero] at hj; omega
    · intro hj
      rw [physical_tail_inner]
      exact hz a (by simp only [Fin.val_succ] at hj; omega)
  intro i hi
  rw [pathDirection, inner_sub_left, hc i.castSucc (by simpa only [Fin.val_castSucc] using hi),
    hc i.succ (by simp only [Fin.val_succ]; omega), sub_self, abs_zero]
  exact div_pos hd (by norm_num)

theorem actual_raw_bundle_eq_one_boundary_mask
    (P : FlatCubic.Profile) (delta omega : ℝ) (hd : 0 < delta) (hdw : delta ≤ omega)
    (C : A ≃ₗᵢ[ℝ] B) (h : A) (n k : ℕ) (tail : Fin (n + 2) → W)
    (q nu scale seed : ℝ) (y : PhysicalSpace A B W)
    (hz : ∀ j : Fin (n + 2), k ≤ j.val → inner ℝ (tail j) y.snd = 0) :
    bundle (rawPacket C h n tail (FlatCubic.edge P delta omega) q nu scale seed) y =
      bundle (rawPacket C h n (FangqingPrefixAdaptedModel.mask (min (k + 1) (n + 2)) tail)
        (FlatCubic.edge P delta omega) q nu scale seed) y := by
  apply raw_packet_bundle_eq_of_strict_flat_common_prefix P delta omega hd hdw C h n (k + 1)
  · exact physical_masked_tail_preserves_one_boundary C h n k tail
  · exact future_zero_columns_give_strict_flat_edges C h n k tail y delta hd hz
  · apply future_zero_columns_give_strict_flat_edges C h n k _ y delta hd
    intro j hj
    unfold FangqingPrefixAdaptedModel.mask
    split_ifs with hji
    · exact hz j hj
    · exact inner_zero_left _

theorem actual_raw_bundle_eq_of_tail_prefix_and_future_zeros
    (P : FlatCubic.Profile) (delta omega : ℝ) (hd : 0 < delta) (hdw : delta ≤ omega)
    (C : A ≃ₗᵢ[ℝ] B) (h : A) (n k : ℕ) (tail tail' : Fin (n + 2) → W)
    (q nu scale seed : ℝ) (y : PhysicalSpace A B W)
    (hp : ∀ j, j.val < k + 1 → tail j = tail' j)
    (hz : ∀ j, k ≤ j.val → inner ℝ (tail j) y.snd = 0)
    (hz' : ∀ j, k ≤ j.val → inner ℝ (tail' j) y.snd = 0) :
    bundle (rawPacket C h n tail (FlatCubic.edge P delta omega) q nu scale seed) y =
      bundle (rawPacket C h n tail' (FlatCubic.edge P delta omega) q nu scale seed) y := by
  apply raw_packet_bundle_eq_of_strict_flat_common_prefix P delta omega hd hdw C h n (k + 1)
  · intro j
    refine Fin.cases ?_ (fun i => ?_) j
    · intro _; rfl
    · intro hi
      have he := hp i (by simp only [Fin.val_succ] at hi; omega)
      simp only [physicalFrame, Fin.cons_succ, he]
  · exact future_zero_columns_give_strict_flat_edges C h n k tail y delta hd hz
  · exact future_zero_columns_give_strict_flat_edges C h n k tail' y delta hd hz'

end
end OriginalRawPacketResistingLocality


namespace FangqingFiniteConstraintOrthogonalUnit

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]

theorem unit_orthogonal_to_finite_family
    {k : ℕ} (points : Fin k → W) (hdim : k < Module.finrank ℝ W) :
    ∃ v : W, ‖v‖ = 1 ∧ ∀ i, inner ℝ v (points i) = 0 := by
  let K : Submodule ℝ W := Submodule.span ℝ (Set.range points)
  have hK : Module.finrank ℝ K ≤ k := by
    simpa only [K, Set.finrank, Fintype.card_fin] using (finrank_range_le_card (R := ℝ) points)
  have hadd := K.finrank_add_finrank_orthogonal
  have hpos : 0 < Module.finrank ℝ Kᗮ := by omega
  obtain ⟨v, hv⟩ := Module.finrank_pos_iff_exists_ne_zero.mp hpos
  have hv0 : (v : W) ≠ 0 := by
    intro hz
    apply hv
    apply Subtype.ext
    exact hz
  have hn : 0 < ‖(v : W)‖ := norm_pos_iff.mpr hv0
  refine ⟨‖(v : W)‖⁻¹ • (v : W), ?_, ?_⟩
  · rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hn), inv_mul_cancel₀ (ne_of_gt hn)]
  · intro i
    have hmem : points i ∈ K := Submodule.subset_span ⟨i, rfl⟩
    rw [real_inner_smul_left, Submodule.inner_left_of_mem_orthogonal hmem v.property, mul_zero]

theorem unit_orthogonal_to_known_columns_and_queries
    {m k : ℕ} (columns : Fin m → W) (queries : Fin k → W)
    (hdim : m + k < Module.finrank ℝ W) :
    ∃ v : W, ‖v‖ = 1 ∧ (∀ i, inner ℝ v (columns i) = 0) ∧
      (∀ j, inner ℝ v (queries j) = 0) := by
  obtain ⟨v, hv, horth⟩ := unit_orthogonal_to_finite_family (Fin.addCases columns queries) hdim
  refine ⟨v, hv, ?_, ?_⟩
  · intro i
    simpa using horth (i.castAdd k)
  · intro j
    simpa using horth (j.natAdd m)

end FangqingFiniteConstraintOrthogonalUnit


namespace FangqingOrthogonalCompletionAvoidingQueries

open FangqingFiniteConstraintOrthogonalUnit

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]

theorem orthonormal_snoc_of_unit
    {k : ℕ} (v : Fin k → W) (hv : Orthonormal ℝ v) (w : W) (hw : ‖w‖ = 1)
    (horth : ∀ i, inner ℝ w (v i) = 0) :
    Orthonormal ℝ (Fin.snoc v w) := by
  rw [orthonormal_iff_ite]
  intro i j
  refine Fin.lastCases ?_ (fun i => ?_) i
  · refine Fin.lastCases ?_ (fun j => ?_) j
    · simp [Fin.snoc_last, real_inner_self_eq_norm_sq, hw]
    · have hne : Fin.last k ≠ j.castSucc := by
        intro he
        have hh := congrArg Fin.val he
        simp only [Fin.val_last, Fin.val_castSucc] at hh
        omega
      simpa only [Fin.snoc_last, Fin.snoc_castSucc, if_neg hne] using horth j
  · refine Fin.lastCases ?_ (fun j => ?_) j
    · have hi : inner ℝ (v i) w = 0 := by rw [real_inner_comm]; exact horth i
      simpa only [Fin.snoc_last, Fin.snoc_castSucc, Fin.castSucc_ne_last, if_false] using hi
    · simpa only [Fin.snoc_castSucc, Fin.castSucc_inj] using (orthonormal_iff_ite.mp hv i j)

theorem extend_orthonormal_family_avoiding_queries
    {k s : ℕ} (initialFrame : Fin k → W) (hprefix : Orthonormal ℝ initialFrame) (queries : Fin s → W)
    (m : ℕ) (hk : k ≤ m) (hdim : m + s ≤ Module.finrank ℝ W) :
    ∃ frame : Fin m → W, Orthonormal ℝ frame ∧
      (∀ i : Fin k, frame (i.castLE hk) = initialFrame i) ∧
      (∀ i : Fin m, k ≤ i.val → ∀ j, inner ℝ (frame i) (queries j) = 0) := by
  induction m, hk using Nat.le_induction with
  | base =>
      refine ⟨initialFrame, hprefix, ?_, ?_⟩
      · intro i
        rfl
      · intro i hi
        omega
  | succ m hk ih =>
      obtain ⟨frame, hframe, hkeep, havoid⟩ := ih (by omega)
      obtain ⟨w, hw, hcols, hqueries⟩ :=
        unit_orthogonal_to_known_columns_and_queries frame queries (by omega)
      refine ⟨Fin.snoc frame w, orthonormal_snoc_of_unit frame hframe w hw hcols, ?_, ?_⟩
      · intro i
        have he : i.castLE (by omega : k ≤ m + 1) = (i.castLE hk).castSucc := Fin.ext rfl
        rw [he, Fin.snoc_castSucc]
        exact hkeep i
      · intro i
        refine Fin.lastCases ?_ (fun i => ?_) i
        · intro _ j
          simpa only [Fin.snoc_last] using hqueries j
        · intro hi j
          simpa only [Fin.snoc_castSucc] using havoid i hi j

theorem completion_avoiding
    {m s : ℕ} (v : Fin m → W) (hv : Orthonormal ℝ v) (k : ℕ) (hk : k ≤ m)
    (queries : Fin s → W) (hdim : m + s ≤ Module.finrank ℝ W) :
    ∃ frame : Fin m → W, Orthonormal ℝ frame ∧
      (∀ i : Fin m, i.val < k → v i = frame i) ∧
      (∀ i : Fin m, k ≤ i.val → ∀ j, inner ℝ (frame i) (queries j) = 0) := by
  let initial : Fin k → W := fun i => v (i.castLE hk)
  have hinj : Function.Injective (fun i : Fin k => i.castLE hk) := by
    intro i j he
    apply Fin.ext
    exact congrArg (fun a : Fin m => a.val) he
  have hi : Orthonormal ℝ initial := hv.comp (fun i : Fin k => i.castLE hk) hinj
  obtain ⟨frame, hframe, hkeep, havoid⟩ := extend_orthonormal_family_avoiding_queries
    initial hi queries m hk hdim
  refine ⟨frame, hframe, ?_, havoid⟩
  intro i hi
  let j : Fin k := ⟨i.val, hi⟩
  have he : j.castLE hk = i := Fin.ext rfl
  have hh := hkeep j
  simpa only [initial, he] using hh.symm

end FangqingOrthogonalCompletionAvoidingQueries

open scoped BigOperators
namespace OriginalDeterministicResistingExecution
noncomputable section
set_option maxHeartbeats 2200000
variable {W Q R : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  [Zero Q] [Zero R] {m N : ℕ}

abbrev Completion (W : Type*) [NormedAddCommGroup W] [InnerProductSpace ℝ W] (m s : ℕ) :=
  ∀ (k : ℕ), k ≤ m → ∀ (v : Fin m → W), Orthonormal ℝ v → ∀ u : Fin s → W,
    {w : Fin m → W // Orthonormal ℝ w ∧
      (∀ i, i.val < k → w i = v i) ∧ (∀ i, k ≤ i.val → ∀ j, inner ℝ (w i) (u j) = 0)}

structure Stage (W Q R : Type*) [NormedAddCommGroup W] [InnerProductSpace ℝ W] (m : ℕ) where
  frame : Fin m → W
  orthonormal : Orthonormal ℝ frame
  history : ℕ → R
  queries : ℕ → Q

def candidates (project : Q → W) (k : ℕ) (queries : ℕ → Q) (y : Q) : Fin (N + 1) → W :=
  fun i => if i.val < k then project (queries i.val) else if i.val = k then project y else 0

def initialStage (v : Fin m → W) (hv : Orthonormal ℝ v) : Stage W Q R m := ⟨v, hv, 0, 0⟩

def step (complete : Completion W m (N + 1)) (hNm : N ≤ m)
    (project : Q → W) (query : ℕ → (ℕ → R) → Q) (oracle : (Fin m → W) → Q → R)
    (k : ℕ) (hk : k < N) (st : Stage W Q R m) : Stage W Q R m :=
  let y := query k st.history
  let w := complete k (by omega) st.frame st.orthonormal (candidates project k st.queries y)
  ⟨w.1, w.2.1, Function.update st.history k (oracle w.1 y), Function.update st.queries k y⟩

def runStages (complete : Completion W m (N + 1)) (hNm : N ≤ m)
    (project : Q → W) (query : ℕ → (ℕ → R) → Q) (oracle : (Fin m → W) → Q → R)
    (v : Fin m → W) (hv : Orthonormal ℝ v) : ℕ → Stage W Q R m
  | 0 => initialStage v hv
  | k + 1 => if hk : k < N then step complete hNm project query oracle k hk
      (runStages complete hNm project query oracle v hv k)
    else runStages complete hNm project query oracle v hv k

def Invariant (project : Q → W) (oracle : (Fin m → W) → Q → R)
    (k : ℕ) (st : Stage W Q R m) : Prop :=
  (∀ r < k, ∀ i, r ≤ i.val → inner ℝ (st.frame i) (project (st.queries r)) = 0) ∧
  (∀ r < k, st.history r = oracle st.frame (st.queries r))

/-- The only oracle interface here is a separately proved local flat-prefix
    identity, not a lower-bound conclusion or target output separation. -/
theorem invariant_step
    (complete : Completion W m (N + 1)) (hNm : N ≤ m)
    (project : Q → W) (query : ℕ → (ℕ → R) → Q) (oracle : (Fin m → W) → Q → R)
    (locality : ∀ (v w : Fin m → W) (k : ℕ) (y : Q),
      (∀ i, i.val < k + 1 → v i = w i) →
      (∀ i, k ≤ i.val → inner ℝ (v i) (project y) = 0) →
      (∀ i, k ≤ i.val → inner ℝ (w i) (project y) = 0) → oracle v y = oracle w y)
    (k : ℕ) (hk : k < N) (st : Stage W Q R m) (hI : Invariant project oracle k st) :
    Invariant project oracle (k + 1) (step complete hNm project query oracle k hk st) := by
  let y := query k st.history
  let w := complete k (by omega) st.frame st.orthonormal (candidates project k st.queries y)
  have hp := w.2.2.1
  have hz := w.2.2.2
  have hzero : ∀ r < k + 1, ∀ i, r ≤ i.val →
      inner ℝ (w.1 i) (project ((Function.update st.queries k y) r)) = 0 := by
    intro r hr i hi
    by_cases hrk : r = k
    · subst r
      rw [Function.update_self]
      have he := hz i hi ⟨k, by omega⟩
      simpa [candidates] using he
    · have hrlt : r < k := by omega
      rw [Function.update_of_ne hrk]
      by_cases hik : i.val < k
      · rw [hp i hik]
        exact hI.1 r hrlt i hi
      · have he := hz i (by omega) ⟨r, by omega⟩
        simpa only [candidates, if_pos hrlt] using he
  refine ⟨hzero, ?_⟩
  intro r hr
  change (Function.update st.history k (oracle w.1 y)) r = oracle w.1 ((Function.update st.queries k y) r)
  by_cases hrk : r = k
  · subst r; simp only [Function.update_self]
  · have hrlt : r < k := by omega
    rw [Function.update_of_ne hrk, Function.update_of_ne hrk, hI.2 r hrlt]
    apply locality st.frame w.1 r (st.queries r)
    · intro i hi
      exact (hp i (by omega)).symm
    · exact hI.1 r hrlt
    · intro i hi
      have he := hzero r hr i hi
      simpa only [Function.update_of_ne hrk] using he

theorem stages_invariant
    (complete : Completion W m (N + 1)) (hNm : N ≤ m)
    (project : Q → W) (query : ℕ → (ℕ → R) → Q) (oracle : (Fin m → W) → Q → R)
    (locality : ∀ (v w : Fin m → W) (k : ℕ) (y : Q),
      (∀ i, i.val < k + 1 → v i = w i) →
      (∀ i, k ≤ i.val → inner ℝ (v i) (project y) = 0) →
      (∀ i, k ≤ i.val → inner ℝ (w i) (project y) = 0) → oracle v y = oracle w y)
    (v : Fin m → W) (hv : Orthonormal ℝ v) (k : ℕ) (hk : k ≤ N) :
    Invariant project oracle k (runStages complete hNm project query oracle v hv k) := by
  induction k with
  | zero => exact ⟨fun r hr => by omega, fun r hr => by omega⟩
  | succ k ih =>
      have hklt : k < N := by omega
      simp only [runStages, dif_pos hklt]
      exact invariant_step complete hNm project query oracle locality k hklt _ (ih (by omega))

section Execution
variable (complete : Completion W m (N + 1)) (hNm : N ≤ m)
    (project : Q → W) (query : ℕ → (ℕ → R) → Q) (oracle : (Fin m → W) → Q → R)
    (v : Fin m → W) (hv : Orthonormal ℝ v)

theorem history_persistence (s t : ℕ) (hst : s ≤ t) (ht : t ≤ N) (r : ℕ) (hr : r < s) :
    (runStages complete hNm project query oracle v hv t).history r =
      (runStages complete hNm project query oracle v hv s).history r := by
  revert ht
  induction t, hst using Nat.le_induction with
  | base => intro _; rfl
  | succ t hst ih =>
      intro ht
      have hlt : t < N := by omega
      have hne : r ≠ t := by omega
      simp only [runStages, dif_pos hlt, step, Function.update_of_ne hne]
      exact ih (by omega)

theorem queries_persistence (s t : ℕ) (hst : s ≤ t) (ht : t ≤ N) (r : ℕ) (hr : r < s) :
    (runStages complete hNm project query oracle v hv t).queries r =
      (runStages complete hNm project query oracle v hv s).queries r := by
  revert ht
  induction t, hst using Nat.le_induction with
  | base => intro _; rfl
  | succ t hst ih =>
      intro ht
      have hlt : t < N := by omega
      have hne : r ≠ t := by omega
      simp only [runStages, dif_pos hlt, step, Function.update_of_ne hne]
      exact ih (by omega)

theorem queried_point_eq_generated (r : ℕ) (hr : r < N) :
    (runStages complete hNm project query oracle v hv N).queries r =
      query r (runStages complete hNm project query oracle v hv r).history := by
  rw [queries_persistence complete hNm project query oracle v hv (r + 1) N (by omega) le_rfl r (by omega)]
  simp only [runStages, dif_pos hr, step, Function.update_self]

def finalFrame (out : (ℕ → R) → Q) : {w : Fin m → W // Orthonormal ℝ w} :=
  let st := runStages complete hNm project query oracle v hv N
  let w := complete N hNm st.frame st.orthonormal (candidates project N st.queries (out st.history))
  ⟨w.1, w.2.1⟩

theorem final_frame_consistency
    (locality : ∀ (v w : Fin m → W) (k : ℕ) (y : Q),
      (∀ i, i.val < k + 1 → v i = w i) →
      (∀ i, k ≤ i.val → inner ℝ (v i) (project y) = 0) →
      (∀ i, k ≤ i.val → inner ℝ (w i) (project y) = 0) → oracle v y = oracle w y)
    (out : (ℕ → R) → Q) (r : ℕ) (hr : r < N) :
    (runStages complete hNm project query oracle v hv N).history r =
      oracle (finalFrame complete hNm project query oracle v hv out).1
        ((runStages complete hNm project query oracle v hv N).queries r) := by
  let st := runStages complete hNm project query oracle v hv N
  let w := complete N hNm st.frame st.orthonormal (candidates project N st.queries (out st.history))
  have hI := stages_invariant complete hNm project query oracle locality v hv N le_rfl
  change Invariant project oracle N st at hI
  change st.history r = oracle w.1 (st.queries r)
  rw [hI.2 r hr]
  apply locality st.frame w.1 r (st.queries r)
  · intro i hi
    exact (w.2.2.1 i (by omega)).symm
  · exact hI.1 r hr
  · intro i hi
    by_cases hin : i.val < N
    · rw [w.2.2.1 i hin]
      exact hI.1 r hr i hi
    · have hz := w.2.2.2 i (by omega) ⟨r, by omega⟩
      simpa only [candidates, if_pos hr] using hz

def realHistory (query : ℕ → (ℕ → R) → Q) (answer : Q → R) : ℕ → (ℕ → R)
  | 0 => 0
  | k + 1 => let hist := realHistory query answer k
      Function.update hist k (answer (query k hist))

theorem final_fixed_oracle_replays_every_real_query
    (locality : ∀ (v w : Fin m → W) (k : ℕ) (y : Q),
      (∀ i, i.val < k + 1 → v i = w i) →
      (∀ i, k ≤ i.val → inner ℝ (v i) (project y) = 0) →
      (∀ i, k ≤ i.val → inner ℝ (w i) (project y) = 0) → oracle v y = oracle w y)
    (out : (ℕ → R) → Q) (k : ℕ) (hk : k ≤ N) :
    realHistory query (oracle (finalFrame complete hNm project query oracle v hv out).1) k =
      (runStages complete hNm project query oracle v hv k).history := by
  induction k with
  | zero => rfl
  | succ k ih =>
      have hklt : k < N := by omega
      have hprev := ih (by omega)
      have hanswer := final_frame_consistency complete hNm project query oracle v hv locality out k hklt
      rw [queried_point_eq_generated complete hNm project query oracle v hv k hklt] at hanswer
      have hp := history_persistence complete hNm project query oracle v hv (k + 1) N (by omega) le_rfl k (by omega)
      rw [hp] at hanswer
      change Function.update _ k _ = _
      rw [hprev, ← hanswer]
      simp only [runStages, dif_pos hklt, step, Function.update_self]

theorem fixed_orthonormal_frame_hides_remaining_output_coordinates
    (complete : Completion W m (N + 1)) (hNm : N ≤ m) (v : Fin m → W) (hv : Orthonormal ℝ v)
    (locality : ∀ (v w : Fin m → W) (k : ℕ) (y : Q),
      (∀ i, i.val < k + 1 → v i = w i) →
      (∀ i, k ≤ i.val → inner ℝ (v i) (project y) = 0) →
      (∀ i, k ≤ i.val → inner ℝ (w i) (project y) = 0) → oracle v y = oracle w y)
    (out : (ℕ → R) → Q) :
    ∃ frame : Fin m → W, Orthonormal ℝ frame ∧
      ∀ i, N ≤ i.val → inner ℝ (frame i)
        (project (out (realHistory query (oracle frame) N))) = 0 := by
  let st := runStages complete hNm project query oracle v hv N
  let w := complete N hNm st.frame st.orthonormal (candidates project N st.queries (out st.history))
  refine ⟨w.1, w.2.1, ?_⟩
  intro i hi
  have hr := final_fixed_oracle_replays_every_real_query complete hNm project query oracle v hv locality out N le_rfl
  change realHistory query (oracle w.1) N = st.history at hr
  rw [hr]
  have hz := w.2.2.2 i hi ⟨N, by omega⟩
  simpa [candidates] using hz

end Execution

end
end OriginalDeterministicResistingExecution


/- Actual minimizer bulk coefficients imply a quantitative chamber
   separation on any sufficiently large unrevealed subset. -/

open scoped BigOperators

namespace OriginalUnrevealedBulkSeparation

open OriginalPacketDistanceGapBounds

noncomputable section

variable {E I : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [Fintype I]

theorem distance_from_unrevealed_coefficients
    (v : I → E) (hv : Orthonormal ℝ v) (J : Finset I) (Z w : E)
    (q omega : ℝ) (hq : 0 ≤ q) (hw : 0 ≤ omega)
    (hcard : q / 4 ≤ (J.card : ℝ))
    (hbulk : ∀ i ∈ J, 3 * q * omega ≤ inner ℝ (v i) Z)
    (hsmall : ∀ i ∈ J, |inner ℝ (v i) w| ≤ q * omega) :
    distanceScale q omega ≤ ‖Z - w‖ := by
  have hcoef : ∀ i ∈ J, (2 * q * omega) ^ 2 ≤ (inner ℝ (v i) (Z - w)) ^ 2 := by
    intro i hi
    have hs : inner ℝ (v i) w ≤ q * omega := (le_abs_self _).trans (hsmall i hi)
    have hd : 2 * q * omega ≤ inner ℝ (v i) (Z - w) := by
      rw [inner_sub_right]
      linarith only [hbulk i hi, hs]
    have hp : 0 ≤ 2 * q * omega := by positivity
    exact (sq_le_sq₀ hp (hp.trans hd)).mpr hd
  have hsum : (J.card : ℝ) * (2 * q * omega) ^ 2 ≤
      ∑ i ∈ J, (inner ℝ (v i) (Z - w)) ^ 2 := by
    simpa only [Finset.sum_const, nsmul_eq_mul] using Finset.sum_le_sum hcoef
  have hB := hv.sum_inner_products_le (Z - w) (s := J)
  simp only [Real.norm_eq_abs, sq_abs] at hB
  have hcount := mul_le_mul_of_nonneg_right hcard (sq_nonneg (2 * q * omega))
  have hsq : (distanceScale q omega) ^ 2 ≤ ‖Z - w‖ ^ 2 := by
    rw [distanceScale_sq q omega hq]
    nlinarith only [hcount, hsum, hB]
  have hD : 0 ≤ distanceScale q omega := by unfold distanceScale; positivity
  nlinarith only [hsq, hD, norm_nonneg (Z - w)]

def finiteProjection (v : I → E) (J : Finset I) (Z : E) : E :=
  ∑ i ∈ J, inner ℝ (v i) Z • v i

theorem finiteProjection_keeps_selected_coefficients
    (v : I → E) (hv : Orthonormal ℝ v) (J : Finset I) (Z : E) (i : I) (hi : i ∈ J) :
    inner ℝ (v i) (finiteProjection v J Z) = inner ℝ (v i) Z := by
  exact hv.inner_right_sum (fun i => inner ℝ (v i) Z) hi

theorem finiteProjection_is_actual_orthogonal_projection [FiniteDimensional ℝ E]
    (v : I → E) (hv : Orthonormal ℝ v) (J : Finset I) (Z : E) :
    finiteProjection v J Z =
      (Submodule.span ℝ (v '' (J : Set I))).starProjection Z := by
  let K := Submodule.span ℝ (v '' (J : Set I))
  have hmem : finiteProjection v J Z ∈ K := by
    apply Submodule.sum_mem
    intro i hi
    exact Submodule.smul_mem K _ (Submodule.subset_span ⟨i, hi, rfl⟩)
  have hker : K ≤ LinearMap.ker (innerSL ℝ (Z - finiteProjection v J Z)).toLinearMap := by
    apply Submodule.span_le.mpr
    rintro x ⟨i, hi, rfl⟩
    change inner ℝ (Z - finiteProjection v J Z) (v i) = 0
    rw [real_inner_comm, inner_sub_right, finiteProjection_keeps_selected_coefficients v hv J Z i hi]
    ring
  symm
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero hmem
  intro Y hY
  have hh := hker hY
  change inner ℝ (Z - finiteProjection v J Z) Y = 0 at hh
  exact hh

theorem finiteProjection_large_on_bulk
    (v : I → E) (hv : Orthonormal ℝ v) (J : Finset I) (Z : E)
    (q omega : ℝ) (hq : 0 ≤ q) (hw : 0 ≤ omega)
    (hcard : q / 4 ≤ (J.card : ℝ))
    (hbulk : ∀ i ∈ J, 3 * q * omega ≤ inner ℝ (v i) Z) :
    distanceScale q omega ≤ ‖finiteProjection v J Z‖ := by
  have hh := distance_from_unrevealed_coefficients v hv J (finiteProjection v J Z) 0 q omega hq hw hcard
    (fun i hi => by rw [finiteProjection_keeps_selected_coefficients v hv J Z i hi]; exact hbulk i hi)
    (fun _ _ => by simpa using mul_nonneg hq hw)
  simpa only [sub_zero] using hh

universe u

theorem actual_private_packet_unrevealed_separation
    {A B W : Type u}
    [NormedAddCommGroup A] [InnerProductSpace ℝ A] [FiniteDimensional ℝ A]
    [NormedAddCommGroup B] [InnerProductSpace ℝ B] [FiniteDimensional ℝ B]
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
    (P : FlatCubic.Profile) (C : A ≃ₗᵢ[ℝ] B) (h : A) (hh : ‖h‖ = 1)
    (n : ℕ) (tail : Fin (n + 2) → W) (ht : Orthonormal ℝ tail)
    (delta omega q Cm Cw scale lam : ℝ)
    (hd : 0 < delta) (hdw : delta ≤ omega) (hq : 1 ≤ q)
    (hCm : 0 ≤ Cm) (hCw : 4 * (Cm + 2) ≤ Cw) (hscale : 0 < scale) (hlam : 0 < lam)
    (homega : omega = Cw * lam * q ^ 2) (hn : ((n + 2 : ℕ) : ℝ) ≤ Cm * q) :
    ∃ Z : FangqingAmplifier.PhysicalSpace A B W,
      (∀ Y, OriginalPhysicalPacketMinimizer.rawPacket C h n tail (FlatCubic.edge P delta omega)
          q (scale * lam) scale (scale * (2 * omega ^ 2 / Real.sqrt q)) Z ≤
        OriginalPhysicalPacketMinimizer.rawPacket C h n tail (FlatCubic.edge P delta omega)
          q (scale * lam) scale (scale * (2 * omega ^ 2 / Real.sqrt q)) Y) ∧
      ∀ J : Finset (Fin (n + 3)),
        (∀ j ∈ J, (j.val : ℝ) ≤ q) → q / 4 ≤ (J.card : ℝ) →
        distanceScale q omega ≤ ‖finiteProjection
          (OriginalPacketOrientationNormalization.physicalFrame C h n tail) J Z‖ ∧
        (∀ w : FangqingAmplifier.PhysicalSpace A B W,
          (∀ j ∈ J, |inner ℝ (OriginalPacketOrientationNormalization.physicalFrame C h n tail j) w| ≤ q * omega) →
          distanceScale q omega ≤ ‖Z - w‖) := by
  obtain ⟨Z, hm, _, _, _, hb⟩ := actual_physical_minimizer_norm_gap_bulk P C h hh n tail ht
    delta omega q Cm Cw scale lam hd hdw hq hCm hCw hscale hlam homega hn
  have hv := OriginalPhysicalPacketMinimizer.physicalFrame_orthonormal C h hh n tail ht
  have hq0 : 0 ≤ q := by linarith
  have hw0 : 0 ≤ omega := (hd.trans_le hdw).le
  refine ⟨Z, hm, ?_⟩
  intro J hJ hcard
  have hbulk : ∀ j ∈ J, 3 * q * omega ≤ inner ℝ
      (OriginalPacketOrientationNormalization.physicalFrame C h n tail j) Z :=
    fun j hj => hb j (hJ j hj)
  exact ⟨finiteProjection_large_on_bulk _ hv J Z q omega hq0 hw0 hcard hbulk,
    fun w hs => distance_from_unrevealed_coefficients _ hv J Z w q omega hq0 hw0 hcard hbulk hs⟩

end
end OriginalUnrevealedBulkSeparation


/- Original ceil length and q^(3/2) scale, plus the actual unrevealed
   first-q tail subset. This converts a disclosed-count bound into a
   genuine no-chamber-hit statement for the actual packet minimizer. -/

open scoped BigOperators

namespace OriginalPacketBulkIndexing

open OriginalPacketDistanceGapBounds OriginalUnrevealedBulkSeparation

noncomputable section

def packetLength (Cm : ℝ) (q : ℕ) : ℕ := Nat.ceil (Cm * q)
def packetIndex (Cm : ℝ) (q : ℕ) : ℕ := packetLength Cm q - 3

theorem original_ceil_path_conditions (Cm : ℝ) (hCm : 4 ≤ Cm) (q : ℕ) (hq : 1 ≤ q) :
    3 ≤ packetLength Cm q ∧
    packetLength Cm q = packetIndex Cm q + 3 ∧
    ((packetIndex Cm q + 2 : ℕ) : ℝ) ≤ Cm * q ∧
    q ≤ packetIndex Cm q + 2 := by
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hm := Nat.le_ceil (Cm * (q : ℝ))
  change Cm * (q : ℝ) ≤ (packetLength Cm q : ℝ) at hm
  have hmul := mul_le_mul_of_nonneg_right hCm (Nat.cast_nonneg q : (0 : ℝ) ≤ q)
  have hm3 : 3 ≤ packetLength Cm q := by
    have hh : (3 : ℝ) ≤ packetLength Cm q := by linarith only [hm, hmul, hqR]
    exact_mod_cast hh
  have hindex : packetLength Cm q = packetIndex Cm q + 3 := by unfold packetIndex; omega
  have hqfit : q + 1 ≤ packetLength Cm q := by
    have hh : (q : ℝ) + 1 ≤ packetLength Cm q := by linarith only [hm, hmul, hqR]
    exact_mod_cast hh
  have hceil := Nat.ceil_lt_add_one (by positivity : (0 : ℝ) ≤ Cm * q)
  change (packetLength Cm q : ℝ) < Cm * q + 1 at hceil
  have hindexR : (packetLength Cm q : ℝ) = (packetIndex Cm q : ℝ) + 3 := by exact_mod_cast hindex
  refine ⟨hm3, hindex, ?_, by omega⟩
  push_cast
  linarith only [hindexR, hceil]

theorem distanceScale_is_original_power (q omega : ℝ) (hq : 0 < q) :
    distanceScale q omega = q ^ ((3 : ℝ) / 2) * omega := by
  unfold distanceScale
  rw [Real.sqrt_eq_rpow]
  rw [show (3 : ℝ) / 2 = 1 + 1 / 2 by norm_num, Real.rpow_add hq, Real.rpow_one]

def unrevealedFirstTail (n q k : ℕ) (hfit : q ≤ n + 2) : Finset (Fin (n + 3)) :=
  (Finset.univ.filter (fun i : Fin q => k ≤ i.val)).image (fun i => (i.castLE hfit).succ)

theorem unrevealedFirstTail_card (n q k : ℕ) (hfit : q ≤ n + 2) (hk : k ≤ q) :
    (unrevealedFirstTail n q k hfit).card = q - k := by
  have hinj : Function.Injective (fun i : Fin q => (i.castLE hfit).succ) := by
    intro i j hij
    apply Fin.ext
    have hh := congrArg (fun x : Fin (n + 3) => x.val) hij
    simpa only [Fin.val_succ, Fin.val_castLE, Nat.add_right_cancel_iff] using hh
  unfold unrevealedFirstTail
  rw [Finset.card_image_of_injective _ hinj]
  have hset : Finset.univ.filter (fun i : Fin q => k ≤ i.val) =
      Finset.univ \ Finset.univ.filter (fun i : Fin q => i.val < k) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff]
    omega
  rw [hset, Finset.card_sdiff]
  simp only [Finset.inter_univ, Finset.card_univ, Fintype.card_fin, Fin.card_filter_val_lt,
    Nat.min_eq_right hk]

theorem actual_unrevealed_index_properties
    (n q k : ℕ) (hfit : q ≤ n + 2) (hk : k ≤ q / 2) :
    (∀ j ∈ unrevealedFirstTail n q k hfit, (j.val : ℝ) ≤ q ∧ k ≤ j.val) ∧
      (q : ℝ) / 4 ≤ ((unrevealedFirstTail n q k hfit).card : ℝ) := by
  constructor
  · intro j hj
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
    have hik := (Finset.mem_filter.mp hi).2
    constructor
    · exact_mod_cast (show (i.castLE hfit).succ.val ≤ q by simp only [Fin.val_succ, Fin.val_castLE]; omega)
    · simp only [Fin.val_succ, Fin.val_castLE]
      omega
  · rw [unrevealedFirstTail_card n q k hfit (by omega)]
    have hh : q ≤ 4 * (q - k) := by omega
    have hr : (q : ℝ) ≤ 4 * ((q - k : ℕ) : ℝ) := by exact_mod_cast hh
    linarith only [hr]

def originalBulkTail (n q : ℕ) (hfit : q ≤ n + 2) : Finset (Fin (n + 3)) :=
  unrevealedFirstTail n (q / 2 - 1) 0 (by omega)

theorem original_bulk_tail_indices
    (n q : ℕ) (hfit : q ≤ n + 2) :
    (originalBulkTail n q hfit : Set (Fin (n + 3))) =
      {j | 1 ≤ j.val ∧ j.val < q / 2} := by
  ext j
  constructor
  · intro hj
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
    simp only [Set.mem_setOf_eq, Fin.val_succ, Fin.val_castLE]
    have hiq := i.isLt
    omega
  · intro hj
    have h1 : 1 ≤ j.val := hj.1
    have hlt : j.val < q / 2 := hj.2
    let i : Fin (q / 2 - 1) := ⟨j.val - 1, by omega⟩
    apply Finset.mem_image.mpr
    refine ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩, ?_⟩
    apply Fin.ext
    simp only [Fin.val_succ, Fin.val_castLE, i]
    omega

theorem original_bulk_tail_large_enough
    (n q : ℕ) (hfit : q ≤ n + 2) (hq : 8 ≤ q) :
    (∀ j ∈ originalBulkTail n q hfit, (j.val : ℝ) ≤ q) ∧
      (q : ℝ) / 4 ≤ ((originalBulkTail n q hfit).card : ℝ) := by
  constructor
  · intro j hj
    have hs : j ∈ (originalBulkTail n q hfit : Set (Fin (n + 3))) := hj
    rw [original_bulk_tail_indices n q hfit] at hs
    exact_mod_cast (show j.val ≤ q by have := hs.2; omega)
  · unfold originalBulkTail
    rw [unrevealedFirstTail_card n (q / 2 - 1) 0 (by omega) (by omega), Nat.sub_zero]
    have hn : q ≤ 4 * (q / 2 - 1) := by omega
    have hr : (q : ℝ) ≤ 4 * ((q / 2 - 1 : ℕ) : ℝ) := by exact_mod_cast hn
    linarith only [hr]

universe u

theorem actual_packet_cannot_be_hit_with_few_disclosures
    {A B W : Type u}
    [NormedAddCommGroup A] [InnerProductSpace ℝ A] [FiniteDimensional ℝ A]
    [NormedAddCommGroup B] [InnerProductSpace ℝ B] [FiniteDimensional ℝ B]
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
    (P : FlatCubic.Profile) (C : A ≃ₗᵢ[ℝ] B) (h : A) (hh : ‖h‖ = 1)
    (n : ℕ) (tail : Fin (n + 2) → W) (ht : Orthonormal ℝ tail)
    (q : ℕ) (hq : 1 ≤ q) (hfit : q ≤ n + 2)
    (delta omega Cm Cw scale lam : ℝ)
    (hd : 0 < delta) (hdw : delta ≤ omega)
    (hCm : 0 ≤ Cm) (hCw : 4 * (Cm + 2) ≤ Cw) (hscale : 0 < scale) (hlam : 0 < lam)
    (homega : omega = Cw * lam * (q : ℝ) ^ 2) (hn : ((n + 2 : ℕ) : ℝ) ≤ Cm * q) :
    ∃ Z : FangqingAmplifier.PhysicalSpace A B W,
      (∀ Y, OriginalPhysicalPacketMinimizer.rawPacket C h n tail (FlatCubic.edge P delta omega)
          q (scale * lam) scale (scale * (2 * omega ^ 2 / Real.sqrt q)) Z ≤
        OriginalPhysicalPacketMinimizer.rawPacket C h n tail (FlatCubic.edge P delta omega)
          q (scale * lam) scale (scale * (2 * omega ^ 2 / Real.sqrt q)) Y) ∧
      (distanceScale q omega ≤ ‖(Submodule.span ℝ
        (OriginalPacketOrientationNormalization.physicalFrame C h n tail ''
          (unrevealedFirstTail n q 0 hfit : Set (Fin (n + 3))))).starProjection Z‖) ∧
      ∀ k : ℕ, k ≤ q / 2 → ∀ w : FangqingAmplifier.PhysicalSpace A B W,
        (∀ j : Fin (n + 3), k ≤ j.val →
          |inner ℝ (OriginalPacketOrientationNormalization.physicalFrame C h n tail j) w| ≤ (q : ℝ) * omega) →
        distanceScale q omega ≤ ‖Z - w‖ := by
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
  obtain ⟨Z, hm, hsep⟩ := actual_private_packet_unrevealed_separation P C h hh n tail ht delta omega
    q Cm Cw scale lam hd hdw hqR hCm hCw hscale hlam homega hn
  have hv := OriginalPhysicalPacketMinimizer.physicalFrame_orthonormal C h hh n tail ht
  have hidx0 := actual_unrevealed_index_properties n q 0 hfit (by omega)
  have hp := (hsep (unrevealedFirstTail n q 0 hfit) (fun j hj => (hidx0.1 j hj).1) hidx0.2).1
  rw [finiteProjection_is_actual_orthogonal_projection _ hv] at hp
  refine ⟨Z, hm, hp, ?_⟩
  intro k hk w hw
  have hidx := actual_unrevealed_index_properties n q k hfit hk
  exact (hsep (unrevealedFirstTail n q k hfit) (fun j hj => (hidx.1 j hj).1) hidx.2).2 w
    (fun j hj => hw j (hidx.1 j hj).2)

end
end OriginalPacketBulkIndexing

open scoped Topology BigOperators
namespace OriginalActualRawPacketResistingHardness
open FangqingAmplifier FangqingPacketLeakage FangqingShellPrefixLocality
  OriginalPhysicalPacketMinimizer OriginalPacketOrientationNormalization
  OriginalPacketDistanceGapBounds OriginalPacketBulkIndexing OriginalRawPacketResistingLocality
  OriginalDeterministicResistingExecution FangqingOrthogonalCompletionAvoidingQueries
noncomputable section
set_option maxHeartbeats 2400000
universe u
variable {A B W : Type u}
  [NormedAddCommGroup A] [InnerProductSpace ℝ A] [FiniteDimensional ℝ A]
  [NormedAddCommGroup B] [InnerProductSpace ℝ B] [FiniteDimensional ℝ B]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]

def actualCompletion {m s : ℕ} (hdim : m + s ≤ Module.finrank ℝ W) : Completion W m s := by
  classical
  intro k hk v hv queries
  let hex := completion_avoiding v hv k hk queries hdim
  refine ⟨Classical.choose hex, ?_⟩
  have hs := Classical.choose_spec hex
  exact ⟨hs.1, fun i hi => (hs.2.1 i hi).symm, hs.2.2⟩

def basisFrame (m : ℕ) (hm : m ≤ Module.finrank ℝ W) : Fin m → W :=
  fun i => (stdOrthonormalBasis ℝ W) (i.castLE hm)

theorem basisFrame_orthonormal (m : ℕ) (hm : m ≤ Module.finrank ℝ W) :
    Orthonormal ℝ (basisFrame (W := W) m hm) := by
  apply (stdOrthonormalBasis ℝ W).orthonormal.comp
  intro i j hij
  apply Fin.ext
  exact congrArg (fun i : Fin (Module.finrank ℝ W) => i.val) hij

/-- h is the explicitly allowed free input.  The algorithm has no tail input,
    and no full private frame is placed in a seed.  The conclusion uses one
    fixed frame and its actual complete raw second-order oracle. -/
theorem actual_raw_fixed_resisting_frame
    (P : FlatCubic.Profile) (delta omega : ℝ) (hd : 0 < delta) (hdw : delta ≤ omega)
    (C : A ≃ₗᵢ[ℝ] B) (h : A) (n : ℕ) (q nu scale seed : ℝ)
    (N : ℕ) (hNm : N ≤ n + 2) (hdim : n + 2 + (N + 1) ≤ Module.finrank ℝ W)
    (algorithmQuery : A → ℕ → (ℕ → OriginalActualPairedPacketRun.Response (PhysicalSpace A B W)) → PhysicalSpace A B W)
    (algorithmOutput : A → (ℕ → OriginalActualPairedPacketRun.Response (PhysicalSpace A B W)) → PhysicalSpace A B W) :
    ∃ tail : Fin (n + 2) → W, Orthonormal ℝ tail ∧
      ∀ i, N ≤ i.val → inner ℝ (tail i)
        (algorithmOutput h (realHistory (algorithmQuery h)
          (fun y => bundle (rawPacket C h n tail (FlatCubic.edge P delta omega) q nu scale seed) y) N)).snd = 0 := by
  let oracle := fun tail : Fin (n + 2) → W => fun y : PhysicalSpace A B W =>
    bundle (rawPacket C h n tail (FlatCubic.edge P delta omega) q nu scale seed) y
  let init := basisFrame (W := W) (n + 2) (by omega : n + 2 ≤ Module.finrank ℝ W)
  have hinit : Orthonormal ℝ init := basisFrame_orthonormal _ _
  exact fixed_orthonormal_frame_hides_remaining_output_coordinates
    (project := fun y : PhysicalSpace A B W => y.snd) (query := algorithmQuery h) (oracle := oracle)
    (actualCompletion hdim) hNm init hinit
    (fun v w k y hp hz hz' => actual_raw_bundle_eq_of_tail_prefix_and_future_zeros
      P delta omega hd hdw C h n k v w q nu scale seed y hp hz hz') (algorithmOutput h)

theorem actual_raw_resisting_output_distance
    (P : FlatCubic.Profile) (C : A ≃ₗᵢ[ℝ] B) (h : A) (hh : ‖h‖ = 1)
    (n q N : ℕ) (hq : 1 ≤ q) (hfit : q ≤ n + 2) (hqueries : N + 1 ≤ q / 2)
    (hdim : n + 2 + (N + 1) ≤ Module.finrank ℝ W)
    (delta omega Cm Cw scale lam : ℝ) (hd : 0 < delta) (hdw : delta ≤ omega)
    (hCm : 0 ≤ Cm) (hCw : 4 * (Cm + 2) ≤ Cw) (hscale : 0 < scale) (hlam : 0 < lam)
    (homega : omega = Cw * lam * (q : ℝ) ^ 2) (hn : ((n + 2 : ℕ) : ℝ) ≤ Cm * q)
    (algorithmQuery : A → ℕ → (ℕ → OriginalActualPairedPacketRun.Response (PhysicalSpace A B W)) → PhysicalSpace A B W)
    (algorithmOutput : A → (ℕ → OriginalActualPairedPacketRun.Response (PhysicalSpace A B W)) → PhysicalSpace A B W) :
    ∃ tail : Fin (n + 2) → W, Orthonormal ℝ tail ∧
      ∃ Z : PhysicalSpace A B W,
        (∀ Y, rawPacket C h n tail (FlatCubic.edge P delta omega) q (scale * lam) scale
          (scale * (2 * omega ^ 2 / Real.sqrt q)) Z ≤
            rawPacket C h n tail (FlatCubic.edge P delta omega) q (scale * lam) scale
              (scale * (2 * omega ^ 2 / Real.sqrt q)) Y) ∧
        distanceScale q omega ≤ ‖Z - algorithmOutput h (realHistory (algorithmQuery h)
          (fun y => bundle (rawPacket C h n tail (FlatCubic.edge P delta omega) q (scale * lam) scale
            (scale * (2 * omega ^ 2 / Real.sqrt q))) y) N)‖ := by
  have hNm : N ≤ n + 2 := by omega
  obtain ⟨tail, ht, hzero⟩ := actual_raw_fixed_resisting_frame P delta omega hd hdw C h n q
    (scale * lam) scale (scale * (2 * omega ^ 2 / Real.sqrt q)) N hNm hdim algorithmQuery algorithmOutput
  obtain ⟨Z, hm, _, hsep⟩ := actual_packet_cannot_be_hit_with_few_disclosures P C h hh n tail ht q hq hfit
    delta omega Cm Cw scale lam hd hdw hCm hCw hscale hlam homega hn
  refine ⟨tail, ht, Z, hm, hsep (N + 1) hqueries _ ?_⟩
  intro j
  refine Fin.cases ?_ (fun i => ?_) j
  · intro hj; simp only [Fin.val_zero] at hj; omega
  · intro hj
    have hiN : N ≤ i.val := by simp only [Fin.val_succ] at hj; omega
    rw [OriginalActualPairedPacketExecution.physical_tail_inner, hzero i hiN, abs_zero]
    exact mul_nonneg (Nat.cast_nonneg q) (hd.trans_le hdw).le

theorem actual_raw_resisting_output_distance_real_q
    (P : FlatCubic.Profile) (C : A ≃ₗᵢ[ℝ] B) (h : A) (hh : ‖h‖ = 1)
    (n N : ℕ) (q : ℝ) (hq : 8 ≤ q) (hfit : Nat.floor q ≤ n + 2)
    (hqueries : (N : ℝ) < q / 4) (hdim : n + 2 + (N + 1) ≤ Module.finrank ℝ W)
    (delta omega Cm Cw scale lam : ℝ) (hd : 0 < delta) (hdw : delta ≤ omega)
    (hCm : 0 ≤ Cm) (hCw : 4 * (Cm + 2) ≤ Cw) (hscale : 0 < scale) (hlam : 0 < lam)
    (homega : omega = Cw * lam * q ^ 2) (hn : ((n + 2 : ℕ) : ℝ) ≤ Cm * q)
    (algorithmQuery : A → ℕ → (ℕ → OriginalActualPairedPacketRun.Response (PhysicalSpace A B W)) → PhysicalSpace A B W)
    (algorithmOutput : A → (ℕ → OriginalActualPairedPacketRun.Response (PhysicalSpace A B W)) → PhysicalSpace A B W) :
    ∃ tail : Fin (n + 2) → W, Orthonormal ℝ tail ∧
      ∃ Z : PhysicalSpace A B W,
        (∀ Y, rawPacket C h n tail (FlatCubic.edge P delta omega) q (scale * lam) scale
          (scale * (2 * omega ^ 2 / Real.sqrt q)) Z ≤
            rawPacket C h n tail (FlatCubic.edge P delta omega) q (scale * lam) scale
              (scale * (2 * omega ^ 2 / Real.sqrt q)) Y) ∧
        distanceScale q omega ≤ ‖Z - algorithmOutput h (realHistory (algorithmQuery h)
          (fun y => bundle (rawPacket C h n tail (FlatCubic.edge P delta omega) q (scale * lam) scale
            (scale * (2 * omega ^ 2 / Real.sqrt q))) y) N)‖ := by
  have hq0 : 0 ≤ q := by linarith only [hq]
  have hNF : N ≤ Nat.floor q := (Nat.le_floor_iff hq0).mpr (by linarith only [hqueries, hq])
  have hNm : N ≤ n + 2 := hNF.trans hfit
  obtain ⟨tail, ht, hzero⟩ := actual_raw_fixed_resisting_frame P delta omega hd hdw C h n q
    (scale * lam) scale (scale * (2 * omega ^ 2 / Real.sqrt q)) N hNm hdim algorithmQuery algorithmOutput
  obtain ⟨Z, hm, _, _, _, hb⟩ := actual_physical_minimizer_norm_gap_bulk P C h hh n tail ht delta omega q Cm Cw scale lam
    hd hdw (by linarith only [hq]) hCm hCw hscale hlam homega hn
  let J := unrevealedFirstTail n (Nat.floor q) N hfit
  have hbulk : ∀ j ∈ J, 3 * q * omega ≤ inner ℝ (physicalFrame C h n tail j) Z := by
    intro j hj
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
    apply hb
    have hiq : ((i.castLE hfit).succ.val : ℝ) ≤ (Nat.floor q : ℝ) := by
      exact_mod_cast (show (i.castLE hfit).succ.val ≤ Nat.floor q by simp only [Fin.val_succ, Fin.val_castLE]; omega)
    exact hiq.trans (Nat.floor_le hq0)
  have hcard : q / 4 ≤ (J.card : ℝ) := by
    dsimp only [J]
    rw [unrevealedFirstTail_card n (Nat.floor q) N hfit hNF, Nat.cast_sub hNF]
    have hf := Nat.lt_floor_add_one q
    linarith only [hf, hqueries, hq]
  have hsmall : ∀ j ∈ J,
      |inner ℝ (physicalFrame C h n tail j)
        (algorithmOutput h (realHistory (algorithmQuery h)
          (fun y => bundle (rawPacket C h n tail (FlatCubic.edge P delta omega) q (scale * lam) scale
            (scale * (2 * omega ^ 2 / Real.sqrt q))) y) N))| ≤ q * omega := by
    intro j hj
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
    have hiN := (Finset.mem_filter.mp hi).2
    rw [OriginalActualPairedPacketExecution.physical_tail_inner, hzero (i.castLE hfit) hiN, abs_zero]
    exact mul_nonneg hq0 (hd.trans_le hdw).le
  exact ⟨tail, ht, Z, hm,
    OriginalUnrevealedBulkSeparation.distance_from_unrevealed_coefficients _
      (physicalFrame_orthonormal C h hh n tail ht) J Z _ q omega hq0 (hd.trans_le hdw).le hcard hbulk hsmall⟩

end
end OriginalActualRawPacketResistingHardness

open scoped BigOperators
namespace OriginalPrivatePacketScalarsAndBulk
open FangqingAmplifier OriginalPacketDistanceGapBounds OriginalPacketBulkIndexing
  OriginalUnrevealedBulkSeparation OriginalPacketOrientationNormalization OriginalPhysicalPacketMinimizer
noncomputable section
set_option maxHeartbeats 1400000

def originalIndex (Cm q : ℝ) : ℕ := Nat.ceil (Cm * q) - 3

theorem original_real_ceil_conditions (Cm q : ℝ) (hCm : 4 ≤ Cm) (hq : 8 ≤ q) :
    Nat.ceil (Cm * q) = originalIndex Cm q + 3 ∧
    ((originalIndex Cm q + 2 : ℕ) : ℝ) ≤ Cm * q ∧
    Nat.floor q ≤ originalIndex Cm q + 2 := by
  have hq0 : 0 ≤ q := by linarith only [hq]
  have hm := Nat.le_ceil (Cm * q)
  have hmul := mul_le_mul_of_nonneg_right hCm hq0
  have hm3 : 3 ≤ Nat.ceil (Cm * q) := by
    have hh : (3 : ℝ) ≤ Nat.ceil (Cm * q) := by linarith only [hm, hmul, hq]
    exact_mod_cast hh
  have hidx : Nat.ceil (Cm * q) = originalIndex Cm q + 3 := by unfold originalIndex; omega
  have hqfit : Nat.floor q + 1 ≤ Nat.ceil (Cm * q) := by
    have hf := Nat.floor_le hq0
    have hh : (Nat.floor q : ℝ) + 1 ≤ Nat.ceil (Cm * q) := by linarith only [hf, hm, hmul, hq]
    exact_mod_cast hh
  have hceil := Nat.ceil_lt_add_one (show 0 ≤ Cm * q by positivity)
  have hidxR : (Nat.ceil (Cm * q) : ℝ) = (originalIndex Cm q : ℝ) + 3 := by exact_mod_cast hidx
  refine ⟨hidx, ?_, by omega⟩
  push_cast
  linarith only [hidxR, hceil]

def bulkIndices (n : ℕ) (q : ℝ) : Finset (Fin (n + 3)) :=
  Finset.univ.filter (fun j => 1 ≤ j.val ∧ j.val < Nat.floor (q / 2))

theorem original_real_bulk_indices (n : ℕ) (q : ℝ) (hq : 8 ≤ q) (hfit : Nat.floor q ≤ n + 2) :
    (∀ j ∈ bulkIndices n q, (j.val : ℝ) ≤ q) ∧
    q / 4 ≤ ((bulkIndices n q).card : ℝ) := by
  have hq0 : 0 ≤ q := by linarith only [hq]
  have hhalf : 0 ≤ q / 2 := by positivity
  let F := Nat.floor (q / 2)
  let K := F - 1
  have hF1 : 1 ≤ F := (Nat.le_floor_iff hhalf).mpr (by norm_num; linarith only [hq])
  have hFq : F ≤ Nat.floor q := Nat.floor_mono (by linarith only [hq])
  have hKfit : K ≤ n + 2 := by dsimp [K]; omega
  have heq : bulkIndices n q = unrevealedFirstTail n K 0 hKfit := by
    ext j
    constructor
    · intro hj
      have hs := (Finset.mem_filter.mp hj).2
      have hlast : j.val < F := hs.2
      let i : Fin K := ⟨j.val - 1, by dsimp [K]; omega⟩
      refine Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, Nat.zero_le _⟩, ?_⟩
      apply Fin.ext
      simp only [Fin.val_succ, Fin.val_castLE, i]
      omega
    · intro hj
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      simp only [Fin.val_succ, Fin.val_castLE]
      have hiK := i.isLt
      change 1 ≤ i.val + 1 ∧ i.val + 1 < F
      dsimp [K] at hiK
      omega
  constructor
  · intro j hj
    have hs := (Finset.mem_filter.mp hj).2.2
    have hcast : (j.val : ℝ) < (F : ℝ) := by exact_mod_cast hs
    exact (hcast.le.trans (Nat.floor_le hhalf)).trans (by linarith only [hq])
  · rw [heq, unrevealedFirstTail_card n K 0 hKfit (Nat.zero_le _), Nat.sub_zero]
    dsimp [K]
    rw [Nat.cast_sub hF1, Nat.cast_one]
    have hf := Nat.lt_floor_add_one (q / 2)
    change q / 2 < (F : ℝ) + 1 at hf
    linarith only [hq, hf]

theorem scale_budget_identity (q omega Cw cg nu rho : ℝ)
    (hq : 0 < q) (hcg : 0 < cg) (hrho : 0 < rho)
    (homega : omega = Cw * (nu / (cg * rho)) * q ^ 2) :
    distanceScale q omega = (Cw / cg) * (nu / rho) * q ^ ((7 : ℝ) / 2) := by
  have hp : q ^ ((7 : ℝ) / 2) = q ^ 3 * Real.sqrt q := by
    rw [show (7 : ℝ) / 2 = 3 + 1 / 2 by norm_num, Real.rpow_add hq, Real.sqrt_eq_rpow]
    norm_num
  rw [hp, distanceScale, homega]
  field_simp [hcg.ne', hrho.ne'] <;> ring

end
end OriginalPrivatePacketScalarsAndBulk

open scoped Topology BigOperators
namespace OriginalRawPacketFreeHandleInitialization
open FangqingAmplifier FangqingPacketLeakage OriginalPacketOrientationNormalization
  OriginalPhysicalPacketMinimizer FangqingShellPrefixLocality
noncomputable section
set_option maxHeartbeats 1000000
variable {A B W : Type*}
  [NormedAddCommGroup A] [InnerProductSpace ℝ A] [FiniteDimensional ℝ A]
  [NormedAddCommGroup B] [InnerProductSpace ℝ B] [FiniteDimensional ℝ B]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]

def publicCarrierWithFreeHandle (C : A ≃ₗᵢ[ℝ] B) (h : A) (q nu seed : ℝ) : PhysicalSpace A B W → ℝ :=
  fun y => QPhysical q nu C y - seed * inner ℝ h y.fst.fst

/-- There is no oracle argument and no tail/frame argument in this initialization.
    It evaluates an explicitly public quadratic/linear function after h is given. -/
def freeInitialData (C : A ≃ₗᵢ[ℝ] B) (h : A) (q nu seed : ℝ) :
    A × OriginalActualPairedPacketRun.Response (PhysicalSpace A B W) :=
  (h, bundle (publicCarrierWithFreeHandle C h q nu seed) 0)

theorem actual_initial_full_raw_bundle_is_public_given_h
    (P : FlatCubic.Profile) (delta omega : ℝ) (hd : 0 < delta) (hdw : delta ≤ omega)
    (C : A ≃ₗᵢ[ℝ] B) (h : A) (n : ℕ) (tail : Fin (n + 2) → W)
    (q nu scale seed : ℝ) :
    bundle (rawPacket C h n tail (FlatCubic.edge P delta omega) q nu scale seed) 0 =
      (freeInitialData (W := W) C h q nu seed).2 := by
  have he := edgeSum_eventually_eq_selected P delta omega hd hdw
    (pathDirection n (physicalFrame C h n tail)) (∅ : Finset (Fin (n + 2))) (0 : PhysicalSpace A B W)
    (by intro i _; simpa only [inner_zero_right, abs_zero] using half_pos hd)
  apply bundle_of_eventuallyEq
  filter_upwards [he] with y hy
  rw [rawPacket_literal, hy]
  simp only [selectedEdgeSum, Finset.sum_empty, mul_zero, add_zero, publicCarrierWithFreeHandle]

def initializedQuery
    (C : A ≃ₗᵢ[ℝ] B) (q nu seed : ℝ)
    (algorithm : (A × OriginalActualPairedPacketRun.Response (PhysicalSpace A B W)) → ℕ →
      (ℕ → OriginalActualPairedPacketRun.Response (PhysicalSpace A B W)) → PhysicalSpace A B W) :
    A → ℕ → (ℕ → OriginalActualPairedPacketRun.Response (PhysicalSpace A B W)) → PhysicalSpace A B W :=
  fun h => algorithm (freeInitialData C h q nu seed)

def initializedOutput
    (C : A ≃ₗᵢ[ℝ] B) (q nu seed : ℝ)
    (algorithm : (A × OriginalActualPairedPacketRun.Response (PhysicalSpace A B W)) →
      (ℕ → OriginalActualPairedPacketRun.Response (PhysicalSpace A B W)) → PhysicalSpace A B W) :
    A → (ℕ → OriginalActualPairedPacketRun.Response (PhysicalSpace A B W)) → PhysicalSpace A B W :=
  fun h => algorithm (freeInitialData C h q nu seed)

theorem initialized_history_zero_paid_responses
    (C : A ≃ₗᵢ[ℝ] B) (h : A) (q nu seed : ℝ)
    (algorithm : (A × OriginalActualPairedPacketRun.Response (PhysicalSpace A B W)) → ℕ →
      (ℕ → OriginalActualPairedPacketRun.Response (PhysicalSpace A B W)) → PhysicalSpace A B W)
    (actualOracle : PhysicalSpace A B W → OriginalActualPairedPacketRun.Response (PhysicalSpace A B W)) :
    OriginalDeterministicResistingExecution.realHistory (initializedQuery C q nu seed algorithm h) actualOracle 0 = 0 := rfl

theorem inactive_actual_transcript_public_when_its_queries_flat
    (P : FlatCubic.Profile) (delta omega : ℝ) (hd : 0 < delta) (hdw : delta ≤ omega)
    (C : A ≃ₗᵢ[ℝ] B) (h : A) (n : ℕ) (tail : Fin (n + 2) → W)
    (q nu scale R gain : ℝ) (hR : 0 < R)
    (query : ℕ → (ℕ → OriginalActualPairedPacketRun.Response (PhysicalSpace A B W)) → PhysicalSpace A B W)
    (N : ℕ)
    (hflat : ∀ k < N, ∀ i : Fin (n + 2),
      |inner ℝ (pathDirection n (physicalFrame C h n tail) i)
        (query k (OriginalDeterministicResistingExecution.realHistory query
          (fun y => bundle (FangqingInactiveShellClass.inactiveShell (QPhysical q nu C)
            (fun z => scale * FangqingPathEdgeRegularity.pathEdge P delta omega (n + 2) (physicalFrame C h n tail) z) R gain) y) k))| ≤ delta / 2) :
    OriginalDeterministicResistingExecution.realHistory query
      (fun y => bundle (FangqingInactiveShellClass.inactiveShell (QPhysical q nu C)
        (fun z => scale * FangqingPathEdgeRegularity.pathEdge P delta omega (n + 2) (physicalFrame C h n tail) z) R gain) y) N =
    OriginalDeterministicResistingExecution.realHistory query
      (fun y => bundle (OriginalPhysicalPairedShellPrefix.publicEndpoint (QPhysical q nu C) R gain) y) N := by
  induction N with
  | zero => rfl
  | succ N ih =>
      have hp := ih (fun k hk => hflat k (by omega))
      have he := OriginalPhysicalPairedShellPrefix.actual_physical_inactive_public_closed_no_handle
        P delta omega hd hdw n C h tail q nu scale R gain hR _ (hflat N (by omega))
      change Function.update _ N _ = Function.update _ N _
      rw [hp] at he
      rw [hp]
      dsimp only
      rw [he]

end
end OriginalRawPacketFreeHandleInitialization

open scoped BigOperators NNReal
namespace OriginalPrivatePacketOriginalAnalytic
open FangqingAmplifier FangqingPrivatePacketAnalytic OriginalPhysicalPacketExistence
  OriginalPhysicalPacketMinimizer OriginalPacketOrientationNormalization OriginalPacketDistanceGapBounds
  OriginalUnrevealedBulkSeparation OriginalPrivatePacketScalarsAndBulk
noncomputable section
set_option maxHeartbeats 2200000
universe u

theorem universal_original_raw_budgets (P : FlatCubic.Profile) :
    ∃ Ce : ℝ≥0, ∃ cg : ℝ, 0 < cg ∧
    ∀ (A B W : Type u)
      [NormedAddCommGroup A] [InnerProductSpace ℝ A] [FiniteDimensional ℝ A]
      [NormedAddCommGroup B] [InnerProductSpace ℝ B] [FiniteDimensional ℝ B]
      [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W],
    ∀ (C : A ≃ₗᵢ[ℝ] B) (h : A) (n : ℕ) (tail : Fin (n + 2) → W)
      (delta omega q Cw nu rho seed : ℝ),
      ‖h‖ = 1 → Orthonormal ℝ tail → 0 < delta → delta ≤ omega → 1 ≤ q →
      0 ≤ Cw → 0 ≤ nu → 0 ≤ rho →
      cg * rho * omega = Cw * nu * q ^ 2 →
      let H := rawPacket C h n tail (FlatCubic.edge P delta omega) q nu (cg * rho) seed
      ContDiff ℝ 2 H ∧ StrongConvexOn Set.univ nu H ∧
      GradientRate H ((3 + 4 * (Ce : ℝ) * Cw) * nu * q ^ 2) ∧ HessianRate H rho := by
  obtain ⟨Ce, hCe⟩ := actual_private_packet_regularity.{u} P
  obtain ⟨cg, hcg, _, hbudget⟩ := universal_edge_scale_choice (Ce : ℝ) Ce.coe_nonneg
  refine ⟨Ce, cg, hcg, ?_⟩
  intro A B W inst inst' inst'' instB instB' instB'' instW instW' instW''
    C h n tail delta omega q Cw nu rho seed hh ht hd hdw hq hCw hnu hrho hscale H
  have hc := hCe A B W q nu (cg * rho) seed delta omega C (n + 2) (physicalFrame C h n tail)
    (mkPhysical h 0 0) (by linarith only [hq]) hnu (mul_nonneg hcg.le hrho) hd hdw (physicalFrame_orthonormal C h hh n tail ht)
  rw [← rawPacket_eq_actual_linearPacket] at hc
  have hL := original_smoothness_scalar_budget (Ce : ℝ) Cw q nu (cg * rho) omega Ce.coe_nonneg hCw hq hnu hscale
  refine ⟨hc.1, hc.2.1, ?_, ?_⟩
  · intro x y
    exact (hc.2.2.2.1 x y).trans (mul_le_mul_of_nonneg_right hL (norm_nonneg _))
  · intro x y
    exact (hc.2.2.2.2 x y).trans (mul_le_mul_of_nonneg_right (hbudget rho hrho) (norm_nonneg _))

variable {A B W : Type u}
  [NormedAddCommGroup A] [InnerProductSpace ℝ A] [FiniteDimensional ℝ A]
  [NormedAddCommGroup B] [InnerProductSpace ℝ B] [FiniteDimensional ℝ B]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]

theorem actual_raw_minimizer_with_original_bulk_projection
    (P : FlatCubic.Profile) (C : A ≃ₗᵢ[ℝ] B) (h : A) (hh : ‖h‖ = 1)
    (n : ℕ) (tail : Fin (n + 2) → W) (ht : Orthonormal ℝ tail)
    (delta omega q Cm Cw scale lam : ℝ) (hd : 0 < delta) (hdw : delta ≤ omega) (hq : 8 ≤ q)
    (hfit : Nat.floor q ≤ n + 2) (hCm : 0 ≤ Cm) (hCw : 4 * (Cm + 2) ≤ Cw)
    (hscale : 0 < scale) (hlam : 0 < lam) (homega : omega = Cw * lam * q ^ 2)
    (hn : ((n + 2 : ℕ) : ℝ) ≤ Cm * q) :
    let H := rawPacket C h n tail (FlatCubic.edge P delta omega) q (scale * lam) scale (scale * (2 * omega ^ 2 / Real.sqrt q))
    let D := distanceScale q omega
    ∃ Z : PhysicalSpace A B W,
      (∀ Y, H Z ≤ H Y) ∧ (∀ Y, (∀ X, H Y ≤ H X) → Y = Z) ∧
      ‖Z‖ ≤ 2 * Cw * (Cm + 2) * D ∧ H 0 - H Z ≤ 4 * Cw ^ 2 * (scale * lam) * D ^ 2 ∧
      D ≤ ‖(Submodule.span ℝ (physicalFrame C h n tail ''
        (bulkIndices n q : Set (Fin (n + 3))))).starProjection Z‖ := by
  obtain ⟨Z, hm, hu, hnZ, hgap, hb⟩ := actual_physical_minimizer_norm_gap_bulk P C h hh n tail ht
    delta omega q Cm Cw scale lam hd hdw (by linarith only [hq]) hCm hCw hscale hlam homega hn
  have hi := original_real_bulk_indices n q hq hfit
  have hv := physicalFrame_orthonormal C h hh n tail ht
  have hp := finiteProjection_large_on_bulk (physicalFrame C h n tail) hv (bulkIndices n q) Z q omega
    (by linarith only [hq]) (hd.trans_le hdw).le hi.2 (fun j hj => hb j (hi.1 j hj))
  rw [finiteProjection_is_actual_orthogonal_projection _ hv] at hp
  exact ⟨Z, hm, hu, hnZ, hgap, hp⟩

end
end OriginalPrivatePacketOriginalAnalytic

open scoped Topology BigOperators NNReal
namespace OriginalPrivateHandlePacketComplete
open FangqingAmplifier FangqingPrivatePacketAnalytic OriginalPhysicalPacketExistence
  OriginalPhysicalPacketMinimizer OriginalPacketOrientationNormalization OriginalPacketDistanceGapBounds
  OriginalUnrevealedBulkSeparation OriginalPrivatePacketScalarsAndBulk OriginalPrivatePacketOriginalAnalytic
  OriginalActualRawPacketResistingHardness OriginalRawPacketFreeHandleInitialization
  OriginalDeterministicResistingExecution FangqingShellPrefixLocality FangqingPacketLeakage
  FangqingInactiveShellClass OriginalPhysicalPairedShellPrefix FangqingPathEdgeRegularity
noncomputable section
set_option maxHeartbeats 3500000
universe u

theorem original_private_handle_packet_all_items (P : FlatCubic.Profile)
    (Cm Cw : ℝ) (hCm : 4 ≤ Cm) (hCw : 4 * (Cm + 2) ≤ Cw) :
    ∃ Ce : ℝ≥0, ∃ cg : ℝ, 0 < cg ∧
    ∀ (A B W : Type u)
      [NormedAddCommGroup A] [InnerProductSpace ℝ A] [FiniteDimensional ℝ A]
      [NormedAddCommGroup B] [InnerProductSpace ℝ B] [FiniteDimensional ℝ B]
      [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W],
    ∀ (C : A ≃ₗᵢ[ℝ] B) (h : A) (q nu rho cdelta : ℝ),
      ‖h‖ = 1 → 8 ≤ q → 0 < nu → 0 < rho → 0 < cdelta → cdelta ≤ 1 →
      let n := originalIndex Cm q
      let scale := cg * rho
      let lam := nu / scale
      let omega := Cw * lam * q ^ 2
      let delta := cdelta * omega
      let D := distanceScale q omega
      let seed := scale * (2 * omega ^ 2 / Real.sqrt q)
      let CL := 3 + 4 * (Ce : ℝ) * Cw
      Nat.ceil (Cm * q) = n + 3 ∧
      D = (Cw / cg) * (nu / rho) * q ^ ((7 : ℝ) / 2) ∧
      seed = 2 * Cw * nu * D ∧ 0 < D ∧
      (∀ tail : Fin (n + 2) → W, Orthonormal ℝ tail →
        let H := rawPacket C h n tail (FlatCubic.edge P delta omega) q nu scale seed
        ContDiff ℝ 2 H ∧ StrongConvexOn Set.univ nu H ∧ GradientRate H (CL * nu * q ^ 2) ∧ HessianRate H rho ∧
        ∃ Z : PhysicalSpace A B W,
          (∀ Y, H Z ≤ H Y) ∧ (∀ Y, (∀ X, H Y ≤ H X) → Y = Z) ∧
          ‖Z‖ ≤ 2 * Cw * (Cm + 2) * D ∧ H 0 - H Z ≤ 4 * Cw ^ 2 * nu * D ^ 2 ∧
          D ≤ ‖(Submodule.span ℝ (physicalFrame C h n tail ''
            (bulkIndices n q : Set (Fin (n + 3))))).starProjection Z‖) ∧
      (∀ (N : ℕ), (N : ℝ) < q / 4 → n + 2 + (N + 1) ≤ Module.finrank ℝ W →
        ∀ (algorithmQuery : A → ℕ → (ℕ → OriginalActualPairedPacketRun.Response (PhysicalSpace A B W)) → PhysicalSpace A B W)
          (algorithmOutput : A → (ℕ → OriginalActualPairedPacketRun.Response (PhysicalSpace A B W)) → PhysicalSpace A B W),
        ∃ tail : Fin (n + 2) → W, Orthonormal ℝ tail ∧
          ∃ Z : PhysicalSpace A B W,
            (∀ Y, rawPacket C h n tail (FlatCubic.edge P delta omega) q nu scale seed Z ≤
              rawPacket C h n tail (FlatCubic.edge P delta omega) q nu scale seed Y) ∧
            D ≤ ‖Z - algorithmOutput h (realHistory (algorithmQuery h)
              (fun y => bundle (rawPacket C h n tail (FlatCubic.edge P delta omega) q nu scale seed) y) N)‖) ∧
      (∀ tail : Fin (n + 2) → W,
        bundle (rawPacket C h n tail (FlatCubic.edge P delta omega) q nu scale seed) 0 =
          (freeInitialData (W := W) C h q nu seed).2) ∧
      (∀ (tail : Fin (n + 2) → W) (R gain : ℝ), 0 < R → ∀ y : PhysicalSpace A B W,
        (∀ i : Fin (n + 2), |inner ℝ (pathDirection n (physicalFrame C h n tail) i) y| ≤ delta / 2) →
        bundle (inactiveShell (QPhysical q nu C)
          (fun z => scale * pathEdge P delta omega (n + 2) (physicalFrame C h n tail) z) R gain) y =
        bundle (publicEndpoint (QPhysical q nu C) R gain) y) ∧
      (∀ (tail : Fin (n + 2) → W) (R gain : ℝ), 0 < R →
        ∀ (query : ℕ → (ℕ → OriginalActualPairedPacketRun.Response (PhysicalSpace A B W)) → PhysicalSpace A B W) (N : ℕ),
        (∀ k < N, ∀ i : Fin (n + 2), |inner ℝ (pathDirection n (physicalFrame C h n tail) i)
          (query k (realHistory query (fun y => bundle (inactiveShell (QPhysical q nu C)
            (fun z => scale * pathEdge P delta omega (n + 2) (physicalFrame C h n tail) z) R gain) y) k))| ≤ delta / 2) →
        realHistory query (fun y => bundle (inactiveShell (QPhysical q nu C)
          (fun z => scale * pathEdge P delta omega (n + 2) (physicalFrame C h n tail) z) R gain) y) N =
        realHistory query (fun y => bundle (publicEndpoint (QPhysical q nu C) R gain) y) N) := by
  obtain ⟨Ce, cg, hcg, hRegularity⟩ := universal_original_raw_budgets.{u} P
  refine ⟨Ce, cg, hcg, ?_⟩
  intro A B W inst inst' inst'' instB instB' instB'' instW instW' instW'' C h q nu rho cdelta
    hh hq hnu hrho hcd hcd1 n scale lam omega delta D seed CL
  have hCw0 : 0 < Cw := by linarith only [hCm, hCw]
  have hq0 : 0 < q := by linarith only [hq]
  have hscale : 0 < scale := mul_pos hcg hrho
  have hlam : 0 < lam := div_pos hnu hscale
  have homega : omega = Cw * lam * q ^ 2 := rfl
  have hw : 0 < omega := by dsimp only [omega]; positivity
  have hd : 0 < delta := mul_pos hcd hw
  have hdw : delta ≤ omega := by dsimp only [delta]; exact mul_le_of_le_one_left hw.le hcd1
  have hnuEq : scale * lam = nu := by dsimp only [lam]; field_simp [hscale.ne']
  have hsOmega : scale * omega = Cw * nu * q ^ 2 := by rw [homega]; calc
    scale * (Cw * lam * q ^ 2) = Cw * (scale * lam) * q ^ 2 := by ring
    _ = _ := by rw [hnuEq]
  have hceil := original_real_ceil_conditions Cm q hCm hq
  have hD : 0 < D := by dsimp only [D, distanceScale]; positivity
  have hseed := actual_seed_ratio q omega Cw lam scale hq0 homega
  rw [hnuEq] at hseed
  refine ⟨hceil.1, scale_budget_identity q omega Cw cg nu rho hq0 hcg hrho homega,
    hseed, hD, ?_, ?_, ?_, ?_, ?_⟩
  · intro tail ht
    have hc := hRegularity A B W C h n tail delta omega q Cw nu rho seed hh ht hd hdw
      (by linarith only [hq]) hCw0.le hnu.le hrho.le hsOmega
    have hm := actual_raw_minimizer_with_original_bulk_projection P C h hh n tail ht delta omega q Cm Cw scale lam
      hd hdw hq hceil.2.2 (by linarith only [hCm]) hCw hscale hlam homega hceil.2.1
    rw [hnuEq] at hm
    exact ⟨hc.1, hc.2.1, hc.2.2.1, hc.2.2.2, hm⟩
  · intro N hN hdim algorithmQuery algorithmOutput
    have hhx := actual_raw_resisting_output_distance_real_q P C h hh n N q hq hceil.2.2 hN hdim
      delta omega Cm Cw scale lam hd hdw (by linarith only [hCm]) hCw hscale hlam homega hceil.2.1 algorithmQuery algorithmOutput
    simpa only [hnuEq] using hhx
  · intro tail
    exact actual_initial_full_raw_bundle_is_public_given_h P delta omega hd hdw C h n tail q nu scale seed
  · intro tail R gain hR y hf
    exact actual_physical_inactive_public_closed_no_handle P delta omega hd hdw n C h tail q nu scale R gain hR y hf
  · intro tail R gain hR query N hf
    exact inactive_actual_transcript_public_when_its_queries_flat P delta omega hd hdw C h n tail q nu scale R gain hR query N hf

end
end OriginalPrivateHandlePacketComplete

end PaperAudit.PrivateHandlePacket
