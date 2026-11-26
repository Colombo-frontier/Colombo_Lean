import LeanArticleAudit.Pilot.Halpern

/-!
# Kernel-checked smooth gate

The concrete profile is `1` minus mathlib's bundled `C∞` bump with inner
radius `1/2` and outer radius `1`.  Thus exact flatness is inherited from a
library theorem, including at the boundary.
-/

open Set MeasureTheory intervalIntegral
open scoped ContDiff

namespace LeanArticleAudit.Pilot

/-- A concrete even `C∞` bump equal to one on `[-1/2,1/2]` and zero outside
`(-1,1)`. -/
noncomputable def standardInnerBump : ContDiffBump (0 : ℝ) where
  rIn := 1 / 2
  rOut := 1
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

/-- The explicit profile used by the audited gate construction. -/
noncomputable def standardGateProfile : GateProfile where
  rho := fun u => 1 - standardInnerBump u
  smooth := by
    apply contDiff_infty.mpr
    intro m
    exact contDiff_const.sub (standardInnerBump.contDiff (n := m))
  even := by
    intro u
    exact congrArg (fun z : ℝ => 1 - z) (standardInnerBump.neg u)
  range := by
    intro u
    constructor
    · linarith [standardInnerBump.le_one (x := u)]
    · linarith [standardInnerBump.nonneg (x := u)]
  zero_core := by
    intro u hu
    have hball : u ∈ Metric.closedBall (0 : ℝ) standardInnerBump.rIn := by
      rw [Metric.mem_closedBall, Real.dist_0_eq_abs]
      simpa [standardInnerBump] using hu
    rw [standardInnerBump.one_of_mem_closedBall hball]
    simp
  one_tail := by
    intro u hu
    have hzero : standardInnerBump u = 0 := by
      apply standardInnerBump.zero_of_le_dist
      rw [Real.dist_0_eq_abs]
      simpa [standardInnerBump] using hu
    rw [hzero]
    simp

theorem standardGateProfile_exists : ∃ profile : GateProfile,
    profile = standardGateProfile := ⟨standardGateProfile, rfl⟩

theorem gate_hasDerivAt (profile : GateProfile) {tau : ℝ} (htau : tau ≠ 0)
    (s : ℝ) : HasDerivAt (gate profile tau) (profile.rho (s / tau)) s := by
  have hcont : Continuous profile.rho := profile.smooth.continuous
  have hprimitive : HasDerivAt
      (fun v => ∫ u in 0..v, profile.rho u) (profile.rho (s / tau)) (s / tau) :=
    intervalIntegral.integral_hasDerivAt_right
      (hcont.intervalIntegrable _ _)
      hcont.aestronglyMeasurable.stronglyMeasurableAtFilter hcont.continuousAt
  have hscale : HasDerivAt (fun z : ℝ => z / tau) (1 / tau) s :=
    (hasDerivAt_id s).div_const tau
  have hcomp := hprimitive.comp s hscale
  have hmul := hcomp.const_mul tau
  convert hmul using 1 <;>
    first | subsingleton | (ext z; rfl) | field_simp [htau]

theorem gate_deriv (profile : GateProfile) {tau : ℝ} (htau : tau ≠ 0)
    (s : ℝ) : deriv (gate profile tau) s = profile.rho (s / tau) :=
  (gate_hasDerivAt profile htau s).deriv

theorem gate_contDiff (profile : GateProfile) {tau : ℝ} (htau : tau ≠ 0) :
    ContDiff ℝ ∞ (gate profile tau) := by
  apply contDiff_infty_iff_deriv.mpr
  constructor
  · exact fun s => (gate_hasDerivAt profile htau s).differentiableAt
  · have hderiv : deriv (gate profile tau) = fun s => profile.rho (s / tau) := by
      funext s
      exact gate_deriv profile htau s
    rw [hderiv]
    exact profile.smooth.comp (contDiff_id.div_const tau)

theorem integral_even_zero_neg (profile : GateProfile) (v : ℝ) :
    (∫ u in 0..-v, profile.rho u) = -(∫ u in 0..v, profile.rho u) := by
  have hchange := intervalIntegral.integral_comp_neg (f := profile.rho)
    (a := 0) (b := v)
  simp only [neg_zero] at hchange
  have heven : (∫ u in 0..v, profile.rho (-u)) =
      ∫ u in 0..v, profile.rho u := by
    apply intervalIntegral.integral_congr
    intro u _hu
    exact profile.even u
  rw [heven] at hchange
  rw [intervalIntegral.integral_symm]
  exact congrArg Neg.neg hchange.symm

theorem gate_odd (profile : GateProfile) (tau : ℝ) :
    Function.Odd (gate profile tau) := by
  intro s
  simp only [gate]
  have harg : -s / tau = -(s / tau) := by ring
  rw [harg, integral_even_zero_neg profile]
  ring

theorem gate_norm_sub_le (profile : GateProfile) {tau : ℝ} (htau : tau ≠ 0)
    (x y : ℝ) : |gate profile tau y - gate profile tau x| ≤ |y - x| := by
  have hdiff : ∀ z : ℝ, DifferentiableAt ℝ (gate profile tau) z :=
    fun z => (gate_hasDerivAt profile htau z).differentiableAt
  have hbound : ∀ z : ℝ, ‖deriv (gate profile tau) z‖ ≤ (1 : ℝ) := by
    intro z
    rw [gate_deriv profile htau z, Real.norm_eq_abs,
      abs_of_nonneg (profile.range (z / tau)).1]
    exact (profile.range (z / tau)).2
  simpa only [Real.norm_eq_abs, one_mul] using
    (convex_univ.norm_image_sub_le_of_norm_deriv_le
      (s := Set.univ) (x := x) (y := y) (C := 1)
      (fun z _ => hdiff z) (fun z _ => hbound z)
      (Set.mem_univ x) (Set.mem_univ y))

theorem gate_zero_core (profile : GateProfile) {tau : ℝ} (htau : 0 < tau)
    {s : ℝ} (hs : |s| ≤ tau / 2) : gate profile tau s = 0 := by
  have hsv : |s / tau| ≤ (1 / 2 : ℝ) := by
    rw [abs_div, abs_of_pos htau]
    apply (div_le_iff₀ htau).2
    nlinarith
  have hint : (∫ u in 0..s / tau, profile.rho u) = 0 := by
    calc
      (∫ u in 0..s / tau, profile.rho u) = ∫ _u in 0..s / tau, (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro u hu
        apply profile.zero_core
        rw [Set.mem_uIcc] at hu
        rcases hu with hu | hu
        · rw [abs_of_nonneg hu.1]
          exact hu.2.trans (le_abs_self _ |>.trans hsv)
        · rw [abs_of_nonpos hu.2]
          calc
            -u ≤ -(s / tau) := neg_le_neg hu.1
            _ = |s / tau| := (abs_of_nonpos (hu.1.trans hu.2)).symm
            _ ≤ 1 / 2 := hsv
      _ = 0 := by simp
  simp [gate, hint]

theorem gate_all_derivatives_zero_core (profile : GateProfile) {tau : ℝ}
    (htau : 0 < tau) (n : ℕ) {s : ℝ} (hs : |s| ≤ tau / 2) :
    iteratedDeriv n (gate profile tau) s = 0 := by
  let I : Set ℝ := Set.Icc (-tau / 2) (tau / 2)
  have hends : -tau / 2 < tau / 2 := by nlinarith
  have hI : UniqueDiffOn ℝ I := uniqueDiffOn_Icc hends
  have hsI : s ∈ I := by
    dsimp [I]
    constructor <;> nlinarith [neg_abs_le s, le_abs_self s]
  have heq : Set.EqOn (gate profile tau) (fun _ => (0 : ℝ)) I := by
    intro z hz
    apply gate_zero_core profile htau
    rw [abs_le]
    dsimp [I] at hz
    constructor <;> nlinarith [hz.1, hz.2]
  have hwithin := (iteratedDerivWithin_congr (n := n) heq) hsI
  have hglobal := iteratedDerivWithin_eq_iteratedDeriv
    (n := n) (f := gate profile tau) (s := I) (x := s) hI
    ((contDiff_infty.mp (gate_contDiff profile htau.ne') n).contDiffAt) hsI
  rw [hglobal] at hwithin
  simpa using hwithin

theorem gateShift_bounds (profile : GateProfile) {tau : ℝ} (htau : 0 < tau) :
    tau / 2 ≤ gateShift profile tau ∧ gateShift profile tau ≤ tau := by
  let q : ℝ → ℝ := fun u => 1 - profile.rho u
  have hqcont : Continuous q := continuous_const.sub profile.smooth.continuous
  have hqnonneg : ∀ u, 0 ≤ q u := fun u => by
    dsimp [q]
    linarith [(profile.range u).2]
  have hqle : ∀ u, q u ≤ 1 := fun u => by
    dsimp [q]
    linarith [(profile.range u).1]
  have hwhole_nonneg : 0 ≤ ∫ u in (1 / 2 : ℝ)..1, q u :=
    intervalIntegral.integral_nonneg (by norm_num) (fun u _ => hqnonneg u)
  have hcore : (∫ u in 0..(1 / 2 : ℝ), q u) = 1 / 2 := by
    calc
      (∫ u in 0..(1 / 2 : ℝ), q u) = ∫ _u in 0..(1 / 2 : ℝ), (1 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro u hu
        dsimp [q]
        rw [profile.zero_core]
        · ring
        · rw [Set.mem_uIcc] at hu
          rcases hu with hu | hu
          · rw [abs_of_nonneg hu.1]
            exact hu.2
          · exfalso
            norm_num at hu
            linarith
      _ = 1 / 2 := by norm_num [intervalIntegral.integral_const]
  have hadd := intervalIntegral.integral_add_adjacent_intervals
    (hqcont.intervalIntegrable (μ := volume) 0 (1 / 2))
    (hqcont.intervalIntegrable (μ := volume) (1 / 2) 1)
  have hlower : (1 / 2 : ℝ) ≤ ∫ u in 0..1, q u := by
    rw [← hadd, hcore]
    linarith
  have hupper : (∫ u in 0..1, q u) ≤ 1 := by
    calc
      (∫ u in 0..1, q u) ≤ ∫ _u in 0..1, (1 : ℝ) := by
        exact intervalIntegral.integral_mono_on (by norm_num)
          (hqcont.intervalIntegrable (μ := volume) _ _)
          (continuous_const.intervalIntegrable (μ := volume) 0 1)
          (fun u _ => hqle u)
      _ = 1 := by norm_num [intervalIntegral.integral_const]
  dsimp [gateShift]
  change tau / 2 ≤ tau * (∫ u in 0..1, q u) ∧
    tau * (∫ u in 0..1, q u) ≤ tau
  constructor
  · nlinarith
  · nlinarith

theorem gate_tail (profile : GateProfile) {tau : ℝ} (htau : 0 < tau)
    {s : ℝ} (hs : tau ≤ s) :
    gate profile tau s = s - gateShift profile tau := by
  have hv : 1 ≤ s / tau := (le_div_iff₀ htau).2 (by simpa using hs)
  have hcont : Continuous profile.rho := profile.smooth.continuous
  have htail : (∫ u in 1..s / tau, profile.rho u) = s / tau - 1 := by
    calc
      (∫ u in 1..s / tau, profile.rho u) =
          ∫ _u in 1..s / tau, (1 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro u hu
        apply profile.one_tail
        rw [Set.mem_uIcc] at hu
        rcases hu with hu | hu
        · rw [abs_of_nonneg (le_trans (by norm_num) hu.1)]
          exact hu.1
        · have hueq : u = 1 := by linarith [hv]
          subst u
          norm_num
      _ = s / tau - 1 := by simp [intervalIntegral.integral_const]
  have hadd := intervalIntegral.integral_add_adjacent_intervals
    (hcont.intervalIntegrable (μ := volume) 0 1)
    (hcont.intervalIntegrable (μ := volume) 1 (s / tau))
  have hsplit : (∫ u in 0..s / tau, profile.rho u) =
      (∫ u in 0..1, profile.rho u) + (s / tau - 1) := by
    rw [← hadd, htail]
  have hq : (∫ u in 0..1, (1 - profile.rho u)) =
      1 - ∫ u in 0..1, profile.rho u := by
    rw [intervalIntegral.integral_sub
      (continuous_const.intervalIntegrable (μ := volume) 0 1)
      (hcont.intervalIntegrable (μ := volume) 0 1)]
    norm_num [intervalIntegral.integral_const]
  rw [gate, gateShift, hsplit, hq]
  field_simp [htau.ne']
  ring

theorem gate_residual_norm_sub_le (profile : GateProfile) {tau : ℝ}
    (htau : tau ≠ 0) (x y : ℝ) :
    |(y - gate profile tau y) - (x - gate profile tau x)| ≤ |y - x| := by
  let r : ℝ → ℝ := fun z => z - gate profile tau z
  have hdiff : ∀ z : ℝ, DifferentiableAt ℝ r z := fun z =>
    (hasDerivAt_id z).sub (gate_hasDerivAt profile htau z) |>.differentiableAt
  have hderiv : ∀ z : ℝ, deriv r z = 1 - profile.rho (z / tau) := by
    intro z
    exact ((hasDerivAt_id z).sub (gate_hasDerivAt profile htau z)).deriv
  have hbound : ∀ z : ℝ, ‖deriv r z‖ ≤ (1 : ℝ) := by
    intro z
    rw [hderiv z, Real.norm_eq_abs,
      abs_of_nonneg (by linarith [(profile.range (z / tau)).2])]
    linarith [(profile.range (z / tau)).1]
  simpa only [r, Real.norm_eq_abs, one_mul] using
    (convex_univ.norm_image_sub_le_of_norm_deriv_le
      (s := Set.univ) (x := x) (y := y) (C := 1)
      (fun z _ => hdiff z) (fun z _ => hbound z)
      (Set.mem_univ x) (Set.mem_univ y))

theorem gate_basic_bounds (profile : GateProfile) {tau : ℝ} (htau : 0 < tau)
    (s : ℝ) :
    0 ≤ deriv (gate profile tau) s ∧ deriv (gate profile tau) s ≤ 1 ∧
      |gate profile tau s| ≤ |s| ∧ |s - gate profile tau s| ≤ tau ∧
      gate profile tau s ≥ s - tau := by
  have hgate0 : gate profile tau 0 = 0 := by simp [gate]
  have hres0 : 0 - gate profile tau 0 = 0 := by rw [hgate0]; ring
  have hgateabs : |gate profile tau s| ≤ |s| := by
    have h := gate_norm_sub_le profile htau.ne' 0 s
    simpa [hgate0] using h
  have hresabs : |s - gate profile tau s| ≤ tau := by
    by_cases hs0 : 0 ≤ s
    · by_cases hst : s ≤ tau
      · have h := gate_residual_norm_sub_le profile htau.ne' 0 s
        rw [hres0] at h
        simpa only [sub_zero] using
          h.trans (by simpa [abs_of_nonneg hs0] using hst)
      · have htail := gate_tail profile htau (le_of_not_ge hst)
        rw [htail]
        have hb := (gateShift_bounds profile htau).2
        rw [show s - (s - gateShift profile tau) = gateShift profile tau by ring]
        rw [abs_of_nonneg ((by positivity : 0 ≤ tau / 2).trans
          (gateShift_bounds profile htau).1)]
        exact hb
    · have hsneg : 0 ≤ -s := by linarith
      have hodd := gate_odd profile tau s
      have hpos : |-s - gate profile tau (-s)| ≤ tau := by
        by_cases hle : -s ≤ tau
        · have h := gate_residual_norm_sub_le profile htau.ne' 0 (-s)
          rw [hres0] at h
          simpa only [sub_zero] using
            h.trans (by simpa [abs_of_nonneg hsneg] using hle)
        · have htail := gate_tail profile htau (le_of_not_ge hle)
          rw [htail]
          rw [show -s - (-s - gateShift profile tau) = gateShift profile tau by ring]
          rw [abs_of_nonneg ((by positivity : 0 ≤ tau / 2).trans
            (gateShift_bounds profile htau).1)]
          exact (gateShift_bounds profile htau).2
      rw [hodd] at hpos
      calc
        |s - gate profile tau s| = |-s + gate profile tau s| := by
          rw [← abs_neg]
          congr 1
          ring
        _ ≤ tau := by simpa only [sub_neg_eq_add] using hpos
  have hder := gate_deriv profile htau.ne' s
  refine ⟨?_, ?_, hgateabs, hresabs, ?_⟩
  · rw [hder]
    exact (profile.range (s / tau)).1
  · rw [hder]
    exact (profile.range (s / tau)).2
  · have := le_abs_self (s - gate profile tau s)
    linarith

theorem profile_iteratedDeriv_zero_of_abs_gt (profile : GateProfile) {n : ℕ}
    (hn : 0 < n) {u : ℝ} (hu : 1 < |u|) :
    iteratedDeriv n profile.rho u = 0 := by
  by_cases hneg : u < 0
  · have huI : u ∈ Set.Iio (-1 : ℝ) := by
      rw [abs_of_neg hneg] at hu
      change u < -1
      linarith
    have heq : Set.EqOn profile.rho (fun _ => (1 : ℝ)) (Set.Iio (-1 : ℝ)) := by
      intro z hz
      change z < -1 at hz
      apply profile.one_tail
      rw [abs_of_neg (lt_trans hz (by norm_num))]
      linarith
    have hd := (heq.iteratedDeriv_of_isOpen isOpen_Iio n) huI
    simpa [iteratedDeriv_const, hn.ne'] using hd
  · have hu0 : 0 ≤ u := le_of_not_gt hneg
    have huI : u ∈ Set.Ioi (1 : ℝ) := by
      rw [abs_of_nonneg hu0] at hu
      exact hu
    have heq : Set.EqOn profile.rho (fun _ => (1 : ℝ)) (Set.Ioi (1 : ℝ)) := by
      intro z hz
      apply profile.one_tail
      rw [abs_of_pos (lt_trans (by norm_num) hz)]
      exact hz.le
    have hd := (heq.iteratedDeriv_of_isOpen isOpen_Ioi n) huI
    simpa [iteratedDeriv_const, hn.ne'] using hd

theorem profile_iteratedDeriv_bddAbove (profile : GateProfile) {n : ℕ}
    (hn : 0 < n) :
    BddAbove (Set.range fun u => |iteratedDeriv n profile.rho u|) := by
  let f : ℝ → ℝ := fun u => |iteratedDeriv n profile.rho u|
  have hfcont : Continuous f :=
    ((contDiff_infty.mp profile.smooth n).continuous_iteratedDeriv n (by simp)).abs
  have hcompact : IsCompact (Set.Icc (-1 : ℝ) 1) := isCompact_Icc
  rcases bddAbove_def.mp (hcompact.bddAbove_image hfcont.continuousOn) with ⟨C, hC⟩
  apply bddAbove_def.mpr
  refine ⟨max C 0, ?_⟩
  intro z hz
  rcases hz with ⟨u, rfl⟩
  by_cases hu : u ∈ Set.Icc (-1 : ℝ) 1
  · exact (hC (f u) ⟨u, hu, rfl⟩).trans (le_max_left _ _)
  · have huabs : 1 < |u| := by
      rw [Set.mem_Icc, not_and_or, not_le, not_le] at hu
      rcases hu with hu | hu
      · rw [abs_of_neg (lt_trans hu (by norm_num))]
        linarith
      · rw [abs_of_pos (lt_trans (by norm_num) hu)]
        exact hu
    change |iteratedDeriv n profile.rho u| ≤ max C 0
    rw [profile_iteratedDeriv_zero_of_abs_gt profile hn huabs, abs_zero]
    exact le_max_right _ _

theorem profile_iteratedDeriv_le_gateBp (profile : GateProfile) {p : ℕ}
    (hp : 2 ≤ p) (u : ℝ) :
    |iteratedDeriv (p - 1) profile.rho u| ≤ gateBp p profile := by
  have hn : 0 < p - 1 := by omega
  have hbdd := profile_iteratedDeriv_bddAbove profile hn
  have hsup : |iteratedDeriv (p - 1) profile.rho u| ≤
      sSup (Set.range fun z => |iteratedDeriv (p - 1) profile.rho z|) :=
    le_csSup hbdd ⟨u, rfl⟩
  exact hsup.trans (le_max_right _ _)

theorem gate_high_derivative_lipschitz (p : ℕ) (profile : GateProfile)
    {tau : ℝ} (hp : 2 ≤ p) (htau : 0 < tau) (x y : ℝ) :
    |iteratedDeriv (p - 1) (gate profile tau) x -
      iteratedDeriv (p - 1) (gate profile tau) y| ≤
      gateBp p profile * tau ^ (1 - (p : ℤ)) * |x - y| := by
  let n := p - 1
  let g : ℝ → ℝ := iteratedDeriv n (gate profile tau)
  have hpn : p = n + 1 := by dsimp [n]; omega
  have hgdiff : Differentiable ℝ g := by
    dsimp [g]
    apply ContDiff.differentiable_iteratedDeriv' n
    simpa only [Nat.cast_add, Nat.cast_one] using
      (contDiff_infty.mp (gate_contDiff profile htau.ne') (n + 1))
  have hscale : (tau⁻¹) ^ n = tau ^ (1 - (p : ℤ)) := by
    have hexp : (1 : ℤ) - (p : ℤ) = -(n : ℤ) := by
      rw [hpn]
      push_cast
      ring
    rw [hexp, zpow_neg, zpow_natCast, inv_pow]
  have hderiv : ∀ z, deriv g z =
      tau ^ (1 - (p : ℤ)) * iteratedDeriv n profile.rho (z / tau) := by
    intro z
    have hgateDeriv : deriv (gate profile tau) = fun w => profile.rho (tau⁻¹ * w) := by
      funext w
      rw [gate_deriv profile htau.ne' w]
      congr 1
      field_simp [htau.ne']
    have hcomp := iteratedDeriv_comp_const_mul
      (contDiff_infty.mp profile.smooth n) tau⁻¹
    calc
      deriv g z = iteratedDeriv (n + 1) (gate profile tau) z := by
        simp only [g, iteratedDeriv_succ]
      _ = iteratedDeriv n (deriv (gate profile tau)) z := by
        rw [iteratedDeriv_succ']
      _ = iteratedDeriv n (fun w => profile.rho (tau⁻¹ * w)) z := by rw [hgateDeriv]
      _ = (tau⁻¹) ^ n * iteratedDeriv n profile.rho (tau⁻¹ * z) := by
        exact congrFun hcomp z
      _ = tau ^ (1 - (p : ℤ)) * iteratedDeriv n profile.rho (z / tau) := by
        rw [hscale]
        congr 2
        field_simp [htau.ne']
  have hcoef0 : 0 ≤ tau ^ (1 - (p : ℤ)) := zpow_nonneg htau.le _
  have hBp0 : 0 ≤ gateBp p profile := le_max_left _ _ |>.trans' (by norm_num)
  have hbound : ∀ z, ‖deriv g z‖ ≤ gateBp p profile * tau ^ (1 - (p : ℤ)) := by
    intro z
    rw [hderiv z, Real.norm_eq_abs, abs_mul, abs_of_nonneg hcoef0]
    have hrho := profile_iteratedDeriv_le_gateBp profile hp (z / tau)
    rw [mul_comm]
    simpa [mul_comm] using mul_le_mul_of_nonneg_left hrho hcoef0
  have hmv := convex_univ.norm_image_sub_le_of_norm_deriv_le
    (s := Set.univ) (x := y) (y := x)
    (C := gateBp p profile * tau ^ (1 - (p : ℤ)))
    (fun z _ => hgdiff z) (fun z _ => hbound z)
    (Set.mem_univ y) (Set.mem_univ x)
  simpa only [g, Real.norm_eq_abs] using hmv

/-- Kernel proof of every conclusion in `lem:gate` for any profile satisfying
the source assumptions. -/
theorem gateClaim_proof (p : ℕ) (profile : GateProfile) (tau : ℝ) :
    GateClaim p profile tau := by
  intro hp htau
  refine ⟨gate_odd profile tau, gate_contDiff profile htau.ne', ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact gate_basic_bounds profile htau
  · intro s hs
    exact gate_zero_core profile htau hs
  · intro n s hs
    exact gate_all_derivatives_zero_core profile htau n hs
  · intro x y
    exact gate_high_derivative_lipschitz p profile hp htau x y
  · intro s hs
    exact gate_tail profile htau hs
  · exact gateShift_bounds profile htau

/-- The paper's gate is non-vacuous: the explicit bundled profile satisfies
the complete audited claim for every `p ≥ 2` and `tau > 0`. -/
theorem standardGateClaim (p : ℕ) (tau : ℝ) :
    GateClaim p standardGateProfile tau :=
  gateClaim_proof p standardGateProfile tau

end LeanArticleAudit.Pilot
