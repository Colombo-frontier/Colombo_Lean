import MinimaxAudit.GateBase

/-!
Scalar double primitive and the actual two-variable gate from `main.tex`.
These declarations do not import an oracle lower bound.
-/
open Set MeasureTheory intervalIntegral Filter
open scoped ContDiff Topology
namespace MinimaxAudit

/-- This identity binds the adapted scaled primitive to equation (hH). -/
theorem gate_eq_manuscript_integral (profile : GateProfile) {tau : ℝ}
    (htau : tau ≠ 0) (s : ℝ) :
    gate profile tau s = ∫ u in 0..s, profile.rho (u / tau) := by
  rw [intervalIntegral.integral_comp_div profile.rho htau]
  simp [gate, smul_eq_mul]

noncomputable def doubleGate (profile : GateProfile) (tau s : ℝ) : ℝ :=
  ∫ v in 0..s, gate profile tau v

noncomputable def scalarGate (profile : GateProfile) (tau : ℝ) (a b : ℝ) : ℝ :=
  (doubleGate profile tau (a + b) - doubleGate profile tau (a - b)) / 2

theorem doubleGate_hasDerivAt (profile : GateProfile) {tau : ℝ}
    (htau : tau ≠ 0) (s : ℝ) :
    HasDerivAt (doubleGate profile tau) (gate profile tau s) s := by
  have hcont := (gate_contDiff profile htau).continuous
  exact intervalIntegral.integral_hasDerivAt_right
    (hcont.intervalIntegrable _ _)
    hcont.aestronglyMeasurable.stronglyMeasurableAtFilter hcont.continuousAt

theorem doubleGate_deriv (profile : GateProfile) {tau : ℝ}
    (htau : tau ≠ 0) (s : ℝ) :
    deriv (doubleGate profile tau) s = gate profile tau s :=
  (doubleGate_hasDerivAt profile htau s).deriv

theorem doubleGate_contDiff (profile : GateProfile) {tau : ℝ}
    (htau : tau ≠ 0) : ContDiff ℝ ∞ (doubleGate profile tau) := by
  apply contDiff_infty_iff_deriv.mpr
  refine ⟨fun s => (doubleGate_hasDerivAt profile htau s).differentiableAt, ?_⟩
  have heq : deriv (doubleGate profile tau) = gate profile tau := by
    funext s
    exact doubleGate_deriv profile htau s
  rw [heq]
  exact gate_contDiff profile htau

theorem doubleGate_zero_core (profile : GateProfile) {tau : ℝ}
    (htau : 0 < tau) {s : ℝ} (hs : |s| ≤ tau / 2) :
    doubleGate profile tau s = 0 := by
  unfold doubleGate
  calc
    (∫ v in 0..s, gate profile tau v) = ∫ _v in 0..s, (0 : ℝ) := by
      apply intervalIntegral.integral_congr
      intro v hv
      apply gate_zero_core profile htau
      rw [Set.mem_uIcc] at hv
      rcases hv with hv | hv
      · rw [abs_of_nonneg hv.1]
        exact hv.2.trans ((le_abs_self s).trans hs)
      · rw [abs_of_nonpos hv.2]
        calc
          -v ≤ -s := neg_le_neg hv.1
          _ ≤ |s| := neg_le_abs s
          _ ≤ tau / 2 := hs
    _ = 0 := by simp

theorem doubleGate_all_derivatives_zero_core (profile : GateProfile) {tau : ℝ}
    (htau : 0 < tau) (k : ℕ) {s : ℝ} (hs : |s| ≤ tau / 2) :
    iteratedDeriv k (doubleGate profile tau) s = 0 := by
  let I : Set ℝ := Set.Icc (-tau / 2) (tau / 2)
  have hI : UniqueDiffOn ℝ I := uniqueDiffOn_Icc (by linarith)
  have hsI : s ∈ I := by
    dsimp [I]
    constructor <;> nlinarith [neg_abs_le s, le_abs_self s]
  have heq : Set.EqOn (doubleGate profile tau) (fun _ => (0 : ℝ)) I := by
    intro z hz
    apply doubleGate_zero_core profile htau
    rw [abs_le]
    dsimp [I] at hz
    constructor <;> linarith [hz.1, hz.2]
  have hw := (iteratedDerivWithin_congr (n := k) heq) hsI
  have hg := iteratedDerivWithin_eq_iteratedDeriv (n := k)
    (f := doubleGate profile tau) (s := I) (x := s) hI
    ((contDiff_infty.mp (doubleGate_contDiff profile htau.ne') k).contDiffAt) hsI
  rw [hg] at hw
  simpa using hw

theorem scalarGate_zero_core (profile : GateProfile) {tau a b : ℝ}
    (htau : 0 < tau) (hab : |a| + |b| ≤ tau / 2) :
    scalarGate profile tau a b = 0 := by
  have hp : |a + b| ≤ tau / 2 := (abs_add_le a b).trans hab
  have hm : |a - b| ≤ tau / 2 := (abs_sub a b).trans hab
  simp [scalarGate, doubleGate_zero_core profile htau hp,
    doubleGate_zero_core profile htau hm]

theorem scalarGate_partial_a (profile : GateProfile) {tau : ℝ}
    (htau : tau ≠ 0) (a b : ℝ) :
    HasDerivAt (fun x => scalarGate profile tau x b)
      ((gate profile tau (a + b) - gate profile tau (a - b)) / 2) a := by
  have hp := (doubleGate_hasDerivAt profile htau (a + b)).comp a
    ((hasDerivAt_id a).add_const b)
  have hm := (doubleGate_hasDerivAt profile htau (a - b)).comp a
    ((hasDerivAt_id a).sub_const b)
  simpa [scalarGate] using (hp.sub hm).div_const 2

theorem scalarGate_partial_b (profile : GateProfile) {tau : ℝ}
    (htau : tau ≠ 0) (a b : ℝ) :
    HasDerivAt (fun y => scalarGate profile tau a y)
      ((gate profile tau (a + b) + gate profile tau (a - b)) / 2) b := by
  have hp := (doubleGate_hasDerivAt profile htau (a + b)).comp b
    ((hasDerivAt_id b).const_add a)
  have hm := (doubleGate_hasDerivAt profile htau (a - b)).comp b
    ((hasDerivAt_id b).const_sub a)
  have hp' : HasDerivAt (fun y => doubleGate profile tau (a + y))
      (gate profile tau (a + b)) b := by simpa using! hp
  have hm' : HasDerivAt (fun y => doubleGate profile tau (a - y))
      (-gate profile tau (a - b)) b := by simpa using! hm
  simpa only [scalarGate, sub_neg_eq_add] using! (hp'.sub hm').div_const 2

theorem scalarGate_partial_a_error (profile : GateProfile) {tau : ℝ}
    (htau : 0 < tau) (a b : ℝ) :
    |deriv (fun x => scalarGate profile tau x b) a - b| ≤ tau := by
  rw [(scalarGate_partial_a profile htau.ne' a b).deriv]
  have hp := (gate_basic_bounds profile htau (a + b)).2.2.2.1
  have hm := (gate_basic_bounds profile htau (a - b)).2.2.2.1
  rw [abs_le] at hp hm ⊢
  constructor <;> linarith

theorem scalarGate_partial_b_error (profile : GateProfile) {tau : ℝ}
    (htau : 0 < tau) (a b : ℝ) :
    |deriv (fun y => scalarGate profile tau a y) b - a| ≤ tau := by
  rw [(scalarGate_partial_b profile htau.ne' a b).deriv]
  have hp := (gate_basic_bounds profile htau (a + b)).2.2.2.1
  have hm := (gate_basic_bounds profile htau (a - b)).2.2.2.1
  rw [abs_le] at hp hm ⊢
  constructor <;> linarith

end MinimaxAudit

namespace MinimaxAudit

open Set Filter
open scoped ContDiff Topology

theorem scalarGate_contDiff (profile : GateProfile) {tau : ℝ}
    (htau : tau ≠ 0) :
    ContDiff ℝ ∞ (fun z : ℝ × ℝ => scalarGate profile tau z.1 z.2) := by
  exact ((doubleGate_contDiff profile htau).comp (contDiff_fst.add contDiff_snd) |>.sub
    ((doubleGate_contDiff profile htau).comp (contDiff_fst.sub contDiff_snd))).div_const 2

def gateDiamond (tau : ℝ) : Set (ℝ × ℝ) := {z | |z.1| + |z.2| ≤ tau / 2}

theorem gateDiamond_convex (tau : ℝ) : Convex ℝ (gateDiamond tau) := by
  intro x hx y hy a b ha hb hab
  change |a * x.1 + b * y.1| + |a * x.2 + b * y.2| ≤ tau / 2
  have h1 := abs_add_le (a * x.1) (b * y.1)
  have h2 := abs_add_le (a * x.2) (b * y.2)
  rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb] at h1 h2
  change |x.1| + |x.2| ≤ tau / 2 at hx
  change |y.1| + |y.2| ≤ tau / 2 at hy
  have heq : a * (tau / 2) + b * (tau / 2) = tau / 2 := by
    rw [← add_mul, hab, one_mul]
  nlinarith [mul_le_mul_of_nonneg_left hx ha, mul_le_mul_of_nonneg_left hy hb]

theorem gateDiamond_uniqueDiffOn {tau : ℝ} (htau : 0 < tau) :
    UniqueDiffOn ℝ (gateDiamond tau) := by
  apply uniqueDiffOn_convex (gateDiamond_convex tau)
  have hcont : Continuous (fun z : ℝ × ℝ => |z.1| + |z.2|) :=
    continuous_fst.abs.add continuous_snd.abs
  have ho : IsOpen {z : ℝ × ℝ | |z.1| + |z.2| < tau / 2} :=
    isOpen_lt hcont continuous_const
  have hi : {z : ℝ × ℝ | |z.1| + |z.2| < tau / 2} ⊆ gateDiamond tau :=
    fun z hz => by
      change |z.1| + |z.2| ≤ tau / 2
      exact hz.le
  exact ⟨(0, 0), interior_maximal hi ho (by simp; linarith)⟩

/-- Full Fréchet flatness, including the boundary of the closed diamond.
The domain `ℝ × ℝ` is used only to express derivatives; zero jets are invariant
under replacing this equivalent finite-dimensional norm by the Euclidean one. -/
theorem scalarGate_all_fderivatives_zero_core (profile : GateProfile) {tau : ℝ}
    (htau : 0 < tau) (k : ℕ) {z : ℝ × ℝ} (hz : z ∈ gateDiamond tau) :
    iteratedFDeriv ℝ k (fun v : ℝ × ℝ => scalarGate profile tau v.1 v.2) z = 0 := by
  let f : ℝ × ℝ → ℝ := fun v => scalarGate profile tau v.1 v.2
  have heq : Set.EqOn f (fun _ => (0 : ℝ)) (gateDiamond tau) :=
    fun v hv => scalarGate_zero_core profile htau hv
  have hwithin := iteratedFDerivWithin_congr (𝕜 := ℝ) heq hz k
  have hglobal := iteratedFDerivWithin_eq_iteratedFDeriv (𝕜 := ℝ) (n := k)
    (gateDiamond_uniqueDiffOn htau)
    ((contDiff_infty.mp (scalarGate_contDiff profile htau.ne') k).contDiffAt) hz
  rw [hglobal] at hwithin
  simpa using hwithin

end MinimaxAudit

namespace MinimaxAudit
open Set Metric
open scoped ContDiff

theorem doubleGate_even (profile : GateProfile) (tau : ℝ) :
    Function.Even (doubleGate profile tau) := by
  intro s
  have hc := intervalIntegral.integral_comp_neg (f := gate profile tau) (a := 0) (b := s)
  have ho : (∫ u in 0..s, gate profile tau (-u)) =
      -(∫ u in 0..s, gate profile tau u) := by
    calc
      (∫ u in 0..s, gate profile tau (-u)) = ∫ u in 0..s, -gate profile tau u := by
        apply intervalIntegral.integral_congr
        intro u _
        exact gate_odd profile tau u
      _ = _ := intervalIntegral.integral_neg
  rw [ho] at hc
  simp only [neg_zero] at hc
  change (∫ u in 0..-s, gate profile tau u) = ∫ u in 0..s, gate profile tau u
  apply neg_injective
  calc
    -(∫ u in 0..-s, gate profile tau u) = ∫ u in -s..0, gate profile tau u := by
      rw [intervalIntegral.integral_symm]
      simp
    _ = -(∫ u in 0..s, gate profile tau u) := hc.symm

theorem doubleGate_quadratic_error (profile : GateProfile) {tau : ℝ}
    (htau : 0 < tau) (a : ℝ) :
    |doubleGate profile tau a - a ^ 2 / 2| ≤ tau * |a| := by
  let f : ℝ → ℝ := fun s => doubleGate profile tau s - s ^ 2 / 2
  have hd : ∀ s, HasDerivAt f (gate profile tau s - s) s := by
    intro s
    convert! (doubleGate_hasDerivAt profile htau.ne' s).sub
      (((hasDerivAt_id s).pow 2).div_const 2) using 1 <;> dsimp [f] <;> ring
  have hb : ∀ s, ‖deriv f s‖ ≤ tau := by
    intro s
    rw [(hd s).deriv, Real.norm_eq_abs, abs_sub_comm]
    exact (gate_basic_bounds profile htau s).2.2.2.1
  have hm := convex_univ.norm_image_sub_le_of_norm_deriv_le
    (s := Set.univ) (x := (0 : ℝ)) (y := a) (C := tau)
    (fun s _ => (hd s).differentiableAt) (fun s _ => hb s)
    (Set.mem_univ _) (Set.mem_univ _)
  simpa [f, doubleGate, Real.norm_eq_abs] using hm

theorem scalarGate_bilinear_error (profile : GateProfile) {tau : ℝ}
    (htau : 0 < tau) (a b : ℝ) :
    |scalarGate profile tau a b - a * b| ≤ tau * |b| := by
  let f : ℝ → ℝ := fun s => scalarGate profile tau a s - a * s
  have hd : ∀ s, HasDerivAt f
      ((gate profile tau (a + s) + gate profile tau (a - s)) / 2 - a) s := by
    intro s
    have ha : HasDerivAt (fun v : ℝ => a * v) a s := by
      simpa using! (hasDerivAt_id s).const_mul a
    exact (scalarGate_partial_b profile htau.ne' a s).sub ha
  have hb : ∀ s, ‖deriv f s‖ ≤ tau := by
    intro s
    rw [(hd s).deriv, Real.norm_eq_abs]
    have h := scalarGate_partial_b_error profile htau a s
    rw [(scalarGate_partial_b profile htau.ne' a s).deriv] at h
    exact h
  have hm := convex_univ.norm_image_sub_le_of_norm_deriv_le
    (s := Set.univ) (x := (0 : ℝ)) (y := b) (C := tau)
    (fun s _ => (hd s).differentiableAt) (fun s _ => hb s)
    (Set.mem_univ _) (Set.mem_univ _)
  simpa [f, scalarGate, Real.norm_eq_abs] using hm

end MinimaxAudit
