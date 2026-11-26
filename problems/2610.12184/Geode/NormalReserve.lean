import Geode.Halfspace
import Geode.Subgradient
import Geode.ScalarPersistence

/-! Intrinsic supporting normals and the reserve supplied by an actual public ball. -/
namespace Geode.Lorentz

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem intrinsic_normal_ball_bound_raw {P : Set (Point E)} (c z : Point E)
    (n : Ambient E) (W : Submodule ℝ (Ambient E)) (r : ℝ) (hr : 0 ≤ r)
    (hc : c.val ∈ W) (hnW : n ∈ W) (hn : form E z.val n = 0)
    (hsupport : ∀ x ∈ P, form E n x.val ≤ 0)
    (hball : ∀ x : Point E, x.val ∈ W → dist c x ≤ r → x ∈ P) :
    Real.sqrt (form E n n) * Real.sinh r ≤ -form E n c.val := by
  by_cases hn0 : n = 0
  · simp [hn0]
  · have hsp := tangent_pos z hn hn0
    apply (section_ball_subset_halfspace_iff c n hsp r hr W hc hnW).mp
    intro x hx hd
    exact hsupport x (hball x hx hd)

theorem intrinsic_normal_interior_zero_raw {P : Set (Point E)} (c z : Point E)
    (n : Ambient E) (W : Submodule ℝ (Ambient E)) (r : ℝ) (hr : 0 ≤ r)
    (hc : c.val ∈ W) (hnW : n ∈ W) (hn : form E z.val n = 0)
    (hsupport : ∀ x ∈ P, form E n x.val ≤ 0)
    (hball : ∀ x : Point E, x.val ∈ W → dist c x ≤ r → x ∈ P)
    (hinterior : dist c z < r) : n = 0 := by
  by_contra hn0
  have hsp := tangent_pos z hn hn0
  have hα := Real.sqrt_pos.mpr hsp
  have hb := intrinsic_normal_ball_bound_raw c z n W r hr hc hnW hn hsupport hball
  have hs := Real.sinh_lt_sinh.mpr hinterior
  have hstrict : Real.sqrt (form E n n) * Real.sinh (dist c z) < -form E n c.val :=
    (mul_lt_mul_of_pos_left hs hα).trans_le hb
  have hneg := (ball_support_neg_iff hsp (dist_nonneg : 0 ≤ dist c z)).mpr hstrict
  have hu := form_le_ball_support c z n hsp
  have hnz : form E n z.val = 0 := by rw [form_comm]; exact hn
  rw [hnz] at hu
  linarith

theorem intrinsic_normal_ball_bound {P : Set (Point E)} (c z : Point E)
    (n : Ambient E) (W : Submodule ℝ (Ambient E)) (r : ℝ) (hr : 0 ≤ r)
    (hc : c.val ∈ W) (hnW : n ∈ W) (hn : NormalTo P z n)
    (hball : ∀ x : Point E, x.val ∈ W → dist c x ≤ r → x ∈ P) :
    Real.sqrt (form E n n) * Real.sinh r ≤ -form E n c.val := by
  obtain ⟨ht, hs⟩ := normalTo_iff_lorentz_halfspace.mp hn
  exact intrinsic_normal_ball_bound_raw c z n W r hr hc hnW ht hs hball

theorem intrinsic_normal_interior_zero {P : Set (Point E)} (c z : Point E)
    (n : Ambient E) (W : Submodule ℝ (Ambient E)) (r : ℝ) (hr : 0 ≤ r)
    (hc : c.val ∈ W) (hnW : n ∈ W) (hn : NormalTo P z n)
    (hball : ∀ x : Point E, x.val ∈ W → dist c x ≤ r → x ∈ P)
    (hinterior : dist c z < r) : n = 0 := by
  obtain ⟨ht, hs⟩ := normalTo_iff_lorentz_halfspace.mp hn
  exact intrinsic_normal_interior_zero_raw c z n W r hr hc hnW ht hs hball hinterior

noncomputable def publicRadial (c z : Point E) (S D : ℝ) : Ambient E :=
  (Real.sinh D)⁻¹ • (Real.cosh S • c.val - Real.cosh D • z.val)

theorem normal_reserve_identity (c z : Point E) (n : Ambient E) {S D : ℝ}
    (hS : 0 < S) (hD : 0 < D) (hn : form E z.val n = 0) :
    -(Real.sinh D / Real.sinh S) * form E n (publicRadial c z S D) =
      -(Real.cosh S / Real.sinh S) * form E n c.val := by
  have hs : Real.sinh S ≠ 0 := (Real.sinh_pos_iff.mpr hS).ne'
  have hd : Real.sinh D ≠ 0 := (Real.sinh_pos_iff.mpr hD).ne'
  have hnz : form E n z.val = 0 := by rw [form_comm]; exact hn
  simp only [publicRadial, form_smul_right, form_sub_right, hnz, mul_zero, sub_zero]
  field_simp
  ring

theorem intrinsic_normal_reserve_raw {P : Set (Point E)} (c z : Point E)
    (n : Ambient E) (W : Submodule ℝ (Ambient E)) {r S D η : ℝ}
    (hr : 0 ≤ r) (hS : 0 < S) (hD : 0 < D)
    (hc : c.val ∈ W) (hnW : n ∈ W) (hn : form E z.val n = 0)
    (hsupport : ∀ x ∈ P, form E n x.val ≤ 0)
    (hball : ∀ x : Point E, x.val ∈ W → dist c x ≤ r → x ∈ P)
    (hradius : Real.sinh r = η * Real.tanh S) :
    η * Real.sqrt (form E n n) ≤
      -(Real.sinh D / Real.sinh S) * form E n (publicRadial c z S D) := by
  have hs := Real.sinh_pos_iff.mpr hS
  have hcS := Real.cosh_pos S
  have hb := intrinsic_normal_ball_bound_raw c z n W r hr hc hnW hn hsupport hball
  have hm := mul_le_mul_of_nonneg_left hb (div_pos hcS hs).le
  rw [normal_reserve_identity c z n hS hD hn]
  have heq : (Real.cosh S / Real.sinh S) *
      (Real.sqrt (form E n n) * Real.sinh r) = η * Real.sqrt (form E n n) := by
    rw [hradius, Real.tanh_eq_sinh_div_cosh]
    field_simp
    ring
  rw [heq] at hm
  nlinarith

noncomputable def publicDistance (c z : Point E) (S : ℝ) : ℝ :=
  Geode.arcosh (Real.cosh S * Real.cosh (dist c z))

theorem publicDistance_argument (c z : Point E) (S : ℝ) :
    1 ≤ Real.cosh S * Real.cosh (dist c z) := by
  nlinarith [Real.one_le_cosh S, Real.one_le_cosh (dist c z)]

@[simp] theorem cosh_publicDistance (c z : Point E) (S : ℝ) :
    Real.cosh (publicDistance c z S) = Real.cosh S * Real.cosh (dist c z) :=
  Geode.cosh_arcosh (publicDistance_argument c z S)

theorem publicDistance_ge (c z : Point E) {S : ℝ} (hS : 0 ≤ S) :
    S ≤ publicDistance c z S := by
  apply (Geode.le_arcosh_iff_cosh_le (publicDistance_argument c z S) hS).mpr
  nlinarith [Real.cosh_pos S, Real.one_le_cosh (dist c z)]

theorem publicDistance_pos (c z : Point E) {S : ℝ} (hS : 0 < S) :
    0 < publicDistance c z S := hS.trans_le (publicDistance_ge c z hS.le)

noncomputable def publicDirection (c z : Point E) (S : ℝ) : Ambient E :=
  publicRadial c z S (publicDistance c z S)

noncomputable def publicRatio (c z : Point E) (S : ℝ) : ℝ :=
  Real.sinh (publicDistance c z S) / Real.sinh S

noncomputable def publicRadius (η S : ℝ) : ℝ := Real.arsinh (η * Real.tanh S)

@[simp] theorem sinh_publicRadius (η S : ℝ) : Real.sinh (publicRadius η S) = η * Real.tanh S :=
  Real.sinh_arsinh _

theorem publicRadius_nonneg {η S : ℝ} (hη : 0 ≤ η) (hS : 0 ≤ S) :
    0 ≤ publicRadius η S := by
  apply Real.arsinh_nonneg_iff.mpr
  rw [Real.tanh_eq_sinh_div_cosh]
  exact mul_nonneg hη (div_nonneg (Real.sinh_nonneg_iff.mpr hS) (Real.cosh_pos S).le)

theorem publicRatio_pos (c z : Point E) {S : ℝ} (hS : 0 < S) :
    0 < publicRatio c z S :=
  div_pos (Real.sinh_pos_iff.mpr (publicDistance_pos c z hS)) (Real.sinh_pos_iff.mpr hS)

theorem publicRatio_ge_one (c z : Point E) {S : ℝ} (hS : 0 < S) :
    1 ≤ publicRatio c z S :=
  (one_le_div (Real.sinh_pos_iff.mpr hS)).mpr
    (Real.sinh_le_sinh.mpr (publicDistance_ge c z hS.le))

theorem publicRatio_sq (c z : Point E) {S : ℝ} (hS : 0 < S) :
    publicRatio c z S ^ 2 = 1 +
      (Real.cosh S / Real.sinh S) ^ 2 * Real.sinh (dist c z) ^ 2 := by
  have hs : Real.sinh S ≠ 0 := (Real.sinh_pos_iff.mpr hS).ne'
  have hD := Real.cosh_sq_sub_sinh_sq (publicDistance c z S)
  rw [cosh_publicDistance] at hD
  have hS' := Real.cosh_sq_sub_sinh_sq S
  rw [mul_pow, Real.cosh_sq (x := dist c z)] at hD
  have hid : Real.sinh (publicDistance c z S) ^ 2 =
      Real.cosh S ^ 2 * Real.sinh (dist c z) ^ 2 + Real.sinh S ^ 2 := by nlinarith
  unfold publicRatio
  rw [div_pow, hid]
  field_simp only [hs]
  ring

theorem publicDirection_tangent (c z : Point E) (S : ℝ) :
    form E z.val (publicDirection c z S) = 0 := by
  have hzc : form E z.val c.val = -Real.cosh (dist c z) := by
    rw [form_comm, cosh_dist]
    ring
  simp only [publicDirection, publicRadial, form_smul_right, form_sub_right,
    z.normalized, hzc, cosh_publicDistance]
  ring

theorem publicDirection_form_self (c z : Point E) {S : ℝ} (hS : 0 < S) :
    form E (publicDirection c z S) (publicDirection c z S) =
      1 - 1 / publicRatio c z S ^ 2 := by
  have hs : Real.sinh S ≠ 0 := (Real.sinh_pos_iff.mpr hS).ne'
  have hd : Real.sinh (publicDistance c z S) ≠ 0 :=
    (Real.sinh_pos_iff.mpr (publicDistance_pos c z hS)).ne'
  have hcz : form E c.val z.val = -Real.cosh (dist c z) := by rw [cosh_dist]; ring
  have hzc : form E z.val c.val = -Real.cosh (dist c z) := by rw [form_comm]; exact hcz
  have hnorm : form E
      (Real.cosh S • c.val - Real.cosh (publicDistance c z S) • z.val)
      (Real.cosh S • c.val - Real.cosh (publicDistance c z S) • z.val) =
      Real.sinh (publicDistance c z S) ^ 2 - Real.sinh S ^ 2 := by
    simp only [form_sub_left, form_sub_right, form_smul_left, form_smul_right,
      c.normalized, z.normalized, hcz, hzc]
    have hm := congrArg (fun a : ℝ => a * Real.cosh (publicDistance c z S))
      (cosh_publicDistance c z S)
    dsimp only at hm
    nlinarith [Real.cosh_sq_sub_sinh_sq S,
      Real.cosh_sq_sub_sinh_sq (publicDistance c z S)]
  simp only [publicDirection, publicRadial, form_smul_left, form_smul_right, hnorm, publicRatio]
  field_simp only [hs, hd]
  ring

theorem public_ball_location (c z : Point E) {η S : ℝ} (hη : 0 ≤ η) (hS : 0 < S) :
    dist c z < publicRadius η S ↔ publicRatio c z S < Real.sqrt (1 + η ^ 2) := by
  have hs := Real.sinh_pos_iff.mpr hS
  have hc := Real.cosh_pos S
  have hp := publicRatio_pos c z hS
  have hsq := publicRatio_sq c z hS
  have hroot := Real.sqrt_nonneg (1 + η ^ 2)
  have hrootsq := Real.sq_sqrt (show 0 ≤ 1 + η ^ 2 by positivity)
  have hcoef : 0 < (Real.cosh S / Real.sinh S) ^ 2 := sq_pos_of_pos (div_pos hc hs)
  have hrad : (Real.cosh S / Real.sinh S) ^ 2 * Real.sinh (publicRadius η S) ^ 2 = η ^ 2 := by
    rw [sinh_publicRadius, Real.tanh_eq_sinh_div_cosh]
    field_simp
    ring
  have hsd := Real.sinh_nonneg_iff.mpr (dist_nonneg : 0 ≤ dist c z)
  have hsr := Real.sinh_nonneg_iff.mpr (publicRadius_nonneg hη hS.le)
  constructor
  · intro hlt
    have ht := (sq_lt_sq₀ hsd hsr).mpr (Real.sinh_lt_sinh.mpr hlt)
    have hm := mul_lt_mul_of_pos_left ht hcoef
    apply (sq_lt_sq₀ hp.le hroot).mp
    nlinarith
  · intro hlt
    have ht := (sq_lt_sq₀ hp.le hroot).mpr hlt
    have hm : Real.sinh (dist c z) ^ 2 < Real.sinh (publicRadius η S) ^ 2 := by
      apply (mul_lt_mul_left hcoef).mp
      nlinarith
    exact Real.sinh_lt_sinh.mp ((sq_lt_sq₀ hsd hsr).mp hm)

theorem reference_radius_threshold {μ : ℝ} (hμ : 0 < μ) (hμmax : μ ≤ 1 / 16) :
    Real.sqrt (1 + Geode.eta μ ^ 2) = 1 / Geode.kappa μ := by
  have hk := Geode.kappa_pos hμ hμmax
  have hμ2 := Geode.mu_sq_lt_one hμ hμmax
  have hd : 1 - μ ^ 2 ≠ 0 := by linarith
  have hp : 1 + μ ^ 2 ≠ 0 := by positivity
  have hid : (1 / Geode.kappa μ) ^ 2 = 1 + Geode.eta μ ^ 2 := by
    unfold Geode.kappa Geode.eta
    field_simp
    ring
  have hnonneg : 0 ≤ 1 / Geode.kappa μ := (div_pos (by norm_num) hk).le
  have hs := Real.sq_sqrt (show 0 ≤ 1 + Geode.eta μ ^ 2 by positivity)
  nlinarith [Real.sqrt_nonneg (1 + Geode.eta μ ^ 2)]

theorem public_ball_location_reference (c z : Point E) {μ S : ℝ}
    (hμ : 0 < μ) (hμmax : μ ≤ 1 / 16) (hS : 0 < S) :
    dist c z < publicRadius (Geode.eta μ) S ↔ publicRatio c z S < 1 / Geode.kappa μ := by
  rw [public_ball_location c z (Geode.eta_pos hμ hμmax).le hS,
    reference_radius_threshold hμ hμmax]

theorem intrinsic_normal_reserve {P : Set (Point E)} (c z : Point E)
    (n : Ambient E) (W : Submodule ℝ (Ambient E)) {η S : ℝ}
    (hη : 0 ≤ η) (hS : 0 < S) (hc : c.val ∈ W) (hnW : n ∈ W)
    (hn : NormalTo P z n)
    (hball : ∀ x : Point E, x.val ∈ W → dist c x ≤ publicRadius η S → x ∈ P) :
    η * Real.sqrt (form E n n) ≤ -publicRatio c z S * form E n (publicDirection c z S) := by
  obtain ⟨ht, hs⟩ := normalTo_iff_lorentz_halfspace.mp hn
  exact intrinsic_normal_reserve_raw c z n W (publicRadius_nonneg hη hS.le) hS
    (publicDistance_pos c z hS) hc hnW ht hs hball (sinh_publicRadius η S)

theorem intrinsic_normal_zero_of_ratio {P : Set (Point E)} (c z : Point E)
    (n : Ambient E) (W : Submodule ℝ (Ambient E)) {μ S : ℝ}
    (hμ : 0 < μ) (hμmax : μ ≤ 1 / 16) (hS : 0 < S)
    (hc : c.val ∈ W) (hnW : n ∈ W) (hn : NormalTo P z n)
    (hball : ∀ x : Point E, x.val ∈ W → dist c x ≤ publicRadius (Geode.eta μ) S → x ∈ P)
    (ha : publicRatio c z S < 1 / Geode.kappa μ) : n = 0 :=
  intrinsic_normal_interior_zero c z n W _
    (publicRadius_nonneg (Geode.eta_pos hμ hμmax).le hS.le) hc hnW hn hball
    ((public_ball_location_reference c z hμ hμmax hS).mpr ha)

end Geode.Lorentz
