import Geode.NormalReserve

/-! Exact geometric projection of a historical normal and containment of a
later public ball. The scalar persistence certificate is an explicit input. -/
namespace Geode.Lorentz

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem residual_distance (c z p : Point E) (v : Ambient E) (S : ℝ)
    (W : Submodule ℝ (Ambient E)) (hz : z.val ∈ W)
    (hv : ∀ w ∈ W, form E v w = 0)
    (hrep : p.val = Real.cosh S • c.val + Real.sinh S • v) :
    dist z p = publicDistance c z S := by
  have hzv : form E z.val v = 0 := by rw [form_comm]; exact hv z.val hz
  have hzc : form E z.val c.val = -Real.cosh (dist c z) := by rw [form_comm, cosh_dist]; ring
  rw [dist_eq_arcosh, hrep, form_add_right, form_smul_right, form_smul_right, hzv, hzc]
  unfold publicDistance
  congr 1
  ring

theorem publicDirection_mem (c z : Point E) (S : ℝ) (W : Submodule ℝ (Ambient E))
    (hc : c.val ∈ W) (hz : z.val ∈ W) : publicDirection c z S ∈ W :=
  W.smul_mem _ (W.sub_mem (W.smul_mem _ hc) (W.smul_mem _ hz))

theorem residual_direction (c z p : Point E) (v : Ambient E) {S : ℝ} (hS : 0 < S)
    (W : Submodule ℝ (Ambient E)) (hz : z.val ∈ W)
    (hv : ∀ w ∈ W, form E v w = 0)
    (hrep : p.val = Real.cosh S • c.val + Real.sinh S • v) :
    direction z p = publicDirection c z S + (1 / publicRatio c z S) • v := by
  have hd := residual_distance c z p v S W hz hv hrep
  have hs : Real.sinh S ≠ 0 := (Real.sinh_pos_iff.mpr hS).ne'
  have hD : Real.sinh (publicDistance c z S) ≠ 0 :=
    (Real.sinh_pos_iff.mpr (publicDistance_pos c z hS)).ne'
  have hcoef : 1 / publicRatio c z S = (Real.sinh (publicDistance c z S))⁻¹ * Real.sinh S := by
    unfold publicRatio
    field_simp
  simp only [direction, hd, hrep, publicDirection, publicRadial, hcoef]
  module

theorem public_center_pairing (c z : Point E) (n : Ambient E) {S : ℝ}
    (hS : 0 < S) (hn : form E z.val n = 0) :
    form E n c.val = publicRatio c z S * form E n (publicDirection c z S) * Real.tanh S := by
  have hs : Real.sinh S ≠ 0 := (Real.sinh_pos_iff.mpr hS).ne'
  have hD : Real.sinh (publicDistance c z S) ≠ 0 :=
    (Real.sinh_pos_iff.mpr (publicDistance_pos c z hS)).ne'
  have hc : Real.cosh S ≠ 0 := (Real.cosh_pos S).ne'
  have hnz : form E n z.val = 0 := by rw [form_comm]; exact hn
  simp only [publicRatio, publicDirection, publicRadial, form_smul_right,
    form_sub_right, hnz, mul_zero, sub_zero, Real.tanh_eq_sinh_div_cosh]
  field_simp
  ring

noncomputable def publicNormal (c z : Point E) (q : Ambient E) (μ S : ℝ) : Ambient E :=
  q + μ • publicDirection c z S

theorem physical_normal_residual (c z p : Point E) (q v : Ambient E) {μ S : ℝ}
    (hS : 0 < S) (W : Submodule ℝ (Ambient E)) (hz : z.val ∈ W)
    (hv : ∀ w ∈ W, form E v w = 0)
    (hrep : p.val = Real.cosh S • c.val + Real.sinh S • v) :
    (q + μ • direction z p) - publicNormal c z q μ S = (μ / publicRatio c z S) • v := by
  rw [residual_direction c z p v hS W hz hv hrep]
  unfold publicNormal
  module

theorem residual_ratio_mono (c z p : Point E) (v : Ambient E) {S S₀ : ℝ}
    (hS : 0 < S) (hSS : S ≤ S₀) (W : Submodule ℝ (Ambient E)) (hz : z.val ∈ W)
    (hv : ∀ w ∈ W, form E v w = 0)
    (hrep : p.val = Real.cosh S • c.val + Real.sinh S • v) :
    Real.sinh (dist z p) / Real.sinh S₀ ≤ publicRatio c z S := by
  rw [residual_distance c z p v S W hz hv hrep]
  exact div_le_div_of_nonneg_left
    (Real.sinh_pos_iff.mpr (publicDistance_pos c z hS)).le
    (Real.sinh_pos_iff.mpr hS) (Real.sinh_le_sinh.mpr hSS)

theorem publicNormal_tangent (c z : Point E) (q : Ambient E) (μ S : ℝ)
    (hq : form E z.val q = 0) : form E z.val (publicNormal c z q μ S) = 0 := by
  simp [publicNormal, hq, publicDirection_tangent]

theorem projected_normal_norm (c z : Point E) (q : Ambient E) {μ θ S : ℝ}
    (hS : 0 < S) (hqnorm : form E q q = 1)
    (hangle : form E q (publicDirection c z S) = -θ) :
    form E (publicNormal c z q μ S) (publicNormal c z q μ S) =
      Geode.radicand μ θ (publicRatio c z S) := by
  have huq : form E (publicDirection c z S) q = -θ := by rw [form_comm]; exact hangle
  simp only [publicNormal, form_add_left, form_add_right, form_smul_left,
    form_smul_right, hqnorm, hangle, huq, publicDirection_form_self c z hS,
    Geode.radicand, Geode.angleA]
  ring

theorem projected_normal_center (c z : Point E) (q : Ambient E) {μ θ S : ℝ}
    (hS : 0 < S) (hq : form E z.val q = 0)
    (hangle : form E q (publicDirection c z S) = -θ) :
    -form E (publicNormal c z q μ S) c.val =
      Geode.angleB μ θ (publicRatio c z S) * Real.tanh S := by
  have ha : publicRatio c z S ≠ 0 := (publicRatio_pos c z hS).ne'
  rw [public_center_pairing c z _ hS (publicNormal_tangent c z q μ S hq)]
  simp only [publicNormal, form_add_left, form_smul_left, hangle,
    publicDirection_form_self c z hS, Geode.angleB]
  field_simp
  ring

theorem future_public_ball_persistence (c z p : Point E) (q v : Ambient E)
    (W : Submodule ℝ (Ambient E)) {μ θ S : ℝ}
    (hμ : 0 < μ) (hμmax : μ ≤ 1 / 16) (hS : 0 < S)
    (hc : c.val ∈ W) (hz : z.val ∈ W) (hqW : q ∈ W)
    (hq : form E z.val q = 0) (hqnorm : form E q q = 1)
    (hv : ∀ w ∈ W, form E v w = 0)
    (hrep : p.val = Real.cosh S • c.val + Real.sinh S • v)
    (hangle : θ = -form E q (direction z p)) (hθ : θ ≤ 1)
    (hcertificate : Geode.eta μ ≤ Geode.ratio μ θ (publicRatio c z S)) :
    ∀ x : Point E, x.val ∈ W → dist c x ≤ publicRadius (Geode.eta μ) S →
      form E (q + μ • direction z p) x.val ≤ 0 := by
  have hdecomp := residual_direction c z p v hS W hz hv hrep
  have hqv : form E q v = 0 := by rw [form_comm]; exact hv q hqW
  have hangle' : form E q (publicDirection c z S) = -θ := by
    rw [hdecomp, form_add_right, form_smul_right, hqv, mul_zero, add_zero] at hangle
    linarith
  have hnW : publicNormal c z q μ S ∈ W :=
    W.add_mem hqW (W.smul_mem _ (publicDirection_mem c z S W hc hz))
  have hnorm := projected_normal_norm c z q (μ := μ) hS hqnorm hangle'
  have hrad := Geode.radicand_pos hμ hμmax hθ (publicRatio_ge_one c z hS)
  have hsp : 0 < form E (publicNormal c z q μ S) (publicNormal c z q μ S) := by
    rw [hnorm]
    exact hrad
  have hB : Geode.eta μ * Real.sqrt (Geode.radicand μ θ (publicRatio c z S)) ≤
      Geode.angleB μ θ (publicRatio c z S) :=
    (le_div_iff₀ (Real.sqrt_pos.mpr hrad)).mp hcertificate
  have htanh : 0 ≤ Real.tanh S := by
    rw [Real.tanh_eq_sinh_div_cosh]
    exact (div_pos (Real.sinh_pos_iff.mpr hS) (Real.cosh_pos S)).le
  have hb : Real.sqrt (form E (publicNormal c z q μ S) (publicNormal c z q μ S)) *
      Real.sinh (publicRadius (Geode.eta μ) S) ≤ -form E (publicNormal c z q μ S) c.val := by
    rw [hnorm, sinh_publicRadius, projected_normal_center c z q hS hq hangle']
    nlinarith [mul_le_mul_of_nonneg_right hB htanh]
  have hcontain := (section_ball_subset_halfspace_iff c (publicNormal c z q μ S) hsp _
    (publicRadius_nonneg (Geode.eta_pos hμ hμmax).le hS.le) W hc hnW).mpr hb
  intro x hx hdist
  have hxv := hv x.val hx
  have heq : form E (q + μ • direction z p) x.val = form E (publicNormal c z q μ S) x.val := by
    rw [hdecomp]
    simp only [publicNormal, form_add_left, form_smul_left, hxv, mul_zero, add_zero]
  rw [heq]
  exact hcontain x hx hdist

/-- The all-future scalar certificate at an earlier radius implies actual ball
containment at every smaller residual radius representing the same minimizer. -/
theorem future_public_ball_from_persistence (c z p : Point E) (q v : Ambient E)
    (W : Submodule ℝ (Ambient E)) {μ θ S S₀ : ℝ}
    (hμ : 0 < μ) (hμmax : μ ≤ 1 / 16) (hS : 0 < S) (hSS : S ≤ S₀)
    (hc : c.val ∈ W) (hz : z.val ∈ W) (hqW : q ∈ W)
    (hq : form E z.val q = 0) (hqnorm : form E q q = 1)
    (hv : ∀ w ∈ W, form E v w = 0)
    (hrep : p.val = Real.cosh S • c.val + Real.sinh S • v)
    (hangle : θ = -form E q (direction z p)) (hθ : θ ≤ 1)
    (hpersistence : ∀ a : ℝ, Real.sinh (dist z p) / Real.sinh S₀ ≤ a →
      Geode.eta μ ≤ Geode.ratio μ θ a) :
    ∀ x : Point E, x.val ∈ W → dist c x ≤ publicRadius (Geode.eta μ) S →
      form E (q + μ • direction z p) x.val ≤ 0 := by
  apply future_public_ball_persistence c z p q v W hμ hμmax hS hc hz hqW hq hqnorm
    hv hrep hangle hθ
  exact hpersistence _ (residual_ratio_mono c z p v hS hSS W hz hv hrep)

end Geode.Lorentz
