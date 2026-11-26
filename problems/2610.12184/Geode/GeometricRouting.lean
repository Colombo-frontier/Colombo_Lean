import Geode.FuturePersistence
import Geode.ContactRouting

/-! Small-latitude routing for actual Lorentz tangent vectors and an actual
public carrier. Candidate existence and contact construction are separate. -/
namespace Geode.Lorentz

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

structure RoutingData (P : Set (Point E)) (W : Submodule ℝ (Ambient E))
    (c z : Point E) (μ S : ℝ) where
  q : Ambient E
  qV : Ambient E
  e : Ambient E
  β : ℝ
  center_mem : c.val ∈ W
  contact_mem : z.val ∈ W
  carrier_section : ∀ x ∈ P, x.val ∈ W
  contains_ball : ∀ x : Point E, x.val ∈ W → dist c x ≤ publicRadius (Geode.eta μ) S → x ∈ P
  q_tangent : form E z.val q = 0
  q_unit : form E q q = 1
  public_mem : qV ∈ W
  residual_orthogonal : ∀ w ∈ W, form E e w = 0
  residual_unit : form E e e = 1
  decomposition : q = qV + β • e
  beta_nonneg : 0 ≤ β
  normal : NormalTo P z (publicNormal c z qV μ S)

variable {P : Set (Point E)} {W : Submodule ℝ (Ambient E)}
  {c z : Point E} {μ S : ℝ}

theorem RoutingData.public_tangent (C : RoutingData P W c z μ S) : form E z.val C.qV = 0 := by
  have hze : form E z.val C.e = 0 := by rw [form_comm]; exact C.residual_orthogonal _ C.contact_mem
  have hq := C.q_tangent
  rw [C.decomposition, form_add_right, form_smul_right, hze] at hq
  linarith

theorem RoutingData.public_norm_sq (C : RoutingData P W c z μ S) :
    form E C.qV C.qV + C.β ^ 2 = 1 := by
  have hev := C.residual_orthogonal _ C.public_mem
  have hve : form E C.qV C.e = 0 := by rw [form_comm]; exact hev
  have hq := C.q_unit
  rw [C.decomposition] at hq
  simp only [form_add_left, form_add_right, form_smul_left, form_smul_right,
    hev, hve, C.residual_unit] at hq
  nlinarith

theorem tangent_cauchy_lower_sqrt (z : Point E) (u v : Ambient E)
    (hu : form E z.val u = 0) (hv : form E z.val v = 0) :
    -Real.sqrt (form E u u) * Real.sqrt (form E v v) ≤ form E u v := by
  have hu0 := tangent_nonneg z hu
  have hv0 := tangent_nonneg z hv
  have hcs := tangent_cauchy_sq z hu hv
  have hsu := Real.sq_sqrt hu0
  have hsv := Real.sq_sqrt hv0
  have hp := mul_nonneg (Real.sqrt_nonneg (form E u u)) (Real.sqrt_nonneg (form E v v))
  have hpsq : (Real.sqrt (form E u u) * Real.sqrt (form E v v)) ^ 2 =
      form E u u * form E v v := by rw [mul_pow, hsu, hsv]
  nlinarith

noncomputable def contactAngle (C : RoutingData P W c z μ S) (p : Point E) : ℝ :=
  -form E C.q (direction z p)

theorem RoutingData.angle_formula (C : RoutingData P W c z μ S) (hS : 0 < S)
    (p : Point E) (v : Ambient E) (hv : ∀ w ∈ W, form E v w = 0)
    (hrep : p.val = Real.cosh S • c.val + Real.sinh S • v)
    (hlat : C.β = 0 ∨ form E C.e v = -Geode.eta μ) :
    contactAngle C p = -form E C.qV (publicDirection c z S) +
      C.β * Geode.eta μ / publicRatio c z S := by
  have hqv : form E C.qV v = 0 := by rw [form_comm]; exact hv _ C.public_mem
  have heu := C.residual_orthogonal _ (publicDirection_mem c z S W C.center_mem C.contact_mem)
  unfold contactAngle
  rw [residual_direction c z p v hS W C.contact_mem hv hrep, C.decomposition]
  simp only [form_add_left, form_add_right, form_smul_left, form_smul_right, hqv, heu]
  rcases hlat with hβ | hlat
  · rw [hβ]
    ring
  · rw [hlat]
    ring

theorem RoutingData.angle_le_one (C : RoutingData P W c z μ S) (hS : 0 < S)
    (p : Point E) (v : Ambient E) (hv : ∀ w ∈ W, form E v w = 0)
    (hrep : p.val = Real.cosh S • c.val + Real.sinh S • v) : contactAngle C p ≤ 1 := by
  have hd : 0 < dist z p := by
    rw [residual_distance c z p v S W C.contact_mem hv hrep]
    exact publicDistance_pos c z hS
  have hzp := dist_pos.mp hd
  have hcs := tangent_cauchy_sq z C.q_tangent (direction_tangent z p)
  rw [C.q_unit, direction_unit z p hzp] at hcs
  unfold contactAngle
  nlinarith

theorem RoutingData.scalar_persistence (C : RoutingData P W c z μ S)
    (hμ : 0 < μ) (hμmax : μ ≤ 1 / 16) (hS : 0 < S)
    (p : Point E) (v : Ambient E) (hv : ∀ w ∈ W, form E v w = 0)
    (hrep : p.val = Real.cosh S • c.val + Real.sinh S • v)
    (hlat : C.β = 0 ∨ form E C.e v = -Geode.eta μ) :
    μ < contactAngle C p ∧ ∀ a' : ℝ, publicRatio c z S ≤ a' →
      Geode.eta μ ≤ Geode.ratio μ (contactAngle C p) a' := by
  let α := Real.sqrt (form E (publicNormal c z C.qV μ S) (publicNormal c z C.qV μ S))
  let u := Real.sqrt (form E (publicDirection c z S) (publicDirection c z S))
  let w := Real.sqrt (form E C.qV C.qV)
  let γ := form E C.qV (publicDirection c z S)
  have hα2 : α ^ 2 = form E (publicNormal c z C.qV μ S) (publicNormal c z C.qV μ S) :=
    Real.sq_sqrt (tangent_nonneg z C.normal.1)
  have hu2 : u ^ 2 = form E (publicDirection c z S) (publicDirection c z S) :=
    Real.sq_sqrt (tangent_nonneg z (publicDirection_tangent c z S))
  have hw2 : w ^ 2 = form E C.qV C.qV := Real.sq_sqrt (tangent_nonneg z C.public_tangent)
  have hnorm : α ^ 2 = w ^ 2 + μ ^ 2 * u ^ 2 + 2 * μ * γ := by
    rw [hα2, hw2, hu2]
    have huq : form E (publicDirection c z S) C.qV = γ := form_comm _ _
    simp only [publicNormal, form_add_left, form_add_right, form_smul_left, form_smul_right, huq]
    dsimp [γ]
    ring
  have hnW : publicNormal c z C.qV μ S ∈ W :=
    W.add_mem C.public_mem (W.smul_mem _ (publicDirection_mem c z S W C.center_mem C.contact_mem))
  have hreserve := intrinsic_normal_reserve c z (publicNormal c z C.qV μ S) W
    (Geode.eta_pos hμ hμmax).le hS C.center_mem hnW C.normal C.contains_ball
  have hreserve' : Geode.eta μ * α ≤ -publicRatio c z S * (γ + μ * u ^ 2) := by
    have hpair : form E (publicNormal c z C.qV μ S) (publicDirection c z S) = γ + μ * u ^ 2 := by
      rw [hu2]
      simp only [publicNormal, form_add_left, form_smul_left]
      rfl
    change Geode.eta μ * α ≤ -publicRatio c z S *
      form E (publicNormal c z C.qV μ S) (publicDirection c z S) at hreserve
    rwa [hpair] at hreserve
  have hInterior : publicRatio c z S < 1 / Geode.kappa μ → α = 0 := by
    intro ha
    have hn0 := intrinsic_normal_zero_of_ratio c z (publicNormal c z C.qV μ S) W
      hμ hμmax hS C.center_mem hnW C.normal C.contains_ball ha
    dsimp [α]
    rw [hn0]
    simp
  apply Geode.routing_all_future (α := α) (β := C.β) (u := u) (v := w) (γ := γ)
    hμ hμmax (publicRatio_ge_one c z hS)
    (Real.sqrt_nonneg _) C.beta_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  · exact hu2.trans (publicDirection_form_self c z hS)
  · rw [hw2]
    exact C.public_norm_sq
  · exact tangent_cauchy_lower_sqrt z C.qV (publicDirection c z S)
      C.public_tangent (publicDirection_tangent c z S)
  · exact hnorm
  · exact hreserve'
  · exact C.angle_formula hS p v hv hrep hlat
  · exact C.angle_le_one hS p v hv hrep
  · exact hInterior

theorem RoutingData.angle_independent (C : RoutingData P W c z μ S) (hS : 0 < S)
    (p p' : Point E) (v v' : Ambient E)
    (hv : ∀ w ∈ W, form E v w = 0) (hv' : ∀ w ∈ W, form E v' w = 0)
    (hrep : p.val = Real.cosh S • c.val + Real.sinh S • v)
    (hrep' : p'.val = Real.cosh S • c.val + Real.sinh S • v')
    (hlat : C.β = 0 ∨ form E C.e v = -Geode.eta μ)
    (hlat' : C.β = 0 ∨ form E C.e v' = -Geode.eta μ) :
    contactAngle C p = contactAngle C p' :=
  (C.angle_formula hS p v hv hrep hlat).trans (C.angle_formula hS p' v' hv' hrep' hlat').symm

theorem RoutingData.normal_for_candidate (C : RoutingData P W c z μ S) (hS : 0 < S)
    (p : Point E) (v : Ambient E) (hv : ∀ w ∈ W, form E v w = 0)
    (hrep : p.val = Real.cosh S • c.val + Real.sinh S • v) :
    NormalTo P z (C.q + μ • direction z p) := by
  apply normalTo_iff_lorentz_halfspace.mpr
  constructor
  · simp [C.q_tangent, direction_tangent]
  · intro x hx
    have hxW := C.carrier_section x hx
    have he := C.residual_orthogonal _ hxW
    have hvx := hv _ hxW
    have heq : form E (C.q + μ • direction z p) x.val =
        form E (publicNormal c z C.qV μ S) x.val := by
      rw [C.decomposition, residual_direction c z p v hS W C.contact_mem hv hrep]
      simp only [publicNormal, form_add_left, form_smul_left, he, hvx, mul_zero, add_zero]
    rw [heq]
    exact (normalTo_iff_lorentz_halfspace.mp C.normal).2 x hx

theorem RoutingData.normal_candidate_pairing (C : RoutingData P W c z μ S) (hS : 0 < S)
    (p : Point E) (v : Ambient E) (hv : ∀ w ∈ W, form E v w = 0)
    (hrep : p.val = Real.cosh S • c.val + Real.sinh S • v) :
    form E (C.q + μ • direction z p) p.val =
      -(contactAngle C p - μ) * Real.sinh (dist z p) := by
  have hd : 0 < dist z p := by
    rw [residual_distance c z p v S W C.contact_mem hv hrep]
    exact publicDistance_pos c z hS
  have hqz : form E C.q z.val = 0 := by rw [form_comm]; exact C.q_tangent
  have huz : form E (direction z p) z.val = 0 := by rw [form_comm]; exact direction_tangent z p
  conv_lhs => rw [point_decomposition z p]
  simp only [form_add_left, form_add_right, form_smul_left, form_smul_right,
    hqz, huz, direction_unit z p (dist_pos.mp hd)]
  unfold contactAngle
  ring

theorem RoutingData.candidate_strict (C : RoutingData P W c z μ S)
    (hμ : 0 < μ) (hμmax : μ ≤ 1 / 16) (hS : 0 < S)
    (p : Point E) (v : Ambient E) (hv : ∀ w ∈ W, form E v w = 0)
    (hrep : p.val = Real.cosh S • c.val + Real.sinh S • v)
    (hlat : C.β = 0 ∨ form E C.e v = -Geode.eta μ) :
    form E (C.q + μ • direction z p) p.val < 0 := by
  have hθ := (C.scalar_persistence hμ hμmax hS p v hv hrep hlat).1
  have hd : 0 < dist z p := by
    rw [residual_distance c z p v S W C.contact_mem hv hrep]
    exact publicDistance_pos c z hS
  rw [C.normal_candidate_pairing hS p v hv hrep]
  exact mul_neg_of_neg_of_pos (by linarith) (Real.sinh_pos_iff.mpr hd)

/-- A routed contact preserves a later public ball for the same physical
candidate. The scalar certificate is derived from the actual initial contact. -/
theorem RoutingData.future_ball (C : RoutingData P W c z μ S)
    (hμ : 0 < μ) (hμmax : μ ≤ 1 / 16) (hS : 0 < S)
    (p : Point E) (v : Ambient E) (hv : ∀ w ∈ W, form E v w = 0)
    (hrep : p.val = Real.cosh S • c.val + Real.sinh S • v)
    (hlat : C.β = 0 ∨ form E C.e v = -Geode.eta μ)
    (c' : Point E) (v' : Ambient E) (W' : Submodule ℝ (Ambient E)) {S' : ℝ}
    (hS' : 0 < S') (hSS : S' ≤ S) (hc' : c'.val ∈ W') (hz' : z.val ∈ W')
    (hq' : C.q ∈ W') (hv' : ∀ w ∈ W', form E v' w = 0)
    (hrep' : p.val = Real.cosh S' • c'.val + Real.sinh S' • v') :
    ∀ x : Point E, x.val ∈ W' → dist c' x ≤ publicRadius (Geode.eta μ) S' →
      form E (C.q + μ • direction z p) x.val ≤ 0 := by
  apply future_public_ball_from_persistence c' z p C.q v' W' hμ hμmax hS' hSS hc' hz' hq'
    C.q_tangent C.q_unit hv' hrep' (show contactAngle C p = -form E C.q (direction z p) from rfl)
    (C.angle_le_one hS p v hv hrep)
  intro a ha
  apply (C.scalar_persistence hμ hμmax hS p v hv hrep hlat).2 a
  rwa [residual_distance c z p v S W C.contact_mem hv hrep] at ha

end Geode.Lorentz
