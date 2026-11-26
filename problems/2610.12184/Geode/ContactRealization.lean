import Geode.JointSupport
import Geode.MetricCarrier

/-! Exact preservation of a carrier contact, with actual Riemannian
subgradients and separation of every exterior query from the carrier. -/
namespace Geode.Lorentz

open Set

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem dist_unitGeodesic_pos (z : Point E) (q : Ambient E)
    (hq : form E z.val q = 0) (hqu : form E q q = 1) {ℓ : ℝ} (hℓ : 0 < ℓ) :
    dist z (unitGeodesic z q hq hqu ℓ) = ℓ := by
  simpa only [unitGeodesic_zero, zero_sub, abs_neg, abs_of_pos hℓ]
    using unitGeodesic_dist z q hq hqu 0 ℓ

theorem direction_unitGeodesic_pos (z : Point E) (q : Ambient E)
    (hq : form E z.val q = 0) (hqu : form E q q = 1) {ℓ : ℝ} (hℓ : 0 < ℓ) :
    direction z (unitGeodesic z q hq hqu ℓ) = q := by
  have hs : Real.sinh ℓ ≠ 0 := (Real.sinh_pos_iff.mpr hℓ).ne'
  unfold direction
  rw [dist_unitGeodesic_pos z q hq hqu hℓ]
  change (Real.sinh ℓ)⁻¹ •
    (Real.cosh ℓ • z.val + Real.sinh ℓ • q - Real.cosh ℓ • z.val) = q
  rw [show Real.cosh ℓ • z.val + Real.sinh ℓ • q - Real.cosh ℓ • z.val =
    Real.sinh ℓ • q by abel]
  rw [smul_smul, inv_mul_cancel₀ hs, one_smul]

theorem carrier_radial_source_support_of_normal {K : Set (Point E)} {z p : Point E}
    {q : Ambient E} {μ : ℝ} (hμ : 0 ≤ μ) (hzp : z ≠ p)
    (hn : NormalTo K z (q + μ • direction z p)) {x : Point E} (hx : x ∈ K) :
    μ * dist z p + form E q (logMap z x) ≤ μ * dist x p := by
  have hs := distance_source_support z p x hzp
  have hnorm := hn.2 x hx
  simp only [form_add_left, form_smul_left] at hnorm
  nlinarith [mul_le_mul_of_nonneg_left hs hμ]

/-- A single shared carrier supplies global support at any exterior contact. -/
theorem carrier_external_contact_bound {K : Set (Point E)} {z p y : Point E}
    {q : Ambient E} {μ : ℝ} (hz : z ∈ K) (hμ : 0 ≤ μ) (hzp : z ≠ p)
    (hyz : y ≠ z) (hdir : direction z y = q)
    (hn : NormalTo K z (q + μ • direction z p)) (w : Point E) :
    μ * dist z p + dist y z - form E (direction y z) (logMap y w) ≤
      Geode.carrierValue K p μ w := by
  apply le_csInf (Set.Nonempty.image (f := fun x : Point E => μ * dist x p + dist w x) ⟨z, hz⟩)
  rintro _ ⟨x, hx, rfl⟩
  dsimp only
  have hs := carrier_radial_source_support_of_normal hμ hzp hn hx
  have hd := joint_distance_support y z w x hyz
  rw [hdir] at hd
  linarith

theorem carrier_external_contact {K : Set (Point E)} {z p y : Point E}
    {q : Ambient E} {μ : ℝ} (hz : z ∈ K) (hμ : 0 ≤ μ) (hzp : z ≠ p)
    (hyz : y ≠ z) (hdir : direction z y = q)
    (hn : NormalTo K z (q + μ • direction z p)) :
    Geode.carrierValue K p μ y = μ * dist z p + dist y z ∧
      IsSubgradient (Geode.carrierValue K p μ) y (-direction y z) := by
  have hvalue : Geode.carrierValue K p μ y = μ * dist z p + dist y z := by
    apply le_antisymm (Geode.carrierValue_le_contact hμ hz)
    simpa only [logMap_self, form_zero_right, sub_zero] using
      carrier_external_contact_bound hz hμ hzp hyz hdir hn y
  refine ⟨hvalue, ?_⟩
  constructor
  · simp [direction_tangent]
  · intro w
    rw [hvalue, form_neg_left]
    exact carrier_external_contact_bound hz hμ hzp hyz hdir hn w

theorem unit_tangent_log_support {z w x : Point E} {q : Ambient E}
    (hq : form E z.val q = 0) (hqu : form E q q = 1) :
    form E q (logMap z w) ≤ form E q (logMap z x) + dist w x := by
  have hcs := tangent_cauchy_sq z hq
    (v := logMap z w - logMap z x) (by simp)
  rw [hqu, one_mul] at hcs
  have hlog := logMap_contraction_sq z w x
  have hnorm : form E q (logMap z w - logMap z x) ≤ dist w x := by
    nlinarith [dist_nonneg (x := w) (y := x)]
  rw [form_sub_right] at hnorm
  linarith

theorem carrier_internal_contact {K : Set (Point E)} {z p : Point E}
    {q : Ambient E} {μ : ℝ} (hz : z ∈ K) (hμ : 0 ≤ μ) (hμ1 : μ ≤ 1)
    (hzp : z ≠ p) (hq : form E z.val q = 0) (hqu : form E q q = 1)
    (hn : NormalTo K z (q + μ • direction z p)) :
    Geode.carrierValue K p μ z = μ * dist z p ∧
      IsSubgradient (Geode.carrierValue K p μ) z q := by
  have hvalue := Geode.carrierValue_eq_source (p := p) hz hμ hμ1
  refine ⟨hvalue, hq, ?_⟩
  intro w
  rw [hvalue]
  apply le_csInf (Set.Nonempty.image (f := fun x : Point E => μ * dist x p + dist w x) ⟨z, hz⟩)
  rintro _ ⟨x, hx, rfl⟩
  dsimp only
  have hs := carrier_radial_source_support_of_normal hμ hzp hn hx
  have hd := unit_tangent_log_support (w := w) (x := x) hq hqu
  linarith

theorem external_contact_not_mem {K : Set (Point E)} {z p : Point E}
    {q : Ambient E} {μ ℓ : ℝ} (hμ : 0 ≤ μ) (hμ1 : μ < 1) (hzp : z ≠ p)
    (hq : form E z.val q = 0) (hqu : form E q q = 1) (hℓ : 0 < ℓ)
    (hn : NormalTo K z (q + μ • direction z p)) :
    unitGeodesic z q hq hqu ℓ ∉ K := by
  have hcs := tangent_cauchy_sq z hq (direction_tangent z p)
  rw [hqu, direction_unit z p hzp, one_mul] at hcs
  have hlo : -1 ≤ form E q (direction z p) := by nlinarith
  have hpos : 0 < 1 + μ * form E q (direction z p) := by
    nlinarith [mul_nonneg hμ (show 0 ≤ form E q (direction z p) + 1 by linarith)]
  have hnz : form E (q + μ • direction z p) z.val = 0 := by
    rw [form_comm]
    exact hn.1
  have hpair : form E (q + μ • direction z p) (unitGeodesic z q hq hqu ℓ).val =
      Real.sinh ℓ * (1 + μ * form E q (direction z p)) := by
    change form E (q + μ • direction z p) (Real.cosh ℓ • z.val + Real.sinh ℓ • q) = _
    simp only [form_add_right, form_smul_right, hnz, mul_zero, zero_add,
      form_add_left, form_smul_left, hqu, form_comm (direction z p) q]
  intro hy
  have hle := ((normalTo_iff_lorentz_halfspace).mp hn).2 _ hy
  rw [hpair] at hle
  exact (not_lt_of_ge hle) (mul_pos (Real.sinh_pos_iff.mpr hℓ) hpos)

/-- The manuscript's contact realization, including the exact exterior value,
full selected subgradients at exterior/interior queries, and exterior separation. -/
theorem contact_realization {K : Set (Point E)} {z p : Point E}
    {q : Ambient E} {μ ℓ : ℝ} (hz : z ∈ K) (hμ : 0 < μ) (hμ1 : μ < 1)
    (hzp : z ≠ p) (hq : form E z.val q = 0) (hqu : form E q q = 1) (hℓ : 0 < ℓ)
    (hn : NormalTo K z (q + μ • direction z p)) :
    let y := unitGeodesic z q hq hqu ℓ
    Geode.carrierValue K p μ y = μ * dist z p + ℓ ∧
    IsSubgradient (Geode.carrierValue K p μ) y (-direction y z) ∧
    Geode.carrierValue K p μ z = μ * dist z p ∧
    IsSubgradient (Geode.carrierValue K p μ) z q ∧ y ∉ K := by
  dsimp only
  let y := unitGeodesic z q hq hqu ℓ
  have hd : dist y z = ℓ := by
    rw [dist_comm]
    exact dist_unitGeodesic_pos z q hq hqu hℓ
  have hyz : y ≠ z := dist_pos.mp (by rw [hd]; exact hℓ)
  have hdir : direction z y = q := direction_unitGeodesic_pos z q hq hqu hℓ
  obtain ⟨hval, hsub⟩ := carrier_external_contact hz hμ.le hzp hyz hdir hn
  obtain ⟨hvalz, hsubz⟩ := carrier_internal_contact hz hμ.le hμ1.le hzp hq hqu hn
  exact ⟨by simpa only [hd] using hval, hsub, hvalz, hsubz,
    external_contact_not_mem hμ.le hμ1 hzp hq hqu hℓ hn⟩

end Geode.Lorentz

