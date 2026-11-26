import Geode.CarrierOracle

/-! Actual first-order optimality of public radial-distance contacts.
The normal is derived from minimum contact cost along geodesic segments. -/
namespace Geode.Lorentz

open Set Filter
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem nonneg_derivative_of_right_min {C : ℝ → ℝ} {d : ℝ}
    (hd : HasDerivAt C d 0) (hmin : ∀ t, 0 ≤ t → t ≤ 1 → C 0 ≤ C t) : 0 ≤ d := by
  have ht : Tendsto (slope C 0) (𝓝[>] (0 : ℝ)) (𝓝 d) :=
    (hasDerivWithinAt_iff_tendsto_slope' (not_mem_Ioi_self : (0 : ℝ) ∉ Ioi 0)).mp
      hd.hasDerivWithinAt
  apply ge_of_tendsto ht
  filter_upwards [self_mem_nhdsWithin,
    (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds]
    with t ht0 ht1
  have hp : 0 < t := ht0
  rw [slope_def_field, sub_zero]
  exact div_nonneg (sub_nonneg.mpr (hmin t hp.le ht1.le)) hp.le

theorem radial_contact_normal {P : Set (Point E)} {z y p : Point E} {μ : ℝ}
    (hP : GConvex P) (hz : z ∈ P) (hyz : y ≠ z) (hpz : p ≠ z)
    (hmin : ∀ w ∈ P, μ * dist z p + dist y z ≤ μ * dist w p + dist y w) :
    NormalTo P z (direction z y + μ • direction z p) := by
  constructor
  · simp [direction_tangent]
  · intro x hx
    let C : ℝ → ℝ := fun t => μ * dist p (segment z x t) + dist y (segment z x t)
    have hp := hasDerivAt_distance_segment p z x hpz
    have hy := hasDerivAt_distance_segment y z x hyz
    have hd : HasDerivAt C
        (-form E (direction z y + μ • direction z p) (logMap z x)) 0 := by
      convert (hp.const_mul μ).add hy using 1
      simp only [form_add_left, form_smul_left]
      ring
    have hcost : ∀ t, 0 ≤ t → t ≤ 1 → C 0 ≤ C t := by
      intro t ht ht1
      have hm := hmin (segment z x t) (hP z hz x hx t ht ht1)
      simpa only [C, segment_zero, dist_comm p z, dist_comm p (segment z x t)] using hm
    have hn := nonneg_derivative_of_right_min hd hcost
    linarith

/-- If a public component has the same pairings on public logarithm vectors,
the exact full normal induces the corresponding public normal inequality. -/
theorem radial_contact_public_normal {P : Set (Point E)} {z y p : Point E}
    {μ : ℝ} {qV uV : Ambient E}
    (hP : GConvex P) (hz : z ∈ P) (hyz : y ≠ z) (hpz : p ≠ z)
    (hmin : ∀ w ∈ P, μ * dist z p + dist y z ≤ μ * dist w p + dist y w)
    (hqV : form E z.val qV = 0) (huV : form E z.val uV = 0)
    (hqpair : ∀ x ∈ P, form E qV (logMap z x) = form E (direction z y) (logMap z x))
    (hupair : ∀ x ∈ P, form E uV (logMap z x) = form E (direction z p) (logMap z x)) :
    NormalTo P z (qV + μ • uV) := by
  have hn := radial_contact_normal hP hz hyz hpz hmin
  constructor
  · simp [hqV, huV]
  · intro x hx
    have hs := hn.2 x hx
    simp only [form_add_left, form_smul_left] at hs ⊢
    rw [hqpair x hx, hupair x hx]
    exact hs

theorem radial_contact_normal_exists {P : Set (Point E)} {y p : Point E} {μ : ℝ}
    (hPc : IsCompact P) (hP : GConvex P) (hne : P.Nonempty) (hμ : 0 ≤ μ)
    (hy : y ∉ P) (hp : p ∉ P) :
    ∃ z ∈ P, NormalTo P z (direction z y + μ • direction z p) ∧
      ∀ w ∈ P, μ * dist z p + dist y z ≤ μ * dist w p + dist y w := by
  obtain ⟨z, hz, hv⟩ := Geode.carrierValue_attained (p := p) (y := y) (μ := μ) hPc hne
  have hmin : ∀ w ∈ P, μ * dist z p + dist y z ≤ μ * dist w p + dist y w := by
    intro w hw
    rw [← hv]
    exact Geode.carrierValue_le_contact hμ hw
  have hyz : y ≠ z := fun h => hy (h.symm ▸ hz)
  have hpz : p ≠ z := fun h => hp (h.symm ▸ hz)
  exact ⟨z, hz, radial_contact_normal hP hz hyz hpz hmin, hmin⟩

/-- The manuscript's on-domain query direction is an actual unit tangent
vector when the public and residual components are Lorentz-orthogonal. -/
theorem on_domain_contact_direction {z : Point E} {u e : Ambient E} {μ : ℝ}
    (hu : form E z.val u = 0) (he : form E z.val e = 0)
    (he1 : form E e e = 1) (hue : form E u e = 0)
    (hu1 : form E u u ≤ 1) (hμ : 0 ≤ μ) (hμ1 : μ < 1) :
    let β := Real.sqrt (1 - μ ^ 2 * form E u u)
    let q := (-μ) • u + β • e
    0 < β ∧ form E z.val q = 0 ∧ form E q q = 1 := by
  have hun := tangent_nonneg z hu
  have hrad : 0 < 1 - μ ^ 2 * form E u u := by
    nlinarith [mul_nonneg (sq_nonneg μ) (show 0 ≤ 1 - form E u u by linarith)]
  have hbeta := Real.sq_sqrt hrad.le
  have heu : form E e u = 0 := by rw [form_comm]; exact hue
  dsimp only
  refine ⟨Real.sqrt_pos.mpr hrad, ?_, ?_⟩
  · simp [hu, he]
  · simp only [form_add_left, form_add_right, form_smul_left, form_smul_right,
      hue, heu, he1]
    nlinarith

end Geode.Lorentz
