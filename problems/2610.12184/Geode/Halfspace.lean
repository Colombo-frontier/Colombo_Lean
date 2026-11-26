import Geode.Geodesic
import Mathlib.Topology.MetricSpace.HausdorffDistance

/-! Lorentz halfspaces and actual hyperbolic metric balls. -/
namespace Geode.Lorentz

theorem ball_support_nonpos_iff {A b r : ℝ} (hA : 0 < A) (hr : 0 ≤ r) :
    b * Real.cosh r + Real.sqrt (A + b ^ 2) * Real.sinh r ≤ 0 ↔
      Real.sqrt A * Real.sinh r ≤ -b := by
  have hc := Real.cosh_pos r
  have hs := Real.sinh_nonneg_iff.mpr hr
  have hsA := Real.sqrt_nonneg A
  have hC := Real.sqrt_nonneg (A + b ^ 2)
  have hA' : 0 ≤ A := hA.le
  have hC' : 0 ≤ A + b ^ 2 := by positivity
  have hsprod := mul_nonneg hsA hs
  have hCprod := mul_nonneg hC hs
  constructor
  · intro h
    have hb : b ≤ 0 := by nlinarith
    have hp : Real.sqrt (A + b ^ 2) * Real.sinh r ≤ -b * Real.cosh r := by linarith
    have hsq := (sq_le_sq₀ hCprod (mul_nonneg (neg_nonneg.mpr hb) hc.le)).mpr hp
    rw [mul_pow, mul_pow, Real.sq_sqrt hC', neg_sq, Real.cosh_sq] at hsq
    apply (sq_le_sq₀ hsprod (neg_nonneg.mpr hb)).mp
    rw [mul_pow, Real.sq_sqrt hA', neg_sq]
    nlinarith
  · intro h
    have hb : b ≤ 0 := by linarith
    have hsq := (sq_le_sq₀ hsprod (neg_nonneg.mpr hb)).mpr h
    rw [mul_pow, Real.sq_sqrt hA', neg_sq] at hsq
    have hp : Real.sqrt (A + b ^ 2) * Real.sinh r ≤ -b * Real.cosh r := by
      apply (sq_le_sq₀ hCprod (mul_nonneg (neg_nonneg.mpr hb) hc.le)).mp
      rw [mul_pow, mul_pow, Real.sq_sqrt hC', neg_sq, Real.cosh_sq]
      nlinarith
    linarith

theorem ball_support_neg_iff {A b r : ℝ} (hA : 0 < A) (hr : 0 ≤ r) :
    b * Real.cosh r + Real.sqrt (A + b ^ 2) * Real.sinh r < 0 ↔
      Real.sqrt A * Real.sinh r < -b := by
  have hc := Real.cosh_pos r
  have hs := Real.sinh_nonneg_iff.mpr hr
  have hsprod := mul_nonneg (Real.sqrt_nonneg A) hs
  have hCprod := mul_nonneg (Real.sqrt_nonneg (A + b ^ 2)) hs
  have hC' : 0 ≤ A + b ^ 2 := by positivity
  constructor
  · intro h
    have hb : b < 0 := by nlinarith
    have hp : Real.sqrt (A + b ^ 2) * Real.sinh r < -b * Real.cosh r := by linarith
    have hsq := (sq_lt_sq₀ hCprod (mul_nonneg (neg_nonneg.mpr hb.le) hc.le)).mpr hp
    rw [mul_pow, mul_pow, Real.sq_sqrt hC', neg_sq, Real.cosh_sq] at hsq
    apply (sq_lt_sq₀ hsprod (neg_nonneg.mpr hb.le)).mp
    rw [mul_pow, Real.sq_sqrt hA.le, neg_sq]
    nlinarith
  · intro h
    have hb : b < 0 := by linarith
    have hsq := (sq_lt_sq₀ hsprod (neg_nonneg.mpr hb.le)).mpr h
    rw [mul_pow, Real.sq_sqrt hA.le, neg_sq] at hsq
    have hp : Real.sqrt (A + b ^ 2) * Real.sinh r < -b * Real.cosh r := by
      apply (sq_lt_sq₀ hCprod (mul_nonneg (neg_nonneg.mpr hb.le) hc.le)).mp
      rw [mul_pow, mul_pow, Real.sq_sqrt hC', neg_sq, Real.cosh_sq]
      nlinarith
    linarith

theorem ball_support_eq_zero {A b r : ℝ} (hA : 0 < A) (hr : 0 ≤ r)
    (heq : Real.sqrt A * Real.sinh r = -b) :
    b * Real.cosh r + Real.sqrt (A + b ^ 2) * Real.sinh r = 0 := by
  apply le_antisymm ((ball_support_nonpos_iff hA hr).mpr heq.le)
  by_contra hn
  have hlt := (ball_support_neg_iff hA hr).mp (lt_of_not_ge hn)
  linarith

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def halfspace (h : Ambient E) : Set (Point E) := {x | form E h x.val ≤ 0}

/-- Exact upper support bound at the distance of an arbitrary evaluation point. -/
theorem form_le_ball_support (c x : Point E) (h : Ambient E)
    (hsp : 0 < form E h h) :
    form E h x.val ≤ form E h c.val * Real.cosh (dist c x) +
      Real.sqrt (form E h h + form E h c.val ^ 2) * Real.sinh (dist c x) := by
  have ht := tangent_cauchy_sq c (tangentPart_orthogonal c h)
    (tangentPart_orthogonal c x.val)
  have hcx : form E c.val x.val = -Real.cosh (dist c x) := by rw [cosh_dist]; ring
  have hhc : form E c.val h = form E h c.val := form_comm _ _
  simp only [form_tangentPart, x.normalized, hcx, hhc] at ht
  have hnorm : -1 + (-Real.cosh (dist c x)) * (-Real.cosh (dist c x)) =
      Real.sinh (dist c x) ^ 2 := by nlinarith [Real.cosh_sq_sub_sinh_sq (dist c x)]
  rw [hnorm] at ht
  have hA : 0 ≤ form E h h + form E h c.val ^ 2 := by positivity
  have hs := Real.sinh_nonneg_iff.mpr (dist_nonneg : 0 ≤ dist c x)
  have hp : 0 ≤ Real.sqrt (form E h h + form E h c.val ^ 2) * Real.sinh (dist c x) :=
    mul_nonneg (Real.sqrt_nonneg _) hs
  have hsq : (Real.sqrt (form E h h + form E h c.val ^ 2) * Real.sinh (dist c x)) ^ 2 =
      (form E h h + form E h c.val ^ 2) * Real.sinh (dist c x) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hA]
  nlinarith

/-- The supporting point lies in every linear subspace containing center and normal. -/
theorem ball_support_attained_in (c : Point E) (h : Ambient E)
    (hsp : 0 < form E h h) (r : ℝ) (hr : 0 ≤ r)
    (W : Submodule ℝ (Ambient E)) (hc : c.val ∈ W) (hh : h ∈ W) :
    ∃ x : Point E, x.val ∈ W ∧ dist c x = r ∧
      form E h x.val = form E h c.val * Real.cosh r +
        Real.sqrt (form E h h + form E h c.val ^ 2) * Real.sinh r := by
  let C := Real.sqrt (form E h h + form E h c.val ^ 2)
  have hA : 0 < form E h h + form E h c.val ^ 2 := by positivity
  have hC : 0 < C := Real.sqrt_pos.mpr hA
  have hCsq : C ^ 2 = form E h h + form E h c.val ^ 2 := Real.sq_sqrt hA.le
  have hhc : form E c.val h = form E h c.val := form_comm _ _
  let u : Ambient E := C⁻¹ • tangentPart c h
  have hu : form E c.val u = 0 := by simp [u]
  have hnorm : form E (tangentPart c h) (tangentPart c h) = C ^ 2 := by
    rw [form_tangentPart, hhc, hCsq]
    ring
  have hn : form E u u = 1 := by
    dsimp [u]
    rw [form_smul_left, form_smul_right, hnorm]
    field_simp
    ring
  have hhu : form E h u = C := by
    have hw : form E h (tangentPart c h) = C ^ 2 := by
      simp only [tangentPart, form_add_right, form_smul_right, hhc]
      rw [hCsq]
      ring
    dsimp [u]
    rw [form_smul_right, hw]
    field_simp
    ring
  let x := unitGeodesic c u hu hn r
  have hwm : tangentPart c h ∈ W := W.add_mem hh (W.smul_mem _ hc)
  have hum : u ∈ W := W.smul_mem _ hwm
  refine ⟨x, ?_, ?_, ?_⟩
  · exact W.add_mem (W.smul_mem _ hc) (W.smul_mem _ hum)
  · have hd := unitGeodesic_dist c u hu hn 0 r
    simpa only [unitGeodesic_zero, zero_sub, abs_neg, abs_of_nonneg hr] using hd
  · change form E h (rayVector c u r) = _
    simp only [rayVector, form_add_right, form_smul_right, hhu]
    dsimp [C]
    ring

theorem ball_support_attained (c : Point E) (h : Ambient E)
    (hsp : 0 < form E h h) (r : ℝ) (hr : 0 ≤ r) :
    ∃ x : Point E, dist c x = r ∧
      form E h x.val = form E h c.val * Real.cosh r +
        Real.sqrt (form E h h + form E h c.val ^ 2) * Real.sinh r := by
  obtain ⟨x, _, hx⟩ := ball_support_attained_in c h hsp r hr ⊤ (by trivial) (by trivial)
  exact ⟨x, hx⟩

/-- The intrinsic metric ball in a Lorentz linear section is contained in the
halfspace exactly when the manuscript's signed-distance inequality holds. -/
theorem section_ball_subset_halfspace_iff (c : Point E) (h : Ambient E)
    (hsp : 0 < form E h h) (r : ℝ) (hr : 0 ≤ r)
    (W : Submodule ℝ (Ambient E)) (hc : c.val ∈ W) (hh : h ∈ W) :
    (∀ x : Point E, x.val ∈ W → dist c x ≤ r → form E h x.val ≤ 0) ↔
      Real.sqrt (form E h h) * Real.sinh r ≤ -form E h c.val := by
  constructor
  · intro hcontain
    obtain ⟨x, hxW, hdist, hform⟩ := ball_support_attained_in c h hsp r hr W hc hh
    have hx := hcontain x hxW hdist.le
    rw [hform] at hx
    exact (ball_support_nonpos_iff hsp hr).mp hx
  · intro hbound x _ hdist
    have hs := Real.sinh_le_sinh.mpr hdist
    have hmul := mul_le_mul_of_nonneg_left hs (Real.sqrt_nonneg (form E h h))
    have hb := (ball_support_nonpos_iff hsp (dist_nonneg : 0 ≤ dist c x)).mpr
      (hmul.trans hbound)
    exact (form_le_ball_support c x h hsp).trans hb

theorem closedBall_subset_halfspace_iff (c : Point E) (h : Ambient E)
    (hsp : 0 < form E h h) (r : ℝ) (hr : 0 ≤ r) :
    Metric.closedBall c r ⊆ halfspace h ↔
      Real.sqrt (form E h h) * Real.sinh r ≤ -form E h c.val := by
  have h := section_ball_subset_halfspace_iff c h hsp r hr ⊤ (by trivial) (by trivial)
  simpa only [Set.subset_def, Metric.mem_closedBall, halfspace, Set.mem_setOf_eq,
    Submodule.mem_top, true_implies, dist_comm] using h

/-- The boundary distance is attained in every section containing center and normal. -/
theorem halfspace_boundary_nearest (c : Point E) (h : Ambient E)
    (hsp : 0 < form E h h) (hinside : form E h c.val ≤ 0)
    (W : Submodule ℝ (Ambient E)) (hc : c.val ∈ W) (hh : h ∈ W) :
    ∃ z : Point E, z.val ∈ W ∧ form E h z.val = 0 ∧
      dist c z = Real.arsinh (-form E h c.val / Real.sqrt (form E h h)) ∧
      ∀ y : Point E, form E h y.val = 0 → dist c z ≤ dist c y := by
  let r := Real.arsinh (-form E h c.val / Real.sqrt (form E h h))
  have hα : 0 < Real.sqrt (form E h h) := Real.sqrt_pos.mpr hsp
  have hr : 0 ≤ r := Real.arsinh_nonneg_iff.mpr (div_nonneg (neg_nonneg.mpr hinside) hα.le)
  have heq : Real.sqrt (form E h h) * Real.sinh r = -form E h c.val := by
    dsimp [r]
    rw [Real.sinh_arsinh]
    field_simp
    ring
  obtain ⟨z, hzW, hdist, hform⟩ := ball_support_attained_in c h hsp r hr W hc hh
  have hz : form E h z.val = 0 := by
    rw [hform]
    exact ball_support_eq_zero hsp hr heq
  refine ⟨z, hzW, hz, hdist, ?_⟩
  intro y hy
  rw [hdist]
  apply le_of_not_gt
  intro hd
  have hs := Real.sinh_lt_sinh.mpr hd
  have hbound : Real.sqrt (form E h h) * Real.sinh (dist c y) < -form E h c.val := by
    rw [← heq]
    exact mul_lt_mul_of_pos_left hs hα
  have hnegative := (ball_support_neg_iff hsp (dist_nonneg : 0 ≤ dist c y)).mpr hbound
  have hu := form_le_ball_support c y h hsp
  rw [hy] at hu
  linarith

theorem halfspace_boundary_infDist (c : Point E) (h : Ambient E)
    (hsp : 0 < form E h h) (hinside : form E h c.val ≤ 0)
    (W : Submodule ℝ (Ambient E)) (hc : c.val ∈ W) (hh : h ∈ W) :
    Metric.infDist c {x : Point E | x.val ∈ W ∧ form E h x.val = 0} =
      Real.arsinh (-form E h c.val / Real.sqrt (form E h h)) := by
  obtain ⟨z, hzW, hz, hd, hmin⟩ := halfspace_boundary_nearest c h hsp hinside W hc hh
  rw [← hd]
  have hzmem : z ∈ {x : Point E | x.val ∈ W ∧ form E h x.val = 0} := ⟨hzW, hz⟩
  apply le_antisymm (Metric.infDist_le_dist_of_mem hzmem)
  apply (Metric.le_infDist ⟨z, hzmem⟩).mpr
  intro y hy
  exact hmin y hy.2

/-- Lorentz linear sections contain the entire geodesic between their points. -/
theorem section_segment_mem (W : Submodule ℝ (Ambient E)) (x y : Point E)
    (hx : x.val ∈ W) (hy : y.val ∈ W) (t : ℝ) : (segment x y t).val ∈ W := by
  unfold segment
  split_ifs with hxy
  · exact hx
  · have hu : direction x y ∈ W :=
      W.smul_mem _ (W.sub_mem hy (W.smul_mem _ hx))
    exact W.add_mem (W.smul_mem _ hx) (W.smul_mem _ hu)

@[simp] theorem halfspace_zero : halfspace (0 : Ambient E) = Set.univ := by
  ext x
  simp [halfspace]

end Geode.Lorentz
