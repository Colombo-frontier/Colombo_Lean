import Geode.Geodesic
import Mathlib.Analysis.SpecialFunctions.Arsinh

/-! Actual residual candidate spheres and their exact hyperbolic recentering. -/
namespace Geode.Lorentz

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def IsResidual (W : Submodule ℝ (Ambient E)) (v : Ambient E) : Prop :=
  ∀ w ∈ W, form E v w = 0

def candidateSet (W : Submodule ℝ (Ambient E)) (c : Point E) (S : ℝ) : Set (Point E) :=
  {p | ∃ v : Ambient E, IsResidual W v ∧ form E v v = 1 ∧
    p.val = Real.cosh S • c.val + Real.sinh S • v}

theorem residual_tangent {W : Submodule ℝ (Ambient E)} {c : Point E} {v : Ambient E}
    (hc : c.val ∈ W) (hv : IsResidual W v) : form E c.val v = 0 := by
  rw [form_comm]
  exact hv c.val hc

theorem candidate_distance {W : Submodule ℝ (Ambient E)} {c p : Point E} {S : ℝ}
    (hc : c.val ∈ W) (hS : 0 ≤ S) (hp : p ∈ candidateSet W c S) : dist c p = S := by
  obtain ⟨v, hv, _, hpv⟩ := hp
  have hcos : Real.cosh (dist c p) = Real.cosh S := by
    rw [cosh_dist, hpv, form_add_right, form_smul_right, form_smul_right,
      c.normalized, residual_tangent hc hv]
    ring
  exact Real.cosh_strictMonoOn.injOn dist_nonneg hS hcos

theorem candidate_from_residual {W : Submodule ℝ (Ambient E)} {c : Point E}
    {v : Ambient E} (hc : c.val ∈ W) (hv : IsResidual W v) (hv1 : form E v v = 1)
    (S : ℝ) : unitGeodesic c v (residual_tangent hc hv) hv1 S ∈ candidateSet W c S :=
  ⟨v, hv, hv1, rfl⟩

noncomputable def latitudeContraction (η : ℝ) : ℝ := Real.sqrt (1 - η ^ 2)

noncomputable def updatedRadius (η S : ℝ) : ℝ :=
  Real.arsinh (latitudeContraction η * Real.sinh S)

@[simp] theorem sinh_updatedRadius (η S : ℝ) :
    Real.sinh (updatedRadius η S) = latitudeContraction η * Real.sinh S :=
  Real.sinh_arsinh _

theorem latitudeContraction_pos {η : ℝ} (hη : η ^ 2 < 1) : 0 < latitudeContraction η :=
  Real.sqrt_pos.mpr (by linarith)

theorem updatedRadius_pos {η S : ℝ} (hη : η ^ 2 < 1) (hS : 0 < S) :
    0 < updatedRadius η S :=
  Real.arsinh_pos_iff.mpr (mul_pos (latitudeContraction_pos hη) (Real.sinh_pos_iff.mpr hS))

theorem cosh_updatedRadius_sq {η : ℝ} (hη : η ^ 2 ≤ 1) (S : ℝ) :
    Real.cosh (updatedRadius η S) ^ 2 = Real.cosh S ^ 2 - η ^ 2 * Real.sinh S ^ 2 := by
  have hs : latitudeContraction η ^ 2 = 1 - η ^ 2 := Real.sq_sqrt (by linarith)
  rw [Real.cosh_sq, sinh_updatedRadius, mul_pow, hs]
  nlinarith [Real.cosh_sq_sub_sinh_sq S]

noncomputable def recenteredVector (c : Point E) (e : Ambient E) (η S : ℝ) : Ambient E :=
  (Real.cosh (updatedRadius η S))⁻¹ •
    (Real.cosh S • c.val - (η * Real.sinh S) • e)

theorem recenteredVector_normalized (c : Point E) (e : Ambient E)
    (he : form E c.val e = 0) (he1 : form E e e = 1) {η : ℝ} (hη : η ^ 2 ≤ 1) (S : ℝ) :
    form E (recenteredVector c e η S) (recenteredVector c e η S) = -1 := by
  have hec : form E e c.val = 0 := by rw [form_comm]; exact he
  have hnorm : form E (Real.cosh S • c.val - (η * Real.sinh S) • e)
      (Real.cosh S • c.val - (η * Real.sinh S) • e) =
        -Real.cosh (updatedRadius η S) ^ 2 := by
    simp only [form_sub_left, form_sub_right, form_smul_left, form_smul_right,
      c.normalized, he, hec, he1]
    nlinarith [cosh_updatedRadius_sq hη S]
  simp only [recenteredVector, form_smul_left, form_smul_right, hnorm]
  field_simp only [(Real.cosh_pos (updatedRadius η S)).ne']
  ring

theorem recenteredVector_future (c : Point E) (e : Ambient E)
    (he : form E c.val e = 0) (he1 : form E e e = 1) {η : ℝ} (hη : η ^ 2 ≤ 1) (S : ℝ) :
    0 < (recenteredVector c e η S).1 := by
  apply future_of_normalized c (recenteredVector_normalized c e he he1 hη S)
  simp only [recenteredVector, form_smul_right, form_sub_right, form_smul_right,
    c.normalized, he, mul_zero, sub_zero, mul_neg_one]
  exact mul_neg_of_pos_of_neg (inv_pos.mpr (Real.cosh_pos _)) (neg_neg_of_pos (Real.cosh_pos _))

noncomputable def recenteredCenter (c : Point E) (e : Ambient E)
    (he : form E c.val e = 0) (he1 : form E e e = 1) (η S : ℝ) (hη : η ^ 2 ≤ 1) : Point E where
  val := recenteredVector c e η S
  normalized := recenteredVector_normalized c e he he1 hη S
  future := recenteredVector_future c e he he1 hη S

theorem recenteredCenter_identity (c : Point E) (e : Ambient E)
    (he : form E c.val e = 0) (he1 : form E e e = 1) (η S : ℝ) (hη : η ^ 2 ≤ 1) :
    Real.cosh (updatedRadius η S) • (recenteredCenter c e he he1 η S hη).val =
      Real.cosh S • c.val - (η * Real.sinh S) • e := by
  change Real.cosh (updatedRadius η S) • recenteredVector c e η S = _
  rw [recenteredVector, smul_smul, mul_inv_cancel₀ (Real.cosh_pos _).ne', one_smul]

theorem physical_candidate_recentered (c : Point E) (e v w : Ambient E)
    (he : form E c.val e = 0) (he1 : form E e e = 1) (η S : ℝ) (hη : η ^ 2 ≤ 1)
    (hv : v = (-η) • e + latitudeContraction η • w) :
    Real.cosh S • c.val + Real.sinh S • v =
      Real.cosh (updatedRadius η S) • (recenteredCenter c e he he1 η S hη).val +
        Real.sinh (updatedRadius η S) • w := by
  rw [recenteredCenter_identity, sinh_updatedRadius, hv]
  module

end Geode.Lorentz
