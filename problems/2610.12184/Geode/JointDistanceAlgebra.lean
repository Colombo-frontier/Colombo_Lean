import Geode.Lorentz

/-! The Lorentz Gram inequality underlying joint convexity of hyperbolic
distance along pairs of geodesics. All inputs are actual hyperboloid points
and tangent ambient vectors, and all inequalities follow from the form. -/
namespace Geode.Lorentz

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def jointF (x y : Point E) : ℝ := -form E x.val y.val
def jointG (x y : Point E) (u v : Ambient E) : ℝ :=
  -form E u y.val - form E x.val v
def jointH (x y : Point E) (u v : Ambient E) : ℝ :=
  (form E u u + form E v v) * jointF x y - 2 * form E u v

theorem joint_distance_algebra (x y : Point E) {u v : Ambient E}
    (hu : form E x.val u = 0) (hv : form E y.val v = 0) :
    0 ≤ jointH x y u v ∧
      jointF x y * jointG x y u v ^ 2 ≤ (jointF x y ^ 2 - 1) * jointH x y u v := by
  let f := jointF x y
  have hf : 1 ≤ f := reverse_cauchy x y
  by_cases heq : x = y
  · subst y
    have hsub := tangent_nonneg x (v := u - v) (by simp [hu, hv])
    have hux : form E u x.val = 0 := by rw [form_comm]; exact hu
    have hjh : jointH x x u v = form E (u - v) (u - v) := by
      simp only [jointH, jointF, x.normalized, form_sub_left, form_sub_right, form_comm v u]
      ring
    have hjg : jointG x x u v = 0 := by simp [jointG, hux, hv]
    constructor
    · rw [hjh]; exact hsub
    · simp [hjg, jointF, x.normalized]
  have hf' : 1 < f := by
    apply lt_of_le_of_ne hf
    intro h
    exact heq ((reverse_cauchy_eq_iff x y).mp h.symm)
  let c := f ^ 2 - 1
  have hc : 0 < c := by dsimp [c]; nlinarith
  have hc0 : c ≠ 0 := ne_of_gt hc
  let a := form E u y.val
  let b := form E x.val v
  let r := y.val - f • x.val
  let s := x.val - f • y.val
  let U := u - (a / c) • r
  let V := v - (b / c) • s
  have hxy : form E x.val y.val = -f := by dsimp [f, jointF]; ring
  have hyx : form E y.val x.val = -f := by rw [form_comm]; exact hxy
  have hux : form E u x.val = 0 := by rw [form_comm]; exact hu
  have hvy : form E v y.val = 0 := by rw [form_comm]; exact hv
  have hrx : form E x.val r = 0 := by simp [r, hxy, x.normalized]
  have hry : form E y.val r = c := by simp [r, hyx, y.normalized, c]; ring
  have hsx : form E x.val s = c := by simp [s, hxy, x.normalized, c]; ring
  have hsy : form E y.val s = 0 := by simp [s, hyx, y.normalized]
  have hrr : form E r r = c := by
    change form E (y.val - f • x.val) r = c
    simp only [form_sub_left, form_smul_left, hry, hrx]
    ring
  have hss : form E s s = c := by
    change form E (x.val - f • y.val) s = c
    simp only [form_sub_left, form_smul_left, hsx, hsy]
    ring
  have hrs : form E r s = -f * c := by
    change form E (y.val - f • x.val) s = _
    simp only [form_sub_left, form_smul_left, hsy, hsx]
    ring
  have hur : form E u r = a := by simp [r, hux, a]
  have hvs : form E v s = b := by simp [s, hvy, b, form_comm v x.val]
  have hus : form E u s = -f * a := by simp [s, hux, a]
  have hrv : form E r v = -f * b := by simp [r, hv, b]
  have hUx : form E x.val U = 0 := by simp [U, hu, hrx]
  have hVx : form E x.val V = 0 := by
    simp only [V, form_sub_right, form_smul_right, hsx]
    change b - b / c * c = 0
    field_simp
  have hUU : c * form E U U = c * form E u u - a ^ 2 := by
    simp only [U, form_sub_left, form_sub_right, form_smul_left, form_smul_right,
      hur, hrr, form_comm r u]
    field_simp
    ring
  have hVV : c * form E V V = c * form E v v - b ^ 2 := by
    simp only [V, form_sub_left, form_sub_right, form_smul_left, form_smul_right,
      hvs, hss, form_comm s v]
    field_simp
    ring
  have hUV : c * form E U V = c * form E u v + f * a * b := by
    simp only [U, V, form_sub_left, form_sub_right, form_smul_left, form_smul_right,
      hus, hrv, hrs]
    field_simp
    ring
  have hUn := tangent_nonneg x hUx
  have hVn := tangent_nonneg x hVx
  have hUVn := tangent_nonneg x (v := U - V) (by simp [hUx, hVx])
  simp only [form_sub_left, form_sub_right, form_comm V U] at hUVn
  have hres : 0 ≤ f * (form E U U + form E V V) - 2 * form E U V := by
    nlinarith [mul_nonneg (show 0 ≤ f - 1 by linarith) (add_nonneg hUn hVn)]
  have hidentity : c * (f * (form E U U + form E V V) - 2 * form E U V) =
      c * jointH x y u v - f * jointG x y u v ^ 2 := by
    calc
      _ = f * (c * form E U U + c * form E V V) - 2 * (c * form E U V) := by ring
      _ = _ := by
        rw [hUU, hVV, hUV]
        change f * (c * form E u u - a ^ 2 + (c * form E v v - b ^ 2)) -
          2 * (c * form E u v + f * a * b) =
          c * ((form E u u + form E v v) * f - 2 * form E u v) - f * (-a - b) ^ 2
        ring
  have hmain : f * jointG x y u v ^ 2 ≤ c * jointH x y u v := by
    have hp := mul_nonneg hc.le hres
    rw [hidentity] at hp
    linarith
  have hH : 0 ≤ jointH x y u v := by
    have hp : 0 ≤ c * jointH x y u v :=
      (mul_nonneg (by linarith : 0 ≤ f) (sq_nonneg _)).trans hmain
    exact nonneg_of_mul_nonneg_right hp hc
  exact ⟨hH, hmain⟩

end Geode.Lorentz
