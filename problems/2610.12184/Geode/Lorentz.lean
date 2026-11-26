import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic

/-! The actual Lorentz bilinear form and future unit hyperboloid.
`Point` is a structure, so it does not inherit the ambient product distance. -/
namespace Geode.Lorentz

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]

abbrev Ambient := ℝ × E

def form (x y : Ambient E) : ℝ := -x.1 * y.1 + @inner ℝ E _ x.2 y.2

structure Point where
  val : Ambient E
  normalized : form E val val = -1
  future : 0 < val.1

variable {E}

@[ext] theorem Point.ext {x y : Point E} (h : x.val = y.val) : x = y := by
  cases x; cases y; simp_all

theorem form_comm (x y : Ambient E) : form E x y = form E y x := by
  simp only [form, real_inner_comm x.2 y.2]
  ring

@[simp] theorem form_zero_left (x : Ambient E) : form E 0 x = 0 := by simp [form]
@[simp] theorem form_zero_right (x : Ambient E) : form E x 0 = 0 := by simp [form]

@[simp] theorem form_add_left (x y z : Ambient E) :
    form E (x + y) z = form E x z + form E y z := by
  simp only [form, Prod.fst_add, Prod.snd_add, inner_add_left]
  ring

@[simp] theorem form_add_right (x y z : Ambient E) :
    form E x (y + z) = form E x y + form E x z := by
  rw [form_comm, form_add_left, form_comm y x, form_comm z x]

@[simp] theorem form_smul_left (a : ℝ) (x y : Ambient E) :
    form E (a • x) y = a * form E x y := by
  change -(a * x.1) * y.1 + inner (a • x.2) y.2 = a * (-x.1 * y.1 + inner x.2 y.2)
  rw [real_inner_smul_left]
  ring

@[simp] theorem form_smul_right (a : ℝ) (x y : Ambient E) :
    form E x (a • y) = a * form E x y := by
  rw [form_comm, form_smul_left, form_comm y x]

@[simp] theorem form_neg_left (x y : Ambient E) : form E (-x) y = -form E x y := by
  simpa only [neg_one_smul, neg_one_mul] using form_smul_left (-1) x y

@[simp] theorem form_neg_right (x y : Ambient E) : form E x (-y) = -form E x y := by
  rw [form_comm, form_neg_left, form_comm y x]

@[simp] theorem form_sub_left (x y z : Ambient E) :
    form E (x - y) z = form E x z - form E y z := by simp [sub_eq_add_neg]

@[simp] theorem form_sub_right (x y z : Ambient E) :
    form E x (y - z) = form E x y - form E x z := by simp [sub_eq_add_neg]

theorem form_self (v : Ambient E) : form E v v = ‖v.2‖ ^ 2 - v.1 ^ 2 := by
  rw [form, real_inner_self_eq_norm_sq]
  ring

theorem Point.time_sq (x : Point E) : x.val.1 ^ 2 = 1 + ‖x.val.2‖ ^ 2 := by
  have h := x.normalized
  rw [form_self] at h
  linarith

theorem Point.one_le_time (x : Point E) : 1 ≤ x.val.1 := by
  have := x.future
  nlinarith [x.time_sq, sq_nonneg ‖x.val.2‖]

def origin : Point E where
  val := (1, 0)
  normalized := by simp [form]
  future := by norm_num

theorem inner_sq_le (u v : E) : (@inner ℝ E _ u v) ^ 2 ≤ ‖u‖ ^ 2 * ‖v‖ ^ 2 := by
  have h := abs_real_inner_le_norm u v
  have hsq := mul_self_le_mul_self (abs_nonneg (@inner ℝ E _ u v)) h
  rw [← sq, sq_abs] at hsq
  nlinarith

/-- The Lorentz form restricts to a nonnegative form on the tangent hyperplane. -/
theorem tangent_nonneg (x : Point E) {v : Ambient E} (hv : form E x.val v = 0) :
    0 ≤ form E v v := by
  have hi : @inner ℝ E _ x.val.2 v.2 = x.val.1 * v.1 := by unfold form at hv; linarith
  have hcs := inner_sq_le x.val.2 v.2
  rw [hi, mul_pow, x.time_sq] at hcs
  have ht := x.time_sq
  rw [form_self]
  by_contra hneg
  have hn : ‖v.2‖ ^ 2 < v.1 ^ 2 := sub_neg.mp (lt_of_not_ge hneg)
  have hm := mul_nonneg (sq_nonneg ‖x.val.2‖) (sub_nonneg.mpr hn.le)
  nlinarith [sq_nonneg ‖v.2‖]

theorem tangent_eq_zero_iff (x : Point E) {v : Ambient E} (hv : form E x.val v = 0) :
    form E v v = 0 ↔ v = 0 := by
  constructor
  · intro hz
    have hi : @inner ℝ E _ x.val.2 v.2 = x.val.1 * v.1 := by unfold form at hv; linarith
    have hcs := inner_sq_le x.val.2 v.2
    rw [hi, mul_pow, x.time_sq] at hcs
    rw [form_self] at hz
    have hn : ‖v.2‖ ^ 2 = 0 := by nlinarith
    have hv2 : v.2 = 0 := norm_eq_zero.mp (sq_eq_zero_iff.mp hn)
    have hv1 : v.1 = 0 := by nlinarith
    exact Prod.ext hv1 hv2
  · rintro rfl
    simp

theorem tangent_pos (x : Point E) {v : Ambient E} (hv : form E x.val v = 0)
    (hne : v ≠ 0) : 0 < form E v v :=
  lt_of_le_of_ne (tangent_nonneg x hv) (Ne.symm (mt (tangent_eq_zero_iff x hv).mp hne))

theorem tangent_cauchy_sq (x : Point E) {u v : Ambient E}
    (hu : form E x.val u = 0) (hv : form E x.val v = 0) :
    form E u v ^ 2 ≤ form E u u * form E v v := by
  by_cases hv0 : v = 0
  · simp [hv0]
  have hpos := tangent_pos x hv hv0
  have hw : form E x.val (form E v v • u - form E u v • v) = 0 := by
    simp [hu, hv]
  have hn := tangent_nonneg x hw
  simp only [form_sub_left, form_sub_right, form_smul_left, form_smul_right,
    form_comm v u] at hn
  have hp : 0 ≤ form E v v * (form E u u * form E v v - form E u v ^ 2) := by
    nlinarith only [hn]
  have hdiff := nonneg_of_mul_nonneg_right hp hpos
  linarith

theorem reverse_cauchy (x y : Point E) : 1 ≤ -form E x.val y.val := by
  have hx := x.time_sq
  have hy := y.time_sq
  have hp : 0 < x.val.1 * y.val.1 := mul_pos x.future y.future
  have hn : 0 ≤ ‖x.val.2‖ * ‖y.val.2‖ := mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have hprod : (x.val.1 * y.val.1)^2 =
      (1 + ‖x.val.2‖^2) * (1 + ‖y.val.2‖^2) := by rw [mul_pow, hx, hy]
  have hbound : 1 + ‖x.val.2‖ * ‖y.val.2‖ ≤ x.val.1 * y.val.1 := by
    nlinarith [sq_nonneg (‖x.val.2‖ - ‖y.val.2‖)]
  have hinner := real_inner_le_norm x.val.2 y.val.2
  unfold form
  linarith

theorem reverse_cauchy_eq_iff (x y : Point E) : -form E x.val y.val = 1 ↔ x = y := by
  constructor
  · intro h
    have ht : form E x.val (y.val - x.val) = 0 := by
      rw [form_sub_right, x.normalized]
      linarith
    have hz : form E (y.val - x.val) (y.val - x.val) = 0 := by
      simp only [form_sub_left, form_sub_right, x.normalized, y.normalized,
        form_comm y.val x.val]
      linarith
    have he := (tangent_eq_zero_iff x ht).mp hz
    exact Point.ext (sub_eq_zero.mp he).symm
  · rintro rfl
    rw [x.normalized]
    norm_num

theorem Point.time_eq_sqrt (x : Point E) : x.val.1 = Real.sqrt (1 + ‖x.val.2‖ ^ 2) := by
  rw [← x.time_sq, Real.sqrt_sq_eq_abs, abs_of_pos x.future]

/-- The positive sheet is parametrized by its spatial coordinates. -/
noncomputable def Point.ofSpace (z : E) : Point E where
  val := (Real.sqrt (1 + ‖z‖ ^ 2), z)
  normalized := by
    rw [form_self]
    dsimp
    rw [Real.sq_sqrt (by positivity : 0 ≤ 1 + ‖z‖ ^ 2)]
    ring
  future := Real.sqrt_pos.mpr (by positivity)

@[simp] theorem Point.ofSpace_spatial (z : E) : (Point.ofSpace z).val.2 = z := rfl

@[simp] theorem Point.ofSpace_val (z : E) :
    (Point.ofSpace z).val = (Real.sqrt (1 + ‖z‖ ^ 2), z) := rfl

@[simp] theorem Point.ofSpace_spatial_eq (x : Point E) : Point.ofSpace x.val.2 = x := by
  apply Point.ext
  apply Prod.ext
  · exact x.time_eq_sqrt.symm
  · rfl

noncomputable def spatialEquiv : Point E ≃ E where
  toFun x := x.val.2
  invFun := Point.ofSpace
  left_inv := Point.ofSpace_spatial_eq
  right_inv := Point.ofSpace_spatial

end Geode.Lorentz

