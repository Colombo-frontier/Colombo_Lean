import Geode.Lorentz
import Geode.Hyperbolic
import Mathlib.Topology.MetricSpace.Isometry

/-! Explicit Lorentz boosts. The coordinate formulas are proved directly,
before they are applied to hyperboloid points. -/
namespace Geode.Lorentz

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def coordinateBoost (t : ℝ) (u : E) (v : ℝ × E) : ℝ × E :=
  (t * v.1 + @inner ℝ E _ u v.2,
    v.2 + (v.1 + @inner ℝ E _ u v.2 / (t + 1)) • u)

theorem coordinateBoost_preserves_form (t : ℝ) (u : E) (x y : ℝ × E)
    (ht : t + 1 ≠ 0) (hn : t ^ 2 = 1 + ‖u‖ ^ 2) :
    -(coordinateBoost t u x).1 * (coordinateBoost t u y).1 +
      @inner ℝ E _ (coordinateBoost t u x).2 (coordinateBoost t u y).2 =
        -x.1 * y.1 + @inner ℝ E _ x.2 y.2 := by
  have hn' : ‖u‖ ^ 2 = t ^ 2 - 1 := by linarith
  simp only [coordinateBoost, inner_add_left, inner_add_right,
    real_inner_smul_left, real_inner_smul_right, real_inner_self_eq_norm_sq]
  rw [real_inner_comm u x.2, hn']
  field_simp
  ring

theorem coordinateBoost_origin (t : ℝ) (u : E) :
    coordinateBoost t u (1, 0) = (t, u) := by
  simp [coordinateBoost]

theorem coordinateBoost_future (t : ℝ) (u : E) (v : ℝ × E)
    (ht : 0 < t) (hn : t ^ 2 = 1 + ‖u‖ ^ 2)
    (hv : 0 < v.1) (hvn : v.1 ^ 2 = 1 + ‖v.2‖ ^ 2) :
    0 < (coordinateBoost t u v).1 := by
  have hu : ‖u‖ < t := by nlinarith [norm_nonneg u]
  have hw : ‖v.2‖ < v.1 := by nlinarith [norm_nonneg v.2]
  have hc := (abs_le.mp (abs_real_inner_le_norm u v.2)).1
  have hp : ‖u‖ * ‖v.2‖ < t * v.1 :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_left hw.le (norm_nonneg u))
      (mul_lt_mul_of_pos_right hu hv)
  dsimp [coordinateBoost]
  linarith

theorem coordinate_future_of_negative_pairing (t : ℝ) (u : E) (v : ℝ × E)
    (ht : 0 < t) (hn : t ^ 2 = 1 + ‖u‖ ^ 2)
    (hvn : v.1 ^ 2 = 1 + ‖v.2‖ ^ 2)
    (hpair : -t * v.1 + @inner ℝ E _ u v.2 < 0) : 0 < v.1 := by
  by_contra hneg
  have hv : v.1 ≤ 0 := le_of_not_gt hneg
  have hv' : 0 < -v.1 := by nlinarith [sq_nonneg ‖v.2‖]
  have hu : ‖u‖ < t := by nlinarith [norm_nonneg u]
  have hw : ‖v.2‖ < -v.1 := by nlinarith [norm_nonneg v.2]
  have hc := (abs_le.mp (abs_real_inner_le_norm u v.2)).1
  have hp : ‖u‖ * ‖v.2‖ < t * (-v.1) :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_left hw.le (norm_nonneg u))
      (mul_lt_mul_of_pos_right hu hv')
  linarith

theorem coordinateBoost_inverse (t : ℝ) (u : E) (v : ℝ × E)
    (ht : t + 1 ≠ 0) (hn : t ^ 2 = 1 + ‖u‖ ^ 2) :
    coordinateBoost t (-u) (coordinateBoost t u v) = v := by
  have hn' : ‖u‖ ^ 2 = t ^ 2 - 1 := by linarith
  apply Prod.ext
  · simp only [coordinateBoost, inner_neg_left, inner_add_right,
      real_inner_smul_right, real_inner_self_eq_norm_sq]
    rw [hn']
    field_simp
    ring
  · have hcoef : t * v.1 + @inner ℝ E _ u v.2 +
        -(@inner ℝ E _ u v.2 + (v.1 + @inner ℝ E _ u v.2 / (t + 1)) * ‖u‖ ^ 2) / (t + 1) =
        v.1 + @inner ℝ E _ u v.2 / (t + 1) := by
      rw [hn']
      field_simp
      ring
    simp only [coordinateBoost, inner_neg_left, inner_add_right,
      real_inner_smul_right, real_inner_self_eq_norm_sq]
    rw [← neg_add, hcoef, smul_neg]
    abel

theorem coordinateBoost_add (t : ℝ) (u : E) (x y : ℝ × E) :
    coordinateBoost t u (x + y) = coordinateBoost t u x + coordinateBoost t u y := by
  apply Prod.ext
  · simp only [coordinateBoost, Prod.fst_add, Prod.snd_add, inner_add_right]
    ring
  · simp only [coordinateBoost, Prod.fst_add, Prod.snd_add, inner_add_right]
    have hc : x.1 + y.1 + (@inner ℝ E _ u x.2 + @inner ℝ E _ u y.2) / (t + 1) =
        (x.1 + @inner ℝ E _ u x.2 / (t + 1)) +
          (y.1 + @inner ℝ E _ u y.2 / (t + 1)) := by ring
    rw [hc, add_smul]
    abel

theorem coordinateBoost_smul (t : ℝ) (u : E) (a : ℝ) (v : ℝ × E) :
    coordinateBoost t u (a • v) = a • coordinateBoost t u v := by
  apply Prod.ext
  · change t * (a * v.1) + @inner ℝ E _ u (a • v.2) =
      a * (t * v.1 + @inner ℝ E _ u v.2)
    rw [real_inner_smul_right]
    ring
  · change a • v.2 + (a * v.1 + @inner ℝ E _ u (a • v.2) / (t + 1)) • u =
      a • (v.2 + (v.1 + @inner ℝ E _ u v.2 / (t + 1)) • u)
    rw [real_inner_smul_right]
    have hc : a * v.1 + a * @inner ℝ E _ u v.2 / (t + 1) =
        a * (v.1 + @inner ℝ E _ u v.2 / (t + 1)) := by ring
    rw [hc, mul_smul, smul_add]

noncomputable def coordinateBoostEquiv (t : ℝ) (u : E)
    (ht : t + 1 ≠ 0) (hn : t ^ 2 = 1 + ‖u‖ ^ 2) :
    (ℝ × E) ≃ₗ[ℝ] (ℝ × E) where
  toFun := coordinateBoost t u
  invFun := coordinateBoost t (-u)
  left_inv := fun v => coordinateBoost_inverse t u v ht hn
  right_inv := fun v => by
    simpa using coordinateBoost_inverse t (-u) v ht (by simpa using hn)
  map_add' := coordinateBoost_add t u
  map_smul' := coordinateBoost_smul t u

/-- The explicit Lorentz linear equivalence sending the origin to `p`. -/
noncomputable def boost (p : Point E) : Ambient E ≃ₗ[ℝ] Ambient E :=
  coordinateBoostEquiv p.val.1 p.val.2 (by linarith [p.future]) p.time_sq

@[simp] theorem boost_apply (p : Point E) (v : Ambient E) :
    boost p v = coordinateBoost p.val.1 p.val.2 v := rfl

theorem boost_preserves_form (p : Point E) (x y : Ambient E) :
    form E (boost p x) (boost p y) = form E x y := by
  exact coordinateBoost_preserves_form p.val.1 p.val.2 x y
    (by linarith [p.future]) p.time_sq

@[simp] theorem boost_origin (p : Point E) : boost p (1, 0) = p.val := by
  exact coordinateBoost_origin p.val.1 p.val.2

theorem boost_future (p q : Point E) : 0 < (boost p q.val).1 :=
  coordinateBoost_future p.val.1 p.val.2 q.val p.future p.time_sq q.future q.time_sq

/-- A normalized Lorentz vector pairing negatively with a future point is future. -/
theorem future_of_form_neg (p : Point E) (v : Ambient E)
    (hn : form E v v = -1) (hp : form E p.val v < 0) : 0 < v.1 := by
  apply coordinate_future_of_negative_pairing p.val.1 p.val.2 v p.future p.time_sq
  · rw [form_self] at hn
    linarith
  · exact hp

def pointReflect (p : Point E) : Point E where
  val := (p.val.1, -p.val.2)
  normalized := by simpa [form] using p.normalized
  future := p.future

@[simp] theorem pointReflect_reflect (p : Point E) : pointReflect (pointReflect p) = p := by
  apply Point.ext
  simp [pointReflect]

theorem boost_inverse (p : Point E) (v : Ambient E) :
    boost (pointReflect p) (boost p v) = v :=
  coordinateBoost_inverse p.val.1 p.val.2 v (by linarith [p.future]) p.time_sq

theorem boost_inverse_rev (p : Point E) (v : Ambient E) :
    boost p (boost (pointReflect p) v) = v := by
  simpa using boost_inverse (pointReflect p) v

noncomputable def boostPoint (p q : Point E) : Point E where
  val := boost p q.val
  normalized := by rw [boost_preserves_form, q.normalized]
  future := boost_future p q

@[simp] theorem boostPoint_origin (p : Point E) : boostPoint p origin = p := by
  apply Point.ext
  exact boost_origin p

@[simp] theorem boostPoint_inverse (p q : Point E) :
    boostPoint (pointReflect p) (boostPoint p q) = q := by
  apply Point.ext
  exact boost_inverse p q.val

@[simp] theorem boostPoint_inverse_rev (p q : Point E) :
    boostPoint p (boostPoint (pointReflect p) q) = q := by
  apply Point.ext
  exact boost_inverse_rev p q.val

noncomputable def boostPointEquiv (p : Point E) : Point E ≃ Point E where
  toFun := boostPoint p
  invFun := boostPoint (pointReflect p)
  left_inv := boostPoint_inverse p
  right_inv := boostPoint_inverse_rev p

theorem boost_form_move (p : Point E) (x y : Ambient E) :
    form E (boost p x) y = form E x (boost (pointReflect p) y) := by
  have h := boost_preserves_form p x (boost (pointReflect p) y)
  rwa [boost_inverse_rev] at h

@[simp] theorem boostPoint_dist (p x y : Point E) :
    dist (boostPoint p x) (boostPoint p y) = dist x y := by
  change Geode.arcosh (-form E (boost p x.val) (boost p y.val)) =
    Geode.arcosh (-form E x.val y.val)
  rw [boost_preserves_form]

theorem boostPoint_isometry (p : Point E) : Isometry (boostPoint p) :=
  Isometry.of_dist_eq (boostPoint_dist p)

noncomputable def boostIsometryEquiv (p : Point E) : Point E ≃ᵢ Point E where
  toEquiv := boostPointEquiv p
  isometry_toFun := boostPoint_isometry p

@[simp] theorem boostPoint_center (p : Point E) : boostPoint (pointReflect p) p = origin := by
  have h := boostPoint_inverse p origin
  rwa [boostPoint_origin] at h

theorem dist_via_origin (p y : Point E) :
    dist p y = dist origin (boostPoint (pointReflect p) y) := by
  have h := boostPoint_dist (pointReflect p) p y
  rw [boostPoint_center] at h
  exact h.symm

end Geode.Lorentz

