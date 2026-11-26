import Geode.OracleModel
import Geode.StrictLocalization
import Geode.ExpMap

/-! The concrete hyperboloid with its metric divided by `k²`. Its distances
are the normalized distances divided by `k`; tangent vectors retain their
coordinates, while the Riemannian pairing is divided by `k²`. -/
namespace Geode.Rescaled

open Geode.Lorentz

@[ext] structure Point (k : ℝ) (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] where
  normalized : Lorentz.Point E

variable {k : ℝ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def pointEquiv : Point k E ≃ Lorentz.Point E where
  toFun := Point.normalized
  invFun := Point.mk
  left_inv := fun x => by cases x; rfl
  right_inv := fun _ => rfl

variable [Fact (0 < k)]

theorem scale_pos : 0 < k := Fact.out

noncomputable instance : MetricSpace (Point k E) where
  dist x y := dist x.normalized y.normalized / k
  dist_self x := by simp
  dist_comm x y := by rw [dist_comm]
  dist_triangle x y z := by
    simpa only [add_div] using div_le_div_of_nonneg_right
      (dist_triangle x.normalized y.normalized z.normalized) (scale_pos (k := k)).le
  eq_of_dist_eq_zero := by
    intro x y h
    apply Point.ext
    exact dist_eq_zero.mp ((div_eq_zero_iff).mp h |>.resolve_right (scale_pos (k := k)).ne')

@[simp] theorem dist_eq (x y : Point k E) :
    dist x y = dist x.normalized y.normalized / k := rfl

theorem normalized_dist (x y : Point k E) :
    dist x.normalized y.normalized = k * dist x y := by
  rw [dist_eq, ← mul_div_assoc, mul_div_cancel_left₀ _ (scale_pos (k := k)).ne']

noncomputable def tangentInner (u v : Ambient E) : ℝ := form E u v / k ^ 2

theorem tangentInner_comm (u v : Ambient E) :
    tangentInner (k := k) u v = tangentInner (k := k) v u := by
  simp only [tangentInner, form_comm u v]

theorem tangentInner_add_left (u v w : Ambient E) :
    tangentInner (k := k) (u + v) w = tangentInner (k := k) u w + tangentInner (k := k) v w := by
  simp only [tangentInner, form_add_left, add_div]

theorem tangentInner_smul_left (a : ℝ) (u v : Ambient E) :
    tangentInner (k := k) (a • u) v = a * tangentInner (k := k) u v := by
  simp only [tangentInner, form_smul_left, mul_div_assoc]

theorem normalized_tensor (u v : Ambient E) :
    k ^ 2 * tangentInner (k := k) u v = form E u v := by
  rw [tangentInner, ← mul_div_assoc, mul_div_cancel_left₀ _ (pow_ne_zero 2 scale_pos.ne')]

theorem tangentInner_pos (x : Point k E) {v : Ambient E}
    (hv : form E x.normalized.val v = 0) (hne : v ≠ 0) :
    0 < tangentInner (k := k) v v :=
  div_pos (tangent_pos x.normalized hv hne) (sq_pos_of_pos scale_pos)

noncomputable def tangentNorm (v : Ambient E) : ℝ := Lorentz.tangentNorm v / k

theorem tangentNorm_sq (x : Point k E) {v : Ambient E}
    (hv : form E x.normalized.val v = 0) :
    tangentNorm (k := k) v ^ 2 = tangentInner (k := k) v v := by
  rw [tangentNorm, div_pow, Lorentz.tangentNorm, Real.sq_sqrt (tangent_nonneg _ hv)]
  rfl

noncomputable def logMap (x y : Point k E) : Ambient E :=
  Lorentz.logMap x.normalized y.normalized

noncomputable def expMap (x : Point k E) (v : Ambient E)
    (hv : form E x.normalized.val v = 0) : Point k E :=
  ⟨Lorentz.expMap x.normalized v hv⟩

theorem logMap_expMap (x : Point k E) (v : Ambient E)
    (hv : form E x.normalized.val v = 0) : logMap x (expMap x v hv) = v :=
  Lorentz.logMap_expMap x.normalized v hv

theorem dist_expMap (x : Point k E) (v : Ambient E)
    (hv : form E x.normalized.val v = 0) :
    dist x (expMap x v hv) = tangentNorm (k := k) v := by
  change dist x.normalized (Lorentz.expMap x.normalized v hv) / k = _
  rw [Lorentz.dist_expMap]
  rfl

@[simp] theorem tangentNorm_logMap (x y : Point k E) :
    tangentNorm (k := k) (logMap x y) = dist x y := by
  exact congrArg (fun a : ℝ => a / k) (Lorentz.tangentNorm_logMap x.normalized y.normalized)

noncomputable def segment (x y : Point k E) (t : ℝ) : Point k E :=
  ⟨Lorentz.segment x.normalized y.normalized t⟩

@[simp] theorem segment_zero (x y : Point k E) : segment x y 0 = x := by
  apply Point.ext
  exact Lorentz.segment_zero x.normalized y.normalized

@[simp] theorem segment_one (x y : Point k E) : segment x y 1 = y := by
  apply Point.ext
  exact Lorentz.segment_one x.normalized y.normalized

theorem segment_dist (x y : Point k E) (s t : ℝ) :
    dist (segment x y s) (segment x y t) = |s - t| * dist x y := by
  change dist (Lorentz.segment x.normalized y.normalized s)
    (Lorentz.segment x.normalized y.normalized t) / k = _
  rw [Lorentz.segment_dist, dist_eq]
  ring

def GConvexFunction (f : Point k E → ℝ) : Prop :=
  ∀ x y : Point k E, ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
    f (segment x y t) ≤ (1 - t) * f x + t * f y

def GConvex (S : Set (Point k E)) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, ∀ t : ℝ, 0 ≤ t → t ≤ 1 → segment x y t ∈ S

theorem gconvex_set_iff (S : Set (Point k E)) :
    GConvex S ↔ Lorentz.GConvex {x : Lorentz.Point E | (⟨x⟩ : Point k E) ∈ S} := by
  constructor
  · intro h x hx y hy t ht ht1
    exact h ⟨x⟩ hx ⟨y⟩ hy t ht ht1
  · intro h x hx y hy t ht ht1
    exact h x.normalized hx y.normalized hy t ht ht1

def normalizeFunction (f : Point k E → ℝ) : Lorentz.Point E → ℝ := fun x => f ⟨x⟩

theorem gconvex_iff (f : Point k E → ℝ) :
    GConvexFunction f ↔ Lorentz.GConvexFunction (normalizeFunction f) := by
  constructor
  · intro h x y t ht ht1
    exact h ⟨x⟩ ⟨y⟩ t ht ht1
  · intro h x y t ht ht1
    exact h x.normalized y.normalized t ht ht1

noncomputable def normalizeGradient (g : Ambient E) : Ambient E := (k ^ 2)⁻¹ • g
noncomputable def physicalGradient (g : Ambient E) : Ambient E := k ^ 2 • g

@[simp] theorem normalize_physicalGradient (g : Ambient E) :
    normalizeGradient (k := k) (physicalGradient (k := k) g) = g := by
  simp only [normalizeGradient, physicalGradient, smul_smul,
    inv_mul_cancel₀ (pow_ne_zero 2 (scale_pos (k := k)).ne'), one_smul]

@[simp] theorem physical_normalizeGradient (g : Ambient E) :
    physicalGradient (k := k) (normalizeGradient (k := k) g) = g := by
  simp only [normalizeGradient, physicalGradient, smul_smul,
    mul_inv_cancel₀ (pow_ne_zero 2 (scale_pos (k := k)).ne'), one_smul]

theorem support_pairing (g : Ambient E) (x y : Point k E) :
    tangentInner (k := k) g (logMap x y) =
      form E (normalizeGradient (k := k) g) (Lorentz.logMap x.normalized y.normalized) := by
  simp only [tangentInner, normalizeGradient, logMap, form_smul_left, div_eq_mul_inv, mul_comm]

def IsSubgradient (f : Point k E → ℝ) (x : Point k E) (g : Ambient E) : Prop :=
  form E x.normalized.val g = 0 ∧
    ∀ y, f x + tangentInner (k := k) g (logMap x y) ≤ f y

theorem subgradient_iff (f : Point k E → ℝ) (x : Point k E) (g : Ambient E) :
    IsSubgradient f x g ↔
      Lorentz.IsSubgradient (normalizeFunction f) x.normalized (normalizeGradient (k := k) g) := by
  have hk : (k ^ 2)⁻¹ ≠ 0 := inv_ne_zero (pow_ne_zero 2 (scale_pos (k := k)).ne')
  constructor
  · rintro ⟨ht, hs⟩
    refine ⟨by simp only [normalizeGradient, form_smul_right, ht, mul_zero], ?_⟩
    intro y
    simpa only [normalizeFunction, support_pairing] using hs ⟨y⟩
  · rintro ⟨ht, hs⟩
    refine ⟨?_, ?_⟩
    · exact (mul_eq_zero.mp (by simpa only [normalizeGradient, form_smul_right] using ht)).resolve_left hk
    · intro y
      simpa only [normalizeFunction, support_pairing] using hs y.normalized

theorem physical_subgradient_iff (f : Point k E → ℝ) (x : Point k E) (g : Ambient E) :
    IsSubgradient f x (physicalGradient (k := k) g) ↔
      Lorentz.IsSubgradient (normalizeFunction f) x.normalized g := by
  rw [subgradient_iff, normalize_physicalGradient]

abbrev Reply (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] := ℝ × Ambient E

noncomputable def replyEquiv : Reply E ≃ FirstOrderReply E where
  toFun r := (r.1, normalizeGradient (k := k) r.2)
  invFun r := (r.1, physicalGradient (k := k) r.2)
  left_inv r := by simp only [physical_normalizeGradient]
  right_inv r := by simp only [normalize_physicalGradient]

def LegalOracle (f : Point k E → ℝ) (O : Point k E → Reply E) : Prop :=
  ∀ x, (O x).1 = f x ∧ IsSubgradient f x (O x).2

noncomputable def normalizeOracle (O : Point k E → Reply E) : Lorentz.Point E → FirstOrderReply E :=
  fun x => replyEquiv (k := k) (O ⟨x⟩)

theorem legalOracle_iff (f : Point k E → ℝ) (O : Point k E → Reply E) :
    LegalOracle f O ↔ Lorentz.LegalOracle (normalizeFunction f) (normalizeOracle O) := by
  constructor
  · intro h x
    exact ⟨(h ⟨x⟩).1, (subgradient_iff f ⟨x⟩ (O ⟨x⟩).2).mp (h ⟨x⟩).2⟩
  · intro h x
    exact ⟨(h x.normalized).1, (subgradient_iff f x (O x).2).mpr (h x.normalized).2⟩

structure AdmissibleObjective (o : Point k E) (r L : ℝ) (f : Point k E → ℝ) : Prop where
  convex : GConvexFunction f
  lipschitz : ∀ x y, |f x - f y| ≤ L * dist x y
  minimizer : ∃ p, dist o p ≤ r ∧ ∀ y, f p ≤ f y

theorem admissible_iff (o : Point k E) (r L : ℝ) (f : Point k E → ℝ) :
    AdmissibleObjective o r L f ↔
      Lorentz.AdmissibleObjective o.normalized (k * r) (L / k) (normalizeFunction f) := by
  constructor
  · intro h
    refine ⟨(gconvex_iff f).mp h.convex, ?_, ?_⟩
    · intro x y
      simpa only [normalizeFunction, dist_eq, mul_div_assoc, div_mul_eq_mul_div] using h.lipschitz ⟨x⟩ ⟨y⟩
    · obtain ⟨p, hp, hmin⟩ := h.minimizer
      refine ⟨p.normalized, ?_, fun y => hmin ⟨y⟩⟩
      exact (div_le_iff₀ scale_pos).mp hp |>.trans_eq (mul_comm r k)
  · intro h
    refine ⟨(gconvex_iff f).mpr h.convex, ?_, ?_⟩
    · intro x y
      simpa only [normalizeFunction, dist_eq, mul_div_assoc, div_mul_eq_mul_div] using h.lipschitz x.normalized y.normalized
    · obtain ⟨p, hp, hmin⟩ := h.minimizer
      refine ⟨⟨p⟩, ?_, fun y => hmin y.normalized⟩
      exact (div_le_iff₀ scale_pos).mpr (hp.trans_eq (mul_comm k r))

structure StrictAdmissibleObjective (o : Point k E) (r L : ℝ) (f : Point k E → ℝ) : Prop where
  convex : GConvexFunction f
  lipschitz : ∀ x y, |f x - f y| ≤ L * dist x y
  minimizer : ∃ p, dist o p < r ∧ ∀ y, f p ≤ f y

theorem strict_admissible_iff (o : Point k E) (r L : ℝ) (f : Point k E → ℝ) :
    StrictAdmissibleObjective o r L f ↔
      Lorentz.StrictAdmissibleObjective o.normalized (k * r) (L / k) (normalizeFunction f) := by
  constructor
  · intro h
    refine ⟨(gconvex_iff f).mp h.convex, ?_, ?_⟩
    · intro x y
      simpa only [normalizeFunction, dist_eq, mul_div_assoc, div_mul_eq_mul_div] using h.lipschitz ⟨x⟩ ⟨y⟩
    · obtain ⟨p, hp, hmin⟩ := h.minimizer
      refine ⟨p.normalized, ?_, fun y => hmin ⟨y⟩⟩
      exact (div_lt_iff₀ scale_pos).mp hp |>.trans_eq (mul_comm r k)
  · intro h
    refine ⟨(gconvex_iff f).mpr h.convex, ?_, ?_⟩
    · intro x y
      simpa only [normalizeFunction, dist_eq, mul_div_assoc, div_mul_eq_mul_div] using h.lipschitz x.normalized y.normalized
    · obtain ⟨p, hp, hmin⟩ := h.minimizer
      refine ⟨⟨p⟩, ?_, fun y => hmin y.normalized⟩
      exact (div_lt_iff₀ scale_pos).mpr (hp.trans_eq (mul_comm k r))

theorem tolerance_identity (ε L r : ℝ) : ε * (L / k) * (k * r) = ε * L * r := by
  calc
    ε * (L / k) * (k * r) = (ε * L * r) * (k / k) := by ring
    _ = ε * L * r := by rw [div_self (scale_pos (k := k)).ne', mul_one]

end Geode.Rescaled
