import Geode.LorentzBoost
import Geode.LogMap
import Mathlib.Analysis.InnerProductSpace.Projection
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! An actual Lorentz-orthogonal projection onto a public subspace containing
a timelike center. The construction boosts the center to the origin, applies
ordinary orthogonal projection to its spatial section, and boosts back. -/
namespace Geode.Lorentz

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def spatialSection (W : Submodule ℝ (Ambient E)) (c : Point E) : Submodule ℝ E :=
  W.comap ((boost c).toLinearMap.comp (LinearMap.inr ℝ ℝ E))

@[simp] theorem mem_spatialSection (W : Submodule ℝ (Ambient E)) (c : Point E) (u : E) :
    u ∈ spatialSection W c ↔ boost c (0, u) ∈ W := Iff.rfl

variable [FiniteDimensional ℝ E]

noncomputable def coordinateProjection (U : Submodule ℝ E) : Ambient E →ₗ[ℝ] Ambient E where
  toFun q := (q.1, (U.orthogonalProjection q.2 : E))
  map_add' a b := by ext <;> simp
  map_smul' a q := by ext <;> simp

noncomputable def publicPart (W : Submodule ℝ (Ambient E)) (c : Point E) :
    Ambient E →ₗ[ℝ] Ambient E :=
  (boost c).toLinearMap.comp ((coordinateProjection (spatialSection W c)).comp
    (boost (pointReflect c)).toLinearMap)

noncomputable def residualPart (W : Submodule ℝ (Ambient E)) (c : Point E) :
    Ambient E →ₗ[ℝ] Ambient E := LinearMap.id - publicPart W c

theorem publicPart_coordinates (W : Submodule ℝ (Ambient E)) (c : Point E) (q : Ambient E) :
    publicPart W c q = boost c ((boost (pointReflect c) q).1,
      ((spatialSection W c).orthogonalProjection (boost (pointReflect c) q).2 : E)) := rfl

theorem publicPart_mem (W : Submodule ℝ (Ambient E)) {c : Point E}
    (hc : c.val ∈ W) (q : Ambient E) : publicPart W c q ∈ W := by
  let t := (boost (pointReflect c) q).1
  let u : E := ((spatialSection W c).orthogonalProjection (boost (pointReflect c) q).2 : E)
  have hu : boost c (0, u) ∈ W :=
    ((spatialSection W c).orthogonalProjection (boost (pointReflect c) q).2).property
  have hdecomp : publicPart W c q = t • c.val + boost c (0, u) := by
    rw [publicPart_coordinates]
    change boost c (t, u) = _
    have hpair : (t, u) = t • (1, (0 : E)) + (0, u) := by ext <;> simp
    rw [hpair, map_add, map_smul, boost_origin]
  rw [hdecomp]
  exact W.add_mem (W.smul_mem t hc) hu

omit [FiniteDimensional ℝ E] in
theorem spatialSection_mem_of_mem (W : Submodule ℝ (Ambient E)) {c : Point E}
    (hc : c.val ∈ W) {w : Ambient E} (hw : w ∈ W) :
    (boost (pointReflect c) w).2 ∈ spatialSection W c := by
  rw [mem_spatialSection]
  have hpair : (0, (boost (pointReflect c) w).2) =
      boost (pointReflect c) w - (boost (pointReflect c) w).1 • (1, (0 : E)) := by
    ext <;> simp
  rw [hpair, map_sub, map_smul, boost_inverse_rev, boost_origin]
  exact W.sub_mem hw (W.smul_mem _ hc)

theorem residualPart_coordinates (W : Submodule ℝ (Ambient E)) (c : Point E) (q : Ambient E) :
    residualPart W c q = boost c (0, (boost (pointReflect c) q).2 -
      ((spatialSection W c).orthogonalProjection (boost (pointReflect c) q).2 : E)) := by
  change q - publicPart W c q = _
  rw [publicPart_coordinates]
  have hq : q = boost c (boost (pointReflect c) q) := (boost_inverse_rev c q).symm
  calc
    q - boost c ((boost (pointReflect c) q).1,
        ((spatialSection W c).orthogonalProjection (boost (pointReflect c) q).2 : E)) =
      boost c (boost (pointReflect c) q - ((boost (pointReflect c) q).1,
        ((spatialSection W c).orthogonalProjection (boost (pointReflect c) q).2 : E))) := by
          rw [map_sub, ← hq]
    _ = _ := by congr 1; ext <;> simp

theorem residualPart_orthogonal (W : Submodule ℝ (Ambient E)) {c : Point E}
    (hc : c.val ∈ W) (q : Ambient E) {w : Ambient E} (hw : w ∈ W) :
    form E (residualPart W c q) w = 0 := by
  rw [residualPart_coordinates, boost_form_move]
  simp only [form, neg_zero, zero_mul, zero_add]
  exact (spatialSection W c).orthogonalProjection_inner_eq_zero
    (boost (pointReflect c) q).2 _ (spatialSection_mem_of_mem W hc hw)

theorem residualPart_tangent (W : Submodule ℝ (Ambient E)) {c : Point E}
    (hc : c.val ∈ W) (q : Ambient E) : form E c.val (residualPart W c q) = 0 := by
  rw [form_comm]
  exact residualPart_orthogonal W hc q hc

theorem publicPart_add_residualPart (W : Submodule ℝ (Ambient E)) (c : Point E) (q : Ambient E) :
    publicPart W c q + residualPart W c q = q := by
  change publicPart W c q + (q - publicPart W c q) = q
  abel

theorem residualPart_nonneg (W : Submodule ℝ (Ambient E)) {c : Point E}
    (hc : c.val ∈ W) (q : Ambient E) :
    0 ≤ form E (residualPart W c q) (residualPart W c q) :=
  tangent_nonneg c (residualPart_tangent W hc q)

theorem residualPart_positive (W : Submodule ℝ (Ambient E)) {c : Point E}
    (hc : c.val ∈ W) {q : Ambient E} (hne : residualPart W c q ≠ 0) :
    0 < form E (residualPart W c q) (residualPart W c q) :=
  tangent_pos c (residualPart_tangent W hc q) hne

theorem publicPart_tangent (W : Submodule ℝ (Ambient E)) {c z : Point E}
    (hc : c.val ∈ W) (hz : z.val ∈ W) {q : Ambient E} (hq : form E z.val q = 0) :
    form E z.val (publicPart W c q) = 0 := by
  have hr : form E z.val (residualPart W c q) = 0 := by
    rw [form_comm]
    exact residualPart_orthogonal W hc q hz
  have hs := congrArg (form E z.val) (publicPart_add_residualPart W c q)
  rw [form_add_right, hr, hq, add_zero] at hs
  exact hs

theorem publicPart_norm_split (W : Submodule ℝ (Ambient E)) {c : Point E}
    (hc : c.val ∈ W) (q : Ambient E) :
    form E q q = form E (publicPart W c q) (publicPart W c q) +
      form E (residualPart W c q) (residualPart W c q) := by
  have hrp := residualPart_orthogonal W hc q (publicPart_mem W hc q)
  have hpr : form E (publicPart W c q) (residualPart W c q) = 0 := by
    rw [form_comm]; exact hrp
  calc
    form E q q = form E (publicPart W c q + residualPart W c q)
      (publicPart W c q + residualPart W c q) :=
        congrArg₂ (form E) (publicPart_add_residualPart W c q).symm
          (publicPart_add_residualPart W c q).symm
    _ = _ := by simp [hrp, hpr]

theorem publicPart_eq_self (W : Submodule ℝ (Ambient E)) {c : Point E}
    (hc : c.val ∈ W) {q : Ambient E} (hq : q ∈ W) : publicPart W c q = q := by
  have hrmem : residualPart W c q ∈ W := W.sub_mem hq (publicPart_mem W hc q)
  have hz := residualPart_orthogonal W hc q hrmem
  have hr := (tangent_eq_zero_iff c (residualPart_tangent W hc q)).mp hz
  have h := publicPart_add_residualPart W c q
  simpa only [hr, add_zero] using h

theorem publicPart_idempotent (W : Submodule ℝ (Ambient E)) {c : Point E}
    (hc : c.val ∈ W) (q : Ambient E) :
    publicPart W c (publicPart W c q) = publicPart W c q :=
  publicPart_eq_self W hc (publicPart_mem W hc q)

noncomputable def residualSize (W : Submodule ℝ (Ambient E)) (c : Point E) (q : Ambient E) : ℝ :=
  tangentNorm (residualPart W c q)

noncomputable def residualUnit (W : Submodule ℝ (Ambient E)) (c : Point E) (q : Ambient E) : Ambient E :=
  (residualSize W c q)⁻¹ • residualPart W c q

theorem residualSize_sq (W : Submodule ℝ (Ambient E)) {c : Point E}
    (hc : c.val ∈ W) (q : Ambient E) :
    residualSize W c q ^ 2 = form E (residualPart W c q) (residualPart W c q) :=
  Real.sq_sqrt (residualPart_nonneg W hc q)

theorem residualSize_pos (W : Submodule ℝ (Ambient E)) {c : Point E}
    (hc : c.val ∈ W) {q : Ambient E} (hne : residualPart W c q ≠ 0) :
    0 < residualSize W c q := Real.sqrt_pos.mpr (residualPart_positive W hc hne)

theorem residualUnit_unit (W : Submodule ℝ (Ambient E)) {c : Point E}
    (hc : c.val ∈ W) {q : Ambient E} (hne : residualPart W c q ≠ 0) :
    form E (residualUnit W c q) (residualUnit W c q) = 1 := by
  have hβ : residualSize W c q ≠ 0 := (residualSize_pos W hc hne).ne'
  simp only [residualUnit, form_smul_left, form_smul_right]
  rw [← residualSize_sq W hc q]
  field_simp
  ring

theorem residualUnit_orthogonal (W : Submodule ℝ (Ambient E)) {c : Point E}
    (hc : c.val ∈ W) (q : Ambient E) {w : Ambient E} (hw : w ∈ W) :
    form E (residualUnit W c q) w = 0 := by
  simp only [residualUnit, form_smul_left, residualPart_orthogonal W hc q hw, mul_zero]

theorem public_residual_decomposition (W : Submodule ℝ (Ambient E)) {c : Point E}
    (hc : c.val ∈ W) {q : Ambient E} (hne : residualPart W c q ≠ 0) :
    q = publicPart W c q + residualSize W c q • residualUnit W c q := by
  have hβ : residualSize W c q ≠ 0 := (residualSize_pos W hc hne).ne'
  rw [residualUnit, smul_smul, mul_inv_cancel₀ hβ, one_smul, publicPart_add_residualPart]

end Geode.Lorentz
