import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-!
# Strongly monotone variational inequalities

The closed-convex Hilbert projection is constructed from Mathlib's minimizer
existence theorem. Its nonexpansiveness and the variational characterization are
proved here. A small explicit forward step makes the projected operator a
contraction, so Banach's theorem constructs the unique VI solution.
-/

noncomputable section

open Set
open scoped InnerProductSpace NNReal

namespace NCConcave16991.VariationalInequality

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [hcomplete : CompleteSpace E] (S : Set E) (hne : S.Nonempty) (hclosed : IsClosed S)
  (hconvex : Convex ℝ S)

/-- The actual nearest-point projection onto a nonempty closed convex set. -/
def projection (x : E) : S :=
  ⟨(exists_norm_eq_iInf_of_complete_convex hne hclosed.isComplete hconvex x).choose,
    (exists_norm_eq_iInf_of_complete_convex hne hclosed.isComplete hconvex x).choose_spec.1⟩

 theorem projection_minimizes (x : E) :
    ‖x - (projection S hne hclosed hconvex x : E)‖ = ⨅ w : S, ‖x - w‖ :=
  (exists_norm_eq_iInf_of_complete_convex hne hclosed.isComplete hconvex x).choose_spec.2

 theorem projection_inner (x w : E) (hw : w ∈ S) :
    ⟪x - (projection S hne hclosed hconvex x : E),
      w - (projection S hne hclosed hconvex x : E)⟫_ℝ ≤ 0 :=
  (norm_eq_iInf_iff_real_inner_le_zero hconvex (projection S hne hclosed hconvex x).property).mp
    (projection_minimizes S hne hclosed hconvex x) w hw

/-- The variational characterization uniquely determines the projection. -/
theorem projection_eq_iff (x : E) (z : S) :
    projection S hne hclosed hconvex x = z ↔
      ∀ w ∈ S, ⟪x - (z : E), w - (z : E)⟫_ℝ ≤ 0 := by
  constructor
  · intro h w hw
    simpa [h] using projection_inner S hne hclosed hconvex x w hw
  · intro hz
    let p : E := projection S hne hclosed hconvex x
    have hp := projection_inner S hne hclosed hconvex x z z.property
    have hq := hz p (projection S hne hclosed hconvex x).property
    have hid : ⟪x - p, (z : E) - p⟫_ℝ + ⟪x - (z : E), p - (z : E)⟫_ℝ =
        ‖p - (z : E)‖ ^ 2 := by
      rw [norm_sub_sq_real]
      simp only [inner_sub_left, inner_sub_right, real_inner_self_eq_norm_sq,
        real_inner_comm (z : E) p]
      ring
    have hn : ‖p - (z : E)‖ = 0 := by nlinarith [norm_nonneg (p - (z : E))]
    apply Subtype.ext
    exact sub_eq_zero.mp (norm_eq_zero.mp hn)

/-- The constructed closed-convex projection is nonexpansive. -/
theorem projection_nonexpansive (x y : E) :
    ‖(projection S hne hclosed hconvex x : E) -
      (projection S hne hclosed hconvex y : E)‖ ≤ ‖x - y‖ := by
  let p : E := projection S hne hclosed hconvex x
  let q : E := projection S hne hclosed hconvex y
  have hp := projection_inner S hne hclosed hconvex x q
    (projection S hne hclosed hconvex y).property
  have hq := projection_inner S hne hclosed hconvex y p
    (projection S hne hclosed hconvex x).property
  have hid : ‖p - q‖ ^ 2 ≤ ⟪x - y, p - q⟫_ℝ := by
    have heq : ⟪x - p, q - p⟫_ℝ + ⟪y - q, p - q⟫_ℝ =
        ‖p - q‖ ^ 2 - ⟪x - y, p - q⟫_ℝ := by
      rw [norm_sub_sq_real]
      simp only [inner_sub_left, inner_sub_right, real_inner_self_eq_norm_sq,
        real_inner_comm q p]
      ring
    linarith
  have hcs := real_inner_le_norm (x - y) (p - q)
  change ‖p - q‖ ≤ ‖x - y‖
  nlinarith [norm_nonneg (p - q), norm_nonneg (x - y)]

 theorem projection_lipschitz : LipschitzWith 1 (projection S hne hclosed hconvex) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simpa [Subtype.dist_eq, dist_eq_norm] using projection_nonexpansive S hne hclosed hconvex x y

/-- The actual projected forward step, a self-map of the complete feasible set. -/
def projectedStep (T : E → E) (η : ℝ) (z : S) : S :=
  projection S hne hclosed hconvex ((z : E) - η • T z)

/-- The variational inequality on the feasible set. -/
def IsSolution (T : E → E) (z : E) : Prop :=
  z ∈ S ∧ ∀ w ∈ S, 0 ≤ ⟪T z, w - z⟫_ℝ

/-- A positive-step projected fixed point is exactly a VI solution. -/
theorem projectedStep_fixed_iff (T : E → E) {η : ℝ} (hη : 0 < η) (z : S) :
    projectedStep S hne hclosed hconvex T η z = z ↔ IsSolution S T z := by
  rw [projectedStep, projection_eq_iff]
  constructor
  · intro hz
    refine ⟨z.property, fun w hw => ?_⟩
    have h := hz w hw
    have heq : (z : E) - η • T z - (z : E) = -η • T z := by
      simp [sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
    rw [heq, real_inner_smul_left] at h
    nlinarith
  · rintro ⟨_, hz⟩ w hw
    have heq : (z : E) - η • T z - (z : E) = -η • T z := by
      simp [sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
    rw [heq, real_inner_smul_left]
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hη.le) (hz w hw)

/-- An explicit positive step, valid even if the feasible set is a singleton. -/
def stepSize (C μ : ℝ) : ℝ := μ / (C ^ 2 + μ ^ 2 + 1)

/-- A convenient contraction rate avoiding any square-root choices. -/
def contractionRate (C μ : ℝ) : ℝ := 1 - stepSize C μ * μ / 2

 theorem stepSize_pos (C : ℝ) {μ : ℝ} (hμ : 0 < μ) : 0 < stepSize C μ := by
  apply div_pos hμ
  nlinarith [sq_nonneg C, sq_nonneg μ]

 theorem stepSize_mul_mu_lt_one (C : ℝ) {μ : ℝ} (hμ : 0 < μ) :
    stepSize C μ * μ < 1 := by
  dsimp [stepSize]
  rw [div_mul_eq_mul_div]
  apply (div_lt_iff₀ (by nlinarith [sq_nonneg C, sq_nonneg μ])).mpr
  nlinarith [sq_nonneg C]

 theorem stepSize_mul_sq_le_mu (C : ℝ) {μ : ℝ} (hμ : 0 < μ) :
    stepSize C μ * C ^ 2 ≤ μ := by
  dsimp [stepSize]
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ (by nlinarith [sq_nonneg C, sq_nonneg μ])).mpr
  exact mul_le_mul_of_nonneg_left (by nlinarith [sq_nonneg μ]) hμ.le

 theorem contractionRate_pos (C : ℝ) {μ : ℝ} (hμ : 0 < μ) :
    0 < contractionRate C μ := by
  have := stepSize_mul_mu_lt_one C hμ
  dsimp [contractionRate]
  linarith

 theorem contractionRate_lt_one (C : ℝ) {μ : ℝ} (hμ : 0 < μ) :
    contractionRate C μ < 1 := by
  have := mul_pos (stepSize_pos C hμ) hμ
  dsimp [contractionRate]
  linarith

/-- Strong monotonicity and Lipschitz continuity make the explicit unprojected step contractive. -/
theorem forwardStep_contraction (T : E → E) (C : ℝ≥0) {μ : ℝ} (hμ : 0 < μ)
    (hLip : LipschitzOnWith C T S)
    (hMono : ∀ x ∈ S, ∀ y ∈ S, μ * ‖x - y‖ ^ 2 ≤ ⟪T x - T y, x - y⟫_ℝ)
    (x : E) (hx : x ∈ S) (y : E) (hy : y ∈ S) :
    ‖(x - stepSize C μ • T x) - (y - stepSize C μ • T y)‖ ≤
      contractionRate C μ * ‖x - y‖ := by
  let η := stepSize C μ
  let q := contractionRate C μ
  have hη : 0 < η := stepSize_pos C hμ
  have hq : 0 < q := contractionRate_pos C hμ
  have hLC : ‖T x - T y‖ ≤ (C : ℝ) * ‖x - y‖ := by
    simpa [dist_eq_norm] using hLip.dist_le_mul x hx y hy
  have hLCsq : ‖T x - T y‖ ^ 2 ≤ (C : ℝ) ^ 2 * ‖x - y‖ ^ 2 := by
    nlinarith [norm_nonneg (T x - T y), norm_nonneg (x - y), C.coe_nonneg]
  have hM := hMono x hx y hy
  have hηC : η ^ 2 * (C : ℝ) ^ 2 ≤ η * μ := by
    have h := mul_le_mul_of_nonneg_left (stepSize_mul_sq_le_mu C hμ) hη.le
    dsimp [η]
    nlinarith
  have hcoef : 1 - 2 * η * μ + η ^ 2 * (C : ℝ) ^ 2 ≤ q ^ 2 := by
    dsimp [q, contractionRate]
    change 1 - 2 * η * μ + η ^ 2 * (C : ℝ) ^ 2 ≤ (1 - η * μ / 2) ^ 2
    nlinarith [sq_nonneg (η * μ / 2)]
  have hexpand : ‖(x - η • T x) - (y - η • T y)‖ ^ 2 =
      ‖x - y‖ ^ 2 - 2 * η * ⟪T x - T y, x - y⟫_ℝ + η ^ 2 * ‖T x - T y‖ ^ 2 := by
    have hdiff : (x - η • T x) - (y - η • T y) = (x - y) - η • (T x - T y) := by
      rw [smul_sub]
      abel
    rw [hdiff, norm_sub_sq_real, real_inner_smul_right, norm_smul,
      Real.norm_eq_abs, abs_of_pos hη, real_inner_comm (x - y) (T x - T y)]
    ring
  have hbound : ‖(x - η • T x) - (y - η • T y)‖ ^ 2 ≤ q ^ 2 * ‖x - y‖ ^ 2 := by
    rw [hexpand]
    calc
      _ ≤ ‖x - y‖ ^ 2 - 2 * η * (μ * ‖x - y‖ ^ 2) +
          η ^ 2 * ((C : ℝ) ^ 2 * ‖x - y‖ ^ 2) := by
        have hm := mul_le_mul_of_nonneg_left hM (by positivity : 0 ≤ 2 * η)
        have hl := mul_le_mul_of_nonneg_left hLCsq (sq_nonneg η)
        linarith
      _ = (1 - 2 * η * μ + η ^ 2 * (C : ℝ) ^ 2) * ‖x - y‖ ^ 2 := by ring
      _ ≤ q ^ 2 * ‖x - y‖ ^ 2 := mul_le_mul_of_nonneg_right hcoef (sq_nonneg _)
  change ‖(x - η • T x) - (y - η • T y)‖ ≤ q * ‖x - y‖
  nlinarith [norm_nonneg ((x - η • T x) - (y - η • T y)),
    mul_nonneg hq.le (norm_nonneg (x - y))]

/-- Nonexpansive projection preserves the explicit contraction estimate. -/
theorem projectedStep_contracting (T : E → E) (C : ℝ≥0) {μ : ℝ} (hμ : 0 < μ)
    (hLip : LipschitzOnWith C T S)
    (hMono : ∀ x ∈ S, ∀ y ∈ S, μ * ‖x - y‖ ^ 2 ≤ ⟪T x - T y, x - y⟫_ℝ) :
    ContractingWith ⟨contractionRate C μ, (contractionRate_pos C hμ).le⟩
      (projectedStep S hne hclosed hconvex T (stepSize C μ)) := by
  refine ⟨?_, LipschitzWith.of_dist_le_mul ?_⟩
  · exact contractionRate_lt_one C hμ
  · intro x y
    change dist (projectedStep S hne hclosed hconvex T (stepSize C μ) x)
      (projectedStep S hne hclosed hconvex T (stepSize C μ) y) ≤
        contractionRate C μ * dist x y
    simpa only [projectedStep, Subtype.dist_eq, dist_eq_norm] using
      (projection_nonexpansive S hne hclosed hconvex _ _).trans
        (forwardStep_contraction S T C hμ hLip hMono x x.property y y.property)

include hcomplete hne hclosed hconvex

/-- Banach's theorem constructs the VI solution; the existence is not assumed. -/
theorem existsUnique_solution (T : E → E) (C : ℝ≥0) {μ : ℝ} (hμ : 0 < μ)
    (hLip : LipschitzOnWith C T S)
    (hMono : ∀ x ∈ S, ∀ y ∈ S, μ * ‖x - y‖ ^ 2 ≤ ⟪T x - T y, x - y⟫_ℝ) :
    ∃! z : E, IsSolution S T z := by
  letI : Nonempty S := hne.to_subtype
  letI : CompleteSpace S := hclosed.completeSpace_coe
  let f := projectedStep S hne hclosed hconvex T (stepSize C μ)
  have hf := projectedStep_contracting S hne hclosed hconvex T C hμ hLip hMono
  let z : S := hf.fixedPoint f
  have hz : IsSolution S T z :=
    (projectedStep_fixed_iff S hne hclosed hconvex T (stepSize_pos C hμ) z).mp
      hf.fixedPoint_isFixedPt
  refine ⟨z, hz, fun w hw => ?_⟩
  let wS : S := ⟨w, hw.1⟩
  have hwfix : f wS = wS :=
    (projectedStep_fixed_iff S hne hclosed hconvex T (stepSize_pos C hμ) wS).mpr hw
  exact congrArg Subtype.val (hf.fixedPoint_unique hwfix)

end NCConcave16991.VariationalInequality




