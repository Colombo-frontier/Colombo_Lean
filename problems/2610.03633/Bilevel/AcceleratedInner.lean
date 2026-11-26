import Bilevel.InnerContraction
import Bilevel.StochasticInner

/-!
The accelerated two-state iteration in `acc:lem:inner` of the November 23
chi-refinement manuscript. These are analytic one-step certificates for the
actual objective and updates, not yet a stochastic execution or complexity
theorem. No potential contraction is assumed as a hypothesis.
-/

noncomputable section
open scoped RealInnerProductSpace
open MeasureTheory

namespace Bilevel.AcceleratedInner

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

def potential (F : E → ℝ) (μ : ℝ) (ys u v : E) : ℝ :=
  F u - F ys + μ / 2 * ‖v - ys‖ ^ 2

def query (α : ℝ) (u v : E) : E := (1 + α)⁻¹ • (u + α • v)

def nextU (M : ℝ) (w G : E) : E := w - M⁻¹ • G

def nextV (μ α : ℝ) (v w G : E) : E :=
  (1 - α) • v + α • w - (α / μ) • G

omit [CompleteSpace E] in
theorem query_identity {α : ℝ} (hα : 0 ≤ α) (u v : E) :
    (1 + α) • query α u v = u + α • v := by
  rw [query, smul_smul, mul_inv_cancel₀ (by linarith : 1 + α ≠ 0), one_smul]

theorem exact_step_descent (F : E → ℝ) (g : E → E) {M : ℝ}
    (hM : 0 < M) (hg : ∀ y, HasGradientAt F (g y) y)
    (hlip : ∀ u v, ‖g u - g v‖ ≤ M * ‖u - v‖) (w : E) :
    F (nextU M w (g w)) ≤ F w - ‖g w‖ ^ 2 / (2 * M) := by
  have hs := InnerContraction.smooth_upper_model F g M hg hlip w (-M⁻¹ • g w)
  have hid : w + -M⁻¹ • g w = nextU M w (g w) := by
    simp [nextU, neg_smul, sub_eq_add_neg]
  rw [hid, real_inner_smul_right, real_inner_self_eq_norm_sq, norm_smul,
    Real.norm_eq_abs, mul_pow, sq_abs] at hs
  convert hs using 1
  field_simp
  ring

omit [CompleteSpace E] in
private theorem energy_identity {M μ α : ℝ} (hM : M ≠ 0) (hμ : μ ≠ 0)
    (hrel : α ^ 2 * M = μ) (u v w ys G : E)
    (hw : (1 + α) • w = u + α • v) :
    μ / 2 * ‖nextV μ α v w G - ys‖ ^ 2 - ‖G‖ ^ 2 / (2 * M) =
      (1 - α) * (μ / 2 * ‖v - ys‖ ^ 2) -
      μ * (1 - α) / 2 * (‖u - w‖ ^ 2 + α * ‖v - w‖ ^ 2) +
      (1 - α) * ⟪G, u - w⟫ + α * ⟪G, ys - w⟫ +
      μ / 2 * ((1 - α) * ‖u - w‖ ^ 2 + α * ‖ys - w‖ ^ 2) := by
  have hi := congrArg (fun z : E => ⟪G, z⟫) hw
  simp only [real_inner_smul_right, inner_add_right] at hi
  simp only [nextV, ← real_inner_self_eq_norm_sq, inner_sub_left, inner_sub_right,
    inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right]
  simp only [real_inner_comm] at hi ⊢
  field_simp
  linear_combination 4 * μ ^ 5 * ⟪G, G⟫ * hrel +
    8 * μ ^ 6 * M * (1 - α) * hi

/-- The precise deterministic potential contraction displayed in the source.
It follows from the objective's gradient smoothness and strong convexity. -/
theorem potential_contraction (F : E → ℝ) (g : E → E) {M μ α : ℝ}
    (hM : 0 < M) (hμ : 0 < μ) (hα : 0 ≤ α) (hα1 : α ≤ 1)
    (hrel : α ^ 2 * M = μ)
    (hg : ∀ y, HasGradientAt F (g y) y)
    (hlip : ∀ u v, ‖g u - g v‖ ≤ M * ‖u - v‖)
    (hstrong : ∀ u v, F u + ⟪g u, v - u⟫ + μ / 2 * ‖v - u‖ ^ 2 ≤ F v)
    (u v ys : E) :
    let w := query α u v
    potential F μ ys (nextU M w (g w)) (nextV μ α v w (g w)) ≤
      (1 - α) * potential F μ ys u v -
        μ * (1 - α) / 2 * (‖u - w‖ ^ 2 + α * ‖v - w‖ ^ 2) := by
  dsimp only
  let w := query α u v
  have hs := exact_step_descent F g hM hg hlip w
  have he := energy_identity hM.ne' hμ.ne' hrel u v w ys (g w)
    (query_identity hα u v)
  have hu := mul_le_mul_of_nonneg_left (hstrong w u) (sub_nonneg.mpr hα1)
  have hy := mul_le_mul_of_nonneg_left (hstrong w ys) hα
  change F (nextU M w (g w)) - F ys + μ / 2 * ‖nextV μ α v w (g w) - ys‖ ^ 2 ≤
    (1 - α) * (F u - F ys + μ / 2 * ‖v - ys‖ ^ 2) -
      μ * (1 - α) / 2 * (‖u - w‖ ^ 2 + α * ‖v - w‖ ^ 2)
  nlinarith

/-- The pathwise noise increment has two linear terms. They disappear under
conditional centering; the remaining squared-noise coefficient is exactly
`1 / M`, as in the manuscript's accelerated potential recurrence. -/
theorem noise_increment_bound (F : E → ℝ) (g : E → E) {M μ α : ℝ}
    (hM : 0 < M) (hμ : 0 < μ) (hrel : α ^ 2 * M = μ)
    (hg : ∀ y, HasGradientAt F (g y) y)
    (hlip : ∀ u v, ‖g u - g v‖ ≤ M * ‖u - v‖)
    (v w ys ξ : E) :
    potential F μ ys (nextU M w (g w + ξ)) (nextV μ α v w (g w + ξ)) ≤
      potential F μ ys (nextU M w (g w)) (nextV μ α v w (g w)) -
        M⁻¹ * ⟪g (nextU M w (g w)), ξ⟫ -
        α * ⟪nextV μ α v w (g w) - ys, ξ⟫ + M⁻¹ * ‖ξ‖ ^ 2 := by
  have hu : nextU M w (g w + ξ) = nextU M w (g w) - M⁻¹ • ξ := by
    simp only [nextU, smul_add]
    abel
  have hv : nextV μ α v w (g w + ξ) - ys =
      (nextV μ α v w (g w) - ys) - (α / μ) • ξ := by
    simp only [nextV, smul_add]
    abel
  have hs := InnerContraction.smooth_upper_model F g M hg hlip
    (nextU M w (g w)) (-M⁻¹ • ξ)
  have hid : nextU M w (g w) + -M⁻¹ • ξ = nextU M w (g w + ξ) := by
    rw [hu]
    simp [neg_smul, sub_eq_add_neg]
  rw [hid, real_inner_smul_right, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs] at hs
  have he : M / 2 * (-M⁻¹) ^ 2 + μ / 2 * (α / μ) ^ 2 = M⁻¹ := by
    field_simp
    linear_combination 2 * μ * M ^ 2 * hrel
  have hc : μ * (α / μ) = α := by field_simp
  unfold potential
  rw [hv, norm_sub_sq_real, real_inner_smul_right, norm_smul,
    Real.norm_eq_abs, mul_pow, sq_abs]
  linear_combination hs + ‖ξ‖ ^ 2 * he -
    ⟪nextV μ α v w (g w) - ys, ξ⟫ * hc

/-- The complete one-step accelerated noisy potential bound, with the actual
query and the same noise vector used in both updates. -/
theorem noisy_potential_bound (F : E → ℝ) (g : E → E) {M μ α : ℝ}
    (hM : 0 < M) (hμ : 0 < μ) (hα : 0 ≤ α) (hα1 : α ≤ 1)
    (hrel : α ^ 2 * M = μ)
    (hg : ∀ y, HasGradientAt F (g y) y)
    (hlip : ∀ u v, ‖g u - g v‖ ≤ M * ‖u - v‖)
    (hstrong : ∀ u v, F u + ⟪g u, v - u⟫ + μ / 2 * ‖v - u‖ ^ 2 ≤ F v)
    (u v ys ξ : E) :
    let w := query α u v
    potential F μ ys (nextU M w (g w + ξ)) (nextV μ α v w (g w + ξ)) ≤
      (1 - α) * potential F μ ys u v -
        M⁻¹ * ⟪g (nextU M w (g w)), ξ⟫ -
        α * ⟪nextV μ α v w (g w) - ys, ξ⟫ + M⁻¹ * ‖ξ‖ ^ 2 := by
  dsimp only
  have hd := potential_contraction F g hM hμ hα hα1 hrel hg hlip hstrong u v ys
  have hn := noise_increment_bound F g hM hμ hrel hg hlip v (query α u v) ys ξ
  dsimp only at hd
  have hr : 0 ≤ μ * (1 - α) / 2 *
      (‖u - query α u v‖ ^ 2 + α * ‖v - query α u v‖ ^ 2) := by
    have := sub_nonneg.mpr hα1
    positivity
  linarith

omit [CompleteSpace E] in
theorem potential_controls_distance (F : E → ℝ) (g : E → E) {μ : ℝ}
    (hμ : 0 ≤ μ)
    (hstrong : ∀ u v, F u + ⟪g u, v - u⟫ + μ / 2 * ‖v - u‖ ^ 2 ≤ F v)
    (u v ys : E) (hstationary : g ys = 0) :
    μ / 2 * ‖u - ys‖ ^ 2 ≤ potential F μ ys u v := by
  have hs := hstrong ys u
  rw [hstationary, inner_zero_left, add_zero] at hs
  have hn : 0 ≤ μ / 2 * ‖v - ys‖ ^ 2 := by positivity
  unfold potential
  linarith

theorem square_root_parameter {M μ : ℝ} (hμ : 0 < μ) (hμM : μ ≤ M) :
    0 < Real.sqrt (μ / M) ∧ Real.sqrt (μ / M) ≤ 1 ∧
      Real.sqrt (μ / M) ^ 2 * M = μ := by
  have hM : 0 < M := hμ.trans_le hμM
  refine ⟨Real.sqrt_pos.2 (div_pos hμ hM), ?_, ?_⟩
  · exact Real.sqrt_le_one.mpr ((div_le_one hM).mpr hμM)
  · rw [Real.sq_sqrt (div_nonneg hμ.le hM.le), div_mul_cancel₀ _ hM.ne']

theorem initial_potential_bound (F : E → ℝ) (g : E → E) {M μ R : ℝ}
    (hM : 0 ≤ M) (hμM : μ ≤ M)
    (hg : ∀ y, HasGradientAt F (g y) y)
    (hlip : ∀ u v, ‖g u - g v‖ ≤ M * ‖u - v‖)
    (u ys : E) (hstationary : g ys = 0) (hradius : ‖u - ys‖ ^ 2 ≤ R ^ 2) :
    potential F μ ys u u ≤ M * R ^ 2 := by
  have hs := InnerContraction.smooth_upper_model F g M hg hlip ys (u - ys)
  have hid : ys + (u - ys) = u := by abel
  rw [hid, hstationary, inner_zero_left, add_zero] at hs
  have hμ := mul_le_mul_of_nonneg_right hμM (sq_nonneg ‖u - ys‖)
  have hr := mul_le_mul_of_nonneg_left hradius hM
  unfold potential
  linarith

/-- Repeated exact updates have the accelerated geometric potential decay. -/
theorem exact_trajectory_bound (F : E → ℝ) (g : E → E) {M μ α : ℝ}
    (hM : 0 < M) (hμ : 0 < μ) (hα : 0 ≤ α) (hα1 : α ≤ 1)
    (hrel : α ^ 2 * M = μ)
    (hg : ∀ y, HasGradientAt F (g y) y)
    (hlip : ∀ u v, ‖g u - g v‖ ≤ M * ‖u - v‖)
    (hstrong : ∀ u v, F u + ⟪g u, v - u⟫ + μ / 2 * ‖v - u‖ ^ 2 ≤ F v)
    (u v : ℕ → E) (ys : E)
    (hu : ∀ n, u (n + 1) = nextU M (query α (u n) (v n)) (g (query α (u n) (v n))))
    (hv : ∀ n, v (n + 1) = nextV μ α (v n) (query α (u n) (v n))
      (g (query α (u n) (v n)))) (n : ℕ) :
    potential F μ ys (u n) (v n) ≤ (1 - α) ^ n * potential F μ ys (u 0) (v 0) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hc := potential_contraction F g hM hμ hα hα1 hrel hg hlip hstrong (u n) (v n) ys
    dsimp only at hc
    have hr : 0 ≤ μ * (1 - α) / 2 *
        (‖u n - query α (u n) (v n)‖ ^ 2 + α * ‖v n - query α (u n) (v n)‖ ^ 2) := by
      have := sub_nonneg.mpr hα1
      positivity
    rw [hu n, hv n]
    calc
      _ ≤ (1 - α) * potential F μ ys (u n) (v n) := by linarith
      _ ≤ (1 - α) * ((1 - α) ^ n * potential F μ ys (u 0) (v 0)) :=
        mul_le_mul_of_nonneg_left ih (sub_nonneg.mpr hα1)
      _ = _ := by rw [pow_succ]; ring

section Expectations

variable {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω} [IsProbabilityMeasure ν]

/-- One conditional-state solve step under a genuine probability law. Output
potential integrability is derived from finite noise moments, not assumed.
The law can be chosen separately after each preceding history. -/
theorem expected_potential_step (F : E → ℝ) (g : E → E) {M μ α : ℝ}
    (hM : 0 < M) (hμ : 0 < μ) (hα : 0 ≤ α) (hα1 : α ≤ 1)
    (hrel : α ^ 2 * M = μ)
    (hg : ∀ y, HasGradientAt F (g y) y)
    (hlip : ∀ u v, ‖g u - g v‖ ≤ M * ‖u - v‖)
    (hstrong : ∀ u v, F u + ⟪g u, v - u⟫ + μ / 2 * ‖v - u‖ ^ 2 ≤ F v)
    (u v ys : E) (hmin : ∀ y, F ys ≤ F y) (noise : Ω → E)
    (hi : Integrable noise ν) (hsecond : Integrable (fun ω => ‖noise ω‖ ^ 2) ν)
    (hcenter : (∫ ω, noise ω ∂ν) = 0) (budget : ℝ)
    (hbudget : (∫ ω, ‖noise ω‖ ^ 2 ∂ν) ≤ budget) :
    let w := query α u v
    let Vnew := fun ω => potential F μ ys (nextU M w (g w + noise ω))
      (nextV μ α v w (g w + noise ω))
    Integrable Vnew ν ∧ (∫ ω, Vnew ω ∂ν) ≤
      (1 - α) * potential F μ ys u v + budget / M := by
  dsimp only
  let w := query α u v
  let un := nextU M w (g w)
  let vn := nextV μ α v w (g w)
  let Vnew := fun ω => potential F μ ys (nextU M w (g w + noise ω))
    (nextV μ α v w (g w + noise ω))
  let bound := fun ω => (1 - α) * potential F μ ys u v -
    M⁻¹ * ⟪g un, noise ω⟫ - α * ⟪vn - ys, noise ω⟫ + M⁻¹ * ‖noise ω‖ ^ 2
  have hdom (ω : Ω) : Vnew ω ≤ bound ω :=
    noisy_potential_bound F g hM hμ hα hα1 hrel hg hlip hstrong u v ys (noise ω)
  have hnonneg (ω : Ω) : 0 ≤ Vnew ω := by
    have hm := hmin (nextU M w (g w + noise ω))
    dsimp [Vnew, potential]
    exact add_nonneg (sub_nonneg.mpr hm) (by positivity)
  have hF : Continuous F := continuous_iff_continuousAt.mpr
    (fun y => (hg y).differentiableAt.continuousAt)
  have hcont : Continuous (fun ξ : E => potential F μ ys
      (nextU M w (g w + ξ)) (nextV μ α v w (g w + ξ))) := by
    unfold potential nextU nextV
    fun_prop
  have hm : AEStronglyMeasurable Vnew ν := hcont.comp_aestronglyMeasurable hi.aestronglyMeasurable
  have hb : Integrable bound ν :=
    (((integrable_const _).sub ((hi.const_inner (g un)).const_mul _)).sub
      ((hi.const_inner (vn - ys)).const_mul _)).add (hsecond.const_mul _)
  have hint : Integrable Vnew ν := hb.mono' hm (Filter.Eventually.of_forall
    (fun ω => by rw [Real.norm_of_nonneg (hnonneg ω)]; exact hdom ω))
  refine ⟨hint, (integral_mono hint hb hdom).trans ?_⟩
  have hzero (z : E) : (∫ ω, ⟪z, noise ω⟫ ∂ν) = 0 := by
    rw [integral_inner hi z, hcenter, inner_zero_right]
  have hp1 : Integrable (fun ω => (1 - α) * potential F μ ys u v -
      M⁻¹ * ⟪g un, noise ω⟫) ν :=
    (integrable_const _).sub ((hi.const_inner (g un)).const_mul _)
  have hp2 : Integrable (fun ω => (1 - α) * potential F μ ys u v -
      M⁻¹ * ⟪g un, noise ω⟫ - α * ⟪vn - ys, noise ω⟫) ν :=
    hp1.sub ((hi.const_inner (vn - ys)).const_mul _)
  dsimp [bound]
  rw [integral_add hp2 (hsecond.const_mul M⁻¹),
    integral_sub hp1 ((hi.const_inner (vn - ys)).const_mul α),
    integral_sub (integrable_const ((1 - α) * potential F μ ys u v))
      ((hi.const_inner (g un)).const_mul M⁻¹)]
  simp only [integral_const_mul, hzero, mul_zero, sub_zero, integral_const,
    measureReal_univ_eq_one, one_smul]
  have hb' := mul_le_mul_of_nonneg_left hbudget (inv_nonneg.mpr hM.le)
  simpa only [div_eq_mul_inv, mul_comm] using add_le_add_left hb' ((1 - α) * potential F μ ys u v)

end Expectations

end Bilevel.AcceleratedInner

namespace Bilevel.Model.Primitive

open AcceleratedInner
variable {X Y : Type*}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y] [Nontrivial Y]
variable {μ Lf Lg Cf ρ : ℝ}
variable (P : Primitive (X := X) (Y := Y) μ Lf Lg Cf ρ)

/-- Instantiation for the actual frozen linear tilt. Its acceleration parameter
depends only on the original lower smoothness and strong-convexity constants;
the frozen vector and tilt size are unrestricted. -/
theorem tilted_accelerated_potential (x : X) (t : ℝ) (a u v ys : Y) :
    let α := Real.sqrt (μ / Lg)
    let w := query α u v
    let grad := fun y => P.gy x y + t • a
    potential (P.tiltedLower x t a) μ ys
        (nextU Lg w (grad w)) (nextV μ α v w (grad w)) ≤
      (1 - α) * potential (P.tiltedLower x t a) μ ys u v -
        μ * (1 - α) / 2 * (‖u - w‖ ^ 2 + α * ‖v - w‖ ^ 2) := by
  obtain ⟨ha, ha1, hrel⟩ := square_root_parameter P.μ_pos P.strong_convexity_le_smoothness
  apply potential_contraction (P.tiltedLower x t a) (fun y => P.gy x y + t • a)
    (P.μ_pos.trans_le P.strong_convexity_le_smoothness) P.μ_pos ha.le ha1 hrel
    (P.tilted_hasGradientAt x t a) _ (P.tilted_strong_convex x t a)
  intro y z
  simpa only [add_sub_add_right_eq_sub] using P.gy_lipschitz_y x y z

theorem tilted_noisy_accelerated_potential (x : X) (t : ℝ) (a u v ys ξ : Y) :
    let α := Real.sqrt (μ / Lg)
    let w := query α u v
    let grad := fun y => P.gy x y + t • a
    potential (P.tiltedLower x t a) μ ys
        (nextU Lg w (grad w + ξ)) (nextV μ α v w (grad w + ξ)) ≤
      (1 - α) * potential (P.tiltedLower x t a) μ ys u v -
        Lg⁻¹ * ⟪grad (nextU Lg w (grad w)), ξ⟫ -
        α * ⟪nextV μ α v w (grad w) - ys, ξ⟫ + Lg⁻¹ * ‖ξ‖ ^ 2 := by
  obtain ⟨ha, ha1, hrel⟩ := square_root_parameter P.μ_pos P.strong_convexity_le_smoothness
  apply noisy_potential_bound (P.tiltedLower x t a) (fun y => P.gy x y + t • a)
    (P.μ_pos.trans_le P.strong_convexity_le_smoothness) P.μ_pos ha.le ha1 hrel
    (P.tilted_hasGradientAt x t a) _ (P.tilted_strong_convex x t a)
  intro y z
  simpa only [add_sub_add_right_eq_sub] using P.gy_lipschitz_y x y z

end Bilevel.Model.Primitive
