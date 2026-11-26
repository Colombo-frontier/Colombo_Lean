import GradientHessian.HigherHierarchyFunctions
import GradientHessian.HierarchyCoercivity

/-! The actual positive common memory baseline, with numerical coefficient
one half. Its finite-height coercivity follows from its explicit formula. -/

noncomputable section
namespace GradientHessian.HigherHierarchy
universe u
open InnerCoordinates HierarchyCoercivity Filter Bornology

variable {Y E : Type u} {H : ℕ → Type u} {m : ℕ}
variable [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [∀ t, NormedAddCommGroup (H t)] [∀ t, InnerProductSpace ℝ (H t)]

def positiveBaseline (K : ℝ) : (t : ℕ) → Space Y E H m t → ℝ
  | 0 => firstEnergy m
  | t+1 => nodeBaseline (positiveBaseline K t) (radius m K t)

def positiveOffset (m : ℕ) (K : ℝ) : ℕ → ℝ
  | 0 => firstCoefficient m
  | t+1 => positiveOffset m K t + 128 * radius m K t

theorem firstEnergy_le_baseline (Z : FirstHeight.SourceSpace Y E m) :
    firstEnergy m Z ≤ FirstHeight.sourceBaseline m Z := by
  unfold firstEnergy FirstHeight.sourceBaseline FirstHeight.baseline Leaf.publicQuadratic
  have hM : (1:ℝ) ≤ m+1 := by exact_mod_cast (show 1≤m+1 by omega)
  have hn := sq_nonneg ‖numerical Y E (m+1) (Inner.absoluteDepth+2)
    (numerical (Leaf.Space Y E (m+1)) E 8 (FirstHeight.depth (m+1)+2) Z)‖
  push_cast
  nlinarith

theorem positiveBaseline_le_baseline (K : ℝ) :
    ∀ t (Z : Space Y E H m t), positiveBaseline K t Z ≤ baseline K t Z := by
  intro t
  induction t with
  | zero => exact firstEnergy_le_baseline
  | succ t ih =>
    intro Z
    change nodeBaseline (positiveBaseline K t) (radius m K t) Z ≤
      nodeBaseline (baseline K t) (radius m K t) Z
    unfold nodeBaseline
    exact add_le_add_right (ih _) _

theorem radius_nonneg (m : ℕ) {K : ℝ} (hK : 0≤K) (t : ℕ) : 0≤radius m K t :=
  mul_nonneg (mul_nonneg hK (baseRadius_pos m).le) (by positivity)

theorem positiveBaseline_nonneg {K : ℝ} (hK : 0≤K) :
    ∀ t (Z : Space Y E H m t), 0≤positiveBaseline K t Z := by
  intro t
  induction t with
  | zero =>
    intro Z
    exact (mul_nonneg (firstCoefficient_pos m).le (sq_nonneg ‖Z‖)).trans
      (firstEnergy_quadratic_lower m Z)
  | succ t ih =>
    intro Z
    change 0 ≤ nodeBaseline (positiveBaseline K t) (radius m K t) Z
    unfold nodeBaseline
    exact add_nonneg (ih _) (Finset.sum_nonneg fun i _ => Localized.publicPotential_nonneg (radius_nonneg m hK t) _)

theorem baseline_nonneg {K : ℝ} (hK : 0≤K) (t : ℕ) (Z : Space Y E H m t) :
    0≤baseline K t Z := (positiveBaseline_nonneg hK t Z).trans (positiveBaseline_le_baseline K t Z)

theorem positiveBaseline_linear_lower (K : ℝ) :
    ∀ t (Z : Space Y E H m t), firstCoefficient m * ‖Z‖ - positiveOffset m K t ≤ positiveBaseline K t Z := by
  intro t
  induction t with
  | zero => exact firstEnergy_linear_lower m
  | succ t ih =>
    intro Z
    have h := extension_linear_lower (positiveBaseline K t) (radius m K t)
      (firstCoefficient m) (positiveOffset m K t) (firstCoefficient_pos m).le
      (le_trans (firstCoefficient_le_half m) (by norm_num : (1/2:ℝ)≤16)) ih Z
    simpa only [positiveBaseline, positiveOffset, extension, nodeBaseline,
      lower_apply, parent_apply, Nat.cast_ofNat, show (16:ℝ)*8=128 by norm_num] using h

theorem positiveBaseline_coercive (K : ℝ) (t : ℕ) :
    Tendsto (positiveBaseline K t : Space Y E H m t → ℝ) (cobounded _) atTop :=
  coercive_of_linear_lower (firstCoefficient_pos m) (positiveBaseline_linear_lower K t)

theorem baseline_coercive (K : ℝ) (t : ℕ) :
    Tendsto (baseline K t : Space Y E H m t → ℝ) (cobounded _) atTop :=
  coercive_of_linear_lower (firstCoefficient_pos m)
    (fun Z => (positiveBaseline_linear_lower K t Z).trans (positiveBaseline_le_baseline K t Z))

theorem firstEnergy_zero : firstEnergy m (0 : FirstHeight.SourceSpace Y E m) = 0 := by
  simp [firstEnergy, Inner.publicQuadratic, LatchChain.publicQuadratic]

theorem firstBaseline_zero : FirstHeight.sourceBaseline m (0 : FirstHeight.SourceSpace Y E m) = 0 := by
  simp [FirstHeight.sourceBaseline, FirstHeight.baseline, Leaf.publicQuadratic,
    Inner.publicQuadratic, LatchChain.publicQuadratic]

theorem nodeBaseline_zero (Q : Y → ℝ) {R : ℝ} (hR : 0≤R) (hQ : Q 0=0) :
    nodeBaseline (E := E) Q R 0 = 0 := by
  simp [nodeBaseline, hQ, Localized.publicPotential_zero hR]

theorem positiveBaseline_zero {K : ℝ} (hK : 0≤K) :
    ∀ t, positiveBaseline K t (0 : Space Y E H m t) = 0 := by
  intro t
  induction t with
  | zero => exact firstEnergy_zero
  | succ t ih => exact nodeBaseline_zero _ (radius_nonneg m hK t) ih

theorem baseline_zero {K : ℝ} (hK : 0≤K) :
    ∀ t, baseline K t (0 : Space Y E H m t) = 0 := by
  intro t
  induction t with
  | zero => exact firstBaseline_zero
  | succ t ih => exact nodeBaseline_zero _ (radius_nonneg m hK t) ih

end GradientHessian.HigherHierarchy
