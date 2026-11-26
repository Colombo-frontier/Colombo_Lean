import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.Module
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

/-! # The local estimate sequence for convex-until-proven-guilty AGD

This is the genuine accelerated recurrence with its actual gradient. The
convexity inequalities are needed only at the finitely many tested pairs.
No global convexity, optimizer, or convergence theorem is assumed.
-/

noncomputable section
open scoped InnerProductSpace

namespace MatchingBounds1005.CUPG

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

structure EstimateState (E : Type*) where
  point : E
  center : E
  minimum : ℝ

def query (q : ℝ) (s : EstimateState E) : E := (1 + q)⁻¹ • (s.point + q • s.center)

def potential (μ : ℝ) (s : EstimateState E) (z : E) : ℝ :=
  s.minimum + μ / 2 * ‖z - s.center‖ ^ 2

def nextCenter (q μ : ℝ) (v x g : E) : E :=
  (1 - q) • v + q • x - (q / μ) • g

def nextMinimum (q μ m fx : ℝ) (v x g : E) : ℝ :=
  (1 - q) * m + q * fx - q ^ 2 / (2 * μ) * ‖g‖ ^ 2 +
    μ * q * (1 - q) / 2 * ‖v - x‖ ^ 2 + q * (1 - q) * ⟪g, v - x⟫_ℝ

def estimateStep (f : E → ℝ) (q μ : ℝ) (s : EstimateState E) : EstimateState E :=
  let x := query q s
  let g := gradient f x
  ⟨x - (q ^ 2 / μ) • g, nextCenter q μ s.center x g,
    nextMinimum q μ s.minimum (f x) s.center x g⟩

def estimateRun (f : E → ℝ) (q μ : ℝ) (start : E) : ℕ → EstimateState E
  | 0 => ⟨start, start, f start⟩
  | n + 1 => estimateStep f q μ (estimateRun f q μ start n)

def LocalConvex (f : E → ℝ) (μ : ℝ) (x y : E) : Prop :=
  f x + ⟪gradient f x, y - x⟫_ℝ + μ / 2 * ‖y - x‖ ^ 2 ≤ f y

/-- This upper Taylor inequality is the only smoothness input used by AGD. -/
def SmoothUpper (f : E → ℝ) (L : ℝ) : Prop :=
  ∀ x y, f y ≤ f x + ⟪gradient f x, y - x⟫_ℝ + L / 2 * ‖y - x‖ ^ 2

omit [CompleteSpace E] in
theorem query_relation {q : ℝ} (hq : 0 ≤ q) (s : EstimateState E) :
    q • (s.center - query q s) = query q s - s.point := by
  have hn : 1 + q ≠ 0 := by linarith
  unfold query
  match_scalars <;> field_simp [hn]

omit [CompleteSpace E] in
/-- Exact completion of the square for the updated estimate function. -/
theorem potential_update {q μ : ℝ} (hμ : μ ≠ 0) (m fx : ℝ) (v x g z : E) :
    nextMinimum q μ m fx v x g + μ / 2 * ‖z - nextCenter q μ v x g‖ ^ 2 =
      (1 - q) * (m + μ / 2 * ‖z - v‖ ^ 2) +
        q * (fx + ⟪g, z - x⟫_ℝ + μ / 2 * ‖z - x‖ ^ 2) := by
  unfold nextMinimum nextCenter
  simp only [← real_inner_self_eq_norm_sq, inner_sub_left, inner_sub_right,
    inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right]
  simp only [real_inner_comm]
  field_simp [hμ]
  ring

theorem potential_step (f : E → ℝ) {q μ : ℝ} (hμ : μ ≠ 0) (s : EstimateState E) (z : E) :
    potential μ (estimateStep f q μ s) z =
      (1 - q) * potential μ s z + q *
        (f (query q s) + ⟪gradient f (query q s), z - query q s⟫_ℝ +
          μ / 2 * ‖z - query q s‖ ^ 2) :=
  potential_update hμ s.minimum (f (query q s)) s.center (query q s) (gradient f (query q s)) z

theorem smooth_gradient_step (f : E → ℝ) {q μ L : ℝ}
    (hμ : 0 < μ) (hscale : L * q ^ 2 = μ)
    (hsm : SmoothUpper f L) (x : E) :
    f (x - (q ^ 2 / μ) • gradient f x) ≤
      f x - q ^ 2 / (2 * μ) * ‖gradient f x‖ ^ 2 := by
  have hη : 0 ≤ q ^ 2 / μ := by positivity
  have hs := hsm x (x - (q ^ 2 / μ) • gradient f x)
  have hd : x - (q ^ 2 / μ) • gradient f x - x = -((q ^ 2 / μ) • gradient f x) := by abel
  rw [hd, inner_neg_right, real_inner_smul_right, real_inner_self_eq_norm_sq,
    norm_neg, norm_smul, Real.norm_eq_abs, abs_of_nonneg hη] at hs
  have he : -(q ^ 2 / μ) + L / 2 * (q ^ 2 / μ) ^ 2 = -(q ^ 2 / (2 * μ)) := by
    field_simp [hμ.ne']
    rw [← hscale]
    ring
  calc
    _ ≤ f x + (-(q ^ 2 / μ) + L / 2 * (q ^ 2 / μ) ^ 2) * ‖gradient f x‖ ^ 2 := by
      convert hs using 1; ring
    _ = _ := by rw [he]; ring

/-- The actual next point lies below the minimum of the next quadratic
estimate whenever the single tested pair `(x,y)` passes convexity. -/
theorem step_below_minimum (f : E → ℝ) {q μ L : ℝ}
    (hq : 0 ≤ q) (hqone : q ≤ 1) (hμ : 0 < μ) (hscale : L * q ^ 2 = μ)
    (hsm : SmoothUpper f L) (s : EstimateState E)
    (hm : f s.point ≤ s.minimum) (hc : LocalConvex f μ (query q s) s.point) :
    f (estimateStep f q μ s).point ≤ (estimateStep f q μ s).minimum := by
  let x := query q s
  let g := gradient f x
  have hd := smooth_gradient_step f hμ hscale hsm x
  change f (x - (q ^ 2 / μ) • g) ≤ f x - q ^ 2 / (2 * μ) * ‖g‖ ^ 2 at hd
  have hr := congrArg (fun v => ⟪g, v⟫_ℝ) (query_relation hq s)
  dsimp only at hr
  rw [real_inner_smul_right] at hr
  change q * ⟪g, s.center - x⟫_ℝ = ⟪g, x - s.point⟫_ℝ at hr
  have hlocal : f x + ⟪g, s.point - x⟫_ℝ ≤ f s.point := by
    have hp : 0 ≤ μ / 2 * ‖s.point - x‖ ^ 2 := by positivity
    exact (le_add_of_nonneg_right hp).trans hc
  have hneg : ⟪g, s.point - x⟫_ℝ = -⟪g, x - s.point⟫_ℝ := by
    rw [← inner_neg_right, neg_sub]
  rw [hneg] at hlocal
  have hm' := mul_le_mul_of_nonneg_left hm (sub_nonneg.mpr hqone)
  have hc' := mul_le_mul_of_nonneg_left hlocal (sub_nonneg.mpr hqone)
  have hr' := congrArg (fun r : ℝ => (1 - q) * r) hr
  dsimp only at hr'
  have hrem : 0 ≤ 1 - q := sub_nonneg.mpr hqone
  have hp : 0 ≤ μ * q * (1 - q) / 2 * ‖s.center - x‖ ^ 2 := by positivity
  change f (x - (q ^ 2 / μ) • g) ≤ nextMinimum q μ s.minimum (f x) s.center x g
  unfold nextMinimum
  nlinarith only [hd, hm', hc', hr', hp]

theorem run_below_minimum (f : E → ℝ) {q μ L : ℝ}
    (hq : 0 ≤ q) (hqone : q ≤ 1) (hμ : 0 < μ) (hscale : L * q ^ 2 = μ)
    (hsm : SmoothUpper f L) (start : E) (n : ℕ)
    (hc : ∀ j < n, LocalConvex f μ (query q (estimateRun f q μ start j))
      (estimateRun f q μ start j).point) :
    f (estimateRun f q μ start n).point ≤ (estimateRun f q μ start n).minimum := by
  induction n with
  | zero => exact le_rfl
  | succ n ih =>
    exact step_below_minimum f hq hqone hμ hscale hsm _
      (ih (fun j hj => hc j (Nat.lt_trans hj (Nat.lt_succ_self n)))) (hc n (Nat.lt_succ_self n))

theorem potential_comparison (f : E → ℝ) {q μ : ℝ}
    (hq : 0 ≤ q) (hqone : q ≤ 1) (hμ : μ ≠ 0) (start w : E) (n : ℕ)
    (hc : ∀ j < n, LocalConvex f μ (query q (estimateRun f q μ start j)) w) :
    potential μ (estimateRun f q μ start n) w ≤
      f w + (1 - q) ^ n * (f start - f w + μ / 2 * ‖w - start‖ ^ 2) := by
  induction n with
  | zero => simp [estimateRun, potential]; ring_nf; exact le_rfl
  | succ n ih =>
    have hi := mul_le_mul_of_nonneg_left
      (ih (fun j hj => hc j (Nat.lt_trans hj (Nat.lt_succ_self n)))) (sub_nonneg.mpr hqone)
    have hj := mul_le_mul_of_nonneg_left (hc n (Nat.lt_succ_self n)) hq
    change potential μ (estimateStep f q μ (estimateRun f q μ start n)) w ≤ _
    rw [potential_step f hμ, pow_succ (1 - q) n]
    change q * (f (query q (estimateRun f q μ start n)) +
      ⟪gradient f (query q (estimateRun f q μ start n)), w - query q (estimateRun f q μ start n)⟫_ℝ +
      μ / 2 * ‖w - query q (estimateRun f q μ start n)‖ ^ 2) ≤ q * f w at hj
    nlinarith only [hi, hj]

/-- Carmon et al.'s local-convexity estimate, derived from the recurrence.
It permits the contrapositive witness search used by AGD-until-guilty. -/
theorem local_accelerated_estimate (f : E → ℝ) {q μ L : ℝ}
    (hq : 0 ≤ q) (hqone : q ≤ 1) (hμ : 0 < μ) (hscale : L * q ^ 2 = μ)
    (hsm : SmoothUpper f L) (start w : E) (n : ℕ)
    (hy : ∀ j < n, LocalConvex f μ (query q (estimateRun f q μ start j))
      (estimateRun f q μ start j).point)
    (hw : ∀ j < n, LocalConvex f μ (query q (estimateRun f q μ start j)) w) :
    f (estimateRun f q μ start n).point - f w ≤
      (1 - q) ^ n * (f start - f w + μ / 2 * ‖w - start‖ ^ 2) := by
  have hm := run_below_minimum f hq hqone hμ hscale hsm start n hy
  have hp := potential_comparison f hq hqone hμ.ne' start w n hw
  have hn : 0 ≤ μ / 2 * ‖w - (estimateRun f q μ start n).center‖ ^ 2 := by positivity
  unfold potential at hp
  linarith

/-- The estimate-state implementation is the ordinary two-point accelerated
recurrence, with momentum `(1-q)/(1+q)`. -/
theorem query_step_extrapolate (f : E → ℝ) {q μ : ℝ} (hq : 0 ≤ q) (hμ : μ ≠ 0)
    (s : EstimateState E) :
    query q (estimateStep f q μ s) = (estimateStep f q μ s).point +
      ((1 - q) / (1 + q)) • ((estimateStep f q μ s).point - s.point) := by
  have hn : 1 + q ≠ 0 := by linarith
  dsimp only [query, estimateStep, nextCenter]
  match_scalars <;> field_simp [hn, hμ] <;> ring

theorem query_run_zero (f : E → ℝ) {q μ : ℝ} (hq : 0 ≤ q) (start : E) :
    query q (estimateRun f q μ start 0) = start := by
  have hn : 1 + q ≠ 0 := by linarith
  dsimp only [query, estimateRun]
  match_scalars <;> field_simp [hn]

end MatchingBounds1005.CUPG
