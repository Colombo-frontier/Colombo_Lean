import MatchingBounds1005.CUPGEstimate
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! # Finite convexity witnesses and the genuine accelerated progress monitor -/
noncomputable section
open scoped InnerProductSpace

namespace MatchingBounds1005.CUPG
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

def descentPoint (f : E → ℝ) (q μ : ℝ) (y : E) : E := y - (q ^ 2 / μ) • gradient f y

def progressGap (f : E → ℝ) (μ : ℝ) (start z : E) : ℝ :=
  f start - f z + μ / 2 * ‖z - start‖ ^ 2

def ProgressPass (f : E → ℝ) (q μ L : ℝ) (start : E) (n : ℕ) : Prop :=
  let y := (estimateRun f q μ start n).point
  let z := descentPoint f q μ y
  f y ≤ f start ∧ ‖gradient f y‖ ^ 2 ≤
    2 * L * progressGap f μ start z * Real.exp (-q * n)

def Stopped (f : E → ℝ) (q μ L δ : ℝ) (start : E) (n : ℕ) : Prop :=
  ¬ ProgressPass f q μ L start n ∨ ‖gradient f (estimateRun f q μ start n).point‖ ≤ δ

theorem contraction_le_exp {q : ℝ} (hqone : q ≤ 1) (n : ℕ) :
    (1 - q) ^ n ≤ Real.exp (-q * n) := by
  have h := pow_le_pow_left₀ (sub_nonneg.mpr hqone)
    (show 1 - q ≤ Real.exp (-q) by linarith [Real.add_one_le_exp (-q)]) n
  simpa only [← Real.exp_nat_mul, mul_comm (n : ℝ) (-q)] using h

theorem descent_decrease (f : E → ℝ) {q μ L : ℝ}
    (hμ : 0 < μ) (hscale : L * q ^ 2 = μ) (hsm : SmoothUpper f L) (y : E) :
    f (descentPoint f q μ y) ≤ f y :=
  (smooth_gradient_step f hμ hscale hsm y).trans (sub_le_self _ (by positivity))

theorem descent_gradient_bound (f : E → ℝ) {q μ L : ℝ}
    (hμ : 0 < μ) (hscale : L * q ^ 2 = μ)
    (hsm : SmoothUpper f L) (y : E) :
    ‖gradient f y‖ ^ 2 ≤ 2 * L * (f y - f (descentPoint f q μ y)) := by
  have hL : 0 < L := by nlinarith [sq_nonneg q]
  have hd := smooth_gradient_step f hμ hscale hsm y
  change f (descentPoint f q μ y) ≤ f y - q ^ 2 / (2 * μ) * ‖gradient f y‖ ^ 2 at hd
  have he : (2 * L) * (q ^ 2 / (2 * μ)) = 1 := by field_simp; nlinarith [hscale]
  have hm := mul_le_mul_of_nonneg_left hd (show 0 ≤ 2 * L by positivity)
  have hm' := congrArg (fun r : ℝ => r * ‖gradient f y‖ ^ 2) he
  nlinarith only [hm, hm']

/-- A violated progress test yields a genuine finite first-order convexity
certificate among the stored iterates and one computable monitor point. -/
theorem progress_failure_witness (f : E → ℝ) {q μ L : ℝ}
    (hq : 0 < q) (hqone : q ≤ 1) (hμ : 0 < μ) (hscale : L * q ^ 2 = μ)
    (hsm : SmoothUpper f L) (start : E) (n : ℕ)
    (hfail : ¬ ProgressPass f q μ L start n) :
    ∃ j < n, ∃ u : E,
      (u = (estimateRun f q μ start j).point ∨
        u = start ∨ u = descentPoint f q μ (estimateRun f q μ start n).point) ∧
      ¬ LocalConvex f μ (query q (estimateRun f q μ start j)) u := by
  by_contra hn
  push_neg at hn
  have hy : ∀ j < n, LocalConvex f μ (query q (estimateRun f q μ start j))
      (estimateRun f q μ start j).point := by
    intro j hj
    exact hn j hj _ (Or.inl rfl)
  have hw (w : E) (hw : w = start ∨ w = descentPoint f q μ (estimateRun f q μ start n).point) :
      f (estimateRun f q μ start n).point - f w ≤
        (1 - q) ^ n * progressGap f μ start w := by
    exact local_accelerated_estimate f hq.le hqone hμ hscale hsm start w n hy
      (fun j hj => hn j hj w (Or.inr hw))
  have hv := hw start (Or.inl rfl)
  have hv' : f (estimateRun f q μ start n).point ≤ f start := by
    simpa [progressGap] using hv
  have hz := hw (descentPoint f q μ (estimateRun f q μ start n).point) (Or.inr rfl)
  have hgap : 0 ≤ progressGap f μ start (descentPoint f q μ (estimateRun f q μ start n).point) := by
    have hd := descent_decrease f hμ hscale hsm (estimateRun f q μ start n).point
    unfold progressGap
    have hp : 0 ≤ μ / 2 * ‖descentPoint f q μ (estimateRun f q μ start n).point - start‖ ^ 2 := by positivity
    linarith
  have hg := descent_gradient_bound f hμ hscale hsm (estimateRun f q μ start n).point
  have hL : 0 < L := by nlinarith [sq_pos_of_pos hq]
  have hz' := mul_le_mul_of_nonneg_left hz (show 0 ≤ 2 * L by positivity)
  have he := mul_le_mul_of_nonneg_left (contraction_le_exp hqone n)
    (show 0 ≤ 2 * L * progressGap f μ start
      (descentPoint f q μ (estimateRun f q μ start n).point) by positivity)
  apply hfail
  refine ⟨hv', ?_⟩
  dsimp only
  nlinarith only [hg, hz', he]

/-- A prescribed finite cap forces either a small actual gradient or a
violated test. Only an upper bound on the initial gap is needed. -/
theorem stopped_at_cap (f : E → ℝ) {q μ L δ Δ : ℝ}
    (hδ : 0 ≤ δ) (hL : 0 ≤ L) (start : E) (N : ℕ)
    (hgap : progressGap f μ start
      (descentPoint f q μ (estimateRun f q μ start N).point) ≤ Δ)
    (hcap : 2 * L * Δ * Real.exp (-q * N) ≤ δ ^ 2) :
    Stopped f q μ L δ start N := by
  by_cases hp : ProgressPass f q μ L start N
  · refine Or.inr ?_
    have hh := hp.2
    have hm := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hgap (by positivity : 0 ≤ 2 * L))
      (Real.exp_nonneg (-q * N))
    have hs : ‖gradient f (estimateRun f q μ start N).point‖ ^ 2 ≤ δ ^ 2 := hh.trans (hm.trans hcap)
    nlinarith [norm_nonneg (gradient f (estimateRun f q μ start N).point)]
  · exact Or.inl hp

/-- The first stopping index is a finite search over the actual run. -/
theorem first_stop_exists (f : E → ℝ) (q μ L δ : ℝ) (start : E) (N : ℕ)
    (hstop : Stopped f q μ L δ start N) :
    ∃ n ≤ N, Stopped f q μ L δ start n ∧
      ∀ j < n, ¬ Stopped f q μ L δ start j := by
  classical
  let he : ∃ n, Stopped f q μ L δ start n := ⟨N, hstop⟩
  exact ⟨Nat.find he, Nat.find_min' he hstop, Nat.find_spec he,
    fun j hj => Nat.find_min he hj⟩

end MatchingBounds1005.CUPG
