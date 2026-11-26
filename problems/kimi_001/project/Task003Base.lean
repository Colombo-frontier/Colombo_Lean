import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Real
import Mathlib
import Mathlib.Probability.ConditionalProbability
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.InformationTheory.KullbackLeibler.ChainRule
import Mathlib.Probability.Kernel.CompProdEqIff
import Mathlib.InformationTheory.KullbackLeibler.Basic
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.Distributions.Exponential
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Probability.Moments.Variance
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence
import Mathlib.Probability.Kernel.Disintegration.Unique
import Mathlib.Probability.Kernel.Composition.Prod
import Mathlib.Probability.Kernel.Composition.Lemmas

-- BEGIN Composition.lean
section

/-!
Conditional real-algebra audit of manuscript §7, lines 399–445.

This file proves the logarithmic comparisons, precision split, and algebraic
composition of the two lower bounds with a supplied upper bound. It does NOT
formalize the minimax/oracle model, regional lower-bound theorem, hidden-spike
corollary, upper-bound algorithms, or normalization. The eventual threshold
existence claimed in (18) is proved below using Mathlib's logarithmic limits.
Those analytic and oracle claims remain explicit hypotheses below. In particular,
`N` is an arbitrary real-valued quantity supplied by the caller, not a replacement
formal definition of the manuscript's minimax quantity.
-/

namespace CompositionAudit

open Filter
open scoped Topology

noncomputable def A (α : ℝ) : ℝ := α⁻¹
noncomputable def M (d α : ℝ) : ℝ := min d (A α ^ 2)
noncomputable def q (d α : ℝ) : ℝ := d * M d α
noncomputable def ell (d : ℝ) : ℝ := Real.log (Real.exp 1 * d)
noncomputable def Lambda (d α : ℝ) : ℝ := ell d + Real.log (Real.exp 1 / α)
noncomputable def tau (d cd : ℝ) : ℝ := cd / Real.sqrt (ell d)
noncomputable def lowerConstant (c c1 cd : ℝ) : ℝ := min (c / 2) (c1 * cd ^ 2)

lemma log_e_mul {x : ℝ} (hx : 0 < x) :
    Real.log (Real.exp 1 * x) = 1 + Real.log x := by
  rw [Real.log_mul (ne_of_gt (Real.exp_pos 1)) (ne_of_gt hx), Real.log_exp]

lemma log_e_div {α : ℝ} (hα : 0 < α) :
    Real.log (Real.exp 1 / α) = 1 + Real.log (A α) := by
  rw [div_eq_mul_inv, log_e_mul (inv_pos.mpr hα)]
  rfl

/-- The two growth inequalities explicitly imply manuscript (18). -/
lemma threshold_of_growth_bounds {d cd c0 : ℝ}
    (hd : 1 ≤ d) (hcd : 0 < cd) (hc0 : 0 < c0)
    (hlinear : ell d ≤ cd ^ 2 * d) (hlarge : (cd / c0) ^ 2 < ell d) :
    (Real.sqrt d)⁻¹ ≤ tau d cd ∧ tau d cd < c0 := by
  have hdpos : 0 < d := by linarith
  have he : 0 < ell d := lt_of_le_of_lt (sq_nonneg _) hlarge
  have hsd : 0 < Real.sqrt d := Real.sqrt_pos.2 hdpos
  have hse : 0 < Real.sqrt (ell d) := Real.sqrt_pos.2 he
  have hrootsq : (cd * Real.sqrt d) ^ 2 = cd ^ 2 * d := by
    rw [mul_pow, Real.sq_sqrt (le_of_lt hdpos)]
  have hroot : Real.sqrt (ell d) ≤ cd * Real.sqrt d := by
    have hnonneg := mul_pos hcd hsd
    nlinarith [Real.sq_sqrt (le_of_lt he)]
  have hratio : cd / c0 < Real.sqrt (ell d) := by
    have hratpos := div_pos hcd hc0
    nlinarith [Real.sq_sqrt (le_of_lt he)]
  constructor
  · apply (le_div_iff₀ hse).2
    calc
      (Real.sqrt d)⁻¹ * Real.sqrt (ell d) ≤
          (Real.sqrt d)⁻¹ * (cd * Real.sqrt d) :=
        mul_le_mul_of_nonneg_left hroot (le_of_lt (inv_pos.mpr hsd))
      _ = cd := by field_simp
  · apply (div_lt_iff₀ hse).2
    have := (div_lt_iff₀ hc0).1 hratio
    linarith

/-- The actual existence assertion (18), for arbitrary positive fixed constants.
It uses log(d)/d → 0 and log(d) → ∞, rather than assuming a threshold. -/
theorem eventual_threshold (cd c0 : ℝ) (hcd : 0 < cd) (hc0 : 0 < c0) :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ d, D ≤ d →
      (Real.sqrt d)⁻¹ ≤ tau d cd ∧ tau d cd < c0 := by
  have hlogratio : Tendsto (fun d : ℝ => Real.log d / d) atTop (𝓝 0) := by
    simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
  have honeratio : Tendsto (fun d : ℝ => (1 : ℝ) / d) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  have hellratio : Tendsto (fun d : ℝ => ell d / d) atTop (𝓝 0) := by
    have hsum : Tendsto (fun d : ℝ => 1 / d + Real.log d / d) atTop (𝓝 0) := by
      simpa using honeratio.add hlogratio
    apply Tendsto.congr' _ hsum
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with d hd
    rw [show ell d = 1 + Real.log d from log_e_mul hd, add_div]
  have hsmall : ∀ᶠ d : ℝ in atTop, ell d / d < cd ^ 2 :=
    hellratio.eventually (gt_mem_nhds (sq_pos_of_pos hcd))
  have hlarge : ∀ᶠ d : ℝ in atTop, (cd / c0) ^ 2 < Real.log d :=
    Real.tendsto_log_atTop.eventually (eventually_gt_atTop _)
  obtain ⟨D, hD⟩ := eventually_atTop.1
    ((eventually_ge_atTop (1 : ℝ)).and (hsmall.and hlarge))
  refine ⟨max 1 D, le_max_left _ _, ?_⟩
  intro d hd
  obtain ⟨hd1, hsmall, hlarge⟩ := hD d ((le_max_right 1 D).trans hd)
  have hdpos : 0 < d := by linarith
  apply threshold_of_growth_bounds hd1 hcd hc0
  · exact le_of_lt ((div_lt_iff₀ hdpos).1 hsmall)
  · rw [show ell d = 1 + Real.log d from log_e_mul hdpos]
    linarith

lemma log_comparisons {d α : ℝ} (hd : 1 ≤ d) (hα : 0 < α) (hα1 : α ≤ 1) :
    0 < ell d ∧ 0 < Real.log (Real.exp 1 * M d α) ∧
    0 < Lambda d α ∧ ell d ≤ Lambda d α ∧
    Real.log (Real.exp 1 * M d α) ≤ 2 * Lambda d α := by
  have hdpos : 0 < d := by linarith
  have ha : 1 ≤ A α := by
    dsimp [A]
    exact (one_le_inv₀ hα).2 hα1
  have hasq : 1 ≤ A α ^ 2 := by nlinarith
  have hm : 1 ≤ M d α := le_min hd hasq
  have hmpos : 0 < M d α := by linarith
  have hlogd : 0 ≤ Real.log d := Real.log_nonneg hd
  have hloga : 0 ≤ Real.log (A α) := Real.log_nonneg ha
  have hlogm : 0 ≤ Real.log (M d α) := Real.log_nonneg hm
  have hma : Real.log (M d α) ≤ 2 * Real.log (A α) := by
    calc
      Real.log (M d α) ≤ Real.log (A α ^ 2) :=
        Real.log_le_log hmpos (min_le_right _ _)
      _ = 2 * Real.log (A α) := by rw [Real.log_pow]; norm_num
  have he : ell d = 1 + Real.log d := log_e_mul hdpos
  have hl : Lambda d α = ell d + (1 + Real.log (A α)) := by
    dsimp [Lambda]
    rw [log_e_div hα]
  have hem : Real.log (Real.exp 1 * M d α) = 1 + Real.log (M d α) :=
    log_e_mul hmpos
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

lemma q_nonneg {d α : ℝ} (hd : 0 ≤ d) : 0 ≤ q d α := by
  exact mul_nonneg hd (le_min hd (sq_nonneg _))

/-- The precision split asserted in §7: above d^(-1/2), M = α^(-2). -/
lemma coarse_precision_split {d α : ℝ} (hd : 0 < d) (hα : 0 < α)
    (hcoarse : (Real.sqrt d)⁻¹ < α) :
    A α ^ 2 < d ∧ M d α = A α ^ 2 ∧ q d α = d * A α ^ 2 := by
  have hs : 0 < Real.sqrt d := Real.sqrt_pos.2 hd
  have ha : A α < Real.sqrt d := by
    dsimp [A]
    exact (inv_lt_comm₀ hα hs).2 hcoarse
  have hap : 0 < A α := inv_pos.mpr hα
  have hsq : A α ^ 2 < d := by
    nlinarith [Real.sq_sqrt (le_of_lt hd)]
  exact ⟨hsq, min_eq_right (le_of_lt hsq), by
    dsimp [q, M]
    rw [min_eq_right (le_of_lt hsq)]⟩

/-- The other half of the precision split, including equality at the boundary. -/
lemma plateau_precision_split {d α : ℝ} (hd : 0 < d) (hα : 0 < α)
    (hfine : α ≤ (Real.sqrt d)⁻¹) :
    d ≤ A α ^ 2 ∧ M d α = d ∧ q d α = d ^ 2 := by
  have hs : 0 < Real.sqrt d := Real.sqrt_pos.2 hd
  have ha : Real.sqrt d ≤ A α := by
    dsimp [A]
    exact (le_inv_comm₀ hs hα).2 hfine
  have hsq : d ≤ A α ^ 2 := by
    nlinarith [Real.sq_sqrt (le_of_lt hd), Real.sqrt_nonneg d]
  exact ⟨hsq, min_eq_left hsq, by dsimp [q, M]; rw [min_eq_left hsq]; ring⟩

/-- The threshold inequality α > c_diamond / sqrt(ell) implies (20)'s
A² c_diamond² < ell. This is proved, rather than assumed as a regional premise. -/
lemma above_tau_inverse_square {d α cd : ℝ} (he : 0 < ell d)
    (hα : 0 < α) (hcd : 0 < cd) (habove : tau d cd < α) :
    A α ^ 2 * cd ^ 2 < ell d := by
  have hs : 0 < Real.sqrt (ell d) := Real.sqrt_pos.2 he
  have hmul : cd < α * Real.sqrt (ell d) := (div_lt_iff₀ hs).1 habove
  have hrecip : A α * cd < Real.sqrt (ell d) := by
    dsimp [A]
    apply (inv_mul_lt_iff₀ hα).2
    nlinarith
  have hapos : 0 < A α := inv_pos.mpr hα
  nlinarith [Real.sq_sqrt (le_of_lt he), mul_pos hapos hcd]

/-- Equation (19), from the explicit regional lower-bound premise. -/
lemma regional_composition {d α c N : ℝ} (hd : 1 ≤ d) (hα : 0 < α)
    (hα1 : α ≤ 1) (hc : 0 < c)
    (hregional : c * q d α / (ell d * Real.log (Real.exp 1 * M d α)) ≤ N) :
    (c / 2) * q d α / Lambda d α ^ 2 ≤ N := by
  obtain ⟨he, hm, hl, hel, hml⟩ := log_comparisons hd hα hα1
  have hq := q_nonneg (α := α) (show 0 ≤ d by linarith)
  have hprod : ell d * Real.log (Real.exp 1 * M d α) ≤ 2 * Lambda d α ^ 2 := by
    calc
      ell d * Real.log (Real.exp 1 * M d α) ≤
          Lambda d α * (2 * Lambda d α) :=
        mul_le_mul hel hml (le_of_lt hm) (le_of_lt hl)
      _ = 2 * Lambda d α ^ 2 := by ring
  have hdiv := div_le_div_of_nonneg_left (mul_nonneg (le_of_lt hc) hq)
    (mul_pos he hm) hprod
  calc
    (c / 2) * q d α / Lambda d α ^ 2 = c * q d α / (2 * Lambda d α ^ 2) := by ring
    _ ≤ c * q d α / (ell d * Real.log (Real.exp 1 * M d α)) := hdiv
    _ ≤ N := hregional

/-- Equation (20), from the explicit spike lower-bound premise. -/
lemma spike_composition {d α cd c1 N : ℝ} (hd : 1 ≤ d) (hα : 0 < α)
    (hα1 : α ≤ 1) (hcd : 0 < cd) (hc1 : 0 < c1)
    (habove : tau d cd < α) (hspike : c1 * d / ell d ≤ N) :
    (c1 * cd ^ 2) * q d α / Lambda d α ^ 2 ≤ N := by
  obtain ⟨he, hm, hl, hel, hml⟩ := log_comparisons hd hα hα1
  have hq := q_nonneg (α := α) (show 0 ≤ d by linarith)
  have hbd := above_tau_inverse_square he hα hcd habove
  have hM : M d α * cd ^ 2 ≤ ell d := by
    exact le_trans (mul_le_mul_of_nonneg_right (min_le_right _ _) (sq_nonneg cd))
      (le_of_lt hbd)
  have hqbd : cd ^ 2 * q d α ≤ d * ell d := by
    have := mul_le_mul_of_nonneg_left hM (show 0 ≤ d by linarith)
    dsimp [q]
    nlinarith
  have hsq : ell d ^ 2 ≤ Lambda d α ^ 2 := by nlinarith
  have hfirst : (c1 * cd ^ 2) * q d α / Lambda d α ^ 2 ≤
      (c1 * cd ^ 2) * q d α / ell d ^ 2 :=
    div_le_div_of_nonneg_left
      (mul_nonneg (mul_nonneg (le_of_lt hc1) (sq_nonneg cd)) hq)
      (sq_pos_of_pos he) hsq
  have hsecond : (c1 * cd ^ 2) * q d α / ell d ^ 2 ≤ c1 * d / ell d := by
    apply (div_le_div_iff₀ (sq_pos_of_pos he) he).2
    have := mul_le_mul_of_nonneg_left hqbd (le_of_lt hc1)
    have := mul_le_mul_of_nonneg_right this (le_of_lt he)
    nlinarith
  exact hfirst.trans (hsecond.trans hspike)

/-- Theorem 1's final uniform constants, conditional on the precise regional,
spike and upper claims and on (18) at the supplied threshold. The same constants
work for every d and α in the authorized domain. No minimax theorem is assumed
under the name of this theorem: its three source inequalities are separate
explicit parameters. The source inequalities remain unresolved analytic/oracle
obligations; `eventual_threshold` proves the required threshold existence. -/
theorem full_domain_conditional_composition
    (N : ℝ → ℝ → ℝ) (D c0 c c1 cd b : ℝ)
    (hD : 1 ≤ D) (_hc0 : 0 < c0) (hc01 : c0 ≤ 1)
    (hc : 0 < c) (hc1 : 0 < c1) (hcd : 0 < cd) (hb : 0 < b)
    (hthreshold : ∀ d, D ≤ d → (Real.sqrt d)⁻¹ ≤ tau d cd ∧ tau d cd < c0)
    (hregional : ∀ d α, D ≤ d → 0 < α → α ≤ c0 → α ≤ tau d cd →
      c * q d α / (ell d * Real.log (Real.exp 1 * M d α)) ≤ N d α)
    (hspike : ∀ d α, D ≤ d → 0 < α → α ≤ c0 →
      c1 * d / ell d ≤ N d α)
    (hupper : ∀ d α, D ≤ d → 0 < α → α ≤ c0 →
      N d α ≤ b * q d α * Lambda d α ^ 2) :
    0 < lowerConstant c c1 cd ∧ 0 < b ∧
    ∀ d α, D ≤ d → 0 < α → α ≤ c0 →
      lowerConstant c c1 cd * q d α / Lambda d α ^ 2 ≤ N d α ∧
      N d α ≤ b * q d α * Lambda d α ^ 2 := by
  have hcmin : 0 < lowerConstant c c1 cd := by
    exact lt_min (div_pos hc (by norm_num)) (mul_pos hc1 (sq_pos_of_pos hcd))
  refine ⟨hcmin, hb, ?_⟩
  intro d α hd hα hα0
  have hd1 : 1 ≤ d := hD.trans hd
  have hα1 : α ≤ 1 := hα0.trans hc01
  have hq := q_nonneg (α := α) (show 0 ≤ d by linarith)
  have hl : 0 < Lambda d α := (log_comparisons hd1 hα hα1).2.2.1
  refine ⟨?_, hupper d α hd hα hα0⟩
  by_cases hregion : α ≤ tau d cd
  · have hbound := regional_composition hd1 hα hα1 hc (hregional d α hd hα hα0 hregion)
    apply le_trans _ hbound
    apply div_le_div_of_nonneg_right _ (sq_nonneg _)
    exact mul_le_mul_of_nonneg_right (min_le_left _ _) hq
  · have habove : tau d cd < α := lt_of_not_ge hregion
    -- This proves, with the supplied (18), the paper's M=A², q=dA² identities.
    have hcoarse := coarse_precision_split (show 0 < d by linarith) hα
      (lt_of_le_of_lt (hthreshold d hd).1 habove)
    have hbound := spike_composition hd1 hα hα1 hcd hc1 habove (hspike d α hd hα hα0)
    apply le_trans _ hbound
    apply div_le_div_of_nonneg_right _ (sq_nonneg _)
    exact mul_le_mul_of_nonneg_right (min_le_right _ _) hq

/-- The final assembly with a genuinely proved eventual threshold. Only the
three separate regional/spike/upper source inequalities remain hypotheses.
All constants are fixed before varying d and α. -/
theorem full_domain_eventual_composition
    (N : ℝ → ℝ → ℝ) (Dsource c0 c c1 cd b : ℝ)
    (hc0 : 0 < c0) (hc01 : c0 ≤ 1)
    (hc : 0 < c) (hc1 : 0 < c1) (hcd : 0 < cd) (hb : 0 < b)
    (hregional : ∀ d α, Dsource ≤ d → 0 < α → α ≤ c0 → α ≤ tau d cd →
      c * q d α / (ell d * Real.log (Real.exp 1 * M d α)) ≤ N d α)
    (hspike : ∀ d α, Dsource ≤ d → 0 < α → α ≤ c0 →
      c1 * d / ell d ≤ N d α)
    (hupper : ∀ d α, Dsource ≤ d → 0 < α → α ≤ c0 →
      N d α ≤ b * q d α * Lambda d α ^ 2) :
    ∃ D : ℝ, Dsource ≤ D ∧ 1 ≤ D ∧
      0 < lowerConstant c c1 cd ∧ 0 < b ∧
      ∀ d α, D ≤ d → 0 < α → α ≤ c0 →
        lowerConstant c c1 cd * q d α / Lambda d α ^ 2 ≤ N d α ∧
        N d α ≤ b * q d α * Lambda d α ^ 2 := by
  obtain ⟨Dt, hDt1, hDt⟩ := eventual_threshold cd c0 hcd hc0
  have hD1 : 1 ≤ max Dsource Dt := hDt1.trans (le_max_right _ _)
  refine ⟨max Dsource Dt, le_max_left _ _, hD1, ?_⟩
  apply full_domain_conditional_composition N (max Dsource Dt) c0 c c1 cd b
    hD1 hc0 hc01 hc hc1 hcd hb
  · intro d hd
    exact hDt d ((le_max_right _ _).trans hd)
  · intro d α hd hα hα0 hreg
    exact hregional d α ((le_max_left _ _).trans hd) hα hα0 hreg
  · intro d α hd hα hα0
    exact hspike d α ((le_max_left _ _).trans hd) hα hα0
  · intro d α hd hα hα0
    exact hupper d α ((le_max_left _ _).trans hd) hα hα0

/-- Natural-dimension version: its source bounds quantify only natural d, so
using it needs no artificial extension of a minimax quantity to real dimension.
It still does not itself define or verify that minimax quantity. -/
theorem full_domain_nat_composition
    (N : ℕ → ℝ → ℝ) (Dsource : ℕ) (c0 c c1 cd b : ℝ)
    (hc0 : 0 < c0) (hc01 : c0 ≤ 1)
    (hc : 0 < c) (hc1 : 0 < c1) (hcd : 0 < cd) (hb : 0 < b)
    (hregional : ∀ (d : ℕ) α, Dsource ≤ d → 0 < α → α ≤ c0 → α ≤ tau d cd →
      c * q d α / (ell d * Real.log (Real.exp 1 * M d α)) ≤ N d α)
    (hspike : ∀ (d : ℕ) α, Dsource ≤ d → 0 < α → α ≤ c0 →
      c1 * d / ell d ≤ N d α)
    (hupper : ∀ (d : ℕ) α, Dsource ≤ d → 0 < α → α ≤ c0 →
      N d α ≤ b * q d α * Lambda d α ^ 2) :
    ∃ D : ℕ, Dsource ≤ D ∧ 1 ≤ D ∧
      0 < lowerConstant c c1 cd ∧ 0 < b ∧
      ∀ (d : ℕ) α, D ≤ d → 0 < α → α ≤ c0 →
        lowerConstant c c1 cd * q d α / Lambda d α ^ 2 ≤ N d α ∧
        N d α ≤ b * q d α * Lambda d α ^ 2 := by
  obtain ⟨Dt, hDt1, hDt⟩ := eventual_threshold cd c0 hcd hc0
  obtain ⟨k, hk⟩ := exists_nat_ge Dt
  let D : ℕ := max Dsource (max 1 k)
  have hDs : Dsource ≤ D := le_max_left _ _
  have hD1 : 1 ≤ D := (le_max_left 1 k).trans (le_max_right _ _)
  have hkD : k ≤ D := (le_max_right 1 k).trans (le_max_right _ _)
  have hcmin : 0 < lowerConstant c c1 cd :=
    lt_min (div_pos hc (by norm_num)) (mul_pos hc1 (sq_pos_of_pos hcd))
  refine ⟨D, hDs, hD1, hcmin, hb, ?_⟩
  intro d α hd hα hα0
  have hdsource : Dsource ≤ d := hDs.trans hd
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hD1.trans hd
  have hdt : Dt ≤ d := hk.trans (by exact_mod_cast hkD.trans hd)
  have hα1 : α ≤ 1 := hα0.trans hc01
  have hq := q_nonneg (α := α) (show (0 : ℝ) ≤ d by positivity)
  refine ⟨?_, hupper d α hdsource hα hα0⟩
  by_cases hregion : α ≤ tau d cd
  · have hbound := regional_composition hd1 hα hα1 hc
      (hregional d α hdsource hα hα0 hregion)
    apply le_trans _ hbound
    apply div_le_div_of_nonneg_right _ (sq_nonneg _)
    exact mul_le_mul_of_nonneg_right (min_le_left _ _) hq
  · have habove : tau d cd < α := lt_of_not_ge hregion
    have hcoarse := coarse_precision_split (show (0 : ℝ) < d by linarith) hα
      (lt_of_le_of_lt (hDt d hdt).1 habove)
    have hbound := spike_composition hd1 hα hα1 hcd hc1 habove
      (hspike d α hdsource hα hα0)
    apply le_trans _ hbound
    apply div_le_div_of_nonneg_right _ (sq_nonneg _)
    exact mul_le_mul_of_nonneg_right (min_le_right _ _) hq

end CompositionAudit


end
-- END Composition.lean

-- BEGIN BoundsArithmetic.lean
section

/-!
# Arithmetic audit for manuscript Sections 4 and 6 and Section 7.1

Source (read-only):
/Users/zhh/Documents/ChatGPT/Colombo_Kimi_Codex_20261118/colobmo_system/downstream_runs/task003_paper_20261123/manuscript/manuscript.md

Line references below refer to that Markdown source, not PDF line numbering.
This file proves real inequalities and identities. Probabilities, independent-seed
factorization, prior integration, the Gaussian channel reduction, reverse KL,
Jensen, and Pinsker are NOT formalized here. They enter only as explicitly named
scalar hypotheses. The file therefore does not verify the full lower bound.
-/

namespace Task003Audit.BoundsArithmetic

/-- MD 331--343: on-event spike-coordinate constants and admissibility margin. -/
theorem spike_coordinate_constants (α b : ℝ) (hα : 0 < α)
    (hsmall : α ≤ 1 / 8) (hb : |b| ≤ α / 4) :
    15 * α / 4 ≤ b + 4 * α ∧ b + 4 * α ≤ 17 * α / 4 ∧
      b + 4 * α ≤ 1 ∧ α / 4 < b + 4 * α := by
  rcases abs_le.mp hb with ⟨hbl, hbu⟩
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

/-- MD 346: the coordinate comparison and its two-coordinate feasibility
consequence are explicit hypotheses; no argmax or finite-sum step is hidden. -/
theorem wrong_index_coordinate_half (xI xJ : ℝ)
    (hmax : |xI| ≤ |xJ|) (hfeasible : |xI| + |xJ| ≤ 1) :
    |xI| ≤ 1 / 2 := by
  linarith

/-- MD 348--350: the lower bound on the other-coordinate contribution is an
explicit premise. The numerical gap is then 13 α / 8, strictly greater than α. -/
theorem wrong_index_gap (α gI xI residual : ℝ) (hα : 0 < α)
    (hgI : 15 * α / 4 ≤ gI) (hxI : |xI| ≤ 1 / 2)
    (hresidual : -(α / 4) ≤ residual) :
    13 * α / 8 ≤ gI * (1 + xI) + residual ∧
      α < gI * (1 + xI) + residual := by
  have hxlow : -(1 / 2 : ℝ) ≤ xI := (abs_le.mp hxI).1
  have hgpos : 0 ≤ gI := by linarith
  have hmul := mul_le_mul_of_nonneg_left (show (1 / 2 : ℝ) ≤ 1 + xI by linarith) hgpos
  constructor <;> nlinarith

/-- MD 354: correct and wrong queried vertices have strictly ordered values. -/
theorem queried_vertex_separation (α correct wrong : ℝ) (hα : 0 < α)
    (hcorrect : correct ≤ -(15 * α / 4)) (hwrong : -(α / 4) ≤ wrong) :
    correct < wrong := by
  linarith

/-- MD 331--337: exact exponent arithmetic, conditional on positive α and ell.
The Gaussian tail inequality itself is not proved here. -/
theorem gaussian_tail_exponent_identity (α ell : ℝ) (hα : 0 < α) (hell : 0 < ell) :
    (α / 4) ^ 2 / (2 * (α / (16 * Real.sqrt ell)) ^ 2) = 8 * ell := by
  simp only [div_pow, mul_pow, Real.sq_sqrt hell.le]
  field_simp
  nlinarith

/-- MD 331--332 and 365: the signal-to-noise ratio is exactly 4096 ell. -/
theorem signal_to_noise_identity (α ell : ℝ) (hα : 0 < α) (hell : 0 < ell) :
    (4 * α) ^ 2 / (α / (16 * Real.sqrt ell)) ^ 2 = 4096 * ell := by
  simp only [div_pow, mul_pow, Real.sq_sqrt hell.le]
  field_simp
  nlinarith

/-- MD 354--356: scalar independent-seed amplification at one fixed admissible
objective. p1 and p2 are the two seed-success probabilities at that same fixed
objective; `hindependent` supplies the product of the failure probabilities.
`hrecovery` supplies the deterministic implication to exact support recovery.
Neither premise is deduced from probability theory in this audit. -/
theorem two_run_recovery_from_fixed_objective_premises
    (p1 p2 bothFail recover : ℝ)
    (hp1 : 2 / 3 ≤ p1) (_hp1one : p1 ≤ 1)
    (hp2 : 2 / 3 ≤ p2) (hp2one : p2 ≤ 1)
    (hindependent : bothFail = (1 - p1) * (1 - p2))
    (hrecovery : 1 - bothFail ≤ recover) :
    8 / 9 ≤ recover := by
  have hproduct : (1 - p1) * (1 - p2) ≤ (1 / 3 : ℝ) * (1 / 3 : ℝ) :=
    mul_le_mul (by linarith) (by linarith) (by linarith) (by norm_num)
  rw [hindependent] at hrecovery
  nlinarith

/-- The same amplification statement quantified separately over every good
fixed objective. No averaging of the two per-instance success bounds is used. -/
theorem two_run_recovery_for_each_good_objective
    {F : Type*} (Good : Set F) (p1 p2 bothFail recover : F → ℝ)
    (hp1 : ∀ f ∈ Good, 2 / 3 ≤ p1 f ∧ p1 f ≤ 1)
    (hp2 : ∀ f ∈ Good, 2 / 3 ≤ p2 f ∧ p2 f ≤ 1)
    (hindependent : ∀ f ∈ Good, bothFail f = (1 - p1 f) * (1 - p2 f))
    (hrecovery : ∀ f ∈ Good, 1 - bothFail f ≤ recover f) :
    ∀ f ∈ Good, 8 / 9 ≤ recover f := by
  intro f hf
  exact two_run_recovery_from_fixed_objective_premises
    (p1 f) (p2 f) (bothFail f) (recover f)
    (hp1 f hf).1 (hp1 f hf).2 (hp2 f hf).1 (hp2 f hf).2
    (hindependent f hf) (hrecovery f hf)

/-- MD 337 and 358: a deliberately crude bound on the displayed Gaussian-tail
expression suffices already for d >= 2. This proves arithmetic, not a tail law. -/
theorem displayed_tail_expression_le_one_sixty_four (d : ℝ) (hd : 2 ≤ d) :
    2 / ((Real.exp 1) ^ 8 * d ^ 7) ≤ 1 / 64 := by
  have hexp : 1 ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hexp8 : 1 ≤ (Real.exp 1) ^ 8 := by
    exact one_le_pow₀ hexp
  have hd7 : (128 : ℝ) ≤ d ^ 7 := by
    have hpow := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hd 7
    norm_num at hpow
    exact hpow
  have hden : (128 : ℝ) ≤ (Real.exp 1) ^ 8 * d ^ 7 := by
    have hmul := mul_le_mul hexp8 hd7 (by norm_num : (0 : ℝ) ≤ 128)
      (by positivity : 0 ≤ (Real.exp 1) ^ 8)
    simpa using hmul
  apply (div_le_iff₀ (show 0 < (Real.exp 1) ^ 8 * d ^ 7 by linarith)).2
  nlinarith

/-- MD 336--358: the prior good-event bound and the integrated recovery lower
bound are supplied as scalar probability premises. The strict 2/3 comparison
is then certified; construction/integration of those probabilities is external. -/
theorem unconditional_recovery_from_integrated_premises (d goodProb recover : ℝ)
    (hd : 2 ≤ d)
    (hgood : 1 - 2 / ((Real.exp 1) ^ 8 * d ^ 7) ≤ goodProb)
    (hintegrated : (8 / 9 : ℝ) * goodProb ≤ recover) :
    2 / 3 < recover := by
  have htail := displayed_tail_expression_le_one_sixty_four d hd
  nlinarith

/-- MD 380--382: final real algebra after the scalar bound (16) has been supplied.
This theorem does not prove Pinsker, adaptive sensing, or a KL chain rule. -/
theorem final_information_cost_from_scalar_pinsker_bound (d obs kappa p : ℝ)
    (hd : 6 ≤ d) (hcost : 0 ≤ obs * kappa) (hp : 2 / 3 < p)
    (hscalarPinsker : p ≤ 1 / d + Real.sqrt (obs * kappa / (4 * d))) :
    d ≤ obs * kappa := by
  have hdpos : 0 < d := by linarith
  have hinverse : 1 / d ≤ (1 / 6 : ℝ) := by
    apply (div_le_div_iff₀ hdpos (by norm_num : (0 : ℝ) < 6)).2
    linarith
  have hroot : (1 / 2 : ℝ) < Real.sqrt (obs * kappa / (4 * d)) := by
    linarith
  have hnonneg : 0 ≤ obs * kappa / (4 * d) := div_nonneg hcost (by positivity)
  have hsquare := Real.sq_sqrt hnonneg
  have hquarter : (1 / 4 : ℝ) < obs * kappa / (4 * d) := by
    nlinarith [Real.sqrt_nonneg (obs * kappa / (4 * d))]
  have hmul := (lt_div_iff₀ (show 0 < 4 * d by positivity)).mp hquarter
  nlinarith

/-- MD 375--382: an optional scalar bridge from the reverse-KL average bound
and a Pinsker/Jensen bound with that average. These are explicit assumptions. -/
theorem final_information_cost_from_kl_scalar_premises
    (d obs kappa p averageKL : ℝ) (hd : 6 ≤ d)
    (hcost : 0 ≤ obs * kappa) (hp : 2 / 3 < p)
    (hreverseKL : averageKL ≤ obs * kappa / (2 * d))
    (hPinskerJensen : p ≤ 1 / d + Real.sqrt (averageKL / 2)) :
    d ≤ obs * kappa := by
  apply final_information_cost_from_scalar_pinsker_bound d obs kappa p hd hcost hp
  have hdiv : averageKL / 2 ≤ obs * kappa / (4 * d) := by
    calc
      averageKL / 2 ≤ (obs * kappa / (2 * d)) / 2 :=
        div_le_div_of_nonneg_right hreverseKL (by norm_num)
      _ = obs * kappa / (4 * d) := by ring
  exact hPinskerJensen.trans (add_le_add (le_refl (1 / d)) (Real.sqrt_le_sqrt hdiv))

/-- MD 326 and 390: rewrite the observation count 2m+2 and kappa=4096 ell. -/
theorem observation_cost_to_query_lower_bound (d m ell : ℝ) (hell : 0 < ell)
    (hcost : d ≤ (2 * m + 2) * (4096 * ell)) :
    d / (8192 * ell) - 1 ≤ m := by
  have hratio : d / (8192 * ell) ≤ m + 1 := by
    apply (div_le_iff₀ (show 0 < 8192 * ell by positivity)).2
    nlinarith
  linarith

/-- MD 390--393: the threshold removes the additive -1 with the stated constant. -/
theorem query_lower_bound_after_threshold (d m ell : ℝ) (hell : 0 < ell)
    (hthreshold : 16384 * ell ≤ d)
    (hm : d / (8192 * ell) - 1 ≤ m) :
    d / (16384 * ell) ≤ m := by
  have hratio : (1 : ℝ) ≤ d / (16384 * ell) := by
    apply (le_div_iff₀ (show 0 < 16384 * ell by positivity)).2
    simpa using hthreshold
  have hid : d / (8192 * ell) = 2 * (d / (16384 * ell)) := by ring
  linarith

/-- MD 91 and 104: the n=2d substitution commutes with the natural ceiling,
so the exact pathwise query count has precisely the displayed constant 576. -/
theorem two_query_ceiling_rewrite (d n α : ℝ) (hn : n = 2 * d) :
    (2 : ℕ) * ⌈288 * n * Real.log n / α ^ 2⌉₊ =
      2 * ⌈576 * d * Real.log (2 * d) / α ^ 2⌉₊ := by
  subst n
  congr 2
  ring

/-- MD 104 and 185--188: the stated iteration budget makes the optimization
term at most alpha/6. `logn` is an explicitly nonnegative scalar; this theorem
does not establish a mirror-descent inequality or a stochastic expectation. -/
theorem smoothing_rate_term_from_iteration_budget (n logn T α : ℝ)
    (hn : 0 ≤ n) (hlog : 0 ≤ logn) (hT : 0 < T) (hα : 0 < α)
    (hbudget : 288 * n * logn / α ^ 2 ≤ T) :
    2 * Real.sqrt (2 * n * logn / T) ≤ α / 6 := by
  have hbudgetmul : 288 * n * logn ≤ T * α ^ 2 :=
    (div_le_iff₀ (sq_pos_of_pos hα)).mp hbudget
  have hfrac : 2 * n * logn / T ≤ (α / 12) ^ 2 := by
    apply (div_le_iff₀ hT).2
    nlinarith
  have hnonneg : 0 ≤ 2 * n * logn / T := by positivity
  have hsquare := Real.sq_sqrt hnonneg
  have hroot : Real.sqrt (2 * n * logn / T) ≤ α / 12 := by
    nlinarith [Real.sqrt_nonneg (2 * n * logn / T)]
  linarith

/-- MD 103 and 185--188: the smoothing bias is exactly alpha/6. -/
theorem smoothing_bias_exact (n α h : ℝ) (hn : 0 < n)
    (hh : h = α / (12 * n)) :
    2 * h * n = α / 6 := by
  rw [hh]
  field_simp
  ring

/-- MD 185--188: combining two scalar estimates bounds the expected gap.
The expected-gap estimate itself remains an explicit premise. -/
theorem expected_gap_from_two_scalar_terms (α optimization bias expectedGap : ℝ)
    (hoptimization : optimization ≤ α / 6) (hbias : bias ≤ α / 6)
    (hexpectation : expectedGap ≤ optimization + bias) :
    expectedGap ≤ α / 3 := by
  linarith

/-- MD 188: scalar division in the Markov step. The application of Markov's
inequality is the explicit `hMarkov` premise, not a theorem of this file. -/
theorem markov_success_from_scalar_premises (α expectedGap failureProb : ℝ)
    (hα : 0 < α) (hexpectation : expectedGap ≤ α / 3)
    (hMarkov : failureProb ≤ expectedGap / α) :
    failureProb ≤ 1 / 3 ∧ 2 / 3 ≤ 1 - failureProb := by
  have hratio : expectedGap / α ≤ (1 / 3 : ℝ) := by
    apply (div_le_iff₀ hα).2
    linarith
  constructor <;> linarith

/-- MD 441--443: first normalize alpha=c/sqrt(d). -/
theorem benchmark_inverse_accuracy_identity (d c : ℝ) (hd : 0 < d) (hc : 0 < c) :
    1 / (c / Real.sqrt d) ^ 2 = d / c ^ 2 := by
  rw [div_pow, Real.sq_sqrt hd.le]
  field_simp

/-- MD 443: factor d out of the min, including the exact c=1 boundary. -/
theorem benchmark_min_factorization (d c : ℝ) (hd : 0 ≤ d) :
    d * min d (d / c ^ 2) = d ^ 2 * min 1 (1 / c ^ 2) := by
  have hmin : min d (d / c ^ 2) = d * min 1 (1 / c ^ 2) := by
    rw [mul_min_of_nonneg 1 (1 / c ^ 2) hd]
    simp [div_eq_mul_inv]
  rw [hmin]
  ring

/-- MD 445: c>=1 branch. -/
theorem benchmark_above_transition (d c : ℝ) (hd : 0 ≤ d) (hc : 1 ≤ c) :
    d * min d (d / c ^ 2) = d ^ 2 / c ^ 2 := by
  have hc2pos : 0 < c ^ 2 := by positivity
  have hc2 : 1 ≤ c ^ 2 := by nlinarith
  have hmin : d / c ^ 2 ≤ d := by
    apply (div_le_iff₀ hc2pos).2
    nlinarith [mul_nonneg hd (sub_nonneg.mpr hc2)]
  rw [min_eq_right hmin]
  ring

/-- MD 445: 0<c<=1 branch. -/
theorem benchmark_below_transition (d c : ℝ) (hd : 0 ≤ d)
    (hc : 0 < c) (hcsmall : c ≤ 1) :
    d * min d (d / c ^ 2) = d ^ 2 := by
  have hc2pos : 0 < c ^ 2 := by positivity
  have hc2 : c ^ 2 ≤ 1 := by nlinarith
  have hmin : d ≤ d / c ^ 2 := by
    apply (le_div_iff₀ hc2pos).2
    nlinarith [mul_nonneg hd (sub_nonneg.mpr hc2)]
  rw [min_eq_left hmin]
  ring

theorem benchmark_at_transition (d : ℝ) (hd : 0 ≤ d) :
    d * min d (d / (1 : ℝ) ^ 2) = d ^ 2 := by
  simpa using benchmark_below_transition d 1 hd (by norm_num) (by norm_num)

end Task003Audit.BoundsArithmetic


end
-- END BoundsArithmetic.lean

-- BEGIN PenaltyReduction.lean
section

/-
Partial formal audit of manuscript MD 254-291.
The compact-metric penalty reduction below is genuinely proved.  The concrete
l1 embedding, Borel selector, oracle simulation, source distributions and Yao
argument are separate obligations; none is asserted by these declarations.
The compact-minimum proof adapts the existing task002 penalty excerpt, with
fresh compilation; Lipschitz and convexity proofs are additional obligations.
-/
namespace PaperPenaltyReduction

universe u

noncomputable def penalty {E : Type u} [PseudoMetricSpace E]
    (L : NNReal) (g : E → ℝ) (C : Set E) (x : E) : ℝ :=
  g x + (L : ℝ) * Metric.infDist x C

/-- MD 266: adding the distance penalty at most doubles the Lipschitz constant. -/
theorem penalty_lipschitz {E : Type u} [PseudoMetricSpace E]
    (L : NNReal) (g : E → ℝ) (C : Set E) (hg : LipschitzWith L g) :
    LipschitzWith (2 * L) (penalty L g C) := by
  apply LipschitzWith.of_le_add_mul
  intro x y
  have h1 := hg.le_add_mul x y
  have h2 := Metric.infDist_le_infDist_add_dist (x := x) (y := y) (s := C)
  have h3 := mul_le_mul_of_nonneg_left h2 L.coe_nonneg
  simp only [penalty, NNReal.coe_mul, NNReal.coe_ofNat]
  linarith

/-- MD 264-266: positive normalization makes the penalized objective 1-Lipschitz. -/
theorem normalized_penalty_lipschitz {E : Type u} [PseudoMetricSpace E]
    (L : NNReal) (g : E → ℝ) (C : Set E) (hg : LipschitzWith L g)
    (hL : 0 < (L : ℝ)) :
    LipschitzWith 1 (fun x => penalty L g C x / (2 * (L : ℝ))) := by
  apply LipschitzWith.of_le_add_mul
  intro x y
  have hp := (penalty_lipschitz L g C hg).le_add_mul x y
  have hden : 0 < 2 * (L : ℝ) := by positivity
  have hh := (div_le_div_iff_of_pos_right hden).mpr hp
  simp only [NNReal.coe_one, NNReal.coe_mul, NNReal.coe_ofNat, one_mul] at *
  calc
    penalty L g C x / (2 * (L : ℝ)) ≤
        (penalty L g C y + 2 * (L : ℝ) * dist x y) / (2 * (L : ℝ)) := hh
    _ = penalty L g C y / (2 * (L : ℝ)) + dist x y := by
      field_simp

/-- MD 268-270: an exact nearest point exists and decodes the penalty value. -/
theorem nearest_decoder {E : Type u} [MetricSpace E]
    (C : Set E) (hC : IsCompact C) (hCne : C.Nonempty)
    (L : NNReal) (g : E → ℝ) (hg : LipschitzWith L g) (x : E) :
    ∃ z ∈ C, dist x z = Metric.infDist x C ∧ g z ≤ penalty L g C x := by
  obtain ⟨z, hzC, hz⟩ := hC.exists_infDist_eq_dist hCne x
  refine ⟨z, hzC, hz.symm, ?_⟩
  calc
    g z ≤ g x + (L : ℝ) * dist z x := hg.le_add_mul z x
    _ = g x + (L : ℝ) * dist x z := by rw [dist_comm z x]
    _ = penalty L g C x := by rw [penalty, ← hz]

/-- MD 274-280: one point minimizes the original compact restriction and the
global penalized objective; every approximate output has a compact decoder. -/
theorem global_minimum_and_decoder {E : Type u} [MetricSpace E]
    (C : Set E) (hC : IsCompact C) (hCne : C.Nonempty)
    (L : NNReal) (g : E → ℝ) (hg : LipschitzWith L g) :
    ∃ u ∈ C,
      (∀ y ∈ C, g u ≤ g y) ∧
      penalty L g C u = g u ∧
      (∀ x : E, penalty L g C u ≤ penalty L g C x) ∧
      (∀ x : E, ∀ ε : ℝ, penalty L g C x - penalty L g C u ≤ ε →
        ∃ z ∈ C, dist x z = Metric.infDist x C ∧
          0 ≤ g z - g u ∧ g z - g u ≤ ε) := by
  obtain ⟨u, huC, hu⟩ := hC.exists_isMinOn hCne hg.continuous.continuousOn
  have hFu : penalty L g C u = g u := by
    simp [penalty, Metric.infDist_zero_of_mem huC]
  have hF_le : ∀ x : E, penalty L g C u ≤ penalty L g C x := by
    intro x
    obtain ⟨z, hzC, _, hz⟩ := nearest_decoder C hC hCne L g hg x
    calc
      penalty L g C u = g u := hFu
      _ ≤ g z := hu hzC
      _ ≤ penalty L g C x := hz
  refine ⟨u, huC, hu, hFu, hF_le, ?_⟩
  intro x ε hε
  obtain ⟨z, hzC, hzdist, hz⟩ := nearest_decoder C hC hCne L g hg x
  refine ⟨z, hzC, hzdist, sub_nonneg.mpr (hu hzC), ?_⟩
  rw [hFu] at hε
  linarith

/-- MD 266: distance to a nonempty compact convex set is convex in a real
normed space.  This does not yet instantiate the manuscript's l1 space. -/
theorem compact_convex_infDist {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (C : Set E) (hC : IsCompact C) (hCne : C.Nonempty) (hc : Convex ℝ C) :
    ConvexOn ℝ Set.univ (fun x : E => Metric.infDist x C) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  obtain ⟨p, hp, hxp⟩ := hC.exists_infDist_eq_dist hCne x
  obtain ⟨q, hq, hyq⟩ := hC.exists_infDist_eq_dist hCne y
  have hpq : a • p + b • q ∈ C := hc hp hq ha hb hab
  calc
    Metric.infDist (a • x + b • y) C ≤ dist (a • x + b • y) (a • p + b • q) :=
      Metric.infDist_le_dist_of_mem hpq
    _ = ‖a • (x - p) + b • (y - q)‖ := by
      rw [dist_eq_norm]
      congr 1
      module
    _ ≤ ‖a • (x - p)‖ + ‖b • (y - q)‖ := norm_add_le _ _
    _ = a * Metric.infDist x C + b * Metric.infDist y C := by
      rw [norm_smul, norm_smul, Real.norm_of_nonneg ha, Real.norm_of_nonneg hb,
        ← dist_eq_norm, ← dist_eq_norm, ← hxp, ← hyq]
    _ = a • Metric.infDist x C + b • Metric.infDist y C := by rfl

/-- MD 266: convexity of the penalized objective, assuming convexity of g. -/
theorem penalty_convex {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (C : Set E) (hC : IsCompact C) (hCne : C.Nonempty) (hc : Convex ℝ C)
    (L : NNReal) (g : E → ℝ) (hg : ConvexOn ℝ Set.univ g) :
    ConvexOn ℝ Set.univ (penalty L g C) := by
  have hd := compact_convex_infDist C hC hCne hc
  refine ⟨convex_univ, ?_⟩
  intro x hx y hy a b ha hb hab
  have h1 := hg.2 hx hy ha hb hab
  have h2 := hd.2 hx hy ha hb hab
  have h3 := mul_le_mul_of_nonneg_left h2 L.coe_nonneg
  simp only [penalty, smul_eq_mul] at *
  nlinarith

/-- MD 291: normalization by 2lambda turns target alpha error into at most
2lambda*alpha original error.  This is scalar algebra, not a probability claim. -/
theorem normalized_gap {Hmin Hx lam α : ℝ} (hlam : 0 < lam)
    (hgap : Hx / (2 * lam) - Hmin / (2 * lam) ≤ α) :
    Hx - Hmin ≤ 2 * lam * α := by
  have hden : 0 < 2 * lam := by positivity
  have h : (Hx - Hmin) / (2 * lam) ≤ α := by simpa [sub_div] using hgap
  have hm := (div_le_iff₀ hden).mp h
  nlinarith

/-- MD 287: a positively homogeneous function is exactly recoverable radially
from a single value on the unit sphere. This is a function identity, not yet
an encoded oracle policy/query-count theorem. -/
theorem homogeneous_radial_value {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → ℝ) (hhom : ∀ (t : ℝ), 0 ≤ t → ∀ x, f (t • x) = t * f x)
    (w : E) (hw : w ≠ 0) :
    ‖(‖w‖⁻¹ : ℝ) • w‖ = 1 ∧
      f w = ‖w‖ * f ((‖w‖⁻¹ : ℝ) • w) := by
  have hn : ‖w‖ ≠ 0 := norm_ne_zero_iff.mpr hw
  constructor
  · rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg w)),
      inv_mul_cancel₀ hn]
  · have hh := hhom ‖w‖ (norm_nonneg w) ((‖w‖⁻¹ : ℝ) • w)
    simpa only [smul_smul, mul_inv_cancel₀ hn, one_smul] using hh

theorem homogeneous_zero_value {E : Type u} [AddCommMonoid E] [Module ℝ E]
    (f : E → ℝ) (hhom : ∀ (t : ℝ), 0 ≤ t → ∀ x, f (t • x) = t * f x) :
    f 0 = 0 := by
  simpa using hhom 0 (by norm_num) 0

end PaperPenaltyReduction


end
-- END PenaltyReduction.lean

-- BEGIN ProbabilityTransfers.lean
section

/- Partial probability-theoretic audit of MD 188 and 293-295.
   The expected-gap estimate and hard-prior event bounds remain hypotheses.
   This file does not formalize stochastic mirror descent, Yao, independence
   of optimization runs, or the adaptive Gaussian KL argument. -/
namespace PaperProbabilityTransfers

open MeasureTheory Set

/-- MD 188: an actual measure-theoretic Markov success conversion. -/
theorem markov_success {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (gap : Ω → ℝ)
    (hgap : Measurable gap) (hint : Integrable gap μ)
    (hnonneg : 0 ≤ᵐ[μ] gap) (α : ℝ) (hα : 0 < α)
    (hexpect : (∫ ω, gap ω ∂μ) ≤ α / 3) :
    (2 / 3 : ℝ) ≤ μ.real {ω | gap ω ≤ α} := by
  have hm := mul_meas_ge_le_integral_of_nonneg hnonneg hint α
  have hlarge : μ.real {ω | α ≤ gap ω} ≤ (1 / 3 : ℝ) := by
    nlinarith
  have hstrict : μ.real {ω | α < gap ω} ≤ (1 / 3 : ℝ) := by
    have hmono : μ.real {ω | α < gap ω} ≤ μ.real {ω | α ≤ gap ω} :=
      measureReal_mono (μ := μ) (s₁ := {ω | α < gap ω})
        (s₂ := {ω | α ≤ gap ω}) (by
          intro ω hω
          change α ≤ gap ω
          exact le_of_lt hω)
    exact hmono.trans hlarge
  have hs : MeasurableSet {ω | α < gap ω} := measurableSet_lt measurable_const hgap
  have hc := probReal_compl_eq_one_sub (μ := μ) hs
  have hsuccess : μ.real {ω | gap ω ≤ α} = 1 - μ.real {ω | α < gap ω} := by
    simpa only [compl_setOf, not_lt] using hc
  rw [hsuccess]
  linarith

/-- MD 293-295: the conditional-event ratio bound on an actual probability
space. The ratio is displayed explicitly, without asserting the construction
of the manuscript's source prior or the target-success implication. -/
theorem conditional_event_success_ratio {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (S E : Set Ω)
    (hsource : μ.real S ≤ (1 / 4 : ℝ))
    (hevent : (15 / 16 : ℝ) ≤ μ.real E) :
    μ.real (S ∩ E) / μ.real E ≤ (4 / 15 : ℝ) := by
  have hi : μ.real (S ∩ E) ≤ (1 / 4 : ℝ) :=
    (measureReal_mono inter_subset_left).trans hsource
  have hpos : 0 < μ.real E := by linarith
  apply (div_le_iff₀ hpos).mpr
  nlinarith

end PaperProbabilityTransfers


end
-- END ProbabilityTransfers.lean

-- BEGIN OracleModel.lean
section

/-!
A model of the manuscript's exact scalar value oracle. Queries and stopping
rules use only a private seed and the finite prefix of exact scalar replies.
The seed law is fixed outside the quantifier over objectives. Finite fuel is a
pathwise cap: stopping consumes no query, and fuel exhaustion forces an arbitrary
measurable feasible output. Outputs need not coincide with query points.
-/
noncomputable section
open scoped ENNReal

namespace Task003.OracleModel
open Set MeasureTheory

abbrev Point (d : ℕ) := PiLp 1 (fun _ : Fin d => ℝ)

def Feasible {d : ℕ} (R : ℝ) (x : Point d) : Prop := ‖x‖ ≤ R

structure Objective (d : ℕ) (L : ℝ) where
  toFun : Point d → ℝ
  convex : ConvexOn ℝ univ toFun
  lip : LipschitzWith L.toNNReal toFun

instance {d L} : CoeFun (Objective d L) (fun _ => Point d → ℝ) := ⟨Objective.toFun⟩

theorem Objective.continuous {d L} (f : Objective d L) : Continuous f := f.lip.continuous

/-- All histories, including histories impossible for any promised objective,
receive a measurable action and a feasible fallback. Only finitely many of these
maps are used at any fixed cap. They do not receive the objective as an argument. -/
structure Policy (d : ℕ) (R : ℝ) (Ω : Type*) [MeasurableSpace Ω] where
  query : (n : ℕ) → Ω × (Fin n → ℝ) → Point d
  query_measurable : ∀ n, Measurable (query n)
  stop : (n : ℕ) → Ω × (Fin n → ℝ) → Bool
  stop_measurable : ∀ n, Measurable (stop n)
  output : (n : ℕ) → Ω × (Fin n → ℝ) → Point d
  output_measurable : ∀ n, Measurable (output n)
  output_feasible : ∀ n h, Feasible R (output n h)

/-- One exact query, extending the real reply prefix by its scalar answer. -/
def nextHistory {d R Ω} [MeasurableSpace Ω] (a : Policy d R Ω)
    (f : Point d → ℝ) (n : ℕ) (h : Ω × (Fin n → ℝ)) : Ω × (Fin (n+1) → ℝ) :=
  (h.1, Fin.snoc h.2 (f (a.query n h)))

/-- A real early stop returns immediately, without padding queries. At the cap,
the policy returns its feasible fallback without making another query. -/
def execute {d R Ω} [MeasurableSpace Ω] (a : Policy d R Ω)
    (f : Point d → ℝ) : (fuel n : ℕ) → Ω × (Fin n → ℝ) → Point d
  | 0, n, h => a.output n h
  | k+1, n, h => if a.stop n h then a.output n h
      else execute a f k (n+1) (nextHistory a f n h)

def run {d R Ω} [MeasurableSpace Ω] (a : Policy d R Ω)
    (f : Point d → ℝ) (m : ℕ) (ω : Ω) : Point d :=
  execute a f m 0 (ω, Fin.elim0)

/-- Actual number of oracle calls on this seed/objective execution. -/
def queriesUsed {d R Ω} [MeasurableSpace Ω] (a : Policy d R Ω)
    (f : Point d → ℝ) : (fuel n : ℕ) → Ω × (Fin n → ℝ) → ℕ
  | 0, _, _ => 0
  | k+1, n, h => if a.stop n h then 0
      else 1 + queriesUsed a f k (n+1) (nextHistory a f n h)

theorem queriesUsed_le {d R Ω} [MeasurableSpace Ω] (a : Policy d R Ω)
    (f : Point d → ℝ) (fuel n : ℕ) (h : Ω × (Fin n → ℝ)) :
    queriesUsed a f fuel n h ≤ fuel := by
  induction fuel generalizing n with
  | zero => simp [queriesUsed]
  | succ k ih =>
    simp only [queriesUsed]
    split
    · omega
    · have := ih (n+1) (nextHistory a f n h); omega

theorem execute_feasible {d R Ω} [MeasurableSpace Ω] (a : Policy d R Ω)
    (f : Point d → ℝ) (fuel n : ℕ) (h : Ω × (Fin n → ℝ)) :
    Feasible R (execute a f fuel n h) := by
  induction fuel generalizing n with
  | zero => exact a.output_feasible n h
  | succ k ih =>
    simp only [execute]
    split
    · exact a.output_feasible n h
    · exact ih (n+1) (nextHistory a f n h)

theorem run_feasible {d R Ω} [MeasurableSpace Ω] (a : Policy d R Ω)
    (f : Point d → ℝ) (m : ℕ) (ω : Ω) : Feasible R (run a f m ω) :=
  execute_feasible a f m 0 _

/-- The actual minimum value. Its attainment for nonnegative radii is proved below. -/
def optimum {d : ℕ} (R : ℝ) (f : Point d → ℝ) : ℝ :=
  sInf (f '' {x | Feasible R x})

def successEvent {d R Ω} [MeasurableSpace Ω] (a : Policy d R Ω)
    (f : Point d → ℝ) (m : ℕ) (ε : ℝ) : Set Ω :=
  {ω | f (run a f m ω) - optimum R f ≤ ε}

/-- The same policy and seed law must succeed on every fixed objective. -/
def SolvesOn {d R Ω} [MeasurableSpace Ω] (μ : Measure Ω)
    (a : Policy d R Ω) (m : ℕ) (L ε : ℝ) : Prop :=
  ∀ f : Objective d L, (2 / 3 : ℝ≥0∞) ≤ μ (successEvent a f m ε)

/-- The private seed can have any measurable probability law; there is no
finite-support or deterministic-seed restriction. -/
def AdmissibleBudget (d m : ℕ) (L R ε : ℝ) : Prop :=
  ∃ (Ω : Type) (s : MeasurableSpace Ω) (μ : @Measure Ω s),
    @IsProbabilityMeasure Ω s μ ∧
    ∃ a : @Policy d R Ω s, @SolvesOn d R Ω s μ a m L ε

/-- `none` records failure of existence instead of silently assigning budget 0. -/
def minimaxBudget (d : ℕ) (L R ε : ℝ) : Option ℕ := by
  classical
  exact if h : ∃ m, AdmissibleBudget d m L R ε then some (Nat.find h) else none

theorem nextHistory_measurable {d R Ω} [MeasurableSpace Ω] (a : Policy d R Ω)
    (f : Point d → ℝ) (hf : Measurable f) (n : ℕ) :
    Measurable (nextHistory a f n) := by
  apply measurable_fst.prodMk
  apply measurable_pi_lambda
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simpa [nextHistory, Function.comp_def] using hf.comp (a.query_measurable n)
  · simpa [nextHistory, Function.comp_def] using (measurable_pi_apply j).comp measurable_snd

theorem execute_measurable {d R Ω} [MeasurableSpace Ω] (a : Policy d R Ω)
    (f : Point d → ℝ) (hf : Measurable f) (fuel n : ℕ) :
    Measurable (execute a f fuel n) := by
  induction fuel generalizing n with
  | zero => exact a.output_measurable n
  | succ k ih =>
    exact Measurable.ite (measurableSet_eq_fun (a.stop_measurable n) measurable_const)
      (a.output_measurable n) ((ih (n+1)).comp (nextHistory_measurable a f hf n))

theorem run_measurable {d R Ω} [MeasurableSpace Ω] (a : Policy d R Ω)
    (f : Point d → ℝ) (hf : Measurable f) (m : ℕ) : Measurable (run a f m) :=
  (execute_measurable a f hf m 0).comp (measurable_id.prodMk measurable_const)

theorem successEvent_measurable {d R Ω} [MeasurableSpace Ω] (a : Policy d R Ω)
    (f : Point d → ℝ) (hf : Measurable f) (m : ℕ) (ε : ℝ) :
    MeasurableSet (successEvent a f m ε) :=
  measurableSet_le ((hf.comp (run_measurable a f hf m)).sub measurable_const) measurable_const

theorem optimum_attained {d L R} (f : Objective d L) (hR : 0 ≤ R) :
    ∃ x : Point d, Feasible R x ∧ optimum R f = f x ∧
      ∀ y : Point d, Feasible R y → f x ≤ f y := by
  have hset : {x : Point d | Feasible R x} = Metric.closedBall 0 R := by
    ext x; simp [Feasible, Metric.mem_closedBall, dist_zero_right]
  have hne : ({x : Point d | Feasible R x}).Nonempty := ⟨0, by simpa [Feasible]⟩
  have hc : IsCompact {x : Point d | Feasible R x} := by rw [hset]; exact isCompact_closedBall 0 R
  obtain ⟨x, hx, hmin⟩ := hc.exists_isMinOn hne f.continuous.continuousOn
  have hb : BddBelow (f '' {x : Point d | Feasible R x}) := by
    refine ⟨f x, ?_⟩
    rintro z ⟨y, hy, rfl⟩
    exact hmin hy
  refine ⟨x, hx, le_antisymm (csInf_le hb ⟨x, hx, rfl⟩) ?_, ?_⟩
  · exact le_csInf (hne.image f) (by rintro z ⟨y, hy, rfl⟩; exact hmin hy)
  · exact fun y hy => hmin hy

theorem success_iff_comparison {d L R Ω} [MeasurableSpace Ω] (a : Policy d R Ω)
    (f : Objective d L) (hR : 0 ≤ R) (m : ℕ) (ε : ℝ) (ω : Ω) :
    ω ∈ successEvent a f m ε ↔
      ∀ y : Point d, Feasible R y → f (run a f m ω) ≤ f y + ε := by
  obtain ⟨x, hx, hval, hmin⟩ := optimum_attained f hR
  change f (run a f m ω) - optimum R f ≤ ε ↔ _
  rw [hval]
  constructor
  · intro h y hy; have := hmin y hy; linarith
  · intro h; have := h x hx; linarith

theorem SolvesOn.accuracy_mono {d R Ω} [MeasurableSpace Ω] {μ : Measure Ω}
    {a : Policy d R Ω} {m : ℕ} {L ε ε' : ℝ}
    (h : SolvesOn μ a m L ε) (he : ε ≤ ε') : SolvesOn μ a m L ε' := by
  intro f
  apply (h f).trans
  apply measure_mono
  intro ω hω
  exact hω.trans he

theorem admissible_accuracy_mono {d m L R ε ε'}
    (h : AdmissibleBudget d m L R ε) (he : ε ≤ ε') :
    AdmissibleBudget d m L R ε' := by
  obtain ⟨Ω, s, μ, hp, a, ha⟩ := h
  exact ⟨Ω, s, μ, hp, a, ha.accuracy_mono he⟩

/-- Turn a cap into an explicit absorbing stopping rule. This also permits using
any larger fuel bound without changing a single oracle call or the output. -/
def Policy.forceCap {d R Ω} [MeasurableSpace Ω] (a : Policy d R Ω) (cap : ℕ) :
    Policy d R Ω where
  query := a.query
  query_measurable := a.query_measurable
  stop := fun n h => if cap ≤ n then true else a.stop n h
  stop_measurable := fun n => by
    by_cases h : cap ≤ n
    · simpa [h] using (measurable_const : Measurable (fun _ : Ω × (Fin n → ℝ) => true))
    · simpa [h] using a.stop_measurable n
  output := a.output
  output_measurable := a.output_measurable
  output_feasible := a.output_feasible

theorem execute_forceCap {d R Ω} [MeasurableSpace Ω] (a : Policy d R Ω)
    (f : Point d → ℝ) (k r n : ℕ) (h : Ω × (Fin n → ℝ)) :
    execute (a.forceCap (n+k)) f (k+r) n h = execute a f k n h := by
  induction k generalizing n with
  | zero =>
    cases r <;> simp [execute, Policy.forceCap]
  | succ k ih =>
    have hlt : ¬ n + (k+1) ≤ n := by omega
    simp only [Nat.succ_add, execute, Policy.forceCap, hlt, ↓reduceIte]
    split
    · rfl
    · have hh := ih (n+1) (nextHistory a f n h)
      simpa [nextHistory, Policy.forceCap, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hh

theorem run_forceCap {d R Ω} [MeasurableSpace Ω] (a : Policy d R Ω)
    (f : Point d → ℝ) (m n : ℕ) (hmn : m ≤ n) (ω : Ω) :
    run (a.forceCap m) f n ω = run a f m ω := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hmn
  simpa [run] using execute_forceCap a f m r 0 (ω, Fin.elim0)

theorem admissible_budget_mono {d m n L R ε}
    (h : AdmissibleBudget d m L R ε) (hmn : m ≤ n) :
    AdmissibleBudget d n L R ε := by
  obtain ⟨Ω, s, μ, hp, a, ha⟩ := h
  refine ⟨Ω, s, μ, hp, a.forceCap m, ?_⟩
  intro f
  have he : successEvent (a.forceCap m) f n ε = successEvent a f m ε := by
    ext ω
    simp only [successEvent, mem_setOf_eq, run_forceCap a f m n hmn ω]
  rw [he]
  exact ha f

theorem minimaxBudget_eq_none_iff (d : ℕ) (L R ε : ℝ) :
    minimaxBudget d L R ε = none ↔ ¬ ∃ m, AdmissibleBudget d m L R ε := by
  classical
  unfold minimaxBudget
  split <;> simp_all

theorem minimaxBudget_eq_some_iff (d m : ℕ) (L R ε : ℝ) :
    minimaxBudget d L R ε = some m ↔
    AdmissibleBudget d m L R ε ∧ ∀ n, AdmissibleBudget d n L R ε → m ≤ n := by
  classical
  unfold minimaxBudget
  split
  · rename_i h
    constructor
    · intro hm
      have hm' := Option.some.inj hm
      subst m
      exact ⟨Nat.find_spec h, fun n hn => Nat.find_min' h hn⟩
    · rintro ⟨hm, hmin⟩
      congr 1
      exact le_antisymm (Nat.find_min' h hm) (hmin _ (Nat.find_spec h))
  · rename_i h
    constructor
    · intro he; cases he
    · rintro ⟨hm, _⟩; exact False.elim (h ⟨m, hm⟩)

/-- Every feasible measurable seed-dependent point is a legal zero-query output. -/
def zeroQueryPolicy {d R Ω} [MeasurableSpace Ω] (z : Ω → Point d)
    (hz : Measurable z) (hfeas : ∀ ω, Feasible R (z ω)) : Policy d R Ω where
  query := fun _ _ => 0
  query_measurable := fun _ => measurable_const
  stop := fun _ _ => true
  stop_measurable := fun _ => measurable_const
  output := fun _ h => z h.1
  output_measurable := fun _ => hz.comp measurable_fst
  output_feasible := fun _ h => hfeas h.1

theorem zeroQueryPolicy_run {d R Ω} [MeasurableSpace Ω] (z : Ω → Point d)
    (hz : Measurable z) (hfeas : ∀ ω, Feasible R (z ω))
    (f : Point d → ℝ) (m : ℕ) (ω : Ω) :
    run (zeroQueryPolicy z hz hfeas) f m ω = z ω := by
  cases m <;> rfl

theorem zeroQueryPolicy_uses_zero {d R Ω} [MeasurableSpace Ω] (z : Ω → Point d)
    (hz : Measurable z) (hfeas : ∀ ω, Feasible R (z ω))
    (f : Point d → ℝ) (m : ℕ) (ω : Ω) :
    queriesUsed (zeroQueryPolicy z hz hfeas) f m 0 (ω, Fin.elim0) = 0 := by
  cases m <;> rfl

/-- Divide the reply coordinates, leaving the independent seed unchanged. -/
def replyScale {Ω : Type*} (c : ℝ) {n : ℕ} (h : Ω × (Fin n → ℝ)) :
    Ω × (Fin n → ℝ) := (h.1, fun i => h.2 i / c)

theorem replyScale_measurable {Ω : Type*} [MeasurableSpace Ω] (c : ℝ) (n : ℕ) :
    Measurable (@replyScale Ω c n) := by
  apply measurable_fst.prodMk
  apply measurable_pi_lambda
  intro i
  exact (show Measurable (fun h : Ω × (Fin n → ℝ) => h.2 i) from
    (measurable_pi_apply i).comp measurable_snd).div_const c

/-- A concrete simulator: scale query/output points by `s`, and divide the
observed scalar replies by `c` before passing them to the source policy. -/
def Policy.rescale {d R Ω} [MeasurableSpace Ω] (a : Policy d R Ω)
    (s c : ℝ) (hs : 0 < s) : Policy d (s*R) Ω where
  query := fun n h => s • a.query n (replyScale c h)
  query_measurable := fun n => ((a.query_measurable n).comp (replyScale_measurable c n)).const_smul s
  stop := fun n h => a.stop n (replyScale c h)
  stop_measurable := fun n => (a.stop_measurable n).comp (replyScale_measurable c n)
  output := fun n h => s • a.output n (replyScale c h)
  output_measurable := fun n => ((a.output_measurable n).comp (replyScale_measurable c n)).const_smul s
  output_feasible := by
    intro n h
    change ‖s • a.output n (replyScale c h)‖ ≤ s*R
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hs]
    exact mul_le_mul_of_nonneg_left (a.output_feasible n _) hs.le

theorem replyScale_nextHistory {d R Ω} [MeasurableSpace Ω] (a : Policy d R Ω)
    (s c : ℝ) (hs : 0 < s) (f : Point d → ℝ) (n : ℕ)
    (h : Ω × (Fin n → ℝ)) :
    replyScale c (nextHistory (a.rescale s c hs) f n h) =
    nextHistory a (fun x => f (s • x) / c) n (replyScale c h) := by
  apply Prod.ext
  · rfl
  · funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp [replyScale, nextHistory, Policy.rescale]
    · simp [replyScale, nextHistory, Policy.rescale]

theorem execute_rescale {d R Ω} [MeasurableSpace Ω] (a : Policy d R Ω)
    (s c : ℝ) (hs : 0 < s) (f : Point d → ℝ) (fuel n : ℕ)
    (h : Ω × (Fin n → ℝ)) :
    execute (a.rescale s c hs) f fuel n h =
    s • execute a (fun x => f (s • x) / c) fuel n (replyScale c h) := by
  induction fuel generalizing n with
  | zero => rfl
  | succ k ih =>
    simp only [execute]
    change (if a.stop n (replyScale c h) then s • a.output n (replyScale c h)
      else execute (a.rescale s c hs) f k (n+1) (nextHistory (a.rescale s c hs) f n h)) =
      s • (if a.stop n (replyScale c h) then a.output n (replyScale c h)
      else execute a (fun x => f (s • x) / c) k (n+1)
        (nextHistory a (fun x => f (s • x) / c) n (replyScale c h)))
    split
    · rfl
    · rw [ih, replyScale_nextHistory]

theorem run_rescale {d R Ω} [MeasurableSpace Ω] (a : Policy d R Ω)
    (s c : ℝ) (hs : 0 < s) (f : Point d → ℝ) (m : ℕ) (ω : Ω) :
    run (a.rescale s c hs) f m ω =
    s • run a (fun x => f (s • x) / c) m ω := by
  have he : replyScale c (ω, (Fin.elim0 : Fin 0 → ℝ)) = (ω, Fin.elim0) := by
    apply Prod.ext
    · rfl
    · funext i; exact Fin.elim0 i
  simpa only [run, he] using execute_rescale a s c hs f m 0 (ω, Fin.elim0)

/-- Positive horizontal/vertical scaling preserves the full global objective
class, with the exact transformed Lipschitz constant. -/
def Objective.rescale {d L} (f : Objective d L) (hL : 0 ≤ L)
    (s c : ℝ) (hs : 0 < s) (hc : 0 < c) : Objective d (L*s/c) where
  toFun := fun x => f (s • x) / c
  convex := by
    have hh := f.convex.comp_linearMap (s • (LinearMap.id : Point d →ₗ[ℝ] Point d))
    have hh' : ConvexOn ℝ univ (fun x : Point d => f (s • x)) := by
      simpa [Function.comp_def] using hh
    simpa [smul_eq_mul, div_eq_mul_inv, mul_comm] using hh'.smul (inv_nonneg.mpr hc.le)
  lip := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    have hf := f.lip.dist_le_mul (s • x) (s • y)
    rw [Real.coe_toNNReal L hL, dist_smul₀, Real.norm_eq_abs, abs_of_pos hs] at hf
    have hconst : 0 ≤ L*s/c := by positivity
    rw [Real.coe_toNNReal _ hconst]
    calc
      dist (f (s • x) / c) (f (s • y) / c) = dist (f (s • x)) (f (s • y)) / c := by
        simp only [Real.dist_eq, ← sub_div, abs_div, abs_of_pos hc]
      _ ≤ (L * (s * dist x y)) / c := div_le_div_of_nonneg_right hf hc.le
      _ = L*s/c * dist x y := by ring

theorem feasible_scaled {d R} {s : ℝ} (hs : 0 < s) (x : Point d)
    (hx : Feasible R x) : Feasible (s*R) (s • x) := by
  change ‖s • x‖ ≤ s*R
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hs]
  exact mul_le_mul_of_nonneg_left hx hs.le

theorem feasible_unscaled {d R} {s : ℝ} (hs : 0 < s) (x : Point d)
    (hx : Feasible (s*R) x) : Feasible R (s⁻¹ • x) := by
  change ‖s⁻¹ • x‖ ≤ R
  rw [norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hs]
  apply (inv_mul_le_iff₀ hs).2
  exact hx

theorem successEvent_rescale {d L R Ω} [MeasurableSpace Ω]
    (a : Policy d R Ω) (f : Objective d L) (hL : 0 ≤ L) (hR : 0 ≤ R)
    (s c : ℝ) (hs : 0 < s) (hc : 0 < c) (m : ℕ) (ε : ℝ) :
    successEvent (a.rescale s c hs) f m (c*ε) =
      successEvent a (f.rescale hL s c hs hc) m ε := by
  ext ω
  rw [success_iff_comparison (a.rescale s c hs) f (mul_nonneg hs.le hR),
    success_iff_comparison a (f.rescale hL s c hs hc) hR]
  rw [run_rescale]
  constructor
  · intro h y hy
    have hh := h (s • y) (feasible_scaled hs y hy)
    change f (s • run a (fun x => f (s • x) / c) m ω) / c ≤ f (s • y) / c + ε
    apply (div_le_iff₀ hc).2
    have he : (f (s • y) / c + ε) * c = f (s • y) + c*ε := by field_simp
    rw [he]
    exact hh
  · intro h y hy
    have hh := h (s⁻¹ • y) (feasible_unscaled hs y hy)
    change f (s • run a (fun x => f (s • x) / c) m ω) / c ≤
      f (s • (s⁻¹ • y)) / c + ε at hh
    rw [smul_smul, mul_inv_cancel₀ hs.ne', one_smul] at hh
    have hh' := (div_le_iff₀ hc).1 hh
    have hcval : (f y / c + ε) * c = f y + c*ε := by field_simp
    rw [hcval] at hh'
    exact hh'

theorem admissible_rescale {d m L R ε} (hL : 0 ≤ L) (hR : 0 ≤ R)
    (s c : ℝ) (hs : 0 < s) (hc : 0 < c)
    (h : AdmissibleBudget d m (L*s/c) R ε) :
    AdmissibleBudget d m L (s*R) (c*ε) := by
  obtain ⟨Ω, ms, μ, hp, a, ha⟩ := h
  refine ⟨Ω, ms, μ, hp, a.rescale s c hs, ?_⟩
  intro f
  rw [successEvent_rescale a f hL hR s c hs hc]
  exact ha (f.rescale hL s c hs hc)

/-- Both directions of the manuscript normalization hold for the genuine
randomized adaptive minimax problem, at the same pathwise query cap. -/
theorem admissible_normalization {d m : ℕ} {L R ε : ℝ}
    (hL : 0 < L) (hR : 0 < R) :
    AdmissibleBudget d m L R ε ↔ AdmissibleBudget d m 1 1 (ε/(L*R)) := by
  have hLR : 0 < L*R := mul_pos hL hR
  constructor
  · intro h
    have hh := admissible_rescale (d:=d) (m:=m) (L:=1) (R:=R) (ε:=ε)
      (by norm_num) hR.le R⁻¹ (L*R)⁻¹ (inv_pos.mpr hR) (inv_pos.mpr hLR)
    have he : 1 * R⁻¹ / (L*R)⁻¹ = L := by field_simp
    rw [he] at hh
    have ht := hh h
    simpa [inv_mul_cancel₀ hR.ne', div_eq_mul_inv, mul_comm] using ht
  · intro h
    have hh := admissible_rescale (d:=d) (m:=m) (L:=L) (R:=1)
      (ε:=ε/(L*R)) hL.le (by norm_num) R (L*R) hR hLR
    have he : L*R/(L*R) = 1 := div_self hLR.ne'
    rw [he] at hh
    have ht := hh h
    simpa [mul_one, mul_div_cancel₀ ε hLR.ne'] using ht

theorem minimaxBudget_normalization {d : ℕ} {L R ε : ℝ}
    (hL : 0 < L) (hR : 0 < R) :
    minimaxBudget d L R ε = minimaxBudget d 1 1 (ε/(L*R)) := by
  cases hv : minimaxBudget d L R ε with
  | none =>
    have hn := (minimaxBudget_eq_none_iff d L R ε).1 hv
    symm
    apply (minimaxBudget_eq_none_iff d 1 1 (ε/(L*R))).2
    rintro ⟨m, hm⟩
    exact hn ⟨m, (admissible_normalization hL hR).2 hm⟩
  | some m =>
    have hm := (minimaxBudget_eq_some_iff d m L R ε).1 hv
    symm
    apply (minimaxBudget_eq_some_iff d m 1 1 (ε/(L*R))).2
    exact ⟨(admissible_normalization hL hR).1 hm.1,
      fun n hn => hm.2 n ((admissible_normalization hL hR).2 hn)⟩

/-- The complete finite list of exact query/reply pairs, with no padded calls. -/
def oracleTrace {d R Ω} [MeasurableSpace Ω] (a : Policy d R Ω)
    (f : Point d → ℝ) : (fuel n : ℕ) → Ω × (Fin n → ℝ) → List (Point d × ℝ)
  | 0, _, _ => []
  | k+1, n, h => if a.stop n h then []
      else (a.query n h, f (a.query n h)) :: oracleTrace a f k (n+1) (nextHistory a f n h)

theorem oracleTrace_length {d R Ω} [MeasurableSpace Ω] (a : Policy d R Ω)
    (f : Point d → ℝ) (fuel n : ℕ) (h : Ω × (Fin n → ℝ)) :
    (oracleTrace a f fuel n h).length = queriesUsed a f fuel n h := by
  induction fuel generalizing n with
  | zero => rfl
  | succ k ih =>
    simp only [oracleTrace, queriesUsed]
    split
    · rfl
    · simp only [List.length_cons, ih]; omega

theorem oracleTrace_forceCap {d R Ω} [MeasurableSpace Ω] (a : Policy d R Ω)
    (f : Point d → ℝ) (k r n : ℕ) (h : Ω × (Fin n → ℝ)) :
    oracleTrace (a.forceCap (n+k)) f (k+r) n h = oracleTrace a f k n h := by
  induction k generalizing n with
  | zero => cases r <;> simp [oracleTrace, Policy.forceCap]
  | succ k ih =>
    have hlt : ¬ n + (k+1) ≤ n := by omega
    simp only [Nat.succ_add, oracleTrace, Policy.forceCap, hlt, ↓reduceIte]
    split
    · rfl
    · congr 1
      have hh := ih (n+1) (nextHistory a f n h)
      simpa [nextHistory, Policy.forceCap, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hh

theorem queriesUsed_forceCap {d R Ω} [MeasurableSpace Ω] (a : Policy d R Ω)
    (f : Point d → ℝ) (k r n : ℕ) (h : Ω × (Fin n → ℝ)) :
    queriesUsed (a.forceCap (n+k)) f (k+r) n h = queriesUsed a f k n h := by
  rw [← oracleTrace_length, ← oracleTrace_length, oracleTrace_forceCap]

theorem arbitrary_zero_query_output_error {d L R} (f : Objective d L) (hL : 0 ≤ L)
    (x y : Point d) (hx : Feasible R x) (hy : Feasible R y) :
    f x - f y ≤ 2*L*R := by
  have hf := f.lip.dist_le_mul x y
  rw [Real.coe_toNNReal L hL, Real.dist_eq, dist_eq_norm] at hf
  have hnorm : ‖x-y‖ ≤ R+R := (norm_sub_le x y).trans (add_le_add hx hy)
  have hmul := mul_le_mul_of_nonneg_left hnorm hL
  have habs := le_abs_self (f x - f y)
  nlinarith

theorem center_output_error {d L R} (f : Objective d L) (hL : 0 ≤ L)
    (y : Point d) (hy : Feasible R y) : f 0 - f y ≤ L*R := by
  have hf := f.lip.dist_le_mul 0 y
  rw [Real.coe_toNNReal L hL, Real.dist_eq, dist_zero_left] at hf
  have habs := le_abs_self (f 0 - f y)
  have hmul := mul_le_mul_of_nonneg_left hy hL
  exact habs.trans (hf.trans hmul)

theorem admissible_zero_budget {d : ℕ} {L R ε : ℝ}
    (hL : 0 ≤ L) (hR : 0 ≤ R) (hε : L*R ≤ ε) :
    AdmissibleBudget d 0 L R ε := by
  let z : Unit → Point d := fun _ => 0
  have hz : Measurable z := measurable_const
  have hfeas : ∀ ω, Feasible R (z ω) := by intro ω; simpa [z, Feasible]
  let a := zeroQueryPolicy z hz hfeas
  refine ⟨Unit, inferInstance, Measure.dirac (), inferInstance, a, ?_⟩
  intro f
  have he : successEvent a f 0 ε = univ := by
    apply eq_univ_of_forall
    intro ω
    rw [success_iff_comparison a f hR]
    intro y hy
    rw [zeroQueryPolicy_run]
    change f 0 ≤ f y + ε
    have hh := center_output_error f hL y hy
    linarith
  rw [he]
  simp only [measure_univ]
  apply ENNReal.div_le_of_le_mul
  norm_num

theorem minimaxBudget_zero {d : ℕ} {L R ε : ℝ}
    (hL : 0 ≤ L) (hR : 0 ≤ R) (hε : L*R ≤ ε) :
    minimaxBudget d L R ε = some 0 := by
  apply (minimaxBudget_eq_some_iff d 0 L R ε).2
  exact ⟨admissible_zero_budget hL hR hε, fun n _ => Nat.zero_le n⟩

/-- Manuscript polynomial factor, with natural dimension coerced to the reals. -/
def profileQ (d : ℕ) (α : ℝ) : ℝ := (d:ℝ) * min (d:ℝ) ((α⁻¹)^2)

/-- All logarithms are natural, exactly as in manuscript §3.2. -/
def profileLambda (d : ℕ) (α : ℝ) : ℝ :=
  Real.log (Real.exp 1 * (d:ℝ)) + Real.log (Real.exp 1 / α)

/-- The manuscript's full joint profile, stated for the actual minimax problem.
This is an explicit unproved target, not a theorem or an assumed field in a
certificate. In particular it includes existence of a finite admissible budget.
No inhabitant of this proposition is asserted by this file. -/
def FullJointProfile (c0 : ℝ) : Prop :=
  ∃ (D : ℕ) (a b : ℝ), 0 < D ∧ 0 < a ∧ 0 < b ∧
    ∀ (d : ℕ), D ≤ d → ∀ (α : ℝ), 0 < α → α ≤ c0 →
      ∃ N : ℕ, minimaxBudget d 1 1 α = some N ∧
        a * profileQ d α / (profileLambda d α)^2 ≤ (N:ℝ) ∧
        (N:ℝ) ≤ b * profileQ d α * (profileLambda d α)^2

end Task003.OracleModel

end
end
-- END OracleModel.lean

-- BEGIN Geometry.lean
section

namespace PaperGeometry

abbrev L1Space (ι : Type*) := PiLp 1 (fun _ : ι => ℝ)
abbrev SignedSpace (ι : Type*) := L1Space (ι × Bool)

def simplex {ι : Type*} [Fintype ι] : Set (L1Space ι) :=
  {z | (∀ i, 0 ≤ z i) ∧ ∑ i, z i = 1}

noncomputable def signedLift {ι : Type*} (z : SignedSpace ι) : L1Space ι :=
  WithLp.toLp 1 (fun i => z (i, false) - z (i, true))

theorem l1_norm_eq_sum_abs {ι : Type*} [Fintype ι] (x : L1Space ι) :
    ‖x‖ = ∑ i, |x i| := by
  simpa using PiLp.norm_eq_sum (p := 1) (by norm_num) x

theorem signed_card (d : ℕ) : Fintype.card (Fin d × Bool) = 2 * d := by
  simp [Nat.mul_comm]

theorem signedLift_contraction {ι : Type*} [Fintype ι] (z w : SignedSpace ι) :
    ‖signedLift z - signedLift w‖ ≤ ‖z - w‖ := by
  rw [l1_norm_eq_sum_abs, l1_norm_eq_sum_abs, Fintype.sum_prod_type]
  simp only [Fintype.sum_bool]
  apply Finset.sum_le_sum
  intro i _
  change |(z (i, false) - z (i, true)) - (w (i, false) - w (i, true))| ≤
    |z (i, true) - w (i, true)| + |z (i, false) - w (i, false)|
  have h := abs_sub (z (i, false) - w (i, false)) (z (i, true) - w (i, true))
  calc
    _ = |(z (i, false) - w (i, false)) - (z (i, true) - w (i, true))| := by
      congr 1
      ring
    _ ≤ _ := by simpa [add_comm] using h

theorem signedLift_lipschitz {ι : Type*} [Fintype ι] :
    LipschitzWith 1 (@signedLift ι) := by
  apply LipschitzWith.of_dist_le_mul
  intro z w
  simpa [dist_eq_norm] using signedLift_contraction z w

theorem signedLift_simplex_mem_ball {ι : Type*} [Fintype ι]
    {z : SignedSpace ι} (hz : z ∈ simplex) : ‖signedLift z‖ ≤ 1 := by
  rw [l1_norm_eq_sum_abs]
  calc
    ∑ i, |signedLift z i| ≤ ∑ i, (z (i, false) + z (i, true)) := by
      apply Finset.sum_le_sum
      intro i _
      change |z (i, false) - z (i, true)| ≤ _
      exact abs_sub_le_iff.mpr ⟨by linarith [hz.1 (i, false), hz.1 (i, true)],
        by linarith [hz.1 (i, false), hz.1 (i, true)]⟩
    _ = 1 := by
      have hs := hz.2
      rw [Fintype.sum_prod_type] at hs
      simpa [Fintype.sum_bool, add_comm] using hs

lemma positive_parts_sub (a : ℝ) : max a 0 - max (-a) 0 = a := by
  rcases le_total 0 a with ha | ha
  · rw [max_eq_left ha, max_eq_right (by linarith)]
    ring
  · rw [max_eq_right ha, max_eq_left (by linarith)]
    ring

lemma positive_parts_add (a : ℝ) : max a 0 + max (-a) 0 = |a| := by
  rcases le_total 0 a with ha | ha
  · rw [max_eq_left ha, max_eq_right (by linarith), abs_of_nonneg ha]
    ring
  · rw [max_eq_right ha, max_eq_left (by linarith), abs_of_nonpos ha]
    ring

noncomputable def signedPreimage {ι : Type*} [Fintype ι] [DecidableEq ι]
    (i₀ : ι) (x : L1Space ι) : SignedSpace ι :=
  WithLp.toLp 1 (fun p => max (if p.2 then -x p.1 else x p.1) 0 +
    if p.1 = i₀ then (1 - ‖x‖) / 2 else 0)

theorem signedPreimage_lift {ι : Type*} [Fintype ι] [DecidableEq ι]
    (i₀ : ι) (x : L1Space ι) : signedLift (signedPreimage i₀ x) = x := by
  apply PiLp.ext
  intro i
  change (max (x i) 0 + (if i = i₀ then (1 - ‖x‖) / 2 else 0)) -
    (max (-x i) 0 + (if i = i₀ then (1 - ‖x‖) / 2 else 0)) = x i
  rw [add_sub_add_right_eq_sub, positive_parts_sub]

theorem signedPreimage_mem_simplex {ι : Type*} [Fintype ι] [DecidableEq ι]
    (i₀ : ι) (x : L1Space ι) (hx : ‖x‖ ≤ 1) :
    signedPreimage i₀ x ∈ simplex := by
  constructor
  · intro p
    change 0 ≤ max (if p.2 then -x p.1 else x p.1) 0 +
      if p.1 = i₀ then (1 - ‖x‖) / 2 else 0
    apply add_nonneg (le_max_right _ _)
    split_ifs <;> linarith
  · change ∑ p : ι × Bool, (max (if p.2 then -x p.1 else x p.1) 0 +
        if p.1 = i₀ then (1 - ‖x‖) / 2 else 0) = 1
    rw [Fintype.sum_prod_type]
    simp only [Fintype.sum_bool, Bool.false_eq_true, ↓reduceIte]
    calc
      ∑ i, ((max (-x i) 0 + if i = i₀ then (1 - ‖x‖) / 2 else 0) +
          (max (x i) 0 + if i = i₀ then (1 - ‖x‖) / 2 else 0)) =
          ∑ i, (|x i| + if i = i₀ then 1 - ‖x‖ else 0) := by
        apply Finset.sum_congr rfl
        intro i _
        have h := positive_parts_add (x i)
        split_ifs <;> linarith
      _ = 1 := by
        rw [Finset.sum_add_distrib, ← l1_norm_eq_sum_abs]
        simp

theorem signedLift_simplex_surjective {ι : Type*} [Fintype ι] [Nonempty ι]
    (x : L1Space ι) (hx : ‖x‖ ≤ 1) :
    ∃ z ∈ simplex, signedLift z = x := by
  classical
  let i₀ : ι := Classical.choice inferInstance
  exact ⟨signedPreimage i₀ x, signedPreimage_mem_simplex i₀ x hx,
    signedPreimage_lift i₀ x⟩

theorem signedLift_image_simplex {ι : Type*} [Fintype ι] [Nonempty ι] :
    signedLift '' (simplex : Set (SignedSpace ι)) = {x : L1Space ι | ‖x‖ ≤ 1} := by
  ext x
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact signedLift_simplex_mem_ball hz
  · exact signedLift_simplex_surjective x

noncomputable def toEuclidean {ι : Type*} (x : L1Space ι) : EuclideanSpace ℝ ι :=
  WithLp.toLp 2 (WithLp.ofLp x)

noncomputable def fromEuclidean {ι : Type*} (x : EuclideanSpace ℝ ι) : L1Space ι :=
  WithLp.toLp 1 (WithLp.ofLp x)

theorem l1_le_sqrt_card_l2 {ι : Type*} [Fintype ι] (x : L1Space ι) :
    ‖x‖ ≤ Real.sqrt (Fintype.card ι) * ‖toEuclidean x‖ := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun i : ι => |x i|) (fun _ : ι => (1 : ℝ))
  have he := EuclideanSpace.real_norm_sq_eq (toEuclidean x)
  change ‖toEuclidean x‖ ^ 2 = ∑ i, (x i) ^ 2 at he
  simp only [mul_one, one_pow, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    mul_one, sq_abs] at hcs
  rw [← l1_norm_eq_sum_abs, ← he] at hcs
  have hsq := Real.sq_sqrt (show (0 : ℝ) ≤ Fintype.card ι by positivity)
  have hs : 0 ≤ Real.sqrt (Fintype.card ι) := Real.sqrt_nonneg _
  have hn : 0 ≤ ‖toEuclidean x‖ := norm_nonneg _
  have hsqprod : (Real.sqrt (Fintype.card ι) * ‖toEuclidean x‖) ^ 2 =
      ‖toEuclidean x‖ ^ 2 * Fintype.card ι := by rw [mul_pow, hsq]; ring
  exact (sq_le_sq₀ (norm_nonneg x) (mul_nonneg hs hn)).1 (hcs.trans_eq hsqprod.symm)

def smallEuclideanBall (d : ℕ) : Set (L1Space (Fin d)) :=
  {x | ‖toEuclidean x‖ ≤ (Real.sqrt d)⁻¹}

theorem smallEuclideanBall_subset_l1_ball (d : ℕ) (hd : 0 < d) :
    smallEuclideanBall d ⊆ {x : L1Space (Fin d) | ‖x‖ ≤ 1} := by
  intro x hx
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hs : 0 < Real.sqrt d := Real.sqrt_pos.2 hdR
  calc
    ‖x‖ ≤ Real.sqrt d * ‖toEuclidean x‖ := by
      simpa using l1_le_sqrt_card_l2 x
    _ ≤ Real.sqrt d * (Real.sqrt d)⁻¹ := mul_le_mul_of_nonneg_left hx hs.le
    _ = 1 := mul_inv_cancel₀ hs.ne'

theorem toEuclidean_continuous {ι : Type*} [Fintype ι] :
    Continuous (@toEuclidean ι) :=
  (PiLp.continuous_toLp 2 _).comp (PiLp.continuous_ofLp 1 _)

theorem fromEuclidean_continuous {ι : Type*} [Fintype ι] :
    Continuous (@fromEuclidean ι) :=
  (PiLp.continuous_toLp 1 _).comp (PiLp.continuous_ofLp 2 _)

theorem smallEuclideanBall_compact (d : ℕ) : IsCompact (smallEuclideanBall d) := by
  have he : smallEuclideanBall d = fromEuclidean ''
      Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) (Real.sqrt d)⁻¹ := by
    ext x
    constructor
    · intro hx
      exact ⟨toEuclidean x, by
        simpa [smallEuclideanBall, Metric.mem_closedBall, dist_zero_right] using hx, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      simpa [smallEuclideanBall, toEuclidean, fromEuclidean,
        Metric.mem_closedBall, dist_zero_right] using hy
  rw [he]
  exact (isCompact_closedBall _ _).image fromEuclidean_continuous

theorem smallEuclideanBall_nonempty (d : ℕ) : (smallEuclideanBall d).Nonempty := by
  refine ⟨0, ?_⟩
  simp [smallEuclideanBall, toEuclidean]

theorem smallEuclideanBall_convex (d : ℕ) : Convex ℝ (smallEuclideanBall d) := by
  intro x hx y hy a b ha hb hab
  change ‖toEuclidean (a • x + b • y)‖ ≤ _
  have he : toEuclidean (a • x + b • y) = a • toEuclidean x + b • toEuclidean y := rfl
  rw [he]
  calc
    ‖a • toEuclidean x + b • toEuclidean y‖ ≤
        ‖a • toEuclidean x‖ + ‖b • toEuclidean y‖ := norm_add_le _ _
    _ = a * ‖toEuclidean x‖ + b * ‖toEuclidean y‖ := by
      rw [norm_smul, norm_smul, Real.norm_of_nonneg ha, Real.norm_of_nonneg hb]
    _ ≤ a * (Real.sqrt d)⁻¹ + b * (Real.sqrt d)⁻¹ :=
      add_le_add (mul_le_mul_of_nonneg_left hx ha) (mul_le_mul_of_nonneg_left hy hb)
    _ = (Real.sqrt d)⁻¹ := by rw [← add_mul, hab, one_mul]

noncomputable def rowValue {ι : Type*} [Fintype ι] (a : ι → ℝ) (x : L1Space ι) : ℝ :=
  ∑ j, a j * x j

theorem rowValue_lipschitz {ι : Type*} [Fintype ι] (a : ι → ℝ)
    (U : NNReal) (ha : ∀ j, |a j| ≤ U) : LipschitzWith U (rowValue a) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [Real.dist_eq, dist_eq_norm, l1_norm_eq_sum_abs]
  have he : rowValue a x - rowValue a y = ∑ j, a j * (x j - y j) := by
    simp only [rowValue, mul_sub, Finset.sum_sub_distrib]
  rw [he]
  calc
    |∑ j, a j * (x j - y j)| ≤ ∑ j, |a j * (x j - y j)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, (U : ℝ) * |x j - y j| := by
      apply Finset.sum_le_sum
      intro j _
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right (ha j) (abs_nonneg _)
    _ = _ := by rw [Finset.mul_sum]; rfl

noncomputable def supportValue {ι κ : Type*} [Fintype ι] [Fintype κ] [Nonempty κ]
    (rows : κ → ι → ℝ) (x : L1Space ι) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun i => rowValue (rows i) x)

theorem supportValue_lipschitz {ι κ : Type*} [Fintype ι] [Fintype κ] [Nonempty κ]
    (rows : κ → ι → ℝ) (U : NNReal) (hrows : ∀ i j, |rows i j| ≤ U) :
    LipschitzWith U (supportValue rows) := by
  apply LipschitzWith.of_le_add_mul
  intro x y
  apply (Finset.sup'_le_iff _ _).2
  intro i hi
  calc
    rowValue (rows i) x ≤ rowValue (rows i) y + (U : ℝ) * dist x y :=
      (rowValue_lipschitz (rows i) U (hrows i)).le_add_mul x y
    _ ≤ supportValue rows y + (U : ℝ) * dist x y := by
      exact add_le_add (Finset.le_sup' (fun i => rowValue (rows i) y) hi) le_rfl

theorem supportValue_convex {ι κ : Type*} [Fintype ι] [Fintype κ] [Nonempty κ]
    (rows : κ → ι → ℝ) : ConvexOn ℝ Set.univ (supportValue rows) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb _
  apply (Finset.sup'_le_iff _ _).2
  intro i hi
  have he : rowValue (rows i) (a • x + b • y) =
      a * rowValue (rows i) x + b * rowValue (rows i) y := by
    change (∑ j, rows i j * (a * x j + b * y j)) =
      a * (∑ j, rows i j * x j) + b * (∑ j, rows i j * y j)
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [he]
  apply add_le_add
  · exact mul_le_mul_of_nonneg_left (Finset.le_sup' (f := fun i => rowValue (rows i) x) hi) ha
  · exact mul_le_mul_of_nonneg_left (Finset.le_sup' (f := fun i => rowValue (rows i) y) hi) hb

theorem supportValue_homogeneous {ι κ : Type*} [Fintype ι] [Fintype κ] [Nonempty κ]
    (rows : κ → ι → ℝ) (t : ℝ) (ht : 0 ≤ t) (x : L1Space ι) :
    supportValue rows (t • x) = t * supportValue rows x := by
  classical
  obtain ⟨i, hi, he⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
    (fun i => rowValue (rows i) x)
  have hrow : ∀ j, rowValue (rows j) (t • x) = t * rowValue (rows j) x := by
    intro j
    change (∑ k, rows j k * (t * x k)) = t * ∑ k, rows j k * x k
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring
  apply le_antisymm
  · apply (Finset.sup'_le_iff _ _).2
    intro j hj
    rw [hrow]
    exact mul_le_mul_of_nonneg_left (Finset.le_sup' (fun j => rowValue (rows j) x) hj) ht
  · change t * (Finset.univ.sup' _ (fun i => rowValue (rows i) x)) ≤ _
    rw [he, ← hrow]
    exact Finset.le_sup' (fun i => rowValue (rows i) (t • x)) hi

theorem scaled_supportValue_lipschitz {ι κ : Type*} [Fintype ι] [Fintype κ] [Nonempty κ]
    (rows : κ → ι → ℝ) (U β : NNReal) (hrows : ∀ i j, |rows i j| ≤ U) :
    LipschitzWith (β * U) (fun x : L1Space ι => supportValue rows ((β : ℝ) • x)) := by
  have hs : LipschitzWith β (fun x : L1Space ι => (β : ℝ) • x) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [dist_smul₀]
    simp
  simpa only [Function.comp_def, mul_comm] using (supportValue_lipschitz rows U hrows).comp hs

theorem scaled_supportValue_convex {ι κ : Type*} [Fintype ι] [Fintype κ] [Nonempty κ]
    (rows : κ → ι → ℝ) (β : NNReal) :
    ConvexOn ℝ Set.univ (fun x : L1Space ι => supportValue rows ((β : ℝ) • x)) := by
  have he : (fun x : L1Space ι => supportValue rows ((β : ℝ) • x)) =
      fun x => (β : ℝ) • supportValue rows x := by
    funext x
    exact supportValue_homogeneous rows β β.coe_nonneg x
  rw [he]
  exact (supportValue_convex rows).smul β.coe_nonneg

theorem smallEuclideanBall_scaled_image (d : ℕ) (hd : 0 < d) :
    (fun x : L1Space (Fin d) => Real.sqrt d • toEuclidean x) '' smallEuclideanBall d =
      Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) 1 := by
  have hs : 0 < Real.sqrt (d : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hd)
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_of_nonneg hs.le]
    calc
      Real.sqrt d * ‖toEuclidean x‖ ≤ Real.sqrt d * (Real.sqrt d)⁻¹ :=
        mul_le_mul_of_nonneg_left hx hs.le
      _ = 1 := mul_inv_cancel₀ hs.ne'
  · intro hz
    refine ⟨fromEuclidean ((Real.sqrt d)⁻¹ • z), ?_, ?_⟩
    · change ‖(Real.sqrt d)⁻¹ • z‖ ≤ (Real.sqrt d)⁻¹
      rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hs.le)]
      simpa using mul_le_mul_of_nonneg_left
        (show ‖z‖ ≤ 1 by simpa [Metric.mem_closedBall, dist_zero_right] using hz)
        (inv_nonneg.mpr hs.le)
    · change Real.sqrt d • ((Real.sqrt d)⁻¹ • z) = z
      rw [smul_smul, mul_inv_cancel₀ hs.ne', one_smul]

theorem signedLift_linear_combo {ι : Type*} (a b : ℝ) (z w : SignedSpace ι) :
    signedLift (a • z + b • w) = a • signedLift z + b • signedLift w := by
  apply PiLp.ext
  intro i
  change (a * z (i, false) + b * w (i, false)) -
    (a * z (i, true) + b * w (i, true)) =
    a * (z (i, false) - z (i, true)) + b * (w (i, false) - w (i, true))
  ring

theorem signedLift_comp_convex {ι : Type*} [Fintype ι] (f : L1Space ι → ℝ)
    (hf : ConvexOn ℝ Set.univ f) : ConvexOn ℝ Set.univ (fun z => f (signedLift z)) := by
  refine ⟨convex_univ, ?_⟩
  intro z _ w _ a b ha hb hab
  change f (signedLift (a • z + b • w)) ≤ a • f (signedLift z) + b • f (signedLift w)
  rw [signedLift_linear_combo]
  exact hf.2 (Set.mem_univ _) (Set.mem_univ _) ha hb hab

theorem signedLift_comp_lipschitz {ι : Type*} [Fintype ι] (f : L1Space ι → ℝ)
    (hf : LipschitzWith 1 f) : LipschitzWith 1 (fun z => f (signedLift z)) := by
  simpa only [Function.comp_def, mul_one] using hf.comp signedLift_lipschitz

noncomputable def sourceSupport {ι κ : Type*} [Fintype ι] [Fintype κ] [Nonempty κ]
    (rows : κ → ι → ℝ) (x : EuclideanSpace ℝ ι) : ℝ :=
  supportValue rows (fromEuclidean x)

theorem sourceSupport_convex {ι κ : Type*} [Fintype ι] [Fintype κ] [Nonempty κ]
    (rows : κ → ι → ℝ) : ConvexOn ℝ Set.univ (sourceSupport rows) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  change supportValue rows (a • fromEuclidean x + b • fromEuclidean y) ≤
    a • supportValue rows (fromEuclidean x) + b • supportValue rows (fromEuclidean y)
  exact (supportValue_convex rows).2 (Set.mem_univ _) (Set.mem_univ _) ha hb hab

theorem euclidean_row_lipschitz {ι : Type*} [Fintype ι] (a : ι → ℝ)
    (ha : ‖(WithLp.toLp 2 a : EuclideanSpace ℝ ι)‖ ≤ 1) :
    LipschitzWith 1 (fun x : EuclideanSpace ℝ ι => rowValue a (fromEuclidean x)) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [NNReal.coe_one, one_mul, dist_eq_norm]
  have he : rowValue a (fromEuclidean x) - rowValue a (fromEuclidean y) =
      inner (𝕜 := ℝ) (WithLp.toLp 2 a : EuclideanSpace ℝ ι) (x - y) := by
    simp [rowValue, fromEuclidean, PiLp.inner_apply, mul_sub, mul_comm,
      Finset.sum_sub_distrib]
  rw [he]
  exact (abs_real_inner_le_norm _ _).trans (by nlinarith [norm_nonneg (x - y)])

theorem sourceSupport_lipschitz {ι κ : Type*} [Fintype ι] [Fintype κ] [Nonempty κ]
    (rows : κ → ι → ℝ) (hrows : ∀ i,
      ‖(WithLp.toLp 2 (rows i) : EuclideanSpace ℝ ι)‖ ≤ 1) :
    LipschitzWith 1 (sourceSupport rows) := by
  apply LipschitzWith.of_le_add_mul
  intro x y
  apply (Finset.sup'_le_iff Finset.univ_nonempty
    (fun i => rowValue (rows i) (fromEuclidean x))).2
  intro i hi
  calc
    rowValue (rows i) (fromEuclidean x) ≤
        rowValue (rows i) (fromEuclidean y) + 1 * dist x y :=
      (euclidean_row_lipschitz (rows i) (hrows i)).le_add_mul x y
    _ ≤ sourceSupport rows y + 1 * dist x y := by
      exact add_le_add
        (Finset.le_sup' (fun i => rowValue (rows i) (fromEuclidean y)) hi) le_rfl

end PaperGeometry


end
-- END Geometry.lean

-- BEGIN GeometryPenalty.lean
section

namespace PaperGeometryPenalty

open PaperGeometry PaperPenaltyReduction

noncomputable def beta (d : ℕ) : NNReal := ⟨Real.sqrt d, Real.sqrt_nonneg _⟩

noncomputable def scaledSupport {κ : Type*} [Fintype κ] [Nonempty κ]
    (d : ℕ) (rows : κ → Fin d → ℝ) (x : L1Space (Fin d)) : ℝ :=
  supportValue rows ((beta d : ℝ) • x)

noncomputable def normalizedSupportPenalty {κ : Type*} [Fintype κ] [Nonempty κ]
    (d : ℕ) (rows : κ → Fin d → ℝ) (U : NNReal) (x : L1Space (Fin d)) : ℝ :=
  penalty (beta d * U) (scaledSupport d rows) (smallEuclideanBall d) x /
    (2 * (beta d * U : NNReal))

theorem scaledSupport_source_identity {κ : Type*} [Fintype κ] [Nonempty κ]
    (d : ℕ) (rows : κ → Fin d → ℝ) (x : L1Space (Fin d)) :
    scaledSupport d rows x = sourceSupport rows (Real.sqrt d • PaperGeometry.toEuclidean x) := rfl

theorem beta_mul_pos (d : ℕ) (hd : 0 < d) (U : NNReal) (hU : 0 < U) :
    0 < ((beta d * U : NNReal) : ℝ) := by
  have hs : 0 < Real.sqrt (d : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hd)
  have hUR : (0 : ℝ) < U := by exact_mod_cast hU
  exact mul_pos hs hUR

theorem normalizedSupportPenalty_lipschitz {κ : Type*} [Fintype κ] [Nonempty κ]
    (d : ℕ) (hd : 0 < d) (rows : κ → Fin d → ℝ) (U : NNReal) (hU : 0 < U)
    (hrows : ∀ i j, |rows i j| ≤ U) :
    LipschitzWith 1 (normalizedSupportPenalty d rows U) := by
  exact normalized_penalty_lipschitz (beta d * U) (scaledSupport d rows)
    (smallEuclideanBall d) (scaled_supportValue_lipschitz rows U (beta d) hrows)
    (beta_mul_pos d hd U hU)

theorem normalizedSupportPenalty_convex {κ : Type*} [Fintype κ] [Nonempty κ]
    (d : ℕ) (rows : κ → Fin d → ℝ) (U : NNReal) :
    ConvexOn ℝ Set.univ (normalizedSupportPenalty d rows U) := by
  have hp := penalty_convex (smallEuclideanBall d) (smallEuclideanBall_compact d)
    (smallEuclideanBall_nonempty d) (smallEuclideanBall_convex d) (beta d * U)
    (scaledSupport d rows) (scaled_supportValue_convex rows (beta d))
  refine ⟨convex_univ, ?_⟩
  intro x hx y hy a b ha hb hab
  have h := hp.2 hx hy ha hb hab
  simp only [smul_eq_mul] at h ⊢
  change penalty (beta d * U) (scaledSupport d rows) (smallEuclideanBall d)
      (a • x + b • y) / (2 * (beta d * U : NNReal)) ≤
    a * (penalty (beta d * U) (scaledSupport d rows) (smallEuclideanBall d) x /
      (2 * (beta d * U : NNReal))) +
    b * (penalty (beta d * U) (scaledSupport d rows) (smallEuclideanBall d) y /
      (2 * (beta d * U : NNReal)))
  calc
    _ ≤ (a * penalty (beta d * U) (scaledSupport d rows) (smallEuclideanBall d) x +
        b * penalty (beta d * U) (scaledSupport d rows) (smallEuclideanBall d) y) /
          (2 * (beta d * U : NNReal)) := div_le_div_of_nonneg_right h (by positivity)
    _ = _ := by ring

theorem normalizedSupportPenalty_minimum_decoder {κ : Type*} [Fintype κ] [Nonempty κ]
    (d : ℕ) (hd : 0 < d) (rows : κ → Fin d → ℝ) (U : NNReal) (hU : 0 < U)
    (hrows : ∀ i j, |rows i j| ≤ U) :
    ∃ u ∈ smallEuclideanBall d,
      ‖u‖ ≤ 1 ∧
      (∀ x : L1Space (Fin d), normalizedSupportPenalty d rows U u ≤
        normalizedSupportPenalty d rows U x) ∧
      (∀ z ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) 1,
        scaledSupport d rows u ≤ sourceSupport rows z) ∧
      (∀ x : L1Space (Fin d), ∀ ε : ℝ,
        normalizedSupportPenalty d rows U x - normalizedSupportPenalty d rows U u ≤ ε →
        ∃ z ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) 1,
          0 ≤ sourceSupport rows z - scaledSupport d rows u ∧
          sourceSupport rows z - scaledSupport d rows u ≤
            2 * ((beta d * U : NNReal) : ℝ) * ε) := by
  have hL := beta_mul_pos d hd U hU
  have hg := scaled_supportValue_lipschitz rows U (beta d) hrows
  obtain ⟨u, huS, hmin, huval, hglobal, hdecode⟩ :=
    global_minimum_and_decoder (smallEuclideanBall d) (smallEuclideanBall_compact d)
      (smallEuclideanBall_nonempty d) (beta d * U) (scaledSupport d rows) hg
  refine ⟨u, huS, smallEuclideanBall_subset_l1_ball d hd huS, ?_, ?_, ?_⟩
  · intro x
    exact div_le_div_of_nonneg_right (hglobal x) (by positivity)
  · intro z hz
    have hzimage : z ∈ (fun x : L1Space (Fin d) =>
        Real.sqrt d • PaperGeometry.toEuclidean x) '' smallEuclideanBall d := by
      rw [smallEuclideanBall_scaled_image d hd]
      exact hz
    obtain ⟨x, hxS, hxeq⟩ := hzimage
    rw [← hxeq, ← scaledSupport_source_identity]
    exact hmin x hxS
  · intro x ε hε
    have hgap := normalized_gap hL hε
    obtain ⟨y, hyS, _, hy0, hyε⟩ := hdecode x
      (2 * ((beta d * U : NNReal) : ℝ) * ε) hgap
    refine ⟨Real.sqrt d • PaperGeometry.toEuclidean y, ?_, ?_, ?_⟩
    · rw [← smallEuclideanBall_scaled_image d hd]
      exact ⟨y, hyS, rfl⟩
    · simpa only [← scaledSupport_source_identity] using hy0
    · simpa only [← scaledSupport_source_identity] using hyε

end PaperGeometryPenalty


end
-- END GeometryPenalty.lean

-- BEGIN MeasurableDecoder.lean
section

namespace PaperMeasurableDecoder

theorem exists_measurable_approx_nearest {E : Type*} [MetricSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (C : Set E) (hC : IsCompact C) (hCne : C.Nonempty) (δ : ℝ) (hδ : 0 < δ) :
    ∃ π : E → E, Measurable π ∧
      ∀ x, π x ∈ C ∧ dist x (π x) < Metric.infDist x C + δ := by
  classical
  letI : Nonempty C := hCne.to_subtype
  let s : ℕ → C := TopologicalSpace.denseSeq C
  have hs : DenseRange s := TopologicalSpace.denseRange_denseSeq C
  have hex : ∀ x : E, ∃ n : ℕ, dist x (s n : E) < Metric.infDist x C + δ := by
    intro x
    obtain ⟨y, hy, hxy⟩ := hC.exists_infDist_eq_dist hCne x
    obtain ⟨n, hn⟩ := (Metric.denseRange_iff.mp hs) ⟨y, hy⟩ δ hδ
    refine ⟨n, ?_⟩
    calc
      dist x (s n : E) ≤ dist x y + dist y (s n : E) := dist_triangle _ _ _
      _ < Metric.infDist x C + δ := by
        rw [hxy]
        have hnE : dist y (s n : E) < δ := hn
        linarith
  let π : E → E := fun x => s (Nat.find (hex x))
  refine ⟨π, ?_, ?_⟩
  · change Measurable (fun x : E => (s (Nat.find (hex x)) : E))
    apply Measurable.find (f := fun n (_ : E) => (s n : E))
      (fun _ => measurable_const) _ hex
    intro n
    exact measurableSet_lt (continuous_id.dist continuous_const).measurable
      ((Metric.continuous_infDist_pt C).add continuous_const).measurable
  · intro x
    exact ⟨(s (Nat.find (hex x))).property, Nat.find_spec (hex x)⟩

theorem exists_measurable_approx_penalty_decoder {E : Type*} [MetricSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (C : Set E) (hC : IsCompact C) (hCne : C.Nonempty)
    (L : NNReal) (g : E → ℝ) (hg : LipschitzWith L g) (δ : ℝ) (hδ : 0 < δ) :
    ∃ π : E → E, Measurable π ∧ ∀ x,
      π x ∈ C ∧ g (π x) ≤ g x + (L : ℝ) * Metric.infDist x C + (L : ℝ) * δ := by
  obtain ⟨π, hπ, happrox⟩ := exists_measurable_approx_nearest C hC hCne δ hδ
  refine ⟨π, hπ, ?_⟩
  intro x
  refine ⟨(happrox x).1, ?_⟩
  have h := hg.le_add_mul (π x) x
  have hd := mul_le_mul_of_nonneg_left (happrox x).2.le L.coe_nonneg
  rw [dist_comm (π x) x] at h
  linarith

end PaperMeasurableDecoder


end
-- END MeasurableDecoder.lean

-- BEGIN ApproxGeometryPenalty.lean
section

namespace PaperApproxGeometryPenalty

open PaperGeometry PaperGeometryPenalty PaperPenaltyReduction PaperMeasurableDecoder

theorem measurable_source_decoder_with_slack {κ : Type*} [Fintype κ] [Nonempty κ]
    (d : ℕ) (hd : 0 < d) (U : NNReal) (hU : 0 < U) (η : ℝ) (hη : 0 < η) :
    ∃ decode : L1Space (Fin d) → EuclideanSpace ℝ (Fin d),
      Measurable decode ∧
      (∀ x, decode x ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) 1) ∧
      ∀ (rows : κ → Fin d → ℝ), (∀ i j, |rows i j| ≤ U) →
      ∃ u ∈ smallEuclideanBall d,
        (∀ x : L1Space (Fin d), normalizedSupportPenalty d rows U u ≤
          normalizedSupportPenalty d rows U x) ∧
        (∀ z ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) 1,
          scaledSupport d rows u ≤ sourceSupport rows z) ∧
        (∀ x : L1Space (Fin d),
          normalizedSupportPenalty d rows U x - normalizedSupportPenalty d rows U u ≤
            η / (4 * ((beta d * U : NNReal) : ℝ)) →
          0 ≤ sourceSupport rows (decode x) - scaledSupport d rows u ∧
          sourceSupport rows (decode x) - scaledSupport d rows u ≤ 3 * η / 4 ∧
          sourceSupport rows (decode x) - scaledSupport d rows u < η) := by
  have hL := beta_mul_pos d hd U hU
  let δ : ℝ := η / (4 * ((beta d * U : NNReal) : ℝ))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨π, hπm, hπ⟩ := exists_measurable_approx_nearest
    (smallEuclideanBall d) (smallEuclideanBall_compact d) (smallEuclideanBall_nonempty d) δ hδ
  let decode : L1Space (Fin d) → EuclideanSpace ℝ (Fin d) :=
    fun x => Real.sqrt d • PaperGeometry.toEuclidean (π x)
  have hdmem : ∀ x, decode x ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) 1 := by
    intro x
    rw [← smallEuclideanBall_scaled_image d hd]
    exact ⟨π x, (hπ x).1, rfl⟩
  refine ⟨decode, ?_, hdmem, ?_⟩
  · exact (toEuclidean_continuous.measurable.comp hπm).const_smul (Real.sqrt (d : ℝ))
  · intro rows hrows
    have hg := scaled_supportValue_lipschitz rows U (beta d) hrows
    obtain ⟨u, huS, hmin, huval, hglobal, _⟩ :=
      global_minimum_and_decoder (smallEuclideanBall d) (smallEuclideanBall_compact d)
        (smallEuclideanBall_nonempty d) (beta d * U) (scaledSupport d rows) hg
    refine ⟨u, huS, ?_, ?_, ?_⟩
    · intro x
      exact div_le_div_of_nonneg_right (hglobal x) (by positivity)
    · intro z hz
      rw [← smallEuclideanBall_scaled_image d hd] at hz
      obtain ⟨x, hxS, rfl⟩ := hz
      exact hmin x hxS
    · intro x hx
      have hgap := normalized_gap hL hx
      have hπbound : scaledSupport d rows (π x) ≤
          penalty (beta d * U) (scaledSupport d rows) (smallEuclideanBall d) x +
            ((beta d * U : NNReal) : ℝ) * δ := by
        calc
          scaledSupport d rows (π x) ≤ scaledSupport d rows x +
              ((beta d * U : NNReal) : ℝ) * dist (π x) x := hg.le_add_mul (π x) x
          _ ≤ scaledSupport d rows x + ((beta d * U : NNReal) : ℝ) *
              (Metric.infDist x (smallEuclideanBall d) + δ) := by
            rw [dist_comm (π x) x]
            exact add_le_add le_rfl (mul_le_mul_of_nonneg_left (hπ x).2.le hL.le)
          _ = _ := by dsimp [penalty]; ring
      have halgebra : ∀ l : ℝ, 0 < l → l * (η / (4 * l)) = η / 4 := by
        intro l hl
        field_simp [hl.ne']
      have hLδ : ((beta d * U : NNReal) : ℝ) * δ = η / 4 := by
        exact halgebra _ hL
      have hnorm : 2 * ((beta d * U : NNReal) : ℝ) *
          (η / (4 * ((beta d * U : NNReal) : ℝ))) = η / 2 := by
        calc
          _ = 2 * (((beta d * U : NNReal) : ℝ) *
              (η / (4 * ((beta d * U : NNReal) : ℝ)))) := by ring
          _ = η / 2 := by rw [halgebra _ hL]; ring
      rw [hnorm, huval] at hgap
      rw [hLδ] at hπbound
      have hdiff : sourceSupport rows (decode x) - scaledSupport d rows u ≤ 3 * η / 4 := by
        change scaledSupport d rows (π x) - scaledSupport d rows u ≤ _
        linarith
      refine ⟨?_, hdiff, by linarith⟩
      change 0 ≤ scaledSupport d rows (π x) - scaledSupport d rows u
      exact sub_nonneg.mpr (hmin (π x) (hπ x).1)

end PaperApproxGeometryPenalty


end
-- END ApproxGeometryPenalty.lean

-- BEGIN GeometryOracle.lean
section

namespace PaperGeometryOracle

open PaperGeometry PaperGeometryPenalty PaperPenaltyReduction

noncomputable def radialQuery {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (x : E) : E := ‖x‖⁻¹ • x

theorem radialQuery_norm_le_one {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (x : E) : ‖radialQuery x‖ ≤ 1 := by
  by_cases hx : x = 0
  · simp [radialQuery, hx]
  · have hn := norm_ne_zero_iff.mpr hx
    rw [radialQuery, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg x)),
      inv_mul_cancel₀ hn]

theorem radialQuery_measurable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] : Measurable (@radialQuery E _ _) := by
  exact measurable_id.norm.inv.smul measurable_id

theorem sourceSupport_homogeneous {ι κ : Type*} [Fintype ι] [Fintype κ] [Nonempty κ]
    (rows : κ → ι → ℝ) (t : ℝ) (ht : 0 ≤ t) (x : EuclideanSpace ℝ ι) :
    sourceSupport rows (t • x) = t * sourceSupport rows x :=
  supportValue_homogeneous rows t ht (fromEuclidean x)

theorem sourceSupport_radial_value {ι κ : Type*} [Fintype ι] [Fintype κ] [Nonempty κ]
    (rows : κ → ι → ℝ) (x : EuclideanSpace ℝ ι) :
    sourceSupport rows x = ‖x‖ * sourceSupport rows (radialQuery x) := by
  by_cases hx : x = 0
  · have hz := homogeneous_zero_value (sourceSupport rows)
      (fun t ht x => sourceSupport_homogeneous rows t ht x)
    simp [hx, hz]
  · exact (homogeneous_radial_value (sourceSupport rows)
      (fun t ht x => sourceSupport_homogeneous rows t ht x) x hx).2

noncomputable def sourceQuery (d : ℕ) (x : L1Space (Fin d)) : EuclideanSpace ℝ (Fin d) :=
  radialQuery (Real.sqrt d • PaperGeometry.toEuclidean x)

noncomputable def sourceScale (d : ℕ) (U : NNReal) (x : L1Space (Fin d)) : ℝ :=
  ‖Real.sqrt d • PaperGeometry.toEuclidean x‖ / (2 * ((beta d * U : NNReal) : ℝ))

noncomputable def knownOffset (d : ℕ) (x : L1Space (Fin d)) : ℝ :=
  Metric.infDist x (smallEuclideanBall d) / 2

noncomputable def reconstruct (d : ℕ) (U : NNReal) (x : L1Space (Fin d)) (v : ℝ) : ℝ :=
  sourceScale d U x * v + knownOffset d x

theorem sourceQuery_feasible (d : ℕ) (x : L1Space (Fin d)) :
    sourceQuery d x ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) 1 := by
  simpa [sourceQuery, Metric.mem_closedBall, dist_zero_right] using
    radialQuery_norm_le_one (Real.sqrt d • PaperGeometry.toEuclidean x)

theorem sourceQuery_measurable (d : ℕ) : Measurable (sourceQuery d) := by
  exact radialQuery_measurable.comp
    ((toEuclidean_continuous.const_smul (Real.sqrt (d : ℝ))).measurable)

theorem sourceScale_measurable (d : ℕ) (U : NNReal) : Measurable (sourceScale d U) := by
  exact ((toEuclidean_continuous.const_smul (Real.sqrt (d : ℝ))).norm.measurable).div_const _

theorem knownOffset_measurable (d : ℕ) : Measurable (knownOffset d) := by
  exact (Metric.continuous_infDist_pt (smallEuclideanBall d)).measurable.div_const _

theorem reconstruct_measurable (d : ℕ) (U : NNReal) :
    Measurable (fun p : L1Space (Fin d) × ℝ => reconstruct d U p.1 p.2) := by
  exact ((sourceScale_measurable d U).comp measurable_fst).mul measurable_snd |>.add
    ((knownOffset_measurable d).comp measurable_fst)

theorem one_query_reconstruction {κ : Type*} [Fintype κ] [Nonempty κ]
    (d : ℕ) (hd : 0 < d) (rows : κ → Fin d → ℝ) (U : NNReal) (hU : 0 < U)
    (x : L1Space (Fin d)) :
    normalizedSupportPenalty d rows U x =
      reconstruct d U x (sourceSupport rows (sourceQuery d x)) := by
  have hL := beta_mul_pos d hd U hU
  have halgebra : ∀ a b r l : ℝ, l ≠ 0 →
      (a * r + l * b) / (2 * l) = a / (2 * l) * r + b / 2 := by
    intro a b r l hl
    field_simp [hl]
  change (scaledSupport d rows x + ((beta d * U : NNReal) : ℝ) *
      Metric.infDist x (smallEuclideanBall d)) / (2 * ((beta d * U : NNReal) : ℝ)) = _
  rw [scaledSupport_source_identity, sourceSupport_radial_value]
  exact halgebra _ _ _ _ hL.ne'

end PaperGeometryOracle


end
-- END GeometryOracle.lean

-- BEGIN OracleSimulation.lean
section

/-! Exact adaptive one-query simulation in the Euclidean source oracle model.
Dependencies by concatenation: OracleModel, baseline PenaltyReduction, Geometry,
GeometryPenalty and GeometryOracle. The decoder is a measurable map fixed before
the hidden support rows are supplied. No source lower bound is assumed here. -/
noncomputable section
namespace Task003.OracleSimulation
open Set MeasureTheory
open Task003.OracleModel
open PaperGeometryOracle PaperGeometryPenalty PaperGeometry

abbrev SourcePoint (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- Source queries and outputs belong to the actual Euclidean unit ball. -/
structure SourcePolicy (d : ℕ) (Ω : Type*) [MeasurableSpace Ω] where
  query : (n : ℕ) → Ω × (Fin n → ℝ) → SourcePoint d
  query_measurable : ∀ n, Measurable (query n)
  query_feasible : ∀ n h, ‖query n h‖ ≤ 1
  stop : (n : ℕ) → Ω × (Fin n → ℝ) → Bool
  stop_measurable : ∀ n, Measurable (stop n)
  output : (n : ℕ) → Ω × (Fin n → ℝ) → SourcePoint d
  output_measurable : ∀ n, Measurable (output n)
  output_feasible : ∀ n h, ‖output n h‖ ≤ 1

def historyPrefix {Ω : Type*} {n : ℕ} (h : Ω × (Fin (n+1) → ℝ)) : Ω × (Fin n → ℝ) :=
  (h.1, fun i => h.2 i.castSucc)

theorem historyPrefix_measurable {Ω : Type*} [MeasurableSpace Ω] (n : ℕ) :
    Measurable (@historyPrefix Ω n) := by
  apply measurable_fst.prodMk
  apply measurable_pi_lambda
  intro i
  exact (measurable_pi_apply i.castSucc).comp measurable_snd

/-- Reconstruct the target's reply historyPrefix from raw source replies. This recursive
map uses only the target policy, d and U; it has no hidden-rows argument. -/
def reconstructedHistory {d Ω} [MeasurableSpace Ω] (a : Policy d 1 Ω) (U : NNReal) :
    (n : ℕ) → Ω × (Fin n → ℝ) → Fin n → ℝ
  | 0, _ => Fin.elim0
  | n+1, h =>
    let v := reconstructedHistory a U n (historyPrefix h)
    Fin.snoc v (reconstruct d U (a.query n (h.1, v)) (h.2 (Fin.last n)))

def targetHistory {d Ω} [MeasurableSpace Ω] (a : Policy d 1 Ω) (U : NNReal)
    (n : ℕ) (h : Ω × (Fin n → ℝ)) : Ω × (Fin n → ℝ) :=
  (h.1, reconstructedHistory a U n h)

theorem reconstructedHistory_measurable {d Ω} [MeasurableSpace Ω]
    (a : Policy d 1 Ω) (U : NNReal) (n : ℕ) :
    Measurable (reconstructedHistory a U n) := by
  induction n with
  | zero => exact measurable_pi_lambda _ (fun i => Fin.elim0 i)
  | succ n ih =>
    have hv : Measurable (fun h : Ω × (Fin (n+1) → ℝ) =>
        reconstructedHistory a U n (historyPrefix h)) := ih.comp (historyPrefix_measurable n)
    apply measurable_pi_lambda
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa only [reconstructedHistory, Fin.snoc_last, Function.comp_def] using
        (reconstruct_measurable d U).comp
          (((a.query_measurable n).comp (measurable_fst.prodMk hv)).prodMk
            ((measurable_pi_apply (Fin.last n)).comp measurable_snd))
    · simpa only [reconstructedHistory, Fin.snoc_castSucc, Function.comp_def] using
        (measurable_pi_apply j).comp hv

theorem targetHistory_measurable {d Ω} [MeasurableSpace Ω]
    (a : Policy d 1 Ω) (U : NNReal) (n : ℕ) :
    Measurable (targetHistory a U n) :=
  measurable_fst.prodMk (reconstructedHistory_measurable a U n)

/-- The source simulator makes exactly one feasible source query for every
continued target query, including a source query at zero when that is selected. -/
def simulate {d Ω} [MeasurableSpace Ω] (a : Policy d 1 Ω) (U : NNReal)
    (decode : Point d → SourcePoint d) (hdecode : Measurable decode)
    (hfeas : ∀ x, Feasible 1 x → ‖decode x‖ ≤ 1) : SourcePolicy d Ω where
  query := fun n h => sourceQuery d (a.query n (targetHistory a U n h))
  query_measurable := fun n => (sourceQuery_measurable d).comp
    ((a.query_measurable n).comp (targetHistory_measurable a U n))
  query_feasible := by
    intro n h
    simpa only [Metric.mem_closedBall, dist_zero_right] using
      sourceQuery_feasible d (a.query n (targetHistory a U n h))
  stop := fun n h => a.stop n (targetHistory a U n h)
  stop_measurable := fun n => (a.stop_measurable n).comp (targetHistory_measurable a U n)
  output := fun n h => decode (a.output n (targetHistory a U n h))
  output_measurable := fun n => hdecode.comp
    ((a.output_measurable n).comp (targetHistory_measurable a U n))
  output_feasible := fun n h => hfeas _ (a.output_feasible n _)

def SourcePolicy.nextHistory {d Ω} [MeasurableSpace Ω] (b : SourcePolicy d Ω)
    (f : SourcePoint d → ℝ) (n : ℕ) (h : Ω × (Fin n → ℝ)) :
    Ω × (Fin (n+1) → ℝ) := (h.1, Fin.snoc h.2 (f (b.query n h)))

def SourcePolicy.execute {d Ω} [MeasurableSpace Ω] (b : SourcePolicy d Ω)
    (f : SourcePoint d → ℝ) : (fuel n : ℕ) → Ω × (Fin n → ℝ) → SourcePoint d
  | 0, n, h => b.output n h
  | k+1, n, h => if b.stop n h then b.output n h
    else b.execute f k (n+1) (b.nextHistory f n h)

def SourcePolicy.run {d Ω} [MeasurableSpace Ω] (b : SourcePolicy d Ω)
    (f : SourcePoint d → ℝ) (m : ℕ) (ω : Ω) : SourcePoint d :=
  b.execute f m 0 (ω, Fin.elim0)

def SourcePolicy.queriesUsed {d Ω} [MeasurableSpace Ω] (b : SourcePolicy d Ω)
    (f : SourcePoint d → ℝ) : (fuel n : ℕ) → Ω × (Fin n → ℝ) → ℕ
  | 0, _, _ => 0
  | k+1, n, h => if b.stop n h then 0
    else 1 + b.queriesUsed f k (n+1) (b.nextHistory f n h)

theorem SourcePolicy.queriesUsed_le {d Ω} [MeasurableSpace Ω] (b : SourcePolicy d Ω)
    (f : SourcePoint d → ℝ) (fuel n : ℕ) (h : Ω × (Fin n → ℝ)) :
    b.queriesUsed f fuel n h ≤ fuel := by
  induction fuel generalizing n with
  | zero => rfl
  | succ k ih =>
    simp only [SourcePolicy.queriesUsed]
    split
    · omega
    · have := ih (n+1) (b.nextHistory f n h); omega

theorem SourcePolicy.execute_feasible {d Ω} [MeasurableSpace Ω] (b : SourcePolicy d Ω)
    (f : SourcePoint d → ℝ) (fuel n : ℕ) (h : Ω × (Fin n → ℝ)) :
    ‖b.execute f fuel n h‖ ≤ 1 := by
  induction fuel generalizing n with
  | zero => exact b.output_feasible n h
  | succ k ih =>
    simp only [SourcePolicy.execute]
    split
    · exact b.output_feasible n h
    · exact ih (n+1) (b.nextHistory f n h)

theorem targetHistory_next {κ : Type*} [Fintype κ] [Nonempty κ]
    {d Ω} [MeasurableSpace Ω] (a : Policy d 1 Ω) (hd : 0 < d)
    (U : NNReal) (hU : 0 < U) (rows : κ → Fin d → ℝ)
    (decode : Point d → SourcePoint d) (hdecode : Measurable decode)
    (hfeas : ∀ x, Feasible 1 x → ‖decode x‖ ≤ 1)
    (n : ℕ) (h : Ω × (Fin n → ℝ)) :
    targetHistory a U (n+1)
      ((simulate a U decode hdecode hfeas).nextHistory (sourceSupport rows) n h) =
    nextHistory a (normalizedSupportPenalty d rows U) n (targetHistory a U n h) := by
  have hp : historyPrefix ((simulate a U decode hdecode hfeas).nextHistory (sourceSupport rows) n h) = h := by
    apply Prod.ext
    · rfl
    · funext i; simp [historyPrefix, SourcePolicy.nextHistory]
  apply Prod.ext
  · rfl
  · funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [targetHistory, reconstructedHistory, Fin.snoc_last]
      rw [hp]
      simp only [SourcePolicy.nextHistory, Fin.snoc_last, simulate, nextHistory, targetHistory]
      symm
      exact one_query_reconstruction d hd rows U hU _
    · simp only [targetHistory, reconstructedHistory, hp, Fin.snoc_castSucc, nextHistory]

theorem execute_simulate {κ : Type*} [Fintype κ] [Nonempty κ]
    {d Ω} [MeasurableSpace Ω] (a : Policy d 1 Ω) (hd : 0 < d)
    (U : NNReal) (hU : 0 < U) (rows : κ → Fin d → ℝ)
    (decode : Point d → SourcePoint d) (hdecode : Measurable decode)
    (hfeas : ∀ x, Feasible 1 x → ‖decode x‖ ≤ 1)
    (fuel n : ℕ) (h : Ω × (Fin n → ℝ)) :
    (simulate a U decode hdecode hfeas).execute (sourceSupport rows) fuel n h =
      decode (execute a (normalizedSupportPenalty d rows U) fuel n (targetHistory a U n h)) := by
  induction fuel generalizing n with
  | zero => rfl
  | succ k ih =>
    simp only [SourcePolicy.execute, execute]
    change (if a.stop n (targetHistory a U n h) then decode (a.output n (targetHistory a U n h))
      else (simulate a U decode hdecode hfeas).execute (sourceSupport rows) k (n+1)
        ((simulate a U decode hdecode hfeas).nextHistory (sourceSupport rows) n h)) =
      decode (if a.stop n (targetHistory a U n h) then a.output n (targetHistory a U n h)
        else execute a (normalizedSupportPenalty d rows U) k (n+1)
          (nextHistory a (normalizedSupportPenalty d rows U) n (targetHistory a U n h)))
    split
    · rfl
    · rw [ih, targetHistory_next a hd U hU rows decode hdecode hfeas]

theorem run_simulate {κ : Type*} [Fintype κ] [Nonempty κ]
    {d Ω} [MeasurableSpace Ω] (a : Policy d 1 Ω) (hd : 0 < d)
    (U : NNReal) (hU : 0 < U) (rows : κ → Fin d → ℝ)
    (decode : Point d → SourcePoint d) (hdecode : Measurable decode)
    (hfeas : ∀ x, Feasible 1 x → ‖decode x‖ ≤ 1) (m : ℕ) (ω : Ω) :
    (simulate a U decode hdecode hfeas).run (sourceSupport rows) m ω =
      decode (run a (normalizedSupportPenalty d rows U) m ω) := by
  have he : targetHistory a U 0 (ω, (Fin.elim0 : Fin 0 → ℝ)) = (ω, Fin.elim0) := rfl
  simpa only [SourcePolicy.run, run, he] using
    execute_simulate a hd U hU rows decode hdecode hfeas m 0 (ω, Fin.elim0)

theorem queriesUsed_simulate {κ : Type*} [Fintype κ] [Nonempty κ]
    {d Ω} [MeasurableSpace Ω] (a : Policy d 1 Ω) (hd : 0 < d)
    (U : NNReal) (hU : 0 < U) (rows : κ → Fin d → ℝ)
    (decode : Point d → SourcePoint d) (hdecode : Measurable decode)
    (hfeas : ∀ x, Feasible 1 x → ‖decode x‖ ≤ 1)
    (fuel n : ℕ) (h : Ω × (Fin n → ℝ)) :
    (simulate a U decode hdecode hfeas).queriesUsed (sourceSupport rows) fuel n h =
      queriesUsed a (normalizedSupportPenalty d rows U) fuel n (targetHistory a U n h) := by
  induction fuel generalizing n with
  | zero => rfl
  | succ k ih =>
    simp only [SourcePolicy.queriesUsed, queriesUsed]
    change (if a.stop n (targetHistory a U n h) then 0
      else 1 + (simulate a U decode hdecode hfeas).queriesUsed (sourceSupport rows) k (n+1)
        ((simulate a U decode hdecode hfeas).nextHistory (sourceSupport rows) n h)) =
      (if a.stop n (targetHistory a U n h) then 0
        else 1 + queriesUsed a (normalizedSupportPenalty d rows U) k (n+1)
          (nextHistory a (normalizedSupportPenalty d rows U) n (targetHistory a U n h)))
    split
    · rfl
    · rw [ih, targetHistory_next a hd U hU rows decode hdecode hfeas]

theorem SourcePolicy.nextHistory_measurable {d Ω} [MeasurableSpace Ω] (b : SourcePolicy d Ω)
    (f : SourcePoint d → ℝ) (hf : Measurable f) (n : ℕ) :
    Measurable (b.nextHistory f n) := by
  apply measurable_fst.prodMk
  apply measurable_pi_lambda
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simpa [SourcePolicy.nextHistory, Function.comp_def] using hf.comp (b.query_measurable n)
  · simpa [SourcePolicy.nextHistory, Function.comp_def] using
      (measurable_pi_apply j).comp measurable_snd

theorem SourcePolicy.execute_measurable {d Ω} [MeasurableSpace Ω] (b : SourcePolicy d Ω)
    (f : SourcePoint d → ℝ) (hf : Measurable f) (fuel n : ℕ) :
    Measurable (b.execute f fuel n) := by
  induction fuel generalizing n with
  | zero => exact b.output_measurable n
  | succ k ih =>
    exact Measurable.ite (measurableSet_eq_fun (b.stop_measurable n) measurable_const)
      (b.output_measurable n) ((ih (n+1)).comp (b.nextHistory_measurable f hf n))

theorem SourcePolicy.run_measurable {d Ω} [MeasurableSpace Ω] (b : SourcePolicy d Ω)
    (f : SourcePoint d → ℝ) (hf : Measurable f) (m : ℕ) : Measurable (b.run f m) :=
  (b.execute_measurable f hf m 0).comp (measurable_id.prodMk measurable_const)

theorem SourcePolicy.run_feasible {d Ω} [MeasurableSpace Ω] (b : SourcePolicy d Ω)
    (f : SourcePoint d → ℝ) (m : ℕ) (ω : Ω) : ‖b.run f m ω‖ ≤ 1 :=
  b.execute_feasible f m 0 _

end Task003.OracleSimulation

end
end
-- END OracleSimulation.lean

-- BEGIN OracleReduction.lean
section

/-! Probability-preserving reduction for actual adaptive measurable policies.
Concatenation dependencies: OracleModel, Geometry, GeometryPenalty,
MeasurableDecoder, ApproxGeometryPenalty, GeometryOracle, OracleSimulation, and
the unchanged baseline PenaltyReduction. No source hardness result is assumed. -/
noncomputable section
namespace Task003.OracleReduction
open Set MeasureTheory
open scoped ENNReal
open Task003.OracleModel Task003.OracleSimulation
open PaperGeometry PaperGeometryPenalty PaperApproxGeometryPenalty

/-- The normalized penalties are actual globally convex 1-Lipschitz objectives. -/
def supportPenaltyObjective {κ : Type*} [Fintype κ] [Nonempty κ]
    (d : ℕ) (hd : 0 < d) (rows : κ → Fin d → ℝ) (U : NNReal) (hU : 0 < U)
    (hrows : ∀ i j, |rows i j| ≤ U) : Objective d 1 where
  toFun := normalizedSupportPenalty d rows U
  convex := normalizedSupportPenalty_convex d rows U
  lip := by simpa using normalizedSupportPenalty_lipschitz d hd rows U hU hrows

theorem sourceSupport_measurable {κ : Type*} [Fintype κ] [Nonempty κ]
    (d : ℕ) (rows : κ → Fin d → ℝ) (U : NNReal)
    (hrows : ∀ i j, |rows i j| ≤ U) : Measurable (sourceSupport rows) :=
  ((supportValue_lipschitz rows U hrows).continuous.comp fromEuclidean_continuous).measurable

/-- The source minimum is attained in the Euclidean unit ball, and the same
private-seed success convention is used as in the target model. -/
def SourceSucceeds {d Ω} [MeasurableSpace Ω] (μ : Measure Ω) (b : SourcePolicy d Ω)
    (f : SourcePoint d → ℝ) (m : ℕ) (η : ℝ) : Prop :=
  ∃ z : SourcePoint d, ‖z‖ ≤ 1 ∧
    (∀ y : SourcePoint d, ‖y‖ ≤ 1 → f z ≤ f y) ∧
    MeasurableSet {ω | f (b.run f m ω) - f z ≤ η} ∧
    (2/3 : ℝ≥0∞) ≤ μ {ω | f (b.run f m ω) - f z ≤ η}

/-- A single source policy works for every hidden row family satisfying the
public bound. It shares exactly the target's private seed and pathwise cap.
The concrete measurable decoder is selected before the rows are quantified. -/
theorem source_simulator_of_target_solver {κ : Type*} [Fintype κ] [Nonempty κ]
    {d Ω} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (a : Policy d 1 Ω) (m : ℕ) (hd : 0 < d)
    (U : NNReal) (hU : 0 < U) (η : ℝ) (hη : 0 < η)
    (ha : SolvesOn μ a m 1 (η / (4 * ((beta d * U : NNReal) : ℝ)))) :
    ∃ b : SourcePolicy d Ω,
      (∀ (rows : κ → Fin d → ℝ), (∀ i j, |rows i j| ≤ U) →
        SourceSucceeds μ b (sourceSupport rows) m η) ∧
      (∀ (rows : κ → Fin d → ℝ) ω,
        b.queriesUsed (sourceSupport rows) m 0 (ω, Fin.elim0) ≤ m) := by
  obtain ⟨decode, hdecode, hdecodefeas, hdecodesuccess⟩ :=
    measurable_source_decoder_with_slack (κ:=κ) d hd U hU η hη
  have hfeas : ∀ x : Point d, Feasible 1 x → ‖decode x‖ ≤ 1 := by
    intro x _
    simpa only [Metric.mem_closedBall, dist_zero_right] using hdecodefeas x
  let b := simulate a U decode hdecode hfeas
  refine ⟨b, ?_, ?_⟩
  · intro rows hrows
    obtain ⟨u, huS, hglobal, hsource, hsuccess⟩ := hdecodesuccess rows hrows
    let z : SourcePoint d := Real.sqrt d • PaperGeometry.toEuclidean u
    have hz : ‖z‖ ≤ 1 := by
      have hmem : z ∈ Metric.closedBall (0 : SourcePoint d) 1 := by
        rw [← smallEuclideanBall_scaled_image d hd]
        exact ⟨u, huS, rfl⟩
      simpa only [Metric.mem_closedBall, dist_zero_right] using hmem
    have hfmeas := sourceSupport_measurable d rows U hrows
    refine ⟨z, hz, ?_, ?_, ?_⟩
    · intro y hy
      have hymem : y ∈ Metric.closedBall (0 : SourcePoint d) 1 := by
        simpa only [Metric.mem_closedBall, dist_zero_right] using hy
      exact hsource y hymem
    · exact measurableSet_le
        ((hfmeas.comp (b.run_measurable _ hfmeas m)).sub measurable_const) measurable_const
    · let f := supportPenaltyObjective d hd rows U hU hrows
      have hprob := ha f
      apply hprob.trans
      apply measure_mono
      intro ω hω
      have hu : Feasible 1 u := smallEuclideanBall_subset_l1_ball d hd huS
      have hcmp := (success_iff_comparison a f (by norm_num) m
        (η / (4 * ((beta d * U : NNReal) : ℝ))) ω).1 hω u hu
      have hgap : normalizedSupportPenalty d rows U
          (run a (normalizedSupportPenalty d rows U) m ω) -
          normalizedSupportPenalty d rows U u ≤ η / (4 * ((beta d * U : NNReal) : ℝ)) := by
        change normalizedSupportPenalty d rows U
          (run a (normalizedSupportPenalty d rows U) m ω) ≤
          normalizedSupportPenalty d rows U u + η / (4 * ((beta d * U : NNReal) : ℝ)) at hcmp
        linarith
      have hout := (hsuccess _ hgap).2.2.le
      change sourceSupport rows ((simulate a U decode hdecode hfeas).run (sourceSupport rows) m ω) -
        sourceSupport rows z ≤ η
      rw [run_simulate a hd U hU rows decode hdecode hfeas]
      exact hout
  · intro rows ω
    exact b.queriesUsed_le _ m 0 _

def sourceOptimum {d : ℕ} (f : SourcePoint d → ℝ) : ℝ :=
  sInf (f '' {z : SourcePoint d | ‖z‖ ≤ 1})

def sourceSuccessEvent {d Ω} [MeasurableSpace Ω] (b : SourcePolicy d Ω)
    (f : SourcePoint d → ℝ) (m : ℕ) (η : ℝ) : Set Ω :=
  {ω | f (b.run f m ω) - sourceOptimum f ≤ η}

theorem sourceOptimum_eq_of_min {d : ℕ} (f : SourcePoint d → ℝ)
    (z : SourcePoint d) (hz : ‖z‖ ≤ 1)
    (hmin : ∀ y : SourcePoint d, ‖y‖ ≤ 1 → f z ≤ f y) :
    sourceOptimum f = f z := by
  have hne : (f '' {z : SourcePoint d | ‖z‖ ≤ 1}).Nonempty := ⟨f z, z, hz, rfl⟩
  have hb : BddBelow (f '' {z : SourcePoint d | ‖z‖ ≤ 1}) := by
    refine ⟨f z, ?_⟩
    rintro v ⟨y, hy, rfl⟩
    exact hmin y hy
  apply le_antisymm (csInf_le hb ⟨z, hz, rfl⟩)
  exact le_csInf hne (by rintro v ⟨y, hy, rfl⟩; exact hmin y hy)

theorem SourceSucceeds.actual_success_event {d Ω} [MeasurableSpace Ω]
    {μ : Measure Ω} {b : SourcePolicy d Ω} {f : SourcePoint d → ℝ} {m : ℕ} {η : ℝ}
    (h : SourceSucceeds μ b f m η) :
    MeasurableSet (sourceSuccessEvent b f m η) ∧
      (2/3 : ℝ≥0∞) ≤ μ (sourceSuccessEvent b f m η) := by
  obtain ⟨z, hz, hmin, hmeas, hprob⟩ := h
  have ho := sourceOptimum_eq_of_min f z hz hmin
  simpa only [sourceSuccessEvent, ho] using And.intro hmeas hprob

/-- The source event used by a source-prior lower theorem is exactly the event
for optimization error relative to the Euclidean-ball minimum, not a substitute
scalar and not an event depending on a chosen proof witness. -/
theorem source_simulator_actual_success {κ : Type*} [Fintype κ] [Nonempty κ]
    {d Ω} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (a : Policy d 1 Ω) (m : ℕ) (hd : 0 < d)
    (U : NNReal) (hU : 0 < U) (η : ℝ) (hη : 0 < η)
    (ha : SolvesOn μ a m 1 (η / (4 * ((beta d * U : NNReal) : ℝ)))) :
    ∃ b : SourcePolicy d Ω,
      (∀ (rows : κ → Fin d → ℝ), (∀ i j, |rows i j| ≤ U) →
        MeasurableSet (sourceSuccessEvent b (sourceSupport rows) m η) ∧
          (2/3 : ℝ≥0∞) ≤ μ (sourceSuccessEvent b (sourceSupport rows) m η)) ∧
      (∀ (rows : κ → Fin d → ℝ) ω,
        b.queriesUsed (sourceSupport rows) m 0 (ω, Fin.elim0) ≤ m) := by
  obtain ⟨b, hb, hcap⟩ := source_simulator_of_target_solver (κ:=κ) μ a m hd U hU η hη ha
  exact ⟨b, fun rows hrows => (hb rows hrows).actual_success_event, hcap⟩

/-- The only hardness premise here is a failure theorem for the actual
Euclidean source oracle policies. It is an external interface, not an established
hardness theorem and not a lower bound on the target minimax supplied as input.
All target-to-source algorithms, decoding and success transfer are proved above. -/
theorem not_admissible_of_source_hardness {κ : Type*} [Fintype κ] [Nonempty κ]
    {d m : ℕ} (hd : 0 < d) (U : NNReal) (hU : 0 < U) (η : ℝ) (hη : 0 < η)
    (hsource : ∀ (Ω : Type) (s : MeasurableSpace Ω) (μ : @Measure Ω s),
      @IsProbabilityMeasure Ω s μ → ∀ b : @SourcePolicy d Ω s,
      (∀ (rows : κ → Fin d → ℝ) ω,
        b.queriesUsed (sourceSupport rows) m 0 (ω, Fin.elim0) ≤ m) →
      ∃ rows : κ → Fin d → ℝ, (∀ i j, |rows i j| ≤ U) ∧
        μ (sourceSuccessEvent b (sourceSupport rows) m η) < (2/3 : ℝ≥0∞)) :
    ¬ AdmissibleBudget d m 1 1 (η / (4 * ((beta d * U : NNReal) : ℝ))) := by
  rintro ⟨Ω, s, μ, hp, a, ha⟩
  letI : MeasurableSpace Ω := s
  letI : IsProbabilityMeasure μ := hp
  obtain ⟨b, hb, hcap⟩ := source_simulator_actual_success (κ:=κ) μ a m hd U hU η hη ha
  obtain ⟨rows, hrows, hbad⟩ := hsource Ω s μ hp b hcap
  exact (not_lt_of_ge (hb rows hrows).2) hbad

end Task003.OracleReduction

end
end
-- END OracleReduction.lean

-- BEGIN ProbabilityReduction.lean
section

/- Genuine probability-space reductions for MD 293--297 and 350--357.
   The source success bound is the paper's explicitly external theorem.
   This file does not assume an average success scalar in place of Yao,
   and it does not assert the adaptive Gaussian innovations or KL argument. -/
namespace PaperProbabilityReduction

open MeasureTheory ProbabilityTheory Set

/-- Conditioning on the actual source-prior event, using the target-to-source
success implication only on that event. -/
theorem target_success_under_conditional_prior
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (source target E : Set Ω) (hE : MeasurableSet E)
    (hsource : μ.real source ≤ (1 / 4 : ℝ))
    (hevent : (15 / 16 : ℝ) ≤ μ.real E)
    (htransfer : target ∩ E ⊆ source) :
    (cond μ E).real target ≤ (4 / 15 : ℝ) := by
  have hratio : (cond μ E).real target = μ.real (target ∩ E) / μ.real E := by
    simp only [measureReal_def, cond_apply hE, ENNReal.toReal_mul,
      ENNReal.toReal_inv, div_eq_mul_inv]
    rw [Set.inter_comm, mul_comm]
  rw [hratio]
  have hi : μ.real (target ∩ E) ≤ (1 / 4 : ℝ) :=
    (measureReal_mono htransfer).trans hsource
  have hpos : 0 < μ.real E := by linarith
  apply (div_le_iff₀ hpos).mpr
  nlinarith

/-- The event used in the conditional prior has full conditional probability. -/
theorem conditional_prior_event_probability
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (E : Set Ω) (hevent : (15 / 16 : ℝ) ≤ μ.real E) :
    (cond μ E) E = 1 := by
  apply cond_apply_self
  · apply (measureReal_ne_zero_iff).mp
    linarith
  · exact measure_ne_top μ E

/-- Tonelli averaging over the independent algorithm seed. The hypothesis is
one prior-event bound for each deterministic seed, not an average scalar. -/
theorem product_success_le_of_seedwise
    {Instance Seed : Type*} [MeasurableSpace Instance] [MeasurableSpace Seed]
    (prior : Measure Instance) (seed : Measure Seed)
    [IsProbabilityMeasure prior] [IsProbabilityMeasure seed]
    (success : Set (Instance × Seed)) (hsuccess : MeasurableSet success)
    (c : ℝ) (hc : 0 ≤ c)
    (hseedwise : ∀ s, prior.real {x | (x, s) ∈ success} ≤ c) :
    (prior.prod seed).real success ≤ c := by
  apply ENNReal.toReal_le_of_le_ofReal hc
  rw [Measure.prod_apply_symm hsuccess]
  calc
    (∫⁻ s, prior ((fun x => (x, s)) ⁻¹' success) ∂seed) ≤
        ∫⁻ _, ENNReal.ofReal c ∂seed := by
      apply lintegral_mono
      intro s
      exact (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) hc).mpr (hseedwise s)
    _ = ENNReal.ofReal c := by simp

/-- The other Tonelli direction: if every fixed instance has seed success at
least `c`, the joint product success also has probability at least `c`. -/
theorem product_success_ge_of_instancewise
    {Instance Seed : Type*} [MeasurableSpace Instance] [MeasurableSpace Seed]
    (prior : Measure Instance) (seed : Measure Seed)
    [IsProbabilityMeasure prior] [IsProbabilityMeasure seed]
    (success : Set (Instance × Seed)) (hsuccess : MeasurableSet success)
    (c : ℝ)
    (hinstancewise : ∀ x, c ≤ seed.real {s | (x, s) ∈ success}) :
    c ≤ (prior.prod seed).real success := by
  apply (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).mp
  rw [Measure.prod_apply hsuccess]
  calc
    ENNReal.ofReal c = ∫⁻ _, ENNReal.ofReal c ∂prior := by simp
    _ ≤ ∫⁻ x, seed (Prod.mk x ⁻¹' success) ∂prior := by
      apply lintegral_mono
      intro x
      exact ENNReal.ofReal_le_of_le_toReal (hinstancewise x)

/-- Almost-everywhere version of the lower Tonelli bound, useful when the
prior is a conditional measure concentrated on an admissible event. -/
theorem product_success_ge_of_instancewise_ae
    {Instance Seed : Type*} [MeasurableSpace Instance] [MeasurableSpace Seed]
    (prior : Measure Instance) (seed : Measure Seed)
    [IsProbabilityMeasure prior] [IsProbabilityMeasure seed]
    (success : Set (Instance × Seed)) (hsuccess : MeasurableSet success)
    (c : ℝ)
    (hinstancewise : ∀ᵐ x ∂prior, c ≤ seed.real {s | (x, s) ∈ success}) :
    c ≤ (prior.prod seed).real success := by
  apply (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).mp
  rw [Measure.prod_apply hsuccess]
  calc
    ENNReal.ofReal c = ∫⁻ _, ENNReal.ofReal c ∂prior := by simp
    _ ≤ ∫⁻ x, seed (Prod.mk x ⁻¹' success) ∂prior := by
      apply lintegral_mono_ae
      filter_upwards [hinstancewise] with x hx
      exact ENNReal.ofReal_le_of_le_toReal hx

/-- Yao's fixed bad instance follows from two actual product-measure fiber
integrals. The instance is sampled from the supplied admissible prior. -/
theorem yao_fixed_bad_instance
    {Instance Seed : Type*} [MeasurableSpace Instance] [MeasurableSpace Seed]
    (prior : Measure Instance) (seed : Measure Seed)
    [IsProbabilityMeasure prior] [IsProbabilityMeasure seed]
    (success : Set (Instance × Seed)) (hsuccess : MeasurableSet success)
    (hseedwise : ∀ s, prior.real {x | (x, s) ∈ success} ≤ (4 / 15 : ℝ)) :
    ∃ x, seed.real {s | (x, s) ∈ success} < (2 / 3 : ℝ) := by
  by_contra h
  push Not at h
  have hlo := product_success_ge_of_instancewise prior seed success hsuccess (2 / 3) h
  have hhi := product_success_le_of_seedwise prior seed success hsuccess (4 / 15)
    (by norm_num) hseedwise
  linarith

/-- Yao with an explicit full-prior admissibility event. The conclusion
returns a fixed admissible instance, rather than a point outside the support. -/
theorem yao_fixed_bad_admissible_instance
    {Instance Seed : Type*} [MeasurableSpace Instance] [MeasurableSpace Seed]
    (prior : Measure Instance) (seed : Measure Seed)
    [IsProbabilityMeasure prior] [IsProbabilityMeasure seed]
    (E : Set Instance) (hE : MeasurableSet E) (hfull : prior E = 1)
    (success : Set (Instance × Seed)) (hsuccess : MeasurableSet success)
    (hseedwise : ∀ s, prior.real {x | (x, s) ∈ success} ≤ (4 / 15 : ℝ)) :
    ∃ x ∈ E, seed.real {s | (x, s) ∈ success} < (2 / 3 : ℝ) := by
  by_contra h
  push Not at h
  have hmem : ∀ᵐ x ∂prior, x ∈ E :=
    (ae_mem_iff_measure_eq hE.nullMeasurableSet).mpr (by simpa using hfull)
  have hlo := product_success_ge_of_instancewise_ae prior seed success hsuccess (2 / 3)
    (hmem.mono fun x hx => h x hx)
  have hhi := product_success_le_of_seedwise prior seed success hsuccess (4 / 15)
    (by norm_num) hseedwise
  linarith

/-- The complete fixed-bad-instance step in MD 293--297, starting with
source-prior success bounds for every deterministic seed, then conditioning,
then averaging the independent seed. All admissibility is in the conclusion. -/
theorem source_bound_to_fixed_bad_target
    {Instance Seed : Type*} [MeasurableSpace Instance] [MeasurableSpace Seed]
    (μ : Measure Instance) (seed : Measure Seed)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure seed]
    (E : Set Instance) (hE : MeasurableSet E)
    (hevent : (15 / 16 : ℝ) ≤ μ.real E)
    (source target : Set (Instance × Seed)) (htarget : MeasurableSet target)
    (hsource : ∀ s, μ.real {x | (x, s) ∈ source} ≤ (1 / 4 : ℝ))
    (htransfer : ∀ x ∈ E, ∀ s, (x, s) ∈ target → (x, s) ∈ source) :
    ∃ x ∈ E, seed.real {s | (x, s) ∈ target} < (2 / 3 : ℝ) := by
  have hnonzero : μ E ≠ 0 := by
    apply (measureReal_ne_zero_iff).mp
    linarith
  letI : IsProbabilityMeasure (cond μ E) := cond_isProbabilityMeasure hnonzero
  apply yao_fixed_bad_admissible_instance (cond μ E) seed E hE
    (conditional_prior_event_probability μ E hevent) target htarget
  intro s
  apply target_success_under_conditional_prior μ {x | (x, s) ∈ source}
    {x | (x, s) ∈ target} E hE (hsource s) hevent
  rintro x ⟨hx, hxE⟩
  exact htransfer x hxE s hx

/-- For each fixed objective, the two independent optimizer seeds have the
product law. Each success event may differ, provided both succeed at least
2/3 of the time. Their union succeeds at least 8/9 of the time. -/
theorem independent_two_seed_success
    {Seed₁ Seed₂ : Type*} [MeasurableSpace Seed₁] [MeasurableSpace Seed₂]
    (μ : Measure Seed₁) (ν : Measure Seed₂)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (A : Set Seed₁) (B : Set Seed₂)
    (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hpA : (2 / 3 : ℝ) ≤ μ.real A) (hpB : (2 / 3 : ℝ) ≤ ν.real B) :
    (8 / 9 : ℝ) ≤ (μ.prod ν).real {p | p.1 ∈ A ∨ p.2 ∈ B} := by
  have hfail : {p : Seed₁ × Seed₂ | p.1 ∈ A ∨ p.2 ∈ B} = (Aᶜ ×ˢ Bᶜ)ᶜ := by
    ext p
    simp only [mem_setOf_eq, mem_compl_iff, mem_prod, not_and_or, not_not]
  rw [hfail, probReal_compl_eq_one_sub (hA.compl.prod hB.compl),
    measureReal_prod_prod, probReal_compl_eq_one_sub hA, probReal_compl_eq_one_sub hB]
  have ha : μ.real A ≤ 1 := by
    simpa using (measureReal_mono (μ := μ) (subset_univ A))
  have hb : ν.real B ≤ 1 := by
    simpa using (measureReal_mono (μ := ν) (subset_univ B))
  have hmul := mul_le_mul (show 1 - μ.real A ≤ (1 / 3 : ℝ) by linarith)
    (show 1 - ν.real B ≤ (1 / 3 : ℝ) by linarith)
    (show 0 ≤ 1 - ν.real B by linarith) (by norm_num : (0 : ℝ) ≤ 1 / 3)
  nlinarith

/-- An actual product probability for arbitrary recovery events. On each
fixed objective in E, either optimizer success is enough for recovery. -/
theorem two_run_recovery_product_lower_bound
    {Instance Seed : Type*} [MeasurableSpace Instance] [MeasurableSpace Seed]
    (prior : Measure Instance) (seed : Measure Seed)
    [IsProbabilityMeasure prior] [IsProbabilityMeasure seed]
    (E : Set Instance) (hE : MeasurableSet E)
    (success : Set (Instance × Seed)) (hsuccess : MeasurableSet success)
    (recovery : Set (Instance × (Seed × Seed))) (hrecovery : MeasurableSet recovery)
    (hp : ∀ x ∈ E, (2 / 3 : ℝ) ≤ seed.real {s | (x, s) ∈ success})
    (hrec : ∀ x ∈ E, ∀ s₁ s₂,
      ((x, s₁) ∈ success ∨ (x, s₂) ∈ success) → (x, (s₁, s₂)) ∈ recovery) :
    (8 / 9 : ℝ) * prior.real E ≤ (prior.prod (seed.prod seed)).real recovery := by
  have hfiber : ∀ x ∈ E, (8 / 9 : ℝ) ≤
      (seed.prod seed).real {p | (x, p) ∈ recovery} := by
    intro x hx
    have hs : MeasurableSet {s | (x, s) ∈ success} :=
      hsuccess.preimage (measurable_const.prodMk measurable_id)
    have hb := independent_two_seed_success seed seed {s | (x, s) ∈ success}
      {s | (x, s) ∈ success} hs hs (hp x hx) (hp x hx)
    exact hb.trans (measureReal_mono (fun p hp => hrec x hx p.1 p.2 hp))
  have hbound : ENNReal.ofReal (8 / 9 : ℝ) * prior E ≤
      (prior.prod (seed.prod seed)) recovery := by
    rw [Measure.prod_apply hrecovery]
    calc
      ENNReal.ofReal (8 / 9 : ℝ) * prior E =
          ∫⁻ _ in E, ENNReal.ofReal (8 / 9 : ℝ) ∂prior := by
        rw [setLIntegral_const]
      _ ≤ ∫⁻ x in E, (seed.prod seed) (Prod.mk x ⁻¹' recovery) ∂prior := by
        apply setLIntegral_mono' hE
        intro x hx
        exact ENNReal.ofReal_le_of_le_toReal (hfiber x hx)
      _ ≤ ∫⁻ x, (seed.prod seed) (Prod.mk x ⁻¹' recovery) ∂prior :=
        lintegral_mono' Measure.restrict_le_self le_rfl
  have ht := ENNReal.toReal_mono (measure_ne_top _ _) hbound
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by norm_num :
      (0 : ℝ) ≤ 8 / 9), ← measureReal_def] using ht

end PaperProbabilityReduction


end
-- END ProbabilityReduction.lean

-- BEGIN GaussianChannelKL.lean
section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace PaperGaussianKL

theorem gaussian_equal_variance_llr (m₀ m₁ : ℝ) (v : ℝ≥0) (hv : v ≠ 0) :
    llr (gaussianReal m₀ v) (gaussianReal m₁ v) =ᵐ[gaussianReal m₀ v]
      (fun x => ((m₀ - m₁) / v) * x + (m₁ ^ 2 - m₀ ^ 2) / (2 * v)) := by
  have hμ := gaussianReal_absolutelyContinuous m₀ hv
  have hν := gaussianReal_absolutelyContinuous m₁ hv
  have hac := hμ.trans (gaussianReal_absolutelyContinuous' m₁ hv)
  filter_upwards [hac.ae_le (Measure.rnDeriv_eq_div hμ hν),
      hμ.ae_le (rnDeriv_gaussianReal m₀ v), hμ.ae_le (rnDeriv_gaussianReal m₁ v)]
    with x hratio hpdf₀ hpdf₁
  rw [llr, hratio, hpdf₀, hpdf₁, ENNReal.toReal_div]
  simp only [gaussianPDF, ENNReal.toReal_ofReal (gaussianPDFReal_nonneg _ _ _)]
  rw [Real.log_div (gaussianPDFReal_pos m₀ v x hv).ne'
    (gaussianPDFReal_pos m₁ v x hv).ne']
  have hc : (Real.sqrt (2 * Real.pi * v))⁻¹ ≠ 0 := by
    apply inv_ne_zero
    apply ne_of_gt
    apply Real.sqrt_pos.mpr
    have hvpos : (0 : ℝ) < v := by exact_mod_cast (pos_iff_ne_zero.mpr hv)
    positivity
  simp only [gaussianPDFReal, Real.log_mul hc (Real.exp_ne_zero _), Real.log_exp]
  have hv' : (v : ℝ) ≠ 0 := by exact_mod_cast hv
  field_simp
  ring

/-- Exact equal-variance Gaussian KL, including the actual Radon--Nikodym
and log-likelihood integrability obligations. -/
theorem gaussian_equal_variance_kl (m₀ m₁ : ℝ) (v : ℝ≥0) (hv : v ≠ 0) :
    InformationTheory.klDiv (gaussianReal m₀ v) (gaussianReal m₁ v) =
      ENNReal.ofReal ((m₀ - m₁) ^ 2 / (2 * v)) := by
  have hid : Integrable (fun x : ℝ => x) (gaussianReal m₀ v) :=
    (memLp_id_gaussianReal (μ := m₀) (v := v) 1).integrable le_rfl
  have hllr := gaussian_equal_variance_llr m₀ m₁ v hv
  have hint : Integrable (llr (gaussianReal m₀ v) (gaussianReal m₁ v))
      (gaussianReal m₀ v) := by
    apply (integrable_congr hllr).mpr
    exact (hid.const_mul _).add (integrable_const _)
  rw [InformationTheory.klDiv_of_ac_of_integrable
    ((gaussianReal_absolutelyContinuous m₀ hv).trans
      (gaussianReal_absolutelyContinuous' m₁ hv)) hint]
  simp only [probReal_univ, add_sub_cancel_right]
  congr 1
  rw [integral_congr_ae hllr,
    integral_add (hid.const_mul _) (integrable_const _), integral_const_mul,
    integral_id_gaussianReal, integral_const, probReal_univ, one_smul]
  have hv' : (v : ℝ) ≠ 0 := by exact_mod_cast hv
  field_simp
  ring

/-- Scalar signal unit-noise case in MD 14--15. -/
theorem gaussian_zero_vs_signal_kl (a : ℝ) :
    InformationTheory.klDiv (gaussianReal 0 1) (gaussianReal a 1) =
      ENNReal.ofReal (a ^ 2 / 2) := by
  simpa using gaussian_equal_variance_kl 0 a 1 (by norm_num)

/-- Conditional KL in integral form for actual finite probability kernels.
This is stronger than a scalar chain-rule-bound premise. -/
theorem conditional_kl_integral
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace.CountableOrCountablyGenerated α β]
    (μ : Measure α) [IsProbabilityMeasure μ]
    (κ η : Kernel α β) [IsMarkovKernel κ] [IsMarkovKernel η]
    (hac : ∀ a, κ a ≪ η a) :
    InformationTheory.klDiv (μ ⊗ₘ κ) (μ ⊗ₘ η) =
      ∫⁻ a, InformationTheory.klDiv (κ a) (η a) ∂μ := by
  have hκ : κ = η.withDensity (κ.rnDeriv η) := by
    ext a : 1
    exact (Kernel.withDensity_rnDeriv_eq (hac a)).symm
  have heq : μ ⊗ₘ κ =
      (μ ⊗ₘ η).withDensity (fun p => κ.rnDeriv η p.1 p.2) := by
    conv_lhs => rw [hκ]
    exact Measure.compProd_withDensity (Kernel.measurable_rnDeriv κ η)
  have hjointac : μ ⊗ₘ κ ≪ μ ⊗ₘ η := by
    rw [heq]
    exact withDensity_absolutelyContinuous _ _
  have hrn : (μ ⊗ₘ κ).rnDeriv (μ ⊗ₘ η) =ᵐ[μ ⊗ₘ η]
      (fun p => κ.rnDeriv η p.1 p.2) := by
    conv_lhs => rw [heq]
    exact Measure.rnDeriv_withDensity _ (Kernel.measurable_rnDeriv κ η)
  rw [InformationTheory.klDiv_eq_lintegral_klFun_of_ac hjointac]
  calc
    (∫⁻ p, ENNReal.ofReal
        (InformationTheory.klFun ((μ ⊗ₘ κ).rnDeriv (μ ⊗ₘ η) p).toReal) ∂(μ ⊗ₘ η)) =
        ∫⁻ p, ENNReal.ofReal
          (InformationTheory.klFun (κ.rnDeriv η p.1 p.2).toReal) ∂(μ ⊗ₘ η) := by
      apply lintegral_congr_ae
      filter_upwards [hrn] with p hp
      rw [hp]
    _ = ∫⁻ a, ∫⁻ b, ENNReal.ofReal
          (InformationTheory.klFun (κ.rnDeriv η a b).toReal) ∂η a ∂μ := by
      apply Measure.lintegral_compProd
      fun_prop
    _ = ∫⁻ a, InformationTheory.klDiv (κ a) (η a) ∂μ := by
      apply lintegral_congr
      intro a
      rw [InformationTheory.klDiv_eq_lintegral_klFun_of_ac (hac a)]
      apply lintegral_congr_ae
      filter_upwards [Kernel.rnDeriv_eq_rnDeriv_measure (κ := κ) (η := η) (a := a)]
        with b hb
      rw [hb]

/-- A genuine measurable Markov kernel with mean chosen from the past. -/
noncomputable def gaussianKernel
    {α : Type*} [MeasurableSpace α] (mean : α → ℝ) (hmean : Measurable mean) :
    Kernel α ℝ where
  toFun a := gaussianReal (mean a) 1
  measurable' := measurable_gaussianReal.comp (hmean.prodMk measurable_const)

instance gaussianKernel_isMarkov
    {α : Type*} [MeasurableSpace α] (mean : α → ℝ) (hmean : Measurable mean) :
    IsMarkovKernel (gaussianKernel mean hmean) :=
  ⟨fun _ => by dsimp [gaussianKernel]; infer_instance⟩

/-- One genuinely adaptive Gaussian observation, with conditional mean a
measurable function of the previous transcript. -/
theorem gaussian_one_step_conditional_kl
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ]
    (mean : α → ℝ) (hmean : Measurable mean) :
    InformationTheory.klDiv
        (μ ⊗ₘ gaussianKernel (fun _ : α => 0) measurable_const)
        (μ ⊗ₘ gaussianKernel mean hmean) =
      ∫⁻ a, ENNReal.ofReal (mean a ^ 2 / 2) ∂μ := by
  rw [conditional_kl_integral]
  · apply lintegral_congr
    intro a
    exact gaussian_zero_vs_signal_kl (mean a)
  · intro a
    exact (gaussianReal_absolutelyContinuous 0 (by norm_num : (1 : ℝ≥0) ≠ 0)).trans
      (gaussianReal_absolutelyContinuous' (mean a) (by norm_num : (1 : ℝ≥0) ≠ 0))

/-- The reverse KL chain increment for possibly different past transcript
laws. Its right side is derived from real Gaussian kernels and not assumed. -/
theorem gaussian_one_step_chain_rule
    {α : Type*} [MeasurableSpace α]
    (μ ν : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (mean : α → ℝ) (hmean : Measurable mean) :
    InformationTheory.klDiv
        (μ ⊗ₘ gaussianKernel (fun _ : α => 0) measurable_const)
        (ν ⊗ₘ gaussianKernel mean hmean) =
      InformationTheory.klDiv μ ν +
        ∫⁻ a, ENNReal.ofReal (mean a ^ 2 / 2) ∂μ := by
  rw [InformationTheory.klDiv_compProd_eq_add, gaussian_one_step_conditional_kl]

/-- A transcript carries exactly the observations made so far. -/
def History : ℕ → Type
  | 0 => Unit
  | n + 1 => History n × ℝ

instance historyMeasurableSpace (n : ℕ) : MeasurableSpace (History n) := by
  induction n with
  | zero => exact inferInstanceAs (MeasurableSpace Unit)
  | succ n ih =>
    letI : MeasurableSpace (History n) := ih
    exact inferInstanceAs (MeasurableSpace (History n × ℝ))

/-- Each observation's signal may be any measurable function of past data. -/
structure AdaptiveMean where
  mean : (n : ℕ) → History n → ℝ
  measurable_mean : ∀ n, Measurable (mean n)

noncomputable def nullLaw : (n : ℕ) → Measure (History n)
  | 0 => Measure.dirac ()
  | n + 1 => nullLaw n ⊗ₘ gaussianKernel (fun _ => 0) measurable_const

noncomputable def signalLaw (a : AdaptiveMean) : (n : ℕ) → Measure (History n)
  | 0 => Measure.dirac ()
  | n + 1 => signalLaw a n ⊗ₘ gaussianKernel (a.mean n) (a.measurable_mean n)

instance nullLaw_isProbability (n : ℕ) : IsProbabilityMeasure (nullLaw n) := by
  induction n with
  | zero => exact inferInstanceAs (IsProbabilityMeasure (Measure.dirac ()))
  | succ n ih =>
    letI : IsProbabilityMeasure (nullLaw n) := ih
    change IsProbabilityMeasure (nullLaw n ⊗ₘ gaussianKernel (fun _ => 0) measurable_const)
    infer_instance

instance signalLaw_isProbability (a : AdaptiveMean) (n : ℕ) :
    IsProbabilityMeasure (signalLaw a n) := by
  induction n with
  | zero => exact inferInstanceAs (IsProbabilityMeasure (Measure.dirac ()))
  | succ n ih =>
    letI : IsProbabilityMeasure (signalLaw a n) := ih
    change IsProbabilityMeasure
      (signalLaw a n ⊗ₘ gaussianKernel (a.mean n) (a.measurable_mean n))
    infer_instance

/-- Finite adaptive Gaussian chain rule, derived by induction on actual
transcript laws. Stop/unused steps are represented by a mean of zero. -/
theorem finite_adaptive_gaussian_kl (a : AdaptiveMean) (n : ℕ) :
    InformationTheory.klDiv (nullLaw n) (signalLaw a n) =
      ∑ t ∈ Finset.range n, ∫⁻ h, ENNReal.ofReal (a.mean t h ^ 2 / 2) ∂nullLaw t := by
  induction n with
  | zero => simp [nullLaw, signalLaw]
  | succ n ih =>
    change InformationTheory.klDiv
      (nullLaw n ⊗ₘ gaussianKernel (fun _ => 0) measurable_const)
      (signalLaw a n ⊗ₘ gaussianKernel (a.mean n) (a.measurable_mean n)) = _
    rw [gaussian_one_step_chain_rule, ih, Finset.sum_range_succ]

/-- Average row energy bounds the sum of the actual reverse divergences.
The hypothesis is a pointwise row norm bound, rather than an expected-KL bound. -/
theorem finite_adaptive_gaussian_kl_sum_le
    {d : ℕ} (a : Fin d → AdaptiveMean) (n : ℕ) (κ : ℝ)
    (hκ : 0 ≤ κ)
    (henergy : ∀ t (h : History t), ∑ i, (a i).mean t h ^ 2 ≤ κ) :
    (∑ i, InformationTheory.klDiv (nullLaw n) (signalLaw (a i) n)) ≤
      ENNReal.ofReal ((n : ℝ) * κ / 2) := by
  simp_rw [finite_adaptive_gaussian_kl]
  rw [Finset.sum_comm]
  have hstep (t : ℕ) :
      (∑ i, ∫⁻ h, ENNReal.ofReal ((a i).mean t h ^ 2 / 2) ∂nullLaw t) ≤
        ENNReal.ofReal (κ / 2) := by
    rw [← lintegral_finsetSum Finset.univ]
    · calc
        (∫⁻ h, ∑ i, ENNReal.ofReal ((a i).mean t h ^ 2 / 2) ∂nullLaw t) ≤
            ∫⁻ _ : History t, ENNReal.ofReal (κ / 2) ∂nullLaw t := by
          apply lintegral_mono
          intro h
          dsimp only
          rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => by positivity), ← Finset.sum_div]
          apply ENNReal.ofReal_le_ofReal
          exact div_le_div_of_nonneg_right (henergy t h) (by norm_num)
        _ = ENNReal.ofReal (κ / 2) := by simp
    · intro i hi
      exact (((a i).measurable_mean t).pow_const 2 |>.div_const 2).ennreal_ofReal
  calc
    (∑ t ∈ Finset.range n, ∑ i,
        ∫⁻ h, ENNReal.ofReal ((a i).mean t h ^ 2 / 2) ∂nullLaw t) ≤
        ∑ _ ∈ Finset.range n, ENNReal.ofReal (κ / 2) := by
      apply Finset.sum_le_sum
      intro t ht
      exact hstep t
    _ = ENNReal.ofReal ((n : ℝ) * κ / 2) := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg n)]
      congr 1
      ring

/-- Real-valued averaged reverse KL for the constructed transcript measures.
The preceding finite bound also proves all divergences are finite. -/
theorem finite_adaptive_gaussian_kl_average_le
    {d : ℕ} (a : Fin d → AdaptiveMean) (n : ℕ) (κ : ℝ)
    (hκ : 0 ≤ κ)
    (henergy : ∀ t (h : History t), ∑ i, (a i).mean t h ^ 2 ≤ κ) :
    (∑ i, (InformationTheory.klDiv (nullLaw n) (signalLaw (a i) n)).toReal) / d ≤
      (n : ℝ) * κ / (2 * d) := by
  have hb := finite_adaptive_gaussian_kl_sum_le a n κ hκ henergy
  have hf : (∑ i, InformationTheory.klDiv (nullLaw n) (signalLaw (a i) n)) ≠ ∞ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hb
  have ht := ENNReal.toReal_mono ENNReal.ofReal_ne_top hb
  rw [ENNReal.toReal_sum (ENNReal.sum_ne_top.mp hf),
    ENNReal.toReal_ofReal (by positivity)] at ht
  have hdiv := div_le_div_of_nonneg_right ht (Nat.cast_nonneg d : (0 : ℝ) ≤ d)
  simpa only [div_div] using hdiv

/-- Actual signal means for adaptive sensing rows. Rows depend measurably
on previous observations; they may vanish when a procedure has stopped. -/
noncomputable def rowSignalMean {d : ℕ}
    (rows : (t : ℕ) → History t → Fin d → ℝ)
    (hmeas : ∀ t i, Measurable (fun h => rows t h i))
    (κ : ℝ) (i : Fin d) : AdaptiveMean where
  mean t h := Real.sqrt κ * rows t h i
  measurable_mean t := measurable_const.mul (hmeas t i)

/-- The manuscript's averaged reverse-KL bound (15) for actual finite
adaptive unit-row Gaussian-channel laws, including zero/unused rows.
The missing bridge from the source Gaussian oracle to these channel laws
is not a hypothesis hidden in this theorem. -/
theorem unit_row_adaptive_gaussian_kl_average_le
    {d : ℕ} (rows : (t : ℕ) → History t → Fin d → ℝ)
    (hmeas : ∀ t i, Measurable (fun h => rows t h i))
    (hunit : ∀ t (h : History t), ∑ i, rows t h i ^ 2 ≤ 1)
    (n : ℕ) (κ : ℝ) (hκ : 0 ≤ κ) :
    (∑ i, (InformationTheory.klDiv (nullLaw n)
      (signalLaw (rowSignalMean rows hmeas κ i) n)).toReal) / d ≤
        (n : ℝ) * κ / (2 * d) := by
  apply finite_adaptive_gaussian_kl_average_le _ n κ hκ
  intro t h
  simp only [rowSignalMean, mul_pow, Real.sq_sqrt hκ, ← Finset.mul_sum]
  exact (mul_le_mul_of_nonneg_left (hunit t h) hκ).trans_eq (mul_one κ)

end PaperGaussianKL


end
-- END GaussianChannelKL.lean

-- BEGIN PinskerReduction.lean
section

open MeasureTheory InformationTheory Set
open scoped ENNReal NNReal

namespace PaperPinsker

noncomputable def binaryKL (p q : ℝ) : ℝ :=
  p * Real.log p + (1 - p) * Real.log (1 - p) -
    p * Real.log q - (1 - p) * Real.log (1 - q)

lemma binaryKL_lower_bound (p q : ℝ)
    (hp : p ∈ Icc (0 : ℝ) 1) (hq : q ∈ Ioo (0 : ℝ) 1) :
    2 * (p - q) ^ 2 ≤ binaryKL p q := by
  let f : ℝ → ℝ := fun x => binaryKL x q - 2 * (x - q) ^ 2
  let f' : ℝ → ℝ := fun x =>
    Real.log x - Real.log (1 - x) - Real.log q + Real.log (1 - q) - 4 * (x - q)
  let f'' : ℝ → ℝ := fun x => 1 / x + 1 / (1 - x) - 4
  have hd₁ (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) 1) : HasDerivAt f (f' x) x := by
    have hneg : HasDerivAt (fun x : ℝ => 1 - x) (-1) x := by
      convert! HasDerivAt.const_sub (1 : ℝ) (hasDerivAt_id x) using 1 <;> norm_num
    have hlog := Real.hasDerivAt_mul_log hx.1.ne'
    have hclog := (Real.hasDerivAt_mul_log (show 1 - x ≠ 0 by linarith [hx.2])).comp x hneg
    have hlin := (hasDerivAt_id x).mul_const (Real.log q)
    have hclin := hneg.mul_const (Real.log (1 - q))
    have hquad := (((hasDerivAt_id x).sub_const q).pow 2).const_mul 2
    convert! (((hlog.add hclog).sub hlin).sub hclin).sub hquad using 1 <;>
      (try dsimp [f, f', binaryKL, Function.comp_def]) <;> ring
  have hd₂ (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) 1) : HasDerivAt f' (f'' x) x := by
    have hneg : HasDerivAt (fun x : ℝ => 1 - x) (-1) x := by
      convert! HasDerivAt.const_sub (1 : ℝ) (hasDerivAt_id x) using 1 <;> norm_num
    have hlog := Real.hasDerivAt_log hx.1.ne'
    have hclog := (Real.hasDerivAt_log (show 1 - x ≠ 0 by linarith [hx.2])).comp x hneg
    have hlin := ((hasDerivAt_id x).sub_const q).const_mul 4
    convert! (((hlog.sub hclog).sub_const (Real.log q)).add_const
      (Real.log (1 - q))).sub hlin using 1 <;> (try dsimp [f', f'', Function.comp_def]) <;> ring
  have hc : ConvexOn ℝ (Icc (0 : ℝ) 1) f := by
    apply convexOn_of_hasDerivWithinAt2_nonneg (f' := f') (f'' := f'') (convex_Icc 0 1)
    · dsimp [f, binaryKL]
      exact (((Real.continuous_mul_log.add
        (Real.continuous_mul_log.comp (continuous_const.sub continuous_id))).sub
        (continuous_id.mul continuous_const)).sub
        ((continuous_const.sub continuous_id).mul continuous_const)).sub
        (continuous_const.mul ((continuous_id.sub continuous_const).pow 2)) |>.continuousOn
    · intro x hx
      apply (hd₁ x _).hasDerivWithinAt
      simpa using hx
    · intro x hx
      apply (hd₂ x _).hasDerivWithinAt
      simpa using hx
    · intro x hx
      have hx' : x ∈ Ioo (0 : ℝ) 1 := by simpa using hx
      have heq : f'' x = (2 * x - 1) ^ 2 / (x * (1 - x)) := by
        dsimp [f'']
        field_simp [hx'.1.ne', show 1 - x ≠ 0 by linarith [hx'.2]]
        ring
      rw [heq]
      exact div_nonneg (sq_nonneg _) (mul_nonneg hx'.1.le (by linarith [hx'.2]))
  have hmin : IsMinOn f (Icc (0 : ℝ) 1) q := by
    apply hc.isMinOn_of_rightDeriv_eq_zero (by simpa using hq)
    have hd := (hd₁ q hq).hasDerivWithinAt.derivWithin (uniqueDiffWithinAt_Ioi q)
    simpa [f'] using hd
  have hb := hmin hp
  have hzero : f q = 0 := by dsimp [f, binaryKL]; ring
  rw [hzero] at hb
  dsimp [f] at hb
  linarith

lemma restricted_klFun_jensen
    {Ω : Type*} [MeasurableSpace Ω]
    (μ ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hac : μ ≪ ν) (hint : Integrable (llr μ ν) μ)
    (E : Set Ω) (hE : MeasurableSet E) :
    ν.real E * klFun (μ.real E / ν.real E) ≤
      ∫ x in E, klFun (μ.rnDeriv ν x).toReal ∂ν := by
  have heq : μ.restrict E = (ν.restrict E).withDensity (μ.rnDeriv ν) := by
    rw [← restrict_withDensity hE, (μ.withDensity_rnDeriv_eq ν hac)]
  have hrn : (μ.restrict E).rnDeriv (ν.restrict E) =ᵐ[ν.restrict E] μ.rnDeriv ν := by
    conv_lhs => rw [heq]
    exact Measure.rnDeriv_withDensity _ (Measure.measurable_rnDeriv _ _)
  have hkl := (integrable_klFun_rnDeriv_iff hac).mpr hint
  have hrnkl := hrn.mono (fun _ hx => congrArg (fun r : ℝ≥0∞ => klFun r.toReal) hx)
  have hb := mul_le_integral_rnDeriv_of_ac (μ := μ.restrict E) (ν := ν.restrict E)
    convexOn_klFun continuous_klFun.continuousWithinAt
    ((integrable_congr hrnkl).mpr hkl.restrict) (hac.restrict E)
  rw [integral_congr_ae hrnkl] at hb
  simpa only [measureReal_def, Measure.restrict_apply_univ] using hb

lemma mul_klFun_div (p q : ℝ) (hq : q ≠ 0) :
    q * klFun (p / q) = p * Real.log p - p * Real.log q + q - p := by
  by_cases hp : p = 0
  · simp [hp, klFun]
  · rw [klFun, Real.log_div hp hq]
    field_simp

/-- Data processing to the binary experiment associated with an actual
measurable event, established by Jensen on both restricted measures. -/
theorem event_binaryKL_le
    {Ω : Type*} [MeasurableSpace Ω]
    (μ ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hac : μ ≪ ν) (hint : Integrable (llr μ ν) μ)
    (E : Set Ω) (hE : MeasurableSet E)
    (hq : ν.real E ∈ Ioo (0 : ℝ) 1) :
    binaryKL (μ.real E) (ν.real E) ≤ (klDiv μ ν).toReal := by
  have he := restricted_klFun_jensen μ ν hac hint E hE
  have hec := restricted_klFun_jensen μ ν hac hint Eᶜ hE.compl
  have hb := add_le_add he hec
  rw [integral_add_compl hE ((integrable_klFun_rnDeriv_iff hac).mpr hint),
    probReal_compl_eq_one_sub hE, probReal_compl_eq_one_sub hE,
    ← toReal_klDiv_eq_integral_klFun hac] at hb
  rw [mul_klFun_div _ _ hq.1.ne',
    mul_klFun_div _ _ (show 1 - ν.real E ≠ 0 by linarith [hq.2])] at hb
  unfold binaryKL
  linarith

/-- Pinsker's event inequality for actual probability measures and finite KL.
No scalar probability-gap or total-variation premise is assumed. -/
theorem event_pinsker_squared
    {Ω : Type*} [MeasurableSpace Ω]
    (μ ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hfinite : klDiv μ ν ≠ ∞)
    (E : Set Ω) (hE : MeasurableSet E) :
    2 * (μ.real E - ν.real E) ^ 2 ≤ (klDiv μ ν).toReal := by
  obtain ⟨hac, hint⟩ := klDiv_ne_top_iff.mp hfinite
  have hp : μ.real E ∈ Icc (0 : ℝ) 1 :=
    ⟨measureReal_nonneg, by simpa using (measureReal_mono (μ := μ) (subset_univ E))⟩
  have hq : ν.real E ∈ Icc (0 : ℝ) 1 :=
    ⟨measureReal_nonneg, by simpa using (measureReal_mono (μ := ν) (subset_univ E))⟩
  rcases eq_or_lt_of_le hq.1 with hzero | hpos
  · have hμzero : μ.real E = 0 :=
      (measureReal_eq_zero_iff).mpr (hac ((measureReal_eq_zero_iff).mp hzero.symm))
    simp only [hμzero, ← hzero, sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow, mul_zero]
    exact ENNReal.toReal_nonneg
  rcases eq_or_lt_of_le hq.2 with hone | hlt
  · have hνc : ν.real Eᶜ = 0 := by rw [probReal_compl_eq_one_sub hE, hone, sub_self]
    have hμc : μ.real Eᶜ = 0 :=
      (measureReal_eq_zero_iff).mpr (hac ((measureReal_eq_zero_iff).mp hνc))
    have hμone : μ.real E = 1 := by
      rw [probReal_compl_eq_one_sub hE] at hμc
      linarith
    simp only [hμone, hone, sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow, mul_zero]
    exact ENNReal.toReal_nonneg
  exact (binaryKL_lower_bound _ _ hp ⟨hpos, hlt⟩).trans
    (event_binaryKL_le μ ν hac hint E hE ⟨hpos, hlt⟩)

/-- Recovery under a uniformly sampled index. The baseline fiber masses
sum to one; Pinsker and finite Cauchy--Schwarz control the actual average. -/
theorem finite_estimator_recovery_bound
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} (hd : 0 < d)
    (μ : Measure Ω) (ν : Fin d → Measure Ω)
    [IsProbabilityMeasure μ] [∀ i, IsProbabilityMeasure (ν i)]
    (hfinite : ∀ i, klDiv μ (ν i) ≠ ∞)
    (estimator : Ω → Fin d) (hmeas : Measurable estimator) :
    (∑ i, (ν i).real (estimator ⁻¹' {i})) / d ≤
      1 / d + Real.sqrt ((∑ i, (klDiv μ (ν i)).toReal) / (2 * d)) := by
  let Δ : Fin d → ℝ := fun i => (ν i).real (estimator ⁻¹' {i}) -
    μ.real (estimator ⁻¹' {i})
  have hbaseline : (∑ i, μ.real (estimator ⁻¹' {i})) = 1 := by
    simpa using sum_measureReal_preimage_singleton (μ := μ) Finset.univ
      (fun i _ => hmeas (measurableSet_singleton i))
  have hsum : 2 * ∑ i, Δ i ^ 2 ≤ ∑ i, (klDiv μ (ν i)).toReal := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    have hb := event_pinsker_squared μ (ν i) (hfinite i)
      (estimator ⁻¹' {i}) (hmeas (measurableSet_singleton i))
    dsimp [Δ]
    nlinarith
  have hc := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ Δ (fun _ => (1 : ℝ))
  simp only [mul_one, one_pow, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one] at hc
  have hdreal : (0 : ℝ) < d := by exact_mod_cast hd
  have hquad : 2 * (∑ i, Δ i) ^ 2 ≤
      (∑ i, (klDiv μ (ν i)).toReal) * d := by
    have hm := mul_le_mul_of_nonneg_right hsum hdreal.le
    nlinarith
  have hnormalized : ((∑ i, Δ i) / d) ^ 2 ≤
      (∑ i, (klDiv μ (ν i)).toReal) / (2 * d) := by
    rw [div_pow]
    apply (div_le_div_iff₀ (sq_pos_of_pos hdreal)
      (by positivity : (0 : ℝ) < 2 * d)).mpr
    have hm := mul_le_mul_of_nonneg_right hquad hdreal.le
    nlinarith
  have hroot : (∑ i, Δ i) / d ≤
      Real.sqrt ((∑ i, (klDiv μ (ν i)).toReal) / (2 * d)) := by
    have hsqrt := Real.sq_sqrt (show
      0 ≤ (∑ i, (klDiv μ (ν i)).toReal) / (2 * d) by positivity)
    have hsqrtpos := Real.sqrt_nonneg ((∑ i, (klDiv μ (ν i)).toReal) / (2 * d))
    nlinarith
  dsimp [Δ] at hroot
  rw [Finset.sum_sub_distrib, hbaseline, sub_div] at hroot
  linarith

end PaperPinsker


end
-- END PinskerReduction.lean

-- BEGIN ChannelRecovery.lean
section
/- Theorems for an actual adaptive Gaussian sensing channel.
   They do not establish that a raw adaptive linear Gaussian oracle
   has these channel laws. -/
namespace PaperChannelRecovery

open MeasureTheory ProbabilityTheory InformationTheory PaperGaussianKL PaperPinsker
open scoped ENNReal NNReal

/-- The manuscript's (16), now for actual channel transcript laws,
measurable adaptive rows, and a measurable recovery estimator. -/
theorem unit_row_adaptive_recovery_bound
    {d : ℕ} (hd : 0 < d)
    (rows : (t : ℕ) → History t → Fin d → ℝ)
    (hmeas : ∀ t i, Measurable (fun h => rows t h i))
    (hunit : ∀ t (h : History t), ∑ i, rows t h i ^ 2 ≤ 1)
    (n : ℕ) (κ : ℝ) (hκ : 0 ≤ κ)
    (estimator : History n → Fin d) (hestimator : Measurable estimator) :
    (∑ i, (signalLaw (rowSignalMean rows hmeas κ i) n).real
      (estimator ⁻¹' {i})) / d ≤
        1 / d + Real.sqrt ((n : ℝ) * κ / (4 * d)) := by
  let a : Fin d → AdaptiveMean := rowSignalMean rows hmeas κ
  have henergy : ∀ t (h : History t), ∑ i, (a i).mean t h ^ 2 ≤ κ := by
    intro t h
    dsimp [a, rowSignalMean]
    simp only [mul_pow, Real.sq_sqrt hκ, ← Finset.mul_sum]
    exact (mul_le_mul_of_nonneg_left (hunit t h) hκ).trans_eq (mul_one κ)
  have hbound := finite_adaptive_gaussian_kl_sum_le a n κ hκ henergy
  have hsumfinite : (∑ i, klDiv (nullLaw n) (signalLaw (a i) n)) ≠ ∞ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hbound
  have hfinite : ∀ i, klDiv (nullLaw n) (signalLaw (a i) n) ≠ ∞ := by
    intro i
    exact ENNReal.sum_ne_top.mp hsumfinite i (Finset.mem_univ i)
  have hb := finite_estimator_recovery_bound hd (nullLaw n)
    (fun i => signalLaw (a i) n) hfinite estimator hestimator
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hbound
  rw [ENNReal.toReal_sum (ENNReal.sum_ne_top.mp hsumfinite),
    ENNReal.toReal_ofReal (by positivity)] at hreal
  have hscaled : (∑ i, (klDiv (nullLaw n) (signalLaw (a i) n)).toReal) /
      (2 * d) ≤ (n : ℝ) * κ / (4 * d) := by
    have hm := div_le_div_of_nonneg_right hreal
      (by positivity : (0 : ℝ) ≤ 2 * d)
    simpa only [div_div, show (2 : ℝ) * (2 * d) = 4 * d by ring] using hm
  exact hb.trans (add_le_add le_rfl (Real.sqrt_le_sqrt hscaled))

/-- The information-count consequence of a recovery probability above 2/3.
Every probability in the assumption is the actual signal transcript law. -/
theorem unit_row_adaptive_observation_lower_bound
    {d : ℕ} (hd : 6 ≤ d)
    (rows : (t : ℕ) → History t → Fin d → ℝ)
    (hmeas : ∀ t i, Measurable (fun h => rows t h i))
    (hunit : ∀ t (h : History t), ∑ i, rows t h i ^ 2 ≤ 1)
    (n : ℕ) (κ : ℝ) (hκ : 0 ≤ κ)
    (estimator : History n → Fin d) (hestimator : Measurable estimator)
    (hrecovery : (2 / 3 : ℝ) <
      (∑ i, (signalLaw (rowSignalMean rows hmeas κ i) n).real
        (estimator ⁻¹' {i})) / d) :
    (d : ℝ) ≤ (n : ℝ) * κ := by
  have hdpos : 0 < d := by omega
  have hb := unit_row_adaptive_recovery_bound hdpos rows hmeas hunit n κ hκ
    estimator hestimator
  have hdreal : (6 : ℝ) ≤ d := by exact_mod_cast hd
  have hdrealpos : (0 : ℝ) < d := by linarith
  have hbase : 1 / (d : ℝ) ≤ 1 / 6 :=
    one_div_le_one_div_of_le (by norm_num) hdreal
  have hsqrt : (1 / 2 : ℝ) < Real.sqrt ((n : ℝ) * κ / (4 * d)) := by
    linarith
  have hsquare := Real.sq_sqrt (show 0 ≤ (n : ℝ) * κ / (4 * d) by positivity)
  have hrootnonneg := Real.sqrt_nonneg ((n : ℝ) * κ / (4 * d))
  have hratio : (1 / 4 : ℝ) < (n : ℝ) * κ / (4 * d) := by nlinarith
  have hm := (lt_div_iff₀ (show (0 : ℝ) < 4 * d by positivity)).mp hratio
  nlinarith

end PaperChannelRecovery


end
-- END ChannelRecovery.lean

-- BEGIN EntropyRegret.lean
section

/- Mathematical continuation of manuscript MD 161-180.
This file invokes the actual Mathlib Hoeffding theorem, not a scalar
assumption asserting the desired log bound. Stochastic adaptive iterates,
Laplace variance and conditional unbiasedness still require their proofs.
-/
namespace PaperEntropyRegret

open MeasureTheory ProbabilityTheory Real
open scoped BigOperators

noncomputable def coordinateLaw {n : ℕ} (z : Fin n → ℝ)
    (hz : ∀ i, 0 ≤ z i) (hsum : ∑ i, z i = 1) : PMF (Fin n) :=
  PMF.ofFintype (fun i => ENNReal.ofReal (z i)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => hz i), hsum]
    simp)

theorem coordinate_integral {n : ℕ} (z : Fin n → ℝ)
    (hz : ∀ i, 0 ≤ z i) (hsum : ∑ i, z i = 1) (f : Fin n → ℝ) :
    (∫ i, f i ∂(coordinateLaw z hz hsum).toMeasure) = ∑ i, z i * f i := by
  rw [PMF.integral_eq_sum]
  simp [coordinateLaw, ENNReal.toReal_ofReal, hz, smul_eq_mul]

/-- Realized-gradient Hoeffding inequality under a genuine probability law.
For a finite-coordinate law, K can be the maximum absolute gradient entry;
no deterministic uniform bound over perturbation realizations is required. -/
theorem realized_gradient_hoeffding {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (g : Ω → ℝ)
    (hg : AEMeasurable g μ) (K eta : ℝ) (hK : 0 ≤ K)
    (hbound : ∀ᵐ ω ∂μ, g ω ∈ Set.Icc (-K) K) :
    Real.log (mgf g μ (-eta)) + eta * (∫ ω, g ω ∂μ) ≤ eta ^ 2 * K ^ 2 / 2 := by
  have hsub := hasSubgaussianMGF_of_mem_Icc hg hbound
  have hh := hsub.cgf_le (-eta)
  have hint := integrable_exp_mul_of_mem_Icc (t := -eta) hg hbound
  have hpos := mgf_pos hint
  have hmgf : mgf (fun ω => g ω - (∫ s, g s ∂μ)) μ (-eta) =
      mgf g μ (-eta) * Real.exp (eta * (∫ s, g s ∂μ)) := by
    have heq : (fun ω => g ω - (∫ s, g s ∂μ)) =
        (fun ω => g ω + -(∫ s, g s ∂μ)) := by funext ω; ring
    rw [heq, mgf_add_const]
    congr 2
    ring
  have hlog : cgf (fun ω => g ω - (∫ s, g s ∂μ)) μ (-eta) =
      Real.log (mgf g μ (-eta)) + eta * (∫ s, g s ∂μ) := by
    rw [cgf, hmgf, Real.log_mul (ne_of_gt hpos) (ne_of_gt (Real.exp_pos _)), Real.log_exp]
  rw [hlog] at hh
  have hparam : (((‖K - -K‖₊ / 2) ^ 2 : NNReal) : ℝ) = K ^ 2 := by
    simp only [NNReal.coe_pow, NNReal.coe_div, NNReal.coe_ofNat, coe_nnnorm,
      Real.norm_eq_abs]
    rw [abs_of_nonneg (by linarith)]
    ring
  rw [hparam] at hh
  nlinarith

/-- MD 166-169 with the exact finite coordinate distribution z, not an
assumed scalar inequality. This applies to every realized finite vector g. -/
theorem finite_coordinate_hoeffding {n : ℕ} (z g : Fin n → ℝ)
    (hz : ∀ i, 0 ≤ z i) (hsum : ∑ i, z i = 1)
    (K eta : ℝ) (hK : 0 ≤ K) (hg : ∀ i, |g i| ≤ K) :
    Real.log (∑ i, z i * Real.exp (-eta * g i)) + eta * (∑ i, z i * g i)
      ≤ eta ^ 2 * K ^ 2 / 2 := by
  have hb : ∀ᵐ i ∂(coordinateLaw z hz hsum).toMeasure,
      g i ∈ Set.Icc (-K) K := Filter.Eventually.of_forall (fun i => abs_le.mp (hg i))
  have hh := realized_gradient_hoeffding (coordinateLaw z hz hsum).toMeasure g
    (measurable_of_finite g).aemeasurable K eta hK hb
  change Real.log (∫ i, Real.exp (-eta * g i) ∂(coordinateLaw z hz hsum).toMeasure) +
    eta * (∫ i, g i ∂(coordinateLaw z hz hsum).toMeasure) ≤ _ at hh
  simpa only [coordinate_integral] using hh

noncomputable def entropy {n : ℕ} (x z : Fin n → ℝ) : ℝ :=
  ∑ i, x i * (Real.log (x i) - Real.log (z i))

noncomputable def normalizer {n : ℕ} (z g : Fin n → ℝ) (eta : ℝ) : ℝ :=
  ∑ i, z i * Real.exp (-eta * g i)

noncomputable def update {n : ℕ} (z g : Fin n → ℝ) (eta : ℝ) (i : Fin n) : ℝ :=
  z i * Real.exp (-eta * g i) / normalizer z g eta

theorem normalizer_pos {n : ℕ} (z g : Fin n → ℝ) (eta : ℝ)
    (hz : ∀ i, 0 < z i) (hsum : ∑ i, z i = 1) :
    0 < normalizer z g eta := by
  have hex : ∃ i, 0 < z i := by
    by_contra hn
    push Not at hn
    have hle : (∑ i, z i) ≤ 0 := Finset.sum_nonpos (fun i _ => hn i)
    linarith
  obtain ⟨i, hi⟩ := hex
  apply Finset.sum_pos'
  · intro j _
    exact le_of_lt (mul_pos (hz j) (Real.exp_pos _))
  · exact ⟨i, Finset.mem_univ _, mul_pos hi (Real.exp_pos _)⟩

theorem update_pos {n : ℕ} (z g : Fin n → ℝ) (eta : ℝ)
    (hz : ∀ i, 0 < z i) (hsum : ∑ i, z i = 1) (i : Fin n) :
    0 < update z g eta i :=
  div_pos (mul_pos (hz i) (Real.exp_pos _)) (normalizer_pos z g eta hz hsum)

theorem update_sum {n : ℕ} (z g : Fin n → ℝ) (eta : ℝ)
    (hz : ∀ i, 0 < z i) (hsum : ∑ i, z i = 1) :
    ∑ i, update z g eta i = 1 := by
  simp only [update, ← Finset.sum_div]
  exact div_self (ne_of_gt (normalizer_pos z g eta hz hsum))

/-- Relative entropy is nonnegative on probability vectors; zero comparator
coordinates are included, using the conventional 0 log 0 = 0 interpretation. -/
theorem entropy_nonneg {n : ℕ} (x z : Fin n → ℝ)
    (hx : ∀ i, 0 ≤ x i) (hz : ∀ i, 0 < z i)
    (hsx : ∑ i, x i = 1) (hsz : ∑ i, z i = 1) : 0 ≤ entropy x z := by
  have hterm : ∀ i, x i - z i ≤ x i * (Real.log (x i) - Real.log (z i)) := by
    intro i
    by_cases hi : x i = 0
    · simp only [hi, zero_mul, zero_sub]
      exact neg_nonpos.mpr (le_of_lt (hz i))
    · have hip : 0 < x i := lt_of_le_of_ne (hx i) (Ne.symm hi)
      have hlog := Real.log_le_sub_one_of_pos (div_pos (hz i) hip)
      have hm := mul_le_mul_of_nonneg_left hlog (hx i)
      rw [Real.log_div (ne_of_gt (hz i)) hi] at hm
      have hcancel : x i * (z i / x i) = z i := by field_simp
      nlinarith
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hterm i)
  simpa only [entropy, Finset.sum_sub_distrib, hsx, hsz, sub_self] using hs

/-- MD 163-165: exact entropy identity for the specified multiplicative update. -/
theorem entropy_update_identity {n : ℕ} (x z g : Fin n → ℝ) (eta : ℝ)
    (hz : ∀ i, 0 < z i) (hsz : ∑ i, z i = 1) (hsx : ∑ i, x i = 1) :
    entropy x (update z g eta) - entropy x z =
      eta * (∑ i, x i * g i) + Real.log (normalizer z g eta) := by
  have hp := normalizer_pos z g eta hz hsz
  have hlog : ∀ i, Real.log (update z g eta i) =
      Real.log (z i) - eta * g i - Real.log (normalizer z g eta) := by
    intro i
    rw [update, Real.log_div (ne_of_gt (mul_pos (hz i) (Real.exp_pos _)))
      (ne_of_gt hp), Real.log_mul (ne_of_gt (hz i))
      (ne_of_gt (Real.exp_pos _)), Real.log_exp]
    ring
  have hterm : ∀ i, x i * (Real.log (x i) - Real.log (update z g eta i)) -
      x i * (Real.log (x i) - Real.log (z i)) =
      eta * (x i * g i) + x i * Real.log (normalizer z g eta) := by
    intro i
    rw [hlog]
    ring
  unfold entropy
  rw [← Finset.sum_sub_distrib]
  simp_rw [hterm]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul, hsx, one_mul]

/-- MD 173-175: the one-step regret inequality is now derived from the actual
finite-coordinate Hoeffding theorem and the exact entropy update identity. -/
theorem entropy_one_step {n : ℕ} (x z g : Fin n → ℝ) (eta K : ℝ)
    (hz : ∀ i, 0 < z i) (hsz : ∑ i, z i = 1) (hsx : ∑ i, x i = 1)
    (hK : 0 ≤ K) (hg : ∀ i, |g i| ≤ K) :
    eta * (∑ i, g i * (z i - x i)) ≤
      entropy x z - entropy x (update z g eta) + eta ^ 2 * K ^ 2 / 2 := by
  have hid := entropy_update_identity x z g eta hz hsz hsx
  have hh := finite_coordinate_hoeffding z g (fun i => le_of_lt (hz i)) hsz K eta hK hg
  have hsum : (∑ i, g i * (z i - x i)) =
      (∑ i, z i * g i) - (∑ i, x i * g i) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hsum]
  change Real.log (normalizer z g eta) + _ ≤ _ at hh
  linarith

theorem entropy_uniform_bound {n : ℕ} (hn : 0 < n) (x : Fin n → ℝ)
    (hx : ∀ i, 0 ≤ x i) (hsx : ∑ i, x i = 1) :
    entropy x (fun _ => (n : ℝ)⁻¹) ≤ Real.log n := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hxone : ∀ i, x i ≤ 1 := by
    intro i
    rw [← hsx]
    exact Finset.single_le_sum (fun j _ => hx j) (Finset.mem_univ i)
  have hlog : ∀ i, Real.log (x i) ≤ 0 := fun i => Real.log_nonpos (hx i) (hxone i)
  have hterm : ∀ i, x i * (Real.log (x i) - Real.log ((n : ℝ)⁻¹)) ≤
      x i * Real.log n := by
    intro i
    rw [Real.log_inv]
    have := mul_nonpos_of_nonneg_of_nonpos (hx i) (hlog i)
    nlinarith
  have hh := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hterm i)
  simpa only [entropy, ← Finset.sum_mul, hsx, one_mul] using hh

noncomputable def trajectory {n : ℕ} (z0 : Fin n → ℝ)
    (g : ℕ → Fin n → ℝ) (eta : ℝ) : ℕ → Fin n → ℝ
  | 0 => z0
  | t+1 => update (trajectory z0 g eta t) (g t) eta

theorem trajectory_simplex {n : ℕ} (z0 : Fin n → ℝ)
    (g : ℕ → Fin n → ℝ) (eta : ℝ)
    (hz0 : ∀ i, 0 < z0 i) (hs0 : ∑ i, z0 i = 1) (t : ℕ) :
    (∀ i, 0 < trajectory z0 g eta t i) ∧ (∑ i, trajectory z0 g eta t i) = 1 := by
  induction t with
  | zero => exact ⟨hz0, hs0⟩
  | succ t ih =>
    exact ⟨update_pos _ _ _ ih.1 ih.2, update_sum _ _ _ ih.1 ih.2⟩

/-- Telescoping of the actual finite multiplicative-weights trajectory. -/
theorem entropy_trajectory_regret {n : ℕ} (x z0 : Fin n → ℝ)
    (g : ℕ → Fin n → ℝ) (eta : ℝ) (K : ℕ → ℝ)
    (hx : ∀ i, 0 ≤ x i) (hsx : ∑ i, x i = 1)
    (hz0 : ∀ i, 0 < z0 i) (hs0 : ∑ i, z0 i = 1)
    (T : ℕ) (hK : ∀ t < T, 0 ≤ K t) (hg : ∀ t < T, ∀ i, |g t i| ≤ K t) :
    eta * (∑ t ∈ Finset.range T, ∑ i, g t i * (trajectory z0 g eta t i - x i)) ≤
      entropy x z0 + eta ^ 2 / 2 * (∑ t ∈ Finset.range T, (K t) ^ 2) := by
  let z := trajectory z0 g eta
  have hstep : ∀ t < T,
      eta * (∑ i, g t i * (z t i - x i)) ≤
        entropy x (z t) - entropy x (z (t+1)) + eta ^ 2 / 2 * (K t)^2 := by
    intro t ht
    obtain ⟨hpos, hsum⟩ := trajectory_simplex z0 g eta hz0 hs0 t
    have h := entropy_one_step x (z t) (g t) eta (K t) hpos hsum hsx (hK t ht) (hg t ht)
    simpa only [z, trajectory, mul_div_assoc, div_mul_eq_mul_div] using h
  have hs := Finset.sum_le_sum (fun t ht => hstep t (Finset.mem_range.mp ht))
  have htel : ∀ m : ℕ, (∑ t ∈ Finset.range m, (entropy x (z t) - entropy x (z (t+1)))) =
      entropy x z0 - entropy x (z m) := by
    intro m
    induction m with
    | zero => simp [z, trajectory]
    | succ m ih => rw [Finset.sum_range_succ, ih]; ring
  have hn : 0 ≤ entropy x (z T) := by
    obtain ⟨hpos, hsum⟩ := trajectory_simplex z0 g eta hz0 hs0 T
    exact entropy_nonneg x (z T) hx hpos hsx hsum
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, htel] at hs
  linarith

/-- MD 177-180: integrate the proved pathwise regret against a genuine law,
using only second moments. The Laplace estimator must still supply these
moments and its unbiasedness; no almost-sure uniform perturbation bound enters. -/
theorem expected_trajectory_regret
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {n : ℕ} (x z0 : Fin n → ℝ) (g : Ω → ℕ → Fin n → ℝ)
    (eta : ℝ) (K : Ω → ℕ → ℝ)
    (hx : ∀ i, 0 ≤ x i) (hsx : ∑ i, x i = 1)
    (hz0 : ∀ i, 0 < z0 i) (hs0 : ∑ i, z0 i = 1)
    (T : ℕ) (heta : 0 < eta)
    (hK : ∀ ω, ∀ t < T, 0 ≤ K ω t)
    (hg : ∀ ω, ∀ t < T, ∀ i, |g ω t i| ≤ K ω t)
    (hKi : ∀ t < T, Integrable (fun ω => (K ω t)^2) μ)
    (hKm : ∀ t < T, (∫ ω, (K ω t)^2 ∂μ) ≤ 4 * n)
    (hregret : Integrable (fun ω => ∑ t ∈ Finset.range T,
      ∑ i, g ω t i * (trajectory z0 (g ω) eta t i - x i)) μ) :
    (∫ ω, (∑ t ∈ Finset.range T, ∑ i,
      g ω t i * (trajectory z0 (g ω) eta t i - x i)) ∂μ) ≤
      entropy x z0 / eta + 2 * eta * n * T := by
  let R := fun ω => ∑ t ∈ Finset.range T, ∑ i,
    g ω t i * (trajectory z0 (g ω) eta t i - x i)
  have hpoint : ∀ ω, eta * R ω ≤ entropy x z0 + eta^2 / 2 *
      (∑ t ∈ Finset.range T, (K ω t)^2) := by
    intro ω
    exact entropy_trajectory_regret x z0 (g ω) eta (K ω) hx hsx hz0 hs0 T (hK ω) (hg ω)
  have hsumInt : Integrable (fun ω => ∑ t ∈ Finset.range T, (K ω t)^2) μ :=
    integrable_finsetSum _ (fun t ht => hKi t (Finset.mem_range.mp ht))
  have hcompare := integral_mono (hregret.const_mul eta)
    ((integrable_const (entropy x z0)).add (hsumInt.const_mul (eta^2/2))) hpoint
  change (∫ ω, eta * R ω ∂μ) ≤ (∫ ω, entropy x z0 + eta^2/2 *
    (∑ t ∈ Finset.range T, (K ω t)^2) ∂μ) at hcompare
  rw [integral_add (integrable_const (entropy x z0)) (hsumInt.const_mul (eta^2/2)),
    integral_const_mul, integral_const_mul, integral_const] at hcompare
  simp only [probReal_univ, one_smul] at hcompare
  rw [integral_finsetSum (Finset.range T) (fun t ht => hKi t (Finset.mem_range.mp ht))] at hcompare
  have hsum : (∑ t ∈ Finset.range T, (∫ ω, (K ω t)^2 ∂μ)) ≤ 4 * n * T := by
    calc
      _ ≤ ∑ _t ∈ Finset.range T, (4 * (n : ℝ)) :=
        Finset.sum_le_sum (fun t ht => hKm t (Finset.mem_range.mp ht))
      _ = 4 * n * T := by simp; ring
  have hmul := mul_le_mul_of_nonneg_left hsum (show 0 ≤ eta^2/2 by positivity)
  have hh : eta * (∫ ω, R ω ∂μ) ≤ entropy x z0 + 2 * eta^2 * n * T := by
    nlinarith
  calc
    _ = ∫ ω, R ω ∂μ := rfl
    _ ≤ (entropy x z0 + 2 * eta^2 * n * T) / eta :=
      (le_div_iff₀ heta).mpr (by nlinarith)
    _ = entropy x z0 / eta + 2 * eta * n * T := by field_simp

end PaperEntropyRegret


end
-- END EntropyRegret.lean

-- BEGIN LaplaceMoments.lean
section

namespace PaperLaplace

open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal

theorem exponential_density_identity (x : ℝ) :
    (gammaPDF 1 1 x).toReal = (Ici (0 : ℝ)).indicator (fun x => Real.exp (-x)) x := by
  rw [gammaPDF, ENNReal.toReal_ofReal (gammaPDFReal_nonneg (by norm_num) (by norm_num) x)]
  by_cases hx : 0 ≤ x
  · simp [gammaPDFReal, hx, Real.Gamma_one]
  · simp [gammaPDFReal, hx]

theorem exponential_integral (f : ℝ → ℝ) :
    (∫ x, f x ∂expMeasure 1) = ∫ x in Ici (0 : ℝ), Real.exp (-x) * f x := by
  change (∫ x, f x ∂volume.withDensity (gammaPDF 1 1)) = _
  have hp : Measurable (gammaPDF 1 1) := (measurable_gammaPDFReal 1 1).ennreal_ofReal
  have ht : ∀ᵐ x ∂(volume : Measure ℝ), gammaPDF 1 1 x < ∞ :=
    Filter.Eventually.of_forall (fun x => ENNReal.ofReal_lt_top)
  rw [integral_withDensity_eq_integral_toReal_smul
    hp ht]
  simp only [smul_eq_mul, exponential_density_identity]
  have heq : (fun x => (Ici (0 : ℝ)).indicator (fun x => Real.exp (-x)) x * f x) =
      (Ici (0 : ℝ)).indicator (fun x => Real.exp (-x) * f x) := by
    funext x
    by_cases hx : 0 ≤ x <;> simp [Set.indicator, hx]
  rw [heq, integral_indicator measurableSet_Ici]

theorem exponential_integrable_iff (f : ℝ → ℝ) :
    Integrable f (expMeasure 1) ↔
      IntegrableOn (fun x => Real.exp (-x) * f x) (Ici (0 : ℝ)) := by
  change Integrable f (volume.withDensity (gammaPDF 1 1)) ↔ _
  have hp : Measurable (gammaPDF 1 1) := (measurable_gammaPDFReal 1 1).ennreal_ofReal
  have ht : ∀ᵐ x ∂(volume : Measure ℝ), gammaPDF 1 1 x < ∞ :=
    Filter.Eventually.of_forall (fun x => ENNReal.ofReal_lt_top)
  rw [integrable_withDensity_iff_integrable_smul' hp ht]
  simp only [smul_eq_mul, exponential_density_identity]
  have heq : (fun x => (Ici (0 : ℝ)).indicator (fun x => Real.exp (-x)) x * f x) =
      (Ici (0 : ℝ)).indicator (fun x => Real.exp (-x) * f x) := by
    funext x
    by_cases hx : 0 ≤ x <;> simp [Set.indicator, hx]
  rw [heq, integrable_indicator_iff measurableSet_Ici]

theorem exponential_pow_integrable (k : ℕ) :
    Integrable (fun x : ℝ => x^k) (expMeasure 1) := by
  rw [exponential_integrable_iff, integrableOn_Ici_iff_integrableOn_Ioi]
  have hh := Real.GammaIntegral_convergent (s := (k : ℝ)+1) (by positivity)
  simpa only [add_sub_cancel_right, Real.rpow_natCast] using hh

theorem exponential_pow_integral (k : ℕ) :
    (∫ x : ℝ, x^k ∂expMeasure 1) = Real.Gamma ((k : ℝ)+1) := by
  rw [exponential_integral, integral_Ici_eq_integral_Ioi, Real.Gamma_eq_integral (by positivity)]
  simp only [add_sub_cancel_right, Real.rpow_natCast]

noncomputable def laplaceLaw : Measure ℝ :=
  (1/2 : ℝ≥0∞) • expMeasure 1 + (1/2 : ℝ≥0∞) • (expMeasure 1).map (fun x : ℝ => -x)

instance laplace_isProbability : IsProbabilityMeasure laplaceLaw := by
  letI : IsProbabilityMeasure (expMeasure 1) := isProbabilityMeasure_expMeasure (by norm_num)
  constructor
  simp only [laplaceLaw, Measure.add_apply, Measure.smul_apply, Measure.map_apply measurable_neg
    MeasurableSet.univ]
  simpa using ENNReal.inv_two_add_inv_two

theorem laplace_reflection : laplaceLaw.map (fun x : ℝ => -x) = laplaceLaw := by
  rw [laplaceLaw, Measure.map_add _ _ measurable_neg,
    Measure.map_smul, Measure.map_smul, Measure.map_map measurable_neg measurable_neg]
  simp only [Function.comp_def, neg_neg, Measure.map_id']
  exact add_comm _ _

theorem laplace_pow_two_integrable : Integrable (fun x : ℝ => x^2) laplaceLaw := by
  have hi := exponential_pow_integrable 2
  apply Integrable.add_measure
  · exact hi.smul_measure (by norm_num)
  · have hm : Integrable (fun x : ℝ => x^2) ((expMeasure 1).map (fun x : ℝ => -x)) := by
      apply (integrable_map_measure (by fun_prop) (by fun_prop)).mpr
      simpa [Function.comp_def] using hi
    exact hm.smul_measure (by norm_num)

theorem laplace_pow_two_integral : (∫ x : ℝ, x^2 ∂laplaceLaw) = 2 := by
  have hi := exponential_pow_integrable 2
  have hm : Integrable (fun x : ℝ => x^2) ((expMeasure 1).map (fun x : ℝ => -x)) := by
    apply (integrable_map_measure (by fun_prop) (by fun_prop)).mpr
    simpa [Function.comp_def] using hi
  rw [laplaceLaw, integral_add_measure (hi.smul_measure (by norm_num))
    (hm.smul_measure (by norm_num)), integral_smul_measure, integral_smul_measure,
    integral_map (by fun_prop) (by fun_prop)]
  simp only [smul_eq_mul, neg_sq]
  rw [exponential_pow_integral]
  norm_num [Real.Gamma_add_one, Real.Gamma_one]

theorem laplace_id_memLp_two : MemLp (fun x : ℝ => x) 2 laplaceLaw := by
  exact (memLp_two_iff_integrable_sq (by fun_prop)).mpr laplace_pow_two_integrable

theorem laplace_id_integrable : Integrable (fun x : ℝ => x) laplaceLaw :=
  laplace_id_memLp_two.integrable (by norm_num)

theorem laplace_mean_zero : (∫ x : ℝ, x ∂laplaceLaw) = 0 := by
  have hh : (∫ x : ℝ, x ∂laplaceLaw) = ∫ x : ℝ, -x ∂laplaceLaw := by
    calc
      _ = ∫ x : ℝ, x ∂laplaceLaw.map (fun x : ℝ => -x) := by rw [laplace_reflection]
      _ = _ := by rw [integral_map (by fun_prop) (by fun_prop)]
  rw [integral_neg] at hh
  linarith

theorem laplace_variance_two : ProbabilityTheory.variance (fun x : ℝ => x) laplaceLaw = 2 := by
  rw [ProbabilityTheory.variance_eq_sub laplace_id_memLp_two,
    laplace_mean_zero, zero_pow (by norm_num), sub_zero]
  exact laplace_pow_two_integral

theorem exponential_abs_integrable : Integrable (fun x : ℝ => |x|) (expMeasure 1) := by
  letI : IsProbabilityMeasure (expMeasure 1) := isProbabilityMeasure_expMeasure (by norm_num)
  have hh : MemLp (fun x : ℝ => x) 2 (expMeasure 1) :=
    (memLp_two_iff_integrable_sq (by fun_prop)).mpr (exponential_pow_integrable 2)
  have hi := hh.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  simpa only [Real.norm_eq_abs] using hi.norm

theorem exponential_abs_integral : (∫ x : ℝ, |x| ∂expMeasure 1) = 1 := by
  rw [exponential_integral]
  have hh : (∫ x in Ici (0 : ℝ), Real.exp (-x) * |x|) =
      ∫ x in Ici (0 : ℝ), Real.exp (-x) * x := by
    apply setIntegral_congr_fun measurableSet_Ici
    intro x hx
    change Real.exp (-x) * |x| = Real.exp (-x) * x
    rw [abs_of_nonneg (show 0 ≤ x from hx)]
  rw [hh, ← exponential_integral]
  simpa [Real.Gamma_add_one, Real.Gamma_one] using exponential_pow_integral 1

theorem laplace_abs_integrable : Integrable (fun x : ℝ => |x|) laplaceLaw := by
  simpa only [Real.norm_eq_abs] using laplace_id_integrable.norm

theorem laplace_abs_integral : (∫ x : ℝ, |x| ∂laplaceLaw) = 1 := by
  have hi := exponential_abs_integrable
  have hm : Integrable (fun x : ℝ => |x|) ((expMeasure 1).map (fun x : ℝ => -x)) := by
    apply (integrable_map_measure (by fun_prop) (by fun_prop)).mpr
    simpa [Function.comp_def] using hi
  rw [laplaceLaw, integral_add_measure (hi.smul_measure (by norm_num))
    (hm.smul_measure (by norm_num)), integral_smul_measure, integral_smul_measure,
    integral_map (by fun_prop) (by fun_prop)]
  simp only [smul_eq_mul, abs_neg, exponential_abs_integral]
  norm_num

noncomputable def productLaw (n : ℕ) : Measure (Fin n → ℝ) :=
  Measure.pi (fun _ : Fin n => laplaceLaw)

instance productLaw_isProbability (n : ℕ) : IsProbabilityMeasure (productLaw n) := by
  unfold productLaw
  infer_instance

theorem productLaw_reflection (n : ℕ) :
    MeasurePreserving (fun u : Fin n → ℝ => fun i => -u i) (productLaw n) (productLaw n) := by
  exact measurePreserving_pi (fun _ : Fin n => laplaceLaw) (fun _ : Fin n => laplaceLaw)
    (fun _ => ⟨measurable_neg, laplace_reflection⟩)

theorem product_odd_integral_zero (n : ℕ) (f : (Fin n → ℝ) → ℝ)
    (hf : Measurable f) (hodd : ∀ u, f (fun i => -u i) = -f u) :
    (∫ u, f u ∂productLaw n) = 0 := by
  have hp := productLaw_reflection n
  have hh : (∫ u, f u ∂productLaw n) =
      ∫ u, f (fun i => -u i) ∂productLaw n := by
    calc
      _ = ∫ u, f u ∂(productLaw n).map (fun u : Fin n → ℝ => fun i => -u i) := by rw [hp.map_eq]
      _ = _ := integral_map hp.measurable.aemeasurable (by fun_prop)
  simp_rw [hodd] at hh
  rw [integral_neg] at hh
  linarith

theorem product_abs_coordinate_integrable (n : ℕ) (i : Fin n) :
    Integrable (fun u : Fin n → ℝ => |u i|) (productLaw n) := by
  have hp : MeasurePreserving (Function.eval i) (productLaw n) laplaceLaw :=
    measurePreserving_eval (μ := fun _ : Fin n => laplaceLaw) i
  exact hp.integrable_comp_of_integrable laplace_abs_integrable

theorem product_abs_coordinate_integral (n : ℕ) (i : Fin n) :
    (∫ u : Fin n → ℝ, |u i| ∂productLaw n) = 1 := by
  have hp : MeasurePreserving (Function.eval i) (productLaw n) laplaceLaw :=
    measurePreserving_eval (μ := fun _ : Fin n => laplaceLaw) i
  calc
    _ = ∫ x : ℝ, |x| ∂(productLaw n).map (Function.eval i) :=
      (integral_map hp.measurable.aemeasurable (by fun_prop)).symm
    _ = 1 := by rw [hp.map_eq, laplace_abs_integral]

theorem product_norm_integrable (n : ℕ) :
    Integrable (fun u : Fin n → ℝ => ‖WithLp.toLp 1 u‖) (productLaw n) := by
  simp only [PiLp.norm_eq_of_L1, Real.norm_eq_abs]
  exact integrable_finsetSum _ (fun i _ => product_abs_coordinate_integrable n i)

theorem product_norm_integral (n : ℕ) :
    (∫ u : Fin n → ℝ, ‖WithLp.toLp 1 u‖ ∂productLaw n) = (n : ℝ) := by
  simp only [PiLp.norm_eq_of_L1, Real.norm_eq_abs]
  rw [integral_finsetSum Finset.univ (fun i _ => product_abs_coordinate_integrable n i)]
  simp only [product_abs_coordinate_integral, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one]

end PaperLaplace


end
-- END LaplaceMoments.lean

-- BEGIN ProductVariance.lean
section

namespace PaperProductVariance

open MeasureTheory ProbabilityTheory

theorem lipschitz_memLp_two {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → E) (hX : MemLp X 2 μ) (f : E → ℝ) (hf : LipschitzWith 1 f) :
    MemLp (fun ω => f (X ω)) 2 μ := by
  have hshift : LipschitzWith 1 (fun x => f x - f 0) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa only [Real.dist_eq, sub_sub_sub_cancel_right] using hf.dist_le_mul x y
  have hm := hshift.comp_memLp (by simp) hX
  have ha := hm.add (memLp_const (f 0))
  convert ha using 1
  ext ω
  simp

theorem variance_le_centered_second_moment {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω → ℝ) (hf : MemLp f 2 μ) (c : ℝ) :
    variance f μ ≤ ∫ ω, (f ω - c) ^ 2 ∂μ := by
  calc
    variance f μ = variance (fun ω => f ω - c) μ :=
      (variance_sub_const hf.aestronglyMeasurable c).symm
    _ ≤ _ := variance_le_expectation_sq
      (hf.aestronglyMeasurable.sub aestronglyMeasurable_const)

theorem real_lipschitz_variance_le (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : MemLp (id : ℝ → ℝ) 2 μ) (f : ℝ → ℝ) (hf : LipschitzWith 1 f) :
    variance f μ ≤ variance (id : ℝ → ℝ) μ := by
  have hfm := lipschitz_memLp_two μ id hμ f hf
  have hleft : Integrable (fun x => (f x - f (∫ t, t ∂μ)) ^ 2) μ :=
    (hfm.sub (memLp_const _)).integrable_sq
  have hright : Integrable (fun x => (x - ∫ t, t ∂μ) ^ 2) μ :=
    (hμ.sub (memLp_const _)).integrable_sq
  calc
    variance f μ ≤ ∫ x, (f x - f (∫ t, t ∂μ)) ^ 2 ∂μ :=
      variance_le_centered_second_moment μ f hfm _
    _ ≤ ∫ x, (x - ∫ t, t ∂μ) ^ 2 ∂μ := by
      apply integral_mono hleft hright
      intro x
      have h := hf.dist_le_mul x (∫ t, t ∂μ)
      simp only [NNReal.coe_one, one_mul, Real.dist_eq] at h
      nlinarith [sq_abs (f x - f (∫ t, t ∂μ)), sq_abs (x - ∫ t, t ∂μ),
        abs_nonneg (f x - f (∫ t, t ∂μ)), abs_nonneg (x - ∫ t, t ∂μ)]
    _ = variance (id : ℝ → ℝ) μ := (variance_eq_integral hμ.aemeasurable).symm

theorem variance_prod_decomposition {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (f : α × β → ℝ) (hf : MemLp f 2 (μ.prod ν))
    (hsections : ∀ x, MemLp (fun y => f (x, y)) 2 ν)
    (hmean : MemLp (fun x => ∫ y, f (x, y) ∂ν) 2 μ) :
    variance f (μ.prod ν) =
      (∫ x, variance (fun y => f (x, y)) ν ∂μ) +
        variance (fun x => ∫ y, f (x, y) ∂ν) μ := by
  have hs : (fun x => variance (fun y => f (x, y)) ν) =
      fun x => (∫ y, f (x, y) ^ 2 ∂ν) - (∫ y, f (x, y) ∂ν) ^ 2 := by
    funext x
    exact variance_eq_sub (hsections x)
  rw [hs, integral_sub hf.integrable_sq.integral_prod_left hmean.integrable_sq,
    variance_eq_sub hf, variance_eq_sub hmean]
  simp only [Pi.pow_apply]
  rw [integral_prod f (hf.integrable (by norm_num)),
    integral_prod (fun p => f p ^ 2) hf.integrable_sq]
  ring

theorem integral_lipschitz {E : Type*} [PseudoMetricSpace E]
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (f : E → Ω → ℝ) (hf : ∀ x, Integrable (f x) μ)
    (hLip : ∀ ω, LipschitzWith 1 (fun x => f x ω)) :
    LipschitzWith 1 (fun x => ∫ ω, f x ω ∂μ) := by
  apply LipschitzWith.of_le_add_mul
  intro x y
  have h := integral_mono (hf x) ((hf y).add (integrable_const (dist x y)))
    (fun ω => by simpa only [Pi.add_apply, NNReal.coe_one, one_mul] using
      (hLip ω).le_add_mul x y)
  simp only [Pi.add_apply] at h
  rw [integral_add (hf y) (integrable_const (dist x y))] at h
  simpa using h

abbrev Space (n : ℕ) := PiLp 1 (fun _ : Fin n => ℝ)

noncomputable def join {n : ℕ} (t : ℝ) (x : Space n) : Space (n + 1) :=
  WithLp.toLp 1 (Fin.cons t (WithLp.ofLp x))

theorem norm_eq_sum_abs {n : ℕ} (x : Space n) : ‖x‖ = ∑ i, |x i| := by
  simpa using PiLp.norm_eq_sum (p := 1) (by norm_num) x

theorem join_dist {n : ℕ} (t s : ℝ) (x y : Space n) :
    dist (join t x) (join s y) = dist t s + dist x y := by
  rw [dist_eq_norm, norm_eq_sum_abs, Fin.sum_univ_succ, Real.dist_eq, dist_eq_norm,
    norm_eq_sum_abs]
  rfl

theorem join_head_isometry {n : ℕ} (x : Space n) : Isometry (fun t => join t x) := by
  apply Isometry.of_dist_eq
  intro t s
  simp [join_dist]

theorem join_tail_isometry {n : ℕ} (t : ℝ) : Isometry (fun x : Space n => join t x) := by
  apply Isometry.of_dist_eq
  intro x y
  simp [join_dist]

theorem product_vector_memLp (n : ℕ) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : MemLp (id : ℝ → ℝ) 2 μ) :
    MemLp (fun x : Fin n → ℝ => (WithLp.toLp 1 x : Space n)) 2
      (Measure.pi (fun _ : Fin n => μ)) := by
  apply MemLp.of_eval_piLp
  intro i
  exact hμ.comp_measurePreserving (measurePreserving_eval (μ := fun _ : Fin n => μ) i)

theorem product_lipschitz_memLp (n : ℕ) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : MemLp (id : ℝ → ℝ) 2 μ) (f : Space n → ℝ) (hf : LipschitzWith 1 f) :
    MemLp (fun x : Fin n → ℝ => f (WithLp.toLp 1 x)) 2
      (Measure.pi (fun _ : Fin n => μ)) :=
  lipschitz_memLp_two _ _ (product_vector_memLp n μ hμ) f hf

theorem variance_sections_integrable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (f : α × β → ℝ) (hf : MemLp f 2 (μ.prod ν))
    (hsections : ∀ x, MemLp (fun y => f (x, y)) 2 ν)
    (hmean : MemLp (fun x => ∫ y, f (x, y) ∂ν) 2 μ) :
    Integrable (fun x => variance (fun y => f (x, y)) ν) μ := by
  have he : (fun x => variance (fun y => f (x, y)) ν) =
      fun x => (∫ y, f (x, y) ^ 2 ∂ν) - (∫ y, f (x, y) ∂ν) ^ 2 := by
    funext x
    exact variance_eq_sub (hsections x)
  rw [he]
  exact hf.integrable_sq.integral_prod_left.sub hmean.integrable_sq

theorem product_lipschitz_variance_le (n : ℕ) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : MemLp (id : ℝ → ℝ) 2 μ) (f : Space n → ℝ) (hf : LipschitzWith 1 f) :
    variance (fun x : Fin n → ℝ => f (WithLp.toLp 1 x))
      (Measure.pi (fun _ : Fin n => μ)) ≤ n * variance (id : ℝ → ℝ) μ := by
  induction n with
  | zero =>
    have he : (fun x : Fin 0 → ℝ => f (WithLp.toLp 1 x)) = fun _ => f 0 := by
      funext x
      congr 1
      apply PiLp.ext
      intro i
      exact Fin.elim0 i
    rw [he, variance_eq_integral (by fun_prop)]
    simp
  | succ n ih =>
    let ν : Measure (Fin n → ℝ) := Measure.pi (fun _ : Fin n => μ)
    let F : ℝ × (Fin n → ℝ) → ℝ := fun p => f (join p.1 (WithLp.toLp 1 p.2))
    have htail : ∀ t : ℝ, LipschitzWith 1 (fun x : Space n => f (join t x)) := by
      intro t
      simpa only [Function.comp_def, mul_one] using hf.comp (join_tail_isometry t).lipschitz
    have hsections : ∀ t : ℝ, MemLp (fun x : Fin n → ℝ => F (t, x)) 2 ν := by
      intro t
      exact product_lipschitz_memLp n μ hμ (fun x => f (join t x)) (htail t)
    have hhead : ∀ x : Fin n → ℝ, LipschitzWith 1 (fun t => F (t, x)) := by
      intro x
      simpa only [Function.comp_def, mul_one] using
        hf.comp (join_head_isometry (WithLp.toLp 1 x : Space n)).lipschitz
    have hmeanLip : LipschitzWith 1 (fun t => ∫ x, F (t, x) ∂ν) :=
      integral_lipschitz ν (fun t x => F (t, x))
        (fun t => (hsections t).integrable (by norm_num)) hhead
    have hmean : MemLp (fun t => ∫ x, F (t, x) ∂ν) 2 μ :=
      lipschitz_memLp_two μ id hμ _ hmeanLip
    have hmp : MeasurePreserving (fun p : ℝ × (Fin n → ℝ) => Fin.cons p.1 p.2)
        (μ.prod ν) (Measure.pi (fun _ : Fin (n + 1) => μ)) := by
      simpa [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
        Fin.insertNth_zero, ν] using
        (measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => μ) 0).symm
    have hfm := product_lipschitz_memLp (n + 1) μ hμ f hf
    have hF : MemLp F 2 (μ.prod ν) := hfm.comp_measurePreserving hmp
    have hvar : variance (fun x : Fin (n + 1) → ℝ => f (WithLp.toLp 1 x))
        (Measure.pi (fun _ : Fin (n + 1) => μ)) = variance F (μ.prod ν) :=
      (hmp.variance_fun_comp hfm.aemeasurable).symm
    have hsectionBound : ∀ t : ℝ,
        variance (fun x : Fin n → ℝ => F (t, x)) ν ≤ n * variance (id : ℝ → ℝ) μ := by
      intro t
      exact ih (fun x : Space n => f (join t x)) (htail t)
    have hintBound : (∫ t, variance (fun x : Fin n → ℝ => F (t, x)) ν ∂μ) ≤
        n * variance (id : ℝ → ℝ) μ := by
      have h := integral_mono (variance_sections_integrable μ ν F hF hsections hmean)
        (integrable_const (n * variance (id : ℝ → ℝ) μ)) hsectionBound
      simpa using h
    have hmeanBound := real_lipschitz_variance_le μ hμ _ hmeanLip
    rw [hvar, variance_prod_decomposition μ ν F hF hsections hmean]
    push_cast
    linarith

end PaperProductVariance


end
-- END ProductVariance.lean

-- BEGIN MinimaxAssembly.lean
section

/-!
Conditional assembly of the manuscript profile for the actual minimax problem.
This file is concatenation-tested after the unchanged baseline Composition.lean
and OracleModel.lean. The three regional, spike, and algorithmic components below
are separate substantive premises; none is established by this assembly file.
-/
noncomputable section

namespace Task003.MinimaxAssembly
open Task003.OracleModel
open CompositionAudit

/-- An internal arithmetic interface to `CompositionAudit`. A missing minimax is
assigned zero only outside the domain on which existence is proved. The final
profile explicitly asserts `minimaxBudget = some N`, so the default cannot hide
a missing finite-budget algorithm. -/
def budgetValue (d : ℕ) (α : ℝ) : ℝ :=
  ((minimaxBudget d 1 1 α).getD 0 : ℕ)

theorem minimum_of_admissible {d m : ℕ} {L R ε : ℝ}
    (hm : AdmissibleBudget d m L R ε) :
    ∃ N : ℕ, minimaxBudget d L R ε = some N ∧
      AdmissibleBudget d N L R ε ∧ N ≤ m := by
  cases hN : minimaxBudget d L R ε with
  | none =>
    have hn := (minimaxBudget_eq_none_iff d L R ε).1 hN
    exact False.elim (hn ⟨m, hm⟩)
  | some N =>
    have hh := (minimaxBudget_eq_some_iff d N L R ε).1 hN
    exact ⟨N, rfl, hh.1, hh.2 m hm⟩

theorem budgetValue_of_some {d N : ℕ} {α : ℝ}
    (hN : minimaxBudget d 1 1 α = some N) : budgetValue d α = (N : ℝ) := by
  simp [budgetValue, hN]

theorem profileQ_eq (d : ℕ) (α : ℝ) : profileQ d α = q (d : ℝ) α := rfl

theorem profileLambda_eq (d : ℕ) (α : ℝ) :
    profileLambda d α = Lambda (d : ℝ) α := rfl

/-- Connecting an actual upper-budget witness and actual universal budget lower
bounds to the least feasible natural budget. This is not a proof of the rate
premises: the regional theorem, spike theorem, and algorithmic upper theorem are
all explicit arguments, each expressed directly in terms of `AdmissibleBudget`.
The conclusion is the named full profile for the genuine oracle/minimax model. -/
theorem fullJointProfile_of_components
    (Dsource : ℕ) (c0 c c1 cd b : ℝ)
    (hc0 : 0 < c0) (hc0max : c0 ≤ 1/8)
    (hc : 0 < c) (hc1 : 0 < c1) (hcd : 0 < cd) (hb : 0 < b)
    (hregional : ∀ (d : ℕ) (α : ℝ), Dsource ≤ d → 0 < α → α ≤ c0 →
      α ≤ tau (d:ℝ) cd → ∀ m : ℕ, AdmissibleBudget d m 1 1 α →
      c * q (d:ℝ) α / (ell (d:ℝ) * Real.log (Real.exp 1 * M (d:ℝ) α)) ≤ (m:ℝ))
    (hspike : ∀ (d : ℕ) (α : ℝ), Dsource ≤ d → 0 < α → α ≤ c0 →
      ∀ m : ℕ, AdmissibleBudget d m 1 1 α →
      c1 * (d:ℝ) / ell (d:ℝ) ≤ (m:ℝ))
    (hupper : ∀ (d : ℕ) (α : ℝ), Dsource ≤ d → 0 < α → α ≤ c0 →
      ∃ m : ℕ, AdmissibleBudget d m 1 1 α ∧
      (m:ℝ) ≤ b * q (d:ℝ) α * Lambda (d:ℝ) α ^ 2) :
    FullJointProfile c0 := by
  have hc01 : c0 ≤ 1 := by linarith
  have hregValue : ∀ (d : ℕ) (α : ℝ), Dsource ≤ d → 0 < α → α ≤ c0 →
      α ≤ tau (d:ℝ) cd →
      c * q (d:ℝ) α / (ell (d:ℝ) * Real.log (Real.exp 1 * M (d:ℝ) α)) ≤
        budgetValue d α := by
    intro d α hd hα hα0 hreg
    obtain ⟨m, hm, _⟩ := hupper d α hd hα hα0
    obtain ⟨N, hN, hAdm, _⟩ := minimum_of_admissible hm
    rw [budgetValue_of_some hN]
    exact hregional d α hd hα hα0 hreg N hAdm
  have hspikeValue : ∀ (d : ℕ) (α : ℝ), Dsource ≤ d → 0 < α → α ≤ c0 →
      c1 * (d:ℝ) / ell (d:ℝ) ≤ budgetValue d α := by
    intro d α hd hα hα0
    obtain ⟨m, hm, _⟩ := hupper d α hd hα hα0
    obtain ⟨N, hN, hAdm, _⟩ := minimum_of_admissible hm
    rw [budgetValue_of_some hN]
    exact hspike d α hd hα hα0 N hAdm
  have hupperValue : ∀ (d : ℕ) (α : ℝ), Dsource ≤ d → 0 < α → α ≤ c0 →
      budgetValue d α ≤ b * q (d:ℝ) α * Lambda (d:ℝ) α ^ 2 := by
    intro d α hd hα hα0
    obtain ⟨m, hm, hbound⟩ := hupper d α hd hα hα0
    obtain ⟨N, hN, _, hNm⟩ := minimum_of_admissible hm
    rw [budgetValue_of_some hN]
    exact (Nat.cast_le.mpr hNm).trans hbound
  obtain ⟨D, hDs, hD1, hapos, hbpos, hprofile⟩ :=
    full_domain_nat_composition budgetValue Dsource c0 c c1 cd b
      hc0 hc01 hc hc1 hcd hb hregValue hspikeValue hupperValue
  refine ⟨D, lowerConstant c c1 cd, b, by omega, hapos, hbpos, ?_⟩
  intro d hd α hα hα0
  obtain ⟨m, hm, _⟩ := hupper d α (hDs.trans hd) hα hα0
  obtain ⟨N, hN, _, _⟩ := minimum_of_admissible hm
  have hh := hprofile d α hd hα hα0
  rw [budgetValue_of_some hN] at hh
  refine ⟨N, hN, ?_, ?_⟩
  · simpa only [profileQ_eq, profileLambda_eq] using hh.1
  · simpa only [profileQ_eq, profileLambda_eq] using hh.2

/-- The assembled normalized profile automatically applies to the same genuine
minimax budget at every positive scale, by the proved policy normalization. -/
theorem FullJointProfile.scaled {c0 : ℝ} (h : FullJointProfile c0) :
    ∃ (D : ℕ) (a b : ℝ), 0 < D ∧ 0 < a ∧ 0 < b ∧
      ∀ (d : ℕ), D ≤ d → ∀ (L R ε : ℝ), 0 < L → 0 < R →
        0 < ε/(L*R) → ε/(L*R) ≤ c0 →
        ∃ N : ℕ, minimaxBudget d L R ε = some N ∧
          a * profileQ d (ε/(L*R)) / (profileLambda d (ε/(L*R)))^2 ≤ (N:ℝ) ∧
          (N:ℝ) ≤ b * profileQ d (ε/(L*R)) * (profileLambda d (ε/(L*R)))^2 := by
  obtain ⟨D, a, b, hD, ha, hb, hh⟩ := h
  refine ⟨D, a, b, hD, ha, hb, ?_⟩
  intro d hd L R ε hL hR he he0
  obtain ⟨N, hN, hlo, hhi⟩ := hh d hd (ε/(L*R)) he he0
  exact ⟨N, (minimaxBudget_normalization hL hR).trans hN, hlo, hhi⟩

end Task003.MinimaxAssembly

end
end
-- END MinimaxAssembly.lean

-- BEGIN FiniteNetExistence.lean
section

/-! Finite-budget existence by an actual deterministic finite-net oracle policy.
Concatenation dependency: OracleModel.lean. No rate estimate is asserted. -/
noncomputable section
namespace Task003.FiniteNetExistence
open Set MeasureTheory
open scoped ENNReal
open Task003.OracleModel

/-- The lowest natural index attaining the minimum is used to resolve ties. -/
def MinimumIndex (n : ℕ) (v : Fin n → ℝ) (k : ℕ) : Prop :=
  ∃ hk : k < n, ∀ i : Fin n, v ⟨k, hk⟩ ≤ v i

theorem minimumIndex_exists (n : ℕ) (hn : 0 < n) (v : Fin n → ℝ) :
    ∃ k : ℕ, MinimumIndex n v k := by
  obtain ⟨i, _, hi⟩ := Finset.exists_min_image Finset.univ v
    (by exact ⟨⟨0, hn⟩, Finset.mem_univ _⟩)
  exact ⟨i.val, i.isLt, fun j => hi j (Finset.mem_univ _)⟩

theorem minimumIndex_measurable (n k : ℕ) :
    MeasurableSet {v : Fin n → ℝ | MinimumIndex n v k} := by
  by_cases hk : k < n
  · have he : {v : Fin n → ℝ | MinimumIndex n v k} =
        ⋂ i : Fin n, {v | v ⟨k, hk⟩ ≤ v i} := by
      ext v
      simp [MinimumIndex, hk]
    rw [he]
    exact MeasurableSet.iInter (fun i => measurableSet_le (measurable_pi_apply _) (measurable_pi_apply i))
  · simp [MinimumIndex, hk]

def bestPoint {d : ℕ} (p : ℕ → Point d) (n : ℕ) (v : Fin n → ℝ) : Point d := by
  classical
  exact if hn : 0 < n then p (Nat.find (minimumIndex_exists n hn v)) else p 0

theorem bestPoint_measurable {d : ℕ} (p : ℕ → Point d) (n : ℕ) :
    Measurable (bestPoint p n) := by
  classical
  change Measurable (fun v : Fin n → ℝ => bestPoint p n v)
  by_cases hn : 0 < n
  · simpa only [bestPoint, dif_pos hn] using
      (Measurable.find (fun k => (measurable_const : Measurable (fun _ : Fin n → ℝ => p k)))
        (fun k => minimumIndex_measurable n k) (minimumIndex_exists n hn))
  · simpa only [bestPoint, dif_neg hn] using
      (measurable_const : Measurable (fun _ : Fin n → ℝ => p 0))

theorem bestPoint_feasible {d R} (p : ℕ → Point d)
    (hp : ∀ i, Feasible R (p i)) (n : ℕ) (v : Fin n → ℝ) :
    Feasible R (bestPoint p n v) := by
  classical
  unfold bestPoint
  split <;> exact hp _

theorem bestPoint_le {d : ℕ} (p : ℕ → Point d) (f : Point d → ℝ)
    (n : ℕ) (hn : 0 < n) (v : Fin n → ℝ)
    (hv : ∀ i : Fin n, v i = f (p i.val)) (i : Fin n) :
    f (bestPoint p n v) ≤ f (p i.val) := by
  classical
  unfold bestPoint
  rw [dif_pos hn]
  obtain ⟨hk, hmin⟩ := Nat.find_spec (minimumIndex_exists n hn v)
  have hh := hmin i
  rw [hv ⟨_, hk⟩, hv i] at hh
  exact hh

/-- Deterministic queries enumerate `p`; the final output is a measurable finite
argmin of the exact reply history. Zero observations use the feasible fallback. -/
def samplePolicy {d R} (p : ℕ → Point d) (hp : ∀ i, Feasible R (p i)) :
    Policy d R Unit where
  query := fun n _ => p n
  query_measurable := fun _ => measurable_const
  stop := fun _ _ => false
  stop_measurable := fun _ => measurable_const
  output := fun n h => bestPoint p n h.2
  output_measurable := fun n => (bestPoint_measurable p n).comp measurable_snd
  output_feasible := fun n h => bestPoint_feasible p hp n h.2

def sampleHistory {d : ℕ} (p : ℕ → Point d) (f : Point d → ℝ) (n : ℕ) : Fin n → ℝ :=
  fun i => f (p i.val)

theorem samplePolicy_nextHistory {d R} (p : ℕ → Point d)
    (hp : ∀ i, Feasible R (p i)) (f : Point d → ℝ) (n : ℕ) (ω : Unit) :
    nextHistory (samplePolicy p hp) f n (ω, sampleHistory p f n) =
      (ω, sampleHistory p f (n+1)) := by
  apply Prod.ext
  · rfl
  · funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp [nextHistory, samplePolicy, sampleHistory]
    · simp [nextHistory, samplePolicy, sampleHistory]

theorem execute_samplePolicy {d R} (p : ℕ → Point d)
    (hp : ∀ i, Feasible R (p i)) (f : Point d → ℝ) (fuel n : ℕ) (ω : Unit) :
    execute (samplePolicy p hp) f fuel n (ω, sampleHistory p f n) =
      bestPoint p (n+fuel) (sampleHistory p f (n+fuel)) := by
  induction fuel generalizing n with
  | zero => rfl
  | succ k ih =>
    change execute (samplePolicy p hp) f k (n+1)
      (nextHistory (samplePolicy p hp) f n (ω, sampleHistory p f n)) = _
    rw [samplePolicy_nextHistory, ih]
    have he : n+1+k = n+(k+1) := by omega
    exact congrArg (fun z => bestPoint p z (sampleHistory p f z)) he

theorem run_samplePolicy {d R} (p : ℕ → Point d)
    (hp : ∀ i, Feasible R (p i)) (f : Point d → ℝ) (m : ℕ) (ω : Unit) :
    run (samplePolicy p hp) f m ω = bestPoint p m (sampleHistory p f m) := by
  have he : (Fin.elim0 : Fin 0 → ℝ) = sampleHistory p f 0 := by
    funext i; exact Fin.elim0 i
  have hh := execute_samplePolicy p hp f m 0 ω
  rw [Nat.zero_add] at hh
  change execute (samplePolicy p hp) f m 0 (ω, Fin.elim0) = _
  rw [he]
  exact hh

theorem run_samplePolicy_le {d R} (p : ℕ → Point d)
    (hp : ∀ i, Feasible R (p i)) (f : Point d → ℝ) (m : ℕ) (hm : 0 < m)
    (i : Fin m) (ω : Unit) :
    f (run (samplePolicy p hp) f m ω) ≤ f (p i.val) := by
  rw [run_samplePolicy]
  exact bestPoint_le p f m hm (sampleHistory p f m) (fun _ => rfl) i

/-- Compactness supplies a finite internal net; all its points are feasible.
The enumeration is extended by the feasible center on unused natural indices. -/
theorem finite_feasible_net (d : ℕ) (R δ : ℝ) (hR : 0 ≤ R) (hδ : 0 < δ) :
    ∃ m : ℕ, 0 < m ∧ ∃ p : ℕ → Point d,
      (∀ i, Feasible R (p i)) ∧
      ∀ y : Point d, Feasible R y → ∃ i : Fin m, dist (p i.val) y < δ := by
  classical
  have hset : {x : Point d | Feasible R x} = Metric.closedBall 0 R := by
    ext x; simp [Feasible, Metric.mem_closedBall, dist_zero_right]
  have hc : IsCompact {x : Point d | Feasible R x} := by
    rw [hset]; exact isCompact_closedBall 0 R
  obtain ⟨t, hts, hfinite, hcover⟩ := hc.finite_cover_balls hδ
  have hzero : (0 : Point d) ∈ {x | Feasible R x} := by simpa [Feasible]
  have htne : t.Nonempty := by
    obtain ⟨x, hx⟩ := mem_iUnion.1 (hcover hzero)
    obtain ⟨hxt, _⟩ := mem_iUnion.1 hx
    exact ⟨x, hxt⟩
  letI : Fintype t := hfinite.fintype
  letI : Nonempty t := ⟨⟨htne.some, htne.some_mem⟩⟩
  let m := Fintype.card t
  let e : t ≃ Fin m := Fintype.equivFin t
  let p : ℕ → Point d := fun i => if hi : i < m then (e.symm ⟨i, hi⟩).val else 0
  refine ⟨m, Fintype.card_pos_iff.2 inferInstance, p, ?_, ?_⟩
  · intro i
    dsimp [p]
    split
    · exact hts (e.symm ⟨i, _⟩).property
    · exact hzero
  · intro y hy
    obtain ⟨x, hx⟩ := mem_iUnion.1 (hcover hy)
    obtain ⟨hxt, hball⟩ := mem_iUnion.1 hx
    let j : Fin m := e ⟨x, hxt⟩
    refine ⟨j, ?_⟩
    have hpj : p j.val = x := by
      simp only [p, dif_pos j.isLt]
      exact congrArg Subtype.val (e.symm_apply_apply ⟨x, hxt⟩)
    rw [hpj]
    simpa only [Metric.mem_ball, dist_comm] using hball

/-- Every positive accuracy admits an actual finite pathwise budget. This
compactness proof gives existence, not the manuscript's quantitative rates. -/
theorem admissible_finite_budget {d : ℕ} {L R ε : ℝ}
    (hL : 0 ≤ L) (hR : 0 ≤ R) (hε : 0 < ε) :
    ∃ m : ℕ, AdmissibleBudget d m L R ε := by
  by_cases hLzero : L = 0
  · refine ⟨0, admissible_zero_budget hL hR ?_⟩
    simp only [hLzero, zero_mul]
    exact hε.le
  have hLpos : 0 < L := lt_of_le_of_ne hL (Ne.symm hLzero)
  obtain ⟨m, hm, p, hp, hnet⟩ := finite_feasible_net d R (ε/L) hR (div_pos hε hLpos)
  let a := samplePolicy p hp
  refine ⟨m, Unit, inferInstance, Measure.dirac (), inferInstance, a, ?_⟩
  intro f
  have he : successEvent a f m ε = univ := by
    apply eq_univ_of_forall
    intro ω
    rw [success_iff_comparison a f hR]
    intro y hy
    obtain ⟨i, hi⟩ := hnet y hy
    have hmin := run_samplePolicy_le p hp f m hm i ω
    have hf := f.lip.dist_le_mul (p i.val) y
    rw [Real.coe_toNNReal L hL, Real.dist_eq] at hf
    have habs := le_abs_self (f (p i.val) - f y)
    have hdist : L * dist (p i.val) y < ε := by
      have hh := mul_lt_mul_of_pos_left hi hLpos
      simpa only [mul_div_cancel₀ ε hLpos.ne'] using hh
    linarith
  rw [he]
  simp only [measure_univ]
  exact ENNReal.div_le_of_le_mul (by norm_num)

theorem minimaxBudget_finite {d : ℕ} {L R ε : ℝ}
    (hL : 0 ≤ L) (hR : 0 ≤ R) (hε : 0 < ε) :
    ∃ N : ℕ, minimaxBudget d L R ε = some N := by
  obtain ⟨m, hm⟩ := admissible_finite_budget (d:=d) hL hR hε
  cases hN : minimaxBudget d L R ε with
  | none =>
    exact False.elim ((minimaxBudget_eq_none_iff d L R ε).1 hN ⟨m, hm⟩)
  | some N => exact ⟨N, rfl⟩

end Task003.FiniteNetExistence

end
end
-- END FiniteNetExistence.lean

-- BEGIN SourcePriorBridge.lean
section

/-! Conditioning/Yao applied to the actual source-policy success event.
Dependencies: OracleReduction and ProbabilityReduction plus their dependencies.
The good-prior mass, seedwise external source hardness bound, and joint source
success measurability are explicit remaining premises; no such prior or hardness
result is constructed or claimed here. -/
noncomputable section
namespace Task003.SourcePriorBridge
open Set MeasureTheory
open scoped ENNReal
open Task003.OracleModel Task003.OracleSimulation Task003.OracleReduction
open PaperGeometry PaperGeometryPenalty PaperProbabilityReduction

abbrev Rows (κ : Type*) (d : ℕ) := κ → Fin d → ℝ

def GoodRows {κ : Type*} {d : ℕ} (U : NNReal) : Set (Rows κ d) :=
  {rows | ∀ i j, |rows i j| ≤ U}

theorem goodRows_measurable {κ : Type*} [Fintype κ] (d : ℕ) (U : NNReal) :
    MeasurableSet (@GoodRows κ d U) := by
  have he : @GoodRows κ d U = ⋂ i : κ, ⋂ j : Fin d,
      {rows : Rows κ d | |rows i j| ≤ (U : ℝ)} := by
    ext rows; simp [GoodRows]
  rw [he]
  apply MeasurableSet.iInter
  intro i
  apply MeasurableSet.iInter
  intro j
  exact measurableSet_le (((measurable_pi_apply j).comp (measurable_pi_apply i)).abs) measurable_const

/-- The event is determined by the true Euclidean source minimum and actual
source execution, jointly over the hidden rows and the independent private seed. -/
def priorSuccess {κ : Type*} [Fintype κ] [Nonempty κ] {d Ω} [MeasurableSpace Ω]
    (b : SourcePolicy d Ω) (m : ℕ) (η : ℝ) : Set (Rows κ d × Ω) :=
  {p | p.2 ∈ sourceSuccessEvent b (sourceSupport p.1) m η}

/-- This theorem separates the proved target reduction and conditioning/Yao
argument from the unresolved source-prior theorem. Its source hardness premise
concerns executions of feasible Euclidean policies on a concrete row prior,
with pathwise cap at most `Tk`; it is not a target lower inequality. The remaining
joint-event measurability premise is also stated explicitly and is not hidden in
a proof certificate. -/
theorem not_admissible_of_source_prior {κ : Type*} [Fintype κ] [Nonempty κ]
    {d m Tk : ℕ} (hd : 0 < d) (hm : m ≤ Tk)
    (U : NNReal) (hU : 0 < U) (η : ℝ) (hη : 0 < η)
    (prior : Measure (Rows κ d)) [IsProbabilityMeasure prior]
    (hgood : (15/16 : ℝ) ≤ prior.real (@GoodRows κ d U))
    (hjoint : ∀ (Ω : Type) (s : MeasurableSpace Ω),
      letI : MeasurableSpace Ω := s
      ∀ b : SourcePolicy d Ω, MeasurableSet (@priorSuccess κ _ _ d Ω s b m η))
    (hsource : ∀ (Ω : Type) (s : MeasurableSpace Ω),
      letI : MeasurableSpace Ω := s
      ∀ b : SourcePolicy d Ω,
      (∀ (rows : Rows κ d) ω,
        b.queriesUsed (sourceSupport rows) m 0 (ω, Fin.elim0) ≤ Tk) →
      ∀ ω : Ω, prior.real {rows | (rows, ω) ∈ @priorSuccess κ _ _ d Ω s b m η} ≤ (1/4 : ℝ)) :
    ¬ AdmissibleBudget d m 1 1 (η / (4 * ((beta d * U : NNReal) : ℝ))) := by
  rintro ⟨Ω, s, seed, hp, a, ha⟩
  letI : MeasurableSpace Ω := s
  letI : IsProbabilityMeasure seed := hp
  obtain ⟨b, hb, hcap⟩ := source_simulator_actual_success (κ:=κ) seed a m hd U hU η hη ha
  have hcapTk : ∀ (rows : Rows κ d) ω,
      b.queriesUsed (sourceSupport rows) m 0 (ω, Fin.elim0) ≤ Tk :=
    fun rows ω => (hcap rows ω).trans hm
  let S : Set (Rows κ d × Ω) := priorSuccess b m η
  have hS : MeasurableSet S := hjoint Ω s b
  obtain ⟨rows, hrows, hbad⟩ := source_bound_to_fixed_bad_target prior seed
    (GoodRows U) (goodRows_measurable d U) hgood S S hS (hsource Ω s b hcapTk)
    (fun _ _ _ hs => hs)
  have hprob := (hb rows hrows).2
  have hreal : (2/3 : ℝ) ≤ seed.real (sourceSuccessEvent b (sourceSupport rows) m η) := by
    have hh := ENNReal.toReal_mono (measure_ne_top seed _) hprob
    norm_num [ENNReal.toReal_div, ← measureReal_def] at hh
    exact hh
  change seed.real (sourceSuccessEvent b (sourceSupport rows) m η) < (2/3 : ℝ) at hbad
  exact (not_lt_of_ge hreal) hbad

end Task003.SourcePriorBridge

end
end
-- END SourcePriorBridge.lean

-- BEGIN SourceMeasurabilityClean.lean
section

/-! Joint measurability of the actual source success event over hidden rows and
an arbitrary measurable private seed space. This closes the measurability premise
of SourcePriorBridge without assuming any source hardness theorem. -/
noncomputable section
namespace Task003.SourceMeasurability
open Set MeasureTheory
open Task003.OracleModel Task003.OracleSimulation Task003.OracleReduction
open Task003.SourcePriorBridge
open PaperGeometry PaperGeometryPenalty

/-- Finite maxima of the coordinatewise linear source observations are jointly
continuous in the hidden rows and in the Euclidean query point. -/
theorem sourceSupport_joint_continuous {κ : Type*} [Fintype κ] [Nonempty κ] (d : ℕ) :
    Continuous (fun p : Rows κ d × SourcePoint d => sourceSupport p.1 p.2) := by
  change Continuous (fun p : Rows κ d × SourcePoint d =>
    Finset.univ.sup' Finset.univ_nonempty (fun i => ∑ j, p.1 i j * (fromEuclidean p.2) j))
  apply Continuous.finset_sup'_apply
  intro i _
  apply continuous_finsetSum
  intro j _
  apply Continuous.mul
  · exact (continuous_apply_apply i j).comp continuous_fst
  · exact (PiLp.continuous_apply 1 (fun _ : Fin d => ℝ) j).comp
      (fromEuclidean_continuous.comp continuous_snd)

theorem sourceOptimum_continuous {κ : Type*} [Fintype κ] [Nonempty κ] (d : ℕ) :
    Continuous (fun rows : Rows κ d => sourceOptimum (sourceSupport rows)) := by
  have hset : {z : SourcePoint d | ‖z‖ ≤ 1} = Metric.closedBall 0 1 := by
    ext z; simp only [Metric.mem_closedBall, dist_zero_right, mem_setOf_eq]
  have hc : IsCompact {z : SourcePoint d | ‖z‖ ≤ 1} := by
    rw [hset]; exact isCompact_closedBall 0 1
  exact hc.continuous_sInf (sourceSupport_joint_continuous d)

def jointNext {κ : Type*} [Fintype κ] [Nonempty κ] {d Ω} [MeasurableSpace Ω]
    (b : SourcePolicy d Ω) (n : ℕ) (p : Rows κ d × (Ω × (Fin n → ℝ))) :
    Rows κ d × (Ω × (Fin (n+1) → ℝ)) :=
  (p.1, b.nextHistory (sourceSupport p.1) n p.2)

theorem jointNext_measurable {κ : Type*} [Fintype κ] [Nonempty κ] {d Ω}
    [MeasurableSpace Ω] (b : SourcePolicy d Ω) (n : ℕ) :
    Measurable (@jointNext κ _ _ d Ω _ b n) := by
  apply measurable_fst.prodMk
  apply (measurable_fst.comp measurable_snd).prodMk
  apply measurable_pi_lambda
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simpa [jointNext, SourcePolicy.nextHistory, Function.comp_def] using
      ((sourceSupport_joint_continuous (κ:=κ) d).measurable.comp
        (measurable_fst.prodMk ((b.query_measurable n).comp measurable_snd)))
  · simpa [jointNext, SourcePolicy.nextHistory, Function.comp_def] using
      (measurable_pi_apply j).comp (measurable_snd.comp measurable_snd)

theorem sourceExecute_joint_measurable {κ : Type*} [Fintype κ] [Nonempty κ] {d Ω}
    [MeasurableSpace Ω] (b : SourcePolicy d Ω) (fuel n : ℕ) :
    Measurable (fun p : Rows κ d × (Ω × (Fin n → ℝ)) =>
      b.execute (sourceSupport p.1) fuel n p.2) := by
  induction fuel generalizing n with
  | zero => exact (b.output_measurable n).comp measurable_snd
  | succ k ih =>
    change Measurable (fun p : Rows κ d × (Ω × (Fin n → ℝ)) =>
      if b.stop n p.2 then b.output n p.2 else
        b.execute (sourceSupport p.1) k (n+1) (b.nextHistory (sourceSupport p.1) n p.2))
    apply Measurable.ite
    · exact measurableSet_eq_fun ((b.stop_measurable n).comp measurable_snd) measurable_const
    · exact (b.output_measurable n).comp measurable_snd
    · have hh := (ih (n+1)).comp (jointNext_measurable (κ:=κ) b n)
      simpa only [Function.comp_def, jointNext] using hh

set_option maxHeartbeats 4000000
theorem sourceRun_joint_measurable {κ : Type*} [Fintype κ] [Nonempty κ] {d Ω}
    [MeasurableSpace Ω] (b : SourcePolicy d Ω) (m : ℕ) :
    Measurable (fun p : Rows κ d × Ω => b.run (sourceSupport p.1) m p.2) := by
  change Measurable (fun p : Rows κ d × Ω =>
    b.execute (sourceSupport p.1) m 0 (p.2, (Fin.elim0 : Fin 0 → ℝ)))
  have hi : Measurable (fun p : Rows κ d × Ω =>
      (p.1, (p.2, (Fin.elim0 : Fin 0 → ℝ)))) :=
    measurable_fst.prodMk (measurable_snd.prodMk measurable_const)
  exact (sourceExecute_joint_measurable (κ:=κ) b m 0).comp hi

set_option maxHeartbeats 4000000
theorem priorSuccess_measurable {κ : Type*} [Fintype κ] [Nonempty κ] {d Ω}
    [MeasurableSpace Ω] (b : SourcePolicy d Ω) (m : ℕ) (η : ℝ) :
    MeasurableSet (@priorSuccess κ _ _ d Ω _ b m η) := by
  change MeasurableSet {p : Rows κ d × Ω |
    sourceSupport p.1 (b.run (sourceSupport p.1) m p.2) - sourceOptimum (sourceSupport p.1) ≤ η}
  have hpair : Measurable (fun p : Rows κ d × Ω =>
      (p.1, b.run (sourceSupport p.1) m p.2)) :=
    measurable_fst.prodMk (sourceRun_joint_measurable (κ:=κ) b m)
  have hout : Measurable (fun p : Rows κ d × Ω =>
      sourceSupport p.1 (b.run (sourceSupport p.1) m p.2)) :=
    (sourceSupport_joint_continuous (κ:=κ) d).measurable.comp hpair
  have hopt : Measurable (fun p : Rows κ d × Ω => sourceOptimum (sourceSupport p.1)) :=
    (sourceOptimum_continuous (κ:=κ) d).measurable.comp measurable_fst
  exact measurableSet_le (hout.sub hopt) measurable_const

/-- The genuine lower-bound reduction now requires only the concrete source
prior's good-event mass and external seedwise hardness theorem. All oracle,
measurability, decoding, conditioning, and independent-seed averaging steps are
proved. The existence and source bound for that prior remain external premises. -/
theorem not_admissible_of_source_prior_measurable {κ : Type*} [Fintype κ] [Nonempty κ]
    {d m Tk : ℕ} (hd : 0 < d) (hm : m ≤ Tk)
    (U : NNReal) (hU : 0 < U) (η : ℝ) (hη : 0 < η)
    (prior : Measure (Rows κ d)) [IsProbabilityMeasure prior]
    (hgood : (15/16 : ℝ) ≤ prior.real (@GoodRows κ d U))
    (hsource : ∀ (Ω : Type) (s : MeasurableSpace Ω),
      letI : MeasurableSpace Ω := s
      ∀ b : SourcePolicy d Ω,
      (∀ (rows : Rows κ d) ω,
        b.queriesUsed (sourceSupport rows) m 0 (ω, Fin.elim0) ≤ Tk) →
      ∀ ω : Ω, prior.real {rows | (rows, ω) ∈ @priorSuccess κ _ _ d Ω s b m η} ≤ (1/4 : ℝ)) :
    ¬ AdmissibleBudget d m 1 1 (η / (4 * ((beta d * U : NNReal) : ℝ))) := by
  apply not_admissible_of_source_prior hd hm U hU η hη prior hgood _ hsource
  intro Ω s
  letI : MeasurableSpace Ω := s
  intro b
  exact priorSuccess_measurable b m η

end Task003.SourceMeasurability

end
end
-- END SourceMeasurabilityClean.lean

-- BEGIN SourceFreeze.lean
section

/-! Freezing the private seed of an actual measurable adaptive source policy.
This permits applying deterministic source-prior theorems before Yao averaging.
Dependencies by concatenation: OracleModel, Geometry, OracleSimulation. -/
noncomputable section
namespace Task003.OracleSimulation
open MeasureTheory
open Task003.OracleSimulation

/-- Fixing a private seed produces a deterministic measurable source policy on
Unit, with all Euclidean query/output constraints and total fallbacks preserved. -/
def SourcePolicy.freeze {d Ω} [MeasurableSpace Ω] (b : SourcePolicy d Ω) (ω : Ω) :
    SourcePolicy d Unit where
  query := fun n h => b.query n (ω, h.2)
  query_measurable := fun n => (b.query_measurable n).comp (measurable_const.prodMk measurable_snd)
  query_feasible := fun n h => b.query_feasible n (ω, h.2)
  stop := fun n h => b.stop n (ω, h.2)
  stop_measurable := fun n => (b.stop_measurable n).comp (measurable_const.prodMk measurable_snd)
  output := fun n h => b.output n (ω, h.2)
  output_measurable := fun n => (b.output_measurable n).comp (measurable_const.prodMk measurable_snd)
  output_feasible := fun n h => b.output_feasible n (ω, h.2)

theorem SourcePolicy.execute_freeze {d Ω} [MeasurableSpace Ω]
    (b : SourcePolicy d Ω) (ω : Ω) (f : SourcePoint d → ℝ)
    (fuel n : ℕ) (v : Fin n → ℝ) :
    (b.freeze ω).execute f fuel n ((), v) = b.execute f fuel n (ω, v) := by
  induction fuel generalizing n with
  | zero => rfl
  | succ k ih =>
    simp only [SourcePolicy.execute]
    change (if b.stop n (ω, v) then b.output n (ω, v)
      else (b.freeze ω).execute f k (n+1)
        ((), Fin.snoc v (f (b.query n (ω, v))))) =
      (if b.stop n (ω, v) then b.output n (ω, v)
        else b.execute f k (n+1) (ω, Fin.snoc v (f (b.query n (ω, v)))))
    split
    · rfl
    · exact ih (n+1) _

theorem SourcePolicy.run_freeze {d Ω} [MeasurableSpace Ω]
    (b : SourcePolicy d Ω) (ω : Ω) (f : SourcePoint d → ℝ) (m : ℕ) :
    (b.freeze ω).run f m () = b.run f m ω :=
  b.execute_freeze ω f m 0 Fin.elim0

theorem SourcePolicy.queriesUsed_freeze {d Ω} [MeasurableSpace Ω]
    (b : SourcePolicy d Ω) (ω : Ω) (f : SourcePoint d → ℝ)
    (fuel n : ℕ) (v : Fin n → ℝ) :
    (b.freeze ω).queriesUsed f fuel n ((), v) = b.queriesUsed f fuel n (ω, v) := by
  induction fuel generalizing n with
  | zero => rfl
  | succ k ih =>
    simp only [SourcePolicy.queriesUsed]
    change (if b.stop n (ω, v) then 0
      else 1 + (b.freeze ω).queriesUsed f k (n+1)
        ((), Fin.snoc v (f (b.query n (ω, v))))) =
      (if b.stop n (ω, v) then 0
        else 1 + b.queriesUsed f k (n+1) (ω, Fin.snoc v (f (b.query n (ω, v)))))
    split
    · rfl
    · rw [ih]

end Task003.OracleSimulation

end
end
-- END SourceFreeze.lean

-- BEGIN SourceDeterministicPrior.lean
section

/-! A deterministic source-prior theorem suffices for randomized target
impossibility. Dependencies: SourceMeasurability and SourceFreeze, plus all their
listed dependencies. This file proves seed freezing, conditioning and averaging
are connected to the actual optimizer model. It does not construct the source
prior or prove its good-event mass or deterministic hardness bound. -/
noncomputable section
namespace Task003.SourceDeterministicPrior
open Set MeasureTheory
open Task003.OracleModel Task003.OracleSimulation Task003.OracleReduction
open Task003.SourcePriorBridge Task003.SourceMeasurability
open PaperGeometry PaperGeometryPenalty

/-- The sole source hardness premise quantifies deterministic Unit-seed policies
in the Euclidean unit ball with a true pathwise cap. Private randomization in the
target is handled internally by the proved fixed-seed simulation and Yao step.
The prior mass and deterministic source bound are explicitly external premises. -/
theorem not_admissible_of_deterministic_source_prior
    {κ : Type*} [Fintype κ] [Nonempty κ] {d m Tk : ℕ}
    (hd : 0 < d) (hm : m ≤ Tk) (U : NNReal) (hU : 0 < U)
    (η : ℝ) (hη : 0 < η) (prior : Measure (Rows κ d)) [IsProbabilityMeasure prior]
    (hgood : (15/16 : ℝ) ≤ prior.real (@GoodRows κ d U))
    (hsource : ∀ b : SourcePolicy d Unit,
      (∀ rows : Rows κ d,
        b.queriesUsed (sourceSupport rows) m 0 ((), Fin.elim0) ≤ Tk) →
      prior.real {rows | () ∈ sourceSuccessEvent b (sourceSupport rows) m η} ≤ (1/4 : ℝ)) :
    ¬ AdmissibleBudget d m 1 1 (η / (4 * ((beta d * U : NNReal) : ℝ))) := by
  apply not_admissible_of_source_prior_measurable hd hm U hU η hη prior hgood
  intro Ω s
  letI : MeasurableSpace Ω := s
  intro b hcap ω
  let bω := b.freeze ω
  have hcapω : ∀ rows : Rows κ d,
      bω.queriesUsed (sourceSupport rows) m 0 ((), Fin.elim0) ≤ Tk := by
    intro rows
    rw [SourcePolicy.queriesUsed_freeze]
    exact hcap rows ω
  have hbω := hsource bω hcapω
  have he : {rows : Rows κ d | (rows, ω) ∈ priorSuccess b m η} =
      {rows | () ∈ sourceSuccessEvent bω (sourceSupport rows) m η} := by
    ext rows
    simp only [priorSuccess, sourceSuccessEvent, mem_setOf_eq, bω, SourcePolicy.run_freeze]
  rw [he]
  exact hbω

end Task003.SourceDeterministicPrior

end
end
-- END SourceDeterministicPrior.lean

-- BEGIN StrictSourcePriorClean.lean
section

/-! The exact strict-success interface required by manuscript External Theorem Z.
A source failure at error ≥ η bounds success at error < η, not success at ≤ η.
The decoder's proved 3η/4 margin supplies the strict inequality. Dependencies:
OracleReduction, SourceMeasurability, SourceFreeze and their listed dependencies.
The source prior and its deterministic hardness bound remain external premises. -/
noncomputable section
namespace Task003.StrictSourcePrior
open Set MeasureTheory
open scoped ENNReal
open Task003.OracleModel Task003.OracleSimulation Task003.OracleReduction
open Task003.SourcePriorBridge Task003.SourceMeasurability
open PaperGeometry PaperGeometryPenalty PaperApproxGeometryPenalty PaperProbabilityReduction

def strictSourceSuccessEvent {d Ω} [MeasurableSpace Ω] (b : SourcePolicy d Ω)
    (f : SourcePoint d → ℝ) (m : ℕ) (η : ℝ) : Set Ω :=
  {ω | f (b.run f m ω) - sourceOptimum f < η}

def strictPriorSuccess {κ : Type*} [Fintype κ] [Nonempty κ] {d Ω} [MeasurableSpace Ω]
    (b : SourcePolicy d Ω) (m : ℕ) (η : ℝ) : Set (Rows κ d × Ω) :=
  {p | p.2 ∈ strictSourceSuccessEvent b (sourceSupport p.1) m η}

set_option maxHeartbeats 4000000
theorem strictPriorSuccess_measurable {κ : Type*} [Fintype κ] [Nonempty κ] {d Ω}
    [MeasurableSpace Ω] (b : SourcePolicy d Ω) (m : ℕ) (η : ℝ) :
    MeasurableSet (@strictPriorSuccess κ _ _ d Ω _ b m η) := by
  change MeasurableSet {p : Rows κ d × Ω |
    sourceSupport p.1 (b.run (sourceSupport p.1) m p.2) - sourceOptimum (sourceSupport p.1) < η}
  have hpair : Measurable (fun p : Rows κ d × Ω =>
      (p.1, b.run (sourceSupport p.1) m p.2)) :=
    measurable_fst.prodMk (sourceRun_joint_measurable (κ:=κ) b m)
  have hout : Measurable (fun p : Rows κ d × Ω =>
      sourceSupport p.1 (b.run (sourceSupport p.1) m p.2)) :=
    (sourceSupport_joint_continuous (κ:=κ) d).measurable.comp hpair
  have hopt : Measurable (fun p : Rows κ d × Ω => sourceOptimum (sourceSupport p.1)) :=
    (sourceOptimum_continuous (κ:=κ) d).measurable.comp measurable_fst
  exact measurableSet_lt (hout.sub hopt) measurable_const

/-- The same public decoder succeeds strictly below η on every fixed good source
instance with probability ≥2/3. Its query cap and independent seed are unchanged. -/
theorem source_simulator_strict {κ : Type*} [Fintype κ] [Nonempty κ]
    {d Ω} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (a : Policy d 1 Ω) (m : ℕ) (hd : 0 < d)
    (U : NNReal) (hU : 0 < U) (η : ℝ) (hη : 0 < η)
    (ha : SolvesOn μ a m 1 (η / (4 * ((beta d * U : NNReal) : ℝ)))) :
    ∃ b : SourcePolicy d Ω,
      (∀ (rows : κ → Fin d → ℝ), (∀ i j, |rows i j| ≤ U) →
        MeasurableSet (strictSourceSuccessEvent b (sourceSupport rows) m η) ∧
          (2/3 : ℝ≥0∞) ≤ μ (strictSourceSuccessEvent b (sourceSupport rows) m η)) ∧
      (∀ (rows : κ → Fin d → ℝ) ω,
        b.queriesUsed (sourceSupport rows) m 0 (ω, Fin.elim0) ≤ m) := by
  obtain ⟨decode, hdecode, hdecodefeas, hdecodesuccess⟩ :=
    measurable_source_decoder_with_slack (κ:=κ) d hd U hU η hη
  have hfeas : ∀ x : Point d, Feasible 1 x → ‖decode x‖ ≤ 1 := by
    intro x _
    simpa only [Metric.mem_closedBall, dist_zero_right] using hdecodefeas x
  let b := simulate a U decode hdecode hfeas
  refine ⟨b, ?_, ?_⟩
  · intro rows hrows
    obtain ⟨u, huS, _, hsource, hsuccess⟩ := hdecodesuccess rows hrows
    let z : SourcePoint d := Real.sqrt d • PaperGeometry.toEuclidean u
    have hz : ‖z‖ ≤ 1 := by
      have hmem : z ∈ Metric.closedBall (0 : SourcePoint d) 1 := by
        rw [← smallEuclideanBall_scaled_image d hd]
        exact ⟨u, huS, rfl⟩
      simpa only [Metric.mem_closedBall, dist_zero_right] using hmem
    have hmin : ∀ y : SourcePoint d, ‖y‖ ≤ 1 → sourceSupport rows z ≤ sourceSupport rows y := by
      intro y hy
      exact hsource y (by simpa only [Metric.mem_closedBall, dist_zero_right] using hy)
    have hopt : sourceOptimum (sourceSupport rows) = scaledSupport d rows u :=
      sourceOptimum_eq_of_min (sourceSupport rows) z hz hmin
    have hfmeas := sourceSupport_measurable d rows U hrows
    refine ⟨?_, ?_⟩
    · exact measurableSet_lt
        ((hfmeas.comp (b.run_measurable _ hfmeas m)).sub measurable_const) measurable_const
    · let f := supportPenaltyObjective d hd rows U hU hrows
      have hprob := ha f
      apply hprob.trans
      apply measure_mono
      intro ω hω
      have hu : Feasible 1 u := smallEuclideanBall_subset_l1_ball d hd huS
      have hcmp := (success_iff_comparison a f (by norm_num) m
        (η / (4 * ((beta d * U : NNReal) : ℝ))) ω).1 hω u hu
      have hgap : normalizedSupportPenalty d rows U
          (run a (normalizedSupportPenalty d rows U) m ω) -
          normalizedSupportPenalty d rows U u ≤ η / (4 * ((beta d * U : NNReal) : ℝ)) := by
        change normalizedSupportPenalty d rows U
          (run a (normalizedSupportPenalty d rows U) m ω) ≤
          normalizedSupportPenalty d rows U u + η / (4 * ((beta d * U : NNReal) : ℝ)) at hcmp
        linarith
      change sourceSupport rows ((simulate a U decode hdecode hfeas).run (sourceSupport rows) m ω) -
        sourceOptimum (sourceSupport rows) < η
      rw [run_simulate a hd U hU rows decode hdecode hfeas, hopt]
      exact (hsuccess _ hgap).2.2
  · intro rows ω
    exact b.queriesUsed_le _ m 0 _

/-- Exact deterministic source-prior interface: strict source success at η.
The only unresolved inputs are the source prior's mass bound and its source
hardness theorem. No target oracle lower inequality is assumed here. -/
theorem not_admissible_of_strict_deterministic_source_prior
    {κ : Type*} [Fintype κ] [Nonempty κ] {d m Tk : ℕ}
    (hd : 0 < d) (hm : m ≤ Tk) (U : NNReal) (hU : 0 < U)
    (η : ℝ) (hη : 0 < η) (prior : Measure (Rows κ d)) [IsProbabilityMeasure prior]
    (hgood : (15/16 : ℝ) ≤ prior.real (@GoodRows κ d U))
    (hsource : ∀ b : SourcePolicy d Unit,
      (∀ rows : Rows κ d,
        b.queriesUsed (sourceSupport rows) m 0 ((), Fin.elim0) ≤ Tk) →
      prior.real {rows | () ∈ strictSourceSuccessEvent b (sourceSupport rows) m η} ≤ (1/4 : ℝ)) :
    ¬ AdmissibleBudget d m 1 1 (η / (4 * ((beta d * U : NNReal) : ℝ))) := by
  rintro ⟨Ω, s, seed, hp, a, ha⟩
  letI : MeasurableSpace Ω := s
  letI : IsProbabilityMeasure seed := hp
  obtain ⟨b, hb, hcap⟩ := source_simulator_strict (κ:=κ) seed a m hd U hU η hη ha
  have hseedwise : ∀ ω : Ω,
      prior.real {rows | (rows, ω) ∈ strictPriorSuccess b m η} ≤ (1/4 : ℝ) := by
    intro ω
    let bω := b.freeze ω
    have hcapω : ∀ rows : Rows κ d,
        bω.queriesUsed (sourceSupport rows) m 0 ((), Fin.elim0) ≤ Tk := by
      intro rows
      rw [SourcePolicy.queriesUsed_freeze]
      exact (hcap rows ω).trans hm
    have hbω := hsource bω hcapω
    have he : {rows : Rows κ d | (rows, ω) ∈ strictPriorSuccess b m η} =
        {rows | () ∈ strictSourceSuccessEvent bω (sourceSupport rows) m η} := by
      ext rows
      simp only [strictPriorSuccess, strictSourceSuccessEvent, mem_setOf_eq, bω, SourcePolicy.run_freeze]
    rw [he]
    exact hbω
  let S : Set (Rows κ d × Ω) := strictPriorSuccess b m η
  have hS : MeasurableSet S := strictPriorSuccess_measurable b m η
  obtain ⟨rows, hrows, hbad⟩ := source_bound_to_fixed_bad_target prior seed
    (GoodRows U) (goodRows_measurable d U) hgood S S hS hseedwise (fun _ _ _ hs => hs)
  have hprob := (hb rows hrows).2
  have hreal : (2/3 : ℝ) ≤ seed.real (strictSourceSuccessEvent b (sourceSupport rows) m η) := by
    have hh := ENNReal.toReal_mono (measure_ne_top seed _) hprob
    norm_num [ENNReal.toReal_div, ← measureReal_def] at hh
    exact hh
  change seed.real (strictSourceSuccessEvent b (sourceSupport rows) m η) < (2/3 : ℝ) at hbad
  exact (not_lt_of_ge hreal) hbad

end Task003.StrictSourcePrior

end
end
-- END StrictSourcePriorClean.lean

-- BEGIN RegionalAccuracy.lean
section

/-! Integer selection and accuracy conversion for the regional lower bound.
This arithmetic layer depends on unchanged Composition and OracleModel. Source
prior interfaces are supplied only in a subsequent bridge, not assumed as the
continuous target regional inequality to be proved. -/
noncomputable section
namespace Task003.RegionalAccuracy
open Task003.OracleModel CompositionAudit

/-- A natural floor loses at most a factor two once its real argument is ≥1. -/
theorem floor_half (r : ℝ) (hr : 1 ≤ r) :
    1 ≤ ⌊r⌋₊ ∧ (⌊r⌋₊ : ℝ) ≤ r ∧ r/2 ≤ (⌊r⌋₊ : ℝ) := by
  have hfloor : 1 ≤ ⌊r⌋₊ := (Nat.one_le_floor_iff r).2 hr
  have hfloorR : (1:ℝ) ≤ (⌊r⌋₊ : ℝ) := by exact_mod_cast hfloor
  refine ⟨hfloor, Nat.floor_le (by linarith), ?_⟩
  have hh := Nat.lt_floor_add_one r
  linarith

def selectionConstant (κ δ : ℝ) : ℝ := min (κ/2) (δ^2/2)

theorem selectionConstant_pos {κ δ : ℝ} (hκ : 0 < κ) (hδ : 0 < δ) :
    0 < selectionConstant κ δ :=
  lt_min (by positivity) (by positivity)

/-- This single truncated floor handles both the regional integer and plateau
cases. It is exactly `min K floor(r)`, and no real query budget is rounded into a
natural number in the oracle model. -/
theorem select_coordinate {d : ℕ} {α κ δ : ℝ}
    (hd : 1 ≤ (d:ℝ)) (hκ : 0 < κ) (hκ1 : κ ≤ 1)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hα : 0 < α)
    (hlarge : 2 ≤ κ*(d:ℝ))
    (hscope : α ≤ δ / Real.sqrt (ell (d:ℝ))) :
    ∃ k : ℕ, 1 ≤ k ∧ k ≤ ⌊κ*(d:ℝ)⌋₊ ∧
      (k:ℝ) ≤ δ^2 * (A α)^2 / ell (d:ℝ) ∧
      selectionConstant κ δ * M (d:ℝ) α / ell (d:ℝ) ≤ (k:ℝ) ∧
      (k:ℝ) ≤ M (d:ℝ) α := by
  have hd0 : (0:ℝ) ≤ d := by positivity
  have he1 : 1 ≤ ell (d:ℝ) := by
    rw [show ell (d:ℝ) = 1 + Real.log (d:ℝ) from log_e_mul (by linarith)]
    have := Real.log_nonneg hd
    linarith
  have he : 0 < ell (d:ℝ) := by linarith
  have hs : 0 < Real.sqrt (ell (d:ℝ)) := Real.sqrt_pos.2 he
  have hprod : α * Real.sqrt (ell (d:ℝ)) ≤ δ := (le_div_iff₀ hs).1 hscope
  have hprodsq : α^2 * ell (d:ℝ) ≤ δ^2 := by
    have hh : (α * Real.sqrt (ell (d:ℝ)))^2 ≤ δ^2 :=
      (sq_le_sq₀ (mul_nonneg hα.le hs.le) hδ.le).2 hprod
    simpa only [mul_pow, Real.sq_sqrt he.le] using hh
  have haid : α^2 * (A α)^2 = 1 := by dsimp [A]; field_simp
  let r : ℝ := δ^2 * (A α)^2 / ell (d:ℝ)
  have hr : 1 ≤ r := by
    apply (le_div_iff₀ he).2
    have hh := mul_le_mul_of_nonneg_right hprodsq (sq_nonneg (A α))
    nlinarith [haid]
  let K : ℕ := ⌊κ*(d:ℝ)⌋₊
  have hK := floor_half (κ*(d:ℝ)) (by linarith)
  have hrhalf := floor_half r hr
  let k : ℕ := min K ⌊r⌋₊
  have hk1 : 1 ≤ k := le_min hK.1 hrhalf.1
  have hkK : k ≤ K := min_le_left _ _
  have hkfloorR : (k:ℝ) ≤ (⌊r⌋₊:ℝ) := by exact_mod_cast (min_le_right K ⌊r⌋₊)
  have hkr : (k:ℝ) ≤ r := hkfloorR.trans hrhalf.2.1
  have hM0 : 0 ≤ M (d:ℝ) α := le_min hd0 (sq_nonneg _)
  have hMell : M (d:ℝ) α / ell (d:ℝ) ≤ (d:ℝ) := by
    apply (div_le_iff₀ he).2
    exact (min_le_left _ _).trans (by nlinarith)
  have hcκ : selectionConstant κ δ ≤ κ/2 := min_le_left _ _
  have hcδ : selectionConstant κ δ ≤ δ^2/2 := min_le_right _ _
  have hc0 : 0 ≤ selectionConstant κ δ := (selectionConstant_pos hκ hδ).le
  have hboundK : selectionConstant κ δ * M (d:ℝ) α / ell (d:ℝ) ≤ (K:ℝ) := by
    calc
      selectionConstant κ δ * M (d:ℝ) α / ell (d:ℝ) =
          selectionConstant κ δ * (M (d:ℝ) α / ell (d:ℝ)) := by ring
      _ ≤ (κ/2) * (d:ℝ) := mul_le_mul hcκ hMell (div_nonneg hM0 he.le) (by positivity)
      _ = κ * (d:ℝ) / 2 := by ring
      _ ≤ (K:ℝ) := hK.2.2
  have hboundr : selectionConstant κ δ * M (d:ℝ) α / ell (d:ℝ) ≤ (⌊r⌋₊:ℝ) := by
    have hh : selectionConstant κ δ * M (d:ℝ) α ≤ (δ^2/2) * (A α)^2 :=
      mul_le_mul hcδ (min_le_right _ _) hM0 (by positivity)
    calc
      selectionConstant κ δ * M (d:ℝ) α / ell (d:ℝ) ≤
          ((δ^2/2) * (A α)^2) / ell (d:ℝ) := div_le_div_of_nonneg_right hh he.le
      _ = r/2 := by dsimp [r]; ring
      _ ≤ (⌊r⌋₊:ℝ) := hrhalf.2.2
  have hkLower : selectionConstant κ δ * M (d:ℝ) α / ell (d:ℝ) ≤ (k:ℝ) := by
    rw [show (k:ℝ) = min (K:ℝ) (⌊r⌋₊:ℝ) from Nat.cast_min _ _]
    exact le_min hboundK hboundr
  have hkD : (k:ℝ) ≤ (d:ℝ) := by
    have hKle := hK.2.1
    have hkKreal : (k:ℝ) ≤ (K:ℝ) := by exact_mod_cast hkK
    have hκd : κ*(d:ℝ) ≤ (d:ℝ) := by nlinarith
    exact hkKreal.trans (hKle.trans hκd)
  have hrA : r ≤ (A α)^2 := by
    apply (div_le_iff₀ he).2
    have hδsq : δ^2 ≤ ell (d:ℝ) := by nlinarith
    have hh := mul_le_mul_of_nonneg_right hδsq (sq_nonneg (A α))
    nlinarith
  exact ⟨k, hk1, hkK, hkr, hkLower, le_min hkD (hkr.trans hrA)⟩

theorem accuracy_of_coordinate {d k : ℕ} {α δ : ℝ}
    (hd : 1 ≤ (d:ℝ)) (hk : 1 ≤ k) (hα : 0 < α) (hδ : 0 < δ)
    (hkr : (k:ℝ) ≤ δ^2 * (A α)^2 / ell (d:ℝ)) :
    α ≤ δ / Real.sqrt ((k:ℝ)*ell (d:ℝ)) := by
  have he1 : 1 ≤ ell (d:ℝ) := by
    rw [show ell (d:ℝ) = 1 + Real.log (d:ℝ) from log_e_mul (by linarith)]
    have := Real.log_nonneg hd
    linarith
  have he : 0 < ell (d:ℝ) := by linarith
  have hkR : (0:ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hs : 0 < Real.sqrt ((k:ℝ)*ell (d:ℝ)) := Real.sqrt_pos.2 (mul_pos hkR he)
  have hh := (le_div_iff₀ he).1 hkr
  have hmul := mul_le_mul_of_nonneg_right hh (sq_nonneg α)
  have haid : (A α)^2 * α^2 = 1 := by dsimp [A]; field_simp
  have hprodsq : (α * Real.sqrt ((k:ℝ)*ell (d:ℝ)))^2 ≤ δ^2 := by
    rw [mul_pow, Real.sq_sqrt (mul_pos hkR he).le]
    nlinarith [haid]
  apply (le_div_iff₀ hs).2
  nlinarith [mul_pos hα hs]

theorem exists_dimension_threshold (κ : ℝ) (hκ : 0 < κ) (Dsource : ℕ) :
    ∃ D : ℕ, Dsource ≤ D ∧ 1 ≤ D ∧
      ∀ d : ℕ, D ≤ d → 1 ≤ (d:ℝ) ∧ 2 ≤ κ*(d:ℝ) := by
  obtain ⟨k, hk⟩ := exists_nat_ge (2/κ)
  let D := max Dsource (max 1 k)
  refine ⟨D, le_max_left _ _, (le_max_left _ _).trans (le_max_right _ _), ?_⟩
  intro d hd
  have hd1 : 1 ≤ d := ((le_max_left 1 k).trans (le_max_right Dsource (max 1 k))).trans hd
  have hkd : k ≤ d := ((le_max_right 1 k).trans (le_max_right Dsource (max 1 k))).trans hd
  have hkdR : (k:ℝ) ≤ (d:ℝ) := by exact_mod_cast hkd
  refine ⟨by exact_mod_cast hd1, ?_⟩
  have hh := (div_le_iff₀ hκ).1 (hk.trans hkdR)
  nlinarith

theorem regional_threshold_comparison {d k : ℕ} {α κ δ cp : ℝ}
    (hd : 1 ≤ (d:ℝ)) (hk : 1 ≤ k) (hcp : 0 < cp)
    (hκ : 0 < κ) (hδ : 0 < δ)
    (hklower : selectionConstant κ δ * M (d:ℝ) α / ell (d:ℝ) ≤ (k:ℝ))
    (hkM : (k:ℝ) ≤ M (d:ℝ) α) :
    (cp * selectionConstant κ δ) * q (d:ℝ) α /
        (ell (d:ℝ) * Real.log (Real.exp 1 * M (d:ℝ) α)) ≤
      cp * (d:ℝ) * (k:ℝ) / Real.log (Real.exp 1 * (k:ℝ)) := by
  have hd0 : (0:ℝ) ≤ d := by positivity
  have hk1 : (1:ℝ) ≤ k := by exact_mod_cast hk
  have hkp : (0:ℝ) < k := by linarith
  have hMp : 0 < M (d:ℝ) α := lt_of_lt_of_le hkp hkM
  have he : 0 < ell (d:ℝ) := by
    rw [show ell (d:ℝ) = 1 + Real.log (d:ℝ) from log_e_mul (by linarith)]
    have := Real.log_nonneg hd
    linarith
  have hlk : 0 < Real.log (Real.exp 1 * (k:ℝ)) := by
    rw [log_e_mul hkp]
    have := Real.log_nonneg hk1
    linarith
  have hlle : Real.log (Real.exp 1 * (k:ℝ)) ≤
      Real.log (Real.exp 1 * M (d:ℝ) α) :=
    Real.log_le_log (mul_pos (Real.exp_pos 1) hkp)
      (mul_le_mul_of_nonneg_left hkM (Real.exp_pos 1).le)
  have hlM : 0 < Real.log (Real.exp 1 * M (d:ℝ) α) := hlk.trans_le hlle
  calc
    (cp * selectionConstant κ δ) * q (d:ℝ) α /
        (ell (d:ℝ) * Real.log (Real.exp 1 * M (d:ℝ) α)) =
        cp * (d:ℝ) * (selectionConstant κ δ * M (d:ℝ) α / ell (d:ℝ)) /
          Real.log (Real.exp 1 * M (d:ℝ) α) := by
      dsimp [q]
      field_simp
    _ ≤ cp * (d:ℝ) * (k:ℝ) / Real.log (Real.exp 1 * M (d:ℝ) α) :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hklower (mul_nonneg hcp.le hd0)) hlM.le
    _ ≤ cp * (d:ℝ) * (k:ℝ) / Real.log (Real.exp 1 * (k:ℝ)) :=
      div_le_div_of_nonneg_left (by positivity) hlk hlle

/-- Pure selection/accuracy assembly from discrete-coordinate impossibility.
The discrete premise is the output of the actual source-prior simulation, not
the continuous regional lower inequality concluded here. -/
theorem regional_from_coordinate_impossibility {d : ℕ} {α κ δ cp : ℝ}
    (hd : 1 ≤ (d:ℝ)) (hκ : 0 < κ) (hκ1 : κ ≤ 1)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hcp : 0 < cp) (hα : 0 < α)
    (hlarge : 2 ≤ κ*(d:ℝ)) (hscope : α ≤ δ / Real.sqrt (ell (d:ℝ)))
    (hcoord : ∀ k : ℕ, 1 ≤ k → k ≤ ⌊κ*(d:ℝ)⌋₊ → ∀ m : ℕ,
      (m:ℝ) < cp*(d:ℝ)*(k:ℝ) / Real.log (Real.exp 1 * (k:ℝ)) →
      ¬ AdmissibleBudget d m 1 1 (δ / Real.sqrt ((k:ℝ)*ell (d:ℝ)))) :
    ∀ m : ℕ, AdmissibleBudget d m 1 1 α →
      (cp * selectionConstant κ δ) * q (d:ℝ) α /
        (ell (d:ℝ) * Real.log (Real.exp 1 * M (d:ℝ) α)) ≤ (m:ℝ) := by
  obtain ⟨k, hk, hkK, hkr, hklower, hkM⟩ :=
    select_coordinate hd hκ hκ1 hδ hδ1 hα hlarge hscope
  have hαk := accuracy_of_coordinate hd hk hα hδ hkr
  intro m hm
  have hmk := admissible_accuracy_mono hm hαk
  have hbound : cp*(d:ℝ)*(k:ℝ) / Real.log (Real.exp 1 * (k:ℝ)) ≤ (m:ℝ) := by
    by_contra h
    exact hcoord k hk hkK m (lt_of_not_ge h) hmk
  exact (regional_threshold_comparison hd hk hcp hκ hδ hklower hkM).trans hbound

end Task003.RegionalAccuracy

end
end
-- END RegionalAccuracy.lean

-- BEGIN RegionalSourceBridge.lean
section

/-! The regional lower bound from concrete strict source-prior families.
Dependencies: RegionalAccuracy, StrictSourcePrior, and their dependencies.
The source-prior family, good-event mass and source hardness are explicitly
external. All target model, scaling, integer selection and logarithmic conversion
steps are proved here. Natural zero budgets are promoted to cap one only after
proving every relevant source threshold is at least two. -/
noncomputable section
namespace Task003.RegionalSourceBridge
open Set MeasureTheory
open Task003.OracleModel Task003.OracleSimulation Task003.OracleReduction
open Task003.SourcePriorBridge Task003.StrictSourcePrior Task003.RegionalAccuracy
open CompositionAudit PaperGeometry PaperGeometryPenalty

def coordinateBound (d : ℕ) (C : ℝ) : NNReal :=
  (C * Real.sqrt (ell (d:ℝ) / (d:ℝ))).toNNReal

def sourceAccuracy (C δ : ℝ) (k : ℕ) : ℝ := 4*C*δ / Real.sqrt (k:ℝ)

theorem ell_ge_one {d : ℕ} (hd : 1 ≤ (d:ℝ)) : 1 ≤ ell (d:ℝ) := by
  rw [show ell (d:ℝ) = 1 + Real.log (d:ℝ) from log_e_mul (by linarith)]
  have := Real.log_nonneg hd
  linarith

theorem coordinateBound_pos {d : ℕ} {C : ℝ} (hd : 1 ≤ (d:ℝ)) (hC : 0 < C) :
    0 < coordinateBound d C := by
  apply Real.toNNReal_pos.2
  apply mul_pos hC
  apply Real.sqrt_pos.2
  exact div_pos (by have := ell_ge_one hd; linarith) (by linarith)

theorem lambda_identity {d : ℕ} {C : ℝ} (hd : 1 ≤ (d:ℝ)) (hC : 0 < C) :
    ((beta d * coordinateBound d C : NNReal) : ℝ) = C * Real.sqrt (ell (d:ℝ)) := by
  have he : 0 < ell (d:ℝ) := by have := ell_ge_one hd; linarith
  have hsd : 0 < Real.sqrt (d:ℝ) := Real.sqrt_pos.2 (by linarith)
  have hval : 0 ≤ C * Real.sqrt (ell (d:ℝ)/(d:ℝ)) := by positivity
  change Real.sqrt (d:ℝ) * ((C * Real.sqrt (ell (d:ℝ)/(d:ℝ))).toNNReal : ℝ) = _
  rw [Real.coe_toNNReal _ hval, Real.sqrt_div he.le]
  field_simp

theorem accuracy_identity {d k : ℕ} {C δ : ℝ}
    (hd : 1 ≤ (d:ℝ)) (hk : 1 ≤ k) (hC : 0 < C) :
    sourceAccuracy C δ k / (4 * ((beta d * coordinateBound d C : NNReal) : ℝ)) =
      δ / Real.sqrt ((k:ℝ)*ell (d:ℝ)) := by
  have he : 0 < ell (d:ℝ) := by have := ell_ge_one hd; linarith
  have hkR : (0:ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  rw [lambda_identity hd hC, Real.sqrt_mul hkR.le]
  dsimp [sourceAccuracy]
  field_simp

theorem sourceAccuracy_pos {k : ℕ} {C δ : ℝ}
    (hk : 1 ≤ k) (hC : 0 < C) (hδ : 0 < δ) : 0 < sourceAccuracy C δ k := by
  dsimp [sourceAccuracy]
  have hkR : (0:ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  positivity

theorem source_threshold_ge_dimension {d k : ℕ} {cp : ℝ}
    (hk : 1 ≤ k) (hcp : 0 < cp) :
    cp*(d:ℝ) ≤ cp*(d:ℝ)*(k:ℝ) / Real.log (Real.exp 1 * (k:ℝ)) := by
  have hk1 : (1:ℝ) ≤ k := by exact_mod_cast hk
  have hkp : (0:ℝ) < k := by linarith
  have hlog : Real.log (Real.exp 1 * (k:ℝ)) = 1 + Real.log (k:ℝ) := log_e_mul hkp
  have hlogpos : 0 < Real.log (Real.exp 1 * (k:ℝ)) := by
    rw [hlog]
    have := Real.log_nonneg hk1
    linarith
  have hlogle : Real.log (Real.exp 1 * (k:ℝ)) ≤ (k:ℝ) := by
    rw [hlog]
    have := Real.log_le_sub_one_of_pos hkp
    linarith
  apply (le_div_iff₀ hlogpos).2
  exact mul_le_mul_of_nonneg_left hlogle (by positivity)

/-- Concrete source-prior input for every allowed integer k. The source hardness
premise uses natural budgets N≥1 strictly below its real threshold. Thus no
unstated rounding of strict source query budgets is used. The conclusion is a
bound on every actual target admissible budget, including zero-query policies. -/
theorem regional_from_strict_source_priors {d : ℕ} {α κ δ cp C : ℝ}
    (hd : 1 ≤ (d:ℝ)) (hκ : 0 < κ) (hκ1 : κ ≤ 1)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hcp : 0 < cp) (hC : 0 < C)
    (hα : 0 < α) (hlarge : 2 ≤ κ*(d:ℝ)) (hprobLarge : 2 ≤ cp*(d:ℝ))
    (hscope : α ≤ δ / Real.sqrt (ell (d:ℝ)))
    (hpriors : ∀ (k : ℕ) (hk : 1 ≤ k), k ≤ ⌊κ*(d:ℝ)⌋₊ →
      letI : Nonempty (Fin k) := ⟨⟨0, by omega⟩⟩
      ∃ prior : Measure (Rows (Fin k) d), IsProbabilityMeasure prior ∧
        (15/16 : ℝ) ≤ prior.real (@GoodRows (Fin k) d (coordinateBound d C)) ∧
        ∀ N : ℕ, 1 ≤ N →
          (N:ℝ) < cp*(d:ℝ)*(k:ℝ) / Real.log (Real.exp 1 * (k:ℝ)) →
          ∀ b : SourcePolicy d Unit,
          (∀ rows : Rows (Fin k) d,
            b.queriesUsed (sourceSupport rows) N 0 ((), Fin.elim0) ≤ N) →
          prior.real {rows | () ∈ strictSourceSuccessEvent b (sourceSupport rows) N
            (sourceAccuracy C δ k)} ≤ (1/4 : ℝ)) :
    ∀ m : ℕ, AdmissibleBudget d m 1 1 α →
      (cp * selectionConstant κ δ) * q (d:ℝ) α /
        (ell (d:ℝ) * Real.log (Real.exp 1 * M (d:ℝ) α)) ≤ (m:ℝ) := by
  apply regional_from_coordinate_impossibility hd hκ hκ1 hδ hδ1 hcp hα hlarge hscope
  intro k hk hkK m hm hmAdm
  letI : Nonempty (Fin k) := ⟨⟨0, by omega⟩⟩
  obtain ⟨prior, hpriorProb, hgood, hhard⟩ := hpriors k hk hkK
  letI : IsProbabilityMeasure prior := hpriorProb
  have hdNat : 0 < d := by exact_mod_cast (by linarith : (0:ℝ) < d)
  let N : ℕ := max 1 m
  have hN1 : 1 ≤ N := le_max_left _ _
  have hmN : m ≤ N := le_max_right _ _
  have hT : 1 < cp*(d:ℝ)*(k:ℝ) / Real.log (Real.exp 1 * (k:ℝ)) :=
    lt_of_lt_of_le (by linarith : (1:ℝ) < cp*(d:ℝ)) (source_threshold_ge_dimension hk hcp)
  have hNT : (N:ℝ) < cp*(d:ℝ)*(k:ℝ) / Real.log (Real.exp 1 * (k:ℝ)) := by
    rw [show (N:ℝ) = max (1:ℝ) (m:ℝ) by simp only [N, Nat.cast_max, Nat.cast_one]]
    exact max_lt hT hm
  have hno := not_admissible_of_strict_deterministic_source_prior (κ:=Fin k)
    (d:=d) (m:=N) (Tk:=N) hdNat (le_refl N) (coordinateBound d C)
    (coordinateBound_pos hd hC) (sourceAccuracy C δ k) (sourceAccuracy_pos hk hC hδ)
    prior hgood (hhard N hN1 hNT)
  rw [accuracy_identity hd hk hC] at hno
  exact hno (admissible_budget_mono hmAdm hmN)

/-- One fixed dimension threshold and one fixed lower constant work for every
varying d and α. Source thresholds, priors and hardness stay the explicitly
external source-family inputs; the regional inequality is the proved output. -/
theorem eventual_regional_from_strict_source_priors
    (Dsource : ℕ) (κ δ cp C : ℝ)
    (hκ : 0 < κ) (hκ1 : κ ≤ 1) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hcp : 0 < cp) (hC : 0 < C)
    (hpriors : ∀ (d : ℕ), Dsource ≤ d → ∀ (k : ℕ) (hk : 1 ≤ k), k ≤ ⌊κ*(d:ℝ)⌋₊ →
      letI : Nonempty (Fin k) := ⟨⟨0, by omega⟩⟩
      ∃ prior : Measure (Rows (Fin k) d), IsProbabilityMeasure prior ∧
        (15/16 : ℝ) ≤ prior.real (@GoodRows (Fin k) d (coordinateBound d C)) ∧
        ∀ N : ℕ, 1 ≤ N →
          (N:ℝ) < cp*(d:ℝ)*(k:ℝ) / Real.log (Real.exp 1 * (k:ℝ)) →
          ∀ b : SourcePolicy d Unit,
          (∀ rows : Rows (Fin k) d,
            b.queriesUsed (sourceSupport rows) N 0 ((), Fin.elim0) ≤ N) →
          prior.real {rows | () ∈ strictSourceSuccessEvent b (sourceSupport rows) N
            (sourceAccuracy C δ k)} ≤ (1/4 : ℝ)) :
    ∃ (D : ℕ) (c : ℝ), Dsource ≤ D ∧ 0 < D ∧ 0 < c ∧
      ∀ (d : ℕ), D ≤ d → ∀ (α : ℝ), 0 < α →
        α ≤ δ / Real.sqrt (ell (d:ℝ)) →
        ∀ m : ℕ, AdmissibleBudget d m 1 1 α →
          c * q (d:ℝ) α / (ell (d:ℝ) * Real.log (Real.exp 1 * M (d:ℝ) α)) ≤ (m:ℝ) := by
  have hminpos : 0 < min κ cp := lt_min hκ hcp
  obtain ⟨D, hDs, hD1, hDlarge⟩ := exists_dimension_threshold (min κ cp) hminpos Dsource
  refine ⟨D, cp * selectionConstant κ δ, hDs, by omega,
    mul_pos hcp (selectionConstant_pos hκ hδ), ?_⟩
  intro d hd α hα hscope m hm
  obtain ⟨hd1, hsmall⟩ := hDlarge d hd
  have hd0 : (0:ℝ) ≤ d := by positivity
  have hκlarge : 2 ≤ κ*(d:ℝ) :=
    hsmall.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) hd0)
  have hcplarge : 2 ≤ cp*(d:ℝ) :=
    hsmall.trans (mul_le_mul_of_nonneg_right (min_le_right _ _) hd0)
  exact regional_from_strict_source_priors hd1 hκ hκ1 hδ hδ1 hcp hC hα
    hκlarge hcplarge hscope (hpriors d (hDs.trans hd)) m hm

end Task003.RegionalSourceBridge

end
end
-- END RegionalSourceBridge.lean

-- BEGIN OddDifference.lean
section

namespace PaperOddDifference

open MeasureTheory ProbabilityTheory PaperProductVariance

noncomputable def oddDifference {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : E → ℝ) (z : E) (h : ℝ) (u : E) : ℝ :=
  (F (z + h • u) - F (z - h • u)) / (2 * h)

theorem oddDifference_neg {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : E → ℝ) (z : E) (h : ℝ) (u : E) :
    oddDifference F z h (-u) = -oddDifference F z h u := by
  simp only [oddDifference, smul_neg, sub_neg_eq_add]
  rw [← sub_eq_add_neg]
  ring

theorem oddDifference_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : E → ℝ) (z : E) (h : ℝ) : oddDifference F z h 0 = 0 := by
  simp [oddDifference]

theorem oddDifference_lipschitz {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : E → ℝ) (hF : LipschitzWith 1 F) (z : E) (h : ℝ) (hh : 0 < h) :
    LipschitzWith 1 (oddDifference F z h) := by
  apply LipschitzWith.of_le_add_mul
  intro u v
  have hpos : dist (z + h • u) (z + h • v) = h * dist u v := by
    rw [dist_eq_norm]
    have he : z + h • u - (z + h • v) = h • (u - v) := by module
    rw [he, norm_smul, Real.norm_of_nonneg hh.le, dist_eq_norm]
  have hneg : dist (z - h • v) (z - h • u) = h * dist u v := by
    rw [dist_eq_norm]
    have he : z - h • v - (z - h • u) = h • (u - v) := by module
    rw [he, norm_smul, Real.norm_of_nonneg hh.le, dist_eq_norm]
  have hp := hF.le_add_mul (z + h • u) (z + h • v)
  have hn := hF.le_add_mul (z - h • v) (z - h • u)
  rw [hpos] at hp
  rw [hneg] at hn
  simp only [NNReal.coe_one, one_mul] at hp hn ⊢
  change (F (z + h • u) - F (z - h • u)) / (2 * h) ≤
    (F (z + h • v) - F (z - h • v)) / (2 * h) + dist u v
  apply (div_le_iff₀ (show (0 : ℝ) < 2 * h by positivity)).2
  have he : ((F (z + h • v) - F (z - h • v)) / (2 * h) + dist u v) * (2 * h) =
      (F (z + h • v) - F (z - h • v)) + 2 * h * dist u v := by
    field_simp
  rw [he]
  linarith

theorem oddDifference_second_moment_le (n : ℕ) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : MemLp (id : ℝ → ℝ) 2 μ) (F : Space n → ℝ) (hF : LipschitzWith 1 F)
    (z : Space n) (h : ℝ) (hh : 0 < h)
    (hmean : (∫ u : Fin n → ℝ, oddDifference F z h (WithLp.toLp 1 u)
      ∂Measure.pi (fun _ : Fin n => μ)) = 0) :
    (∫ u : Fin n → ℝ, (oddDifference F z h (WithLp.toLp 1 u)) ^ 2
      ∂Measure.pi (fun _ : Fin n => μ)) ≤ n * variance (id : ℝ → ℝ) μ := by
  have hD := oddDifference_lipschitz F hF z h hh
  have hm := product_lipschitz_memLp n μ hμ (oddDifference F z h) hD
  rw [← variance_of_integral_eq_zero hm.aemeasurable hmean]
  exact product_lipschitz_variance_le n μ hμ _ hD

noncomputable def signEstimator {n : ℕ} (D : Space n → ℝ) (u : Space n) : Fin n → ℝ :=
  fun i => D u * Real.sign (u i)

theorem signEstimator_norm_le {n : ℕ} (D : Space n → ℝ) (u : Space n) :
    ‖signEstimator D u‖ ≤ |D u| := by
  apply (pi_norm_le_iff_of_nonneg (abs_nonneg _)).2
  intro i
  change |D u * Real.sign (u i)| ≤ |D u|
  rw [abs_mul]
  have hs : |Real.sign (u i)| ≤ 1 := by
    rcases lt_trichotomy (u i) 0 with hi | hi | hi
    · simp [Real.sign_of_neg hi]
    · simp [hi]
    · simp [Real.sign_of_pos hi]
  nlinarith [abs_nonneg (D u)]

theorem signEstimator_norm_sq_le {n : ℕ} (D : Space n → ℝ) (u : Space n) :
    ‖signEstimator D u‖ ^ 2 ≤ (D u) ^ 2 := by
  have h := signEstimator_norm_le D u
  nlinarith [norm_nonneg (signEstimator D u), abs_nonneg (D u), sq_abs (D u)]

theorem real_sign_measurable : Measurable (Real.sign : ℝ → ℝ) := by
  unfold Real.sign
  exact Measurable.ite (measurableSet_lt measurable_id measurable_const) measurable_const
    (Measurable.ite (measurableSet_lt measurable_const measurable_id) measurable_const measurable_const)

theorem signEstimator_measurable {n : ℕ} (D : Space n → ℝ) (hD : Measurable D) :
    Measurable (signEstimator D) := by
  apply measurable_pi_iff.mpr
  intro i
  exact hD.mul (real_sign_measurable.comp (PiLp.continuous_apply 1 _ i).measurable)

theorem signEstimator_memLp (n : ℕ) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : MemLp (id : ℝ → ℝ) 2 μ) (D : Space n → ℝ) (hD : LipschitzWith 1 D) :
    MemLp (fun u : Fin n → ℝ => signEstimator D (WithLp.toLp 1 u)) 2
      (Measure.pi (fun _ : Fin n => μ)) := by
  have hm := product_lipschitz_memLp n μ hμ D hD
  have hGm : Measurable (fun u : Fin n → ℝ => signEstimator D (WithLp.toLp 1 u)) :=
    (signEstimator_measurable D hD.continuous.measurable).comp
      (PiLp.continuous_toLp 1 _).measurable
  apply hm.of_le hGm.aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun u => signEstimator_norm_le D _)

theorem signEstimator_second_moment_le (n : ℕ) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : MemLp (id : ℝ → ℝ) 2 μ) (D : Space n → ℝ) (hD : LipschitzWith 1 D)
    (hmean : (∫ u : Fin n → ℝ, D (WithLp.toLp 1 u)
      ∂Measure.pi (fun _ : Fin n => μ)) = 0) :
    (∫ u : Fin n → ℝ, ‖signEstimator D (WithLp.toLp 1 u)‖ ^ 2
      ∂Measure.pi (fun _ : Fin n => μ)) ≤ n * variance (id : ℝ → ℝ) μ := by
  have hDm := product_lipschitz_memLp n μ hμ D hD
  have hGm := signEstimator_memLp n μ hμ D hD
  calc
    _ ≤ ∫ u : Fin n → ℝ, D (WithLp.toLp 1 u) ^ 2
        ∂Measure.pi (fun _ : Fin n => μ) :=
      integral_mono hGm.norm.integrable_sq hDm.integrable_sq
        (fun u => signEstimator_norm_sq_le D _)
    _ = variance (fun u : Fin n → ℝ => D (WithLp.toLp 1 u))
        (Measure.pi (fun _ : Fin n => μ)) :=
      (variance_of_integral_eq_zero hDm.aemeasurable hmean).symm
    _ ≤ _ := product_lipschitz_variance_le n μ hμ D hD

end PaperOddDifference


end
-- END OddDifference.lean

-- BEGIN SmoothingBias.lean
section

namespace PaperSmoothingBias

open MeasureTheory ProbabilityTheory PaperProductVariance

noncomputable def smoothing (n : ℕ) (μ : Measure ℝ) (F : Space n → ℝ)
    (z : Space n) (h : ℝ) : ℝ :=
  ∫ u : Fin n → ℝ, F (z + h • WithLp.toLp 1 u) ∂Measure.pi (fun _ : Fin n => μ)

theorem perturbed_value_memLp (n : ℕ) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : MemLp (id : ℝ → ℝ) 2 μ) (F : Space n → ℝ) (hF : LipschitzWith 1 F)
    (z : Space n) (h : ℝ) :
    MemLp (fun u : Fin n → ℝ => F (z + h • WithLp.toLp 1 u)) 2
      (Measure.pi (fun _ : Fin n => μ)) := by
  have hU := product_vector_memLp n μ hμ
  have hX := (memLp_const z).add (hU.const_smul h)
  exact lipschitz_memLp_two _ _ hX F hF

theorem smoothing_abs_bias_le (n : ℕ) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : MemLp (id : ℝ → ℝ) 2 μ) (F : Space n → ℝ) (hF : LipschitzWith 1 F)
    (z : Space n) (h : ℝ) (hh : 0 ≤ h) :
    |smoothing n μ F z h - F z| ≤
      h * ∫ u : Fin n → ℝ, ‖(WithLp.toLp 1 u : Space n)‖
        ∂Measure.pi (fun _ : Fin n => μ) := by
  let ν : Measure (Fin n → ℝ) := Measure.pi (fun _ : Fin n => μ)
  have hvalue : Integrable (fun u : Fin n → ℝ => F (z + h • WithLp.toLp 1 u)) ν :=
    (perturbed_value_memLp n μ hμ F hF z h).integrable (by norm_num)
  have hUnorm : Integrable (fun u : Fin n → ℝ => ‖(WithLp.toLp 1 u : Space n)‖) ν :=
    ((product_vector_memLp n μ hμ).integrable (by norm_num)).norm
  have hpoint : ∀ u : Fin n → ℝ,
      |F (z + h • WithLp.toLp 1 u) - F z| ≤ h * ‖(WithLp.toLp 1 u : Space n)‖ := by
    intro u
    have hhF := hF.dist_le_mul (z + h • WithLp.toLp 1 u) z
    simpa [Real.dist_eq, dist_eq_norm, norm_smul, Real.norm_of_nonneg hh] using hhF
  have heq : smoothing n μ F z h - F z =
      ∫ u : Fin n → ℝ, (F (z + h • WithLp.toLp 1 u) - F z) ∂ν := by
    rw [integral_sub hvalue (integrable_const (F z))]
    simp [smoothing, ν]
  rw [heq]
  calc
    |∫ u : Fin n → ℝ, F (z + h • WithLp.toLp 1 u) - F z ∂ν| ≤
        ∫ u : Fin n → ℝ, |F (z + h • WithLp.toLp 1 u) - F z| ∂ν := by
      simpa only [Real.norm_eq_abs] using
        (norm_integral_le_integral_norm (fun u : Fin n → ℝ => F (z + h • WithLp.toLp 1 u) - F z))
    _ ≤ ∫ u : Fin n → ℝ, h * ‖(WithLp.toLp 1 u : Space n)‖ ∂ν :=
      integral_mono (hvalue.sub (integrable_const (F z))).norm
        (hUnorm.const_mul h) hpoint
    _ = _ := integral_const_mul _ _

theorem smoothing_lipschitz (n : ℕ) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : MemLp (id : ℝ → ℝ) 2 μ) (F : Space n → ℝ) (hF : LipschitzWith 1 F)
    (h : ℝ) : LipschitzWith 1 (fun z => smoothing n μ F z h) := by
  apply integral_lipschitz (Measure.pi (fun _ : Fin n => μ))
    (fun z u => F (z + h • WithLp.toLp 1 u))
    (fun z => (perturbed_value_memLp n μ hμ F hF z h).integrable (by norm_num))
  intro u
  apply LipschitzWith.of_dist_le_mul
  intro z w
  simpa only [dist_add_right] using hF.dist_le_mul
    (z + h • WithLp.toLp 1 u) (w + h • WithLp.toLp 1 u)

theorem smoothing_convex (n : ℕ) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : MemLp (id : ℝ → ℝ) 2 μ) (F : Space n → ℝ) (hF : LipschitzWith 1 F)
    (hconvex : ConvexOn ℝ Set.univ F) (h : ℝ) :
    ConvexOn ℝ Set.univ (fun z => smoothing n μ F z h) := by
  refine ⟨convex_univ, ?_⟩
  intro z _ w _ a b ha hb hab
  let ν : Measure (Fin n → ℝ) := Measure.pi (fun _ : Fin n => μ)
  have hz := (perturbed_value_memLp n μ hμ F hF z h).integrable (by norm_num)
  have hw := (perturbed_value_memLp n μ hμ F hF w h).integrable (by norm_num)
  have hp := (perturbed_value_memLp n μ hμ F hF (a • z + b • w) h).integrable (by norm_num)
  have hpoint : ∀ u : Fin n → ℝ,
      F (a • z + b • w + h • WithLp.toLp 1 u) ≤
        a * F (z + h • WithLp.toLp 1 u) + b * F (w + h • WithLp.toLp 1 u) := by
    intro u
    have he : a • z + b • w + h • WithLp.toLp 1 u =
        a • (z + h • WithLp.toLp 1 u) + b • (w + h • WithLp.toLp 1 u) := by
      calc
        _ = a • z + b • w + (a + b) • (h • WithLp.toLp 1 u) := by rw [hab, one_smul]
        _ = _ := by module
    rw [he]
    exact hconvex.2 (Set.mem_univ _) (Set.mem_univ _) ha hb hab
  have hint := integral_mono hp ((hz.const_mul a).add (hw.const_mul b)) hpoint
  simp only [Pi.add_apply] at hint
  rw [integral_add (hz.const_mul a) (hw.const_mul b), integral_const_mul,
    integral_const_mul] at hint
  exact hint

end PaperSmoothingBias


end
-- END SmoothingBias.lean

-- BEGIN LaplaceEstimator.lean
section

namespace PaperLaplaceEstimator

open MeasureTheory ProbabilityTheory PaperLaplace PaperProductVariance PaperOddDifference PaperSmoothingBias

theorem laplace_oddDifference_mean_zero (n : ℕ) (F : Space n → ℝ)
    (hF : LipschitzWith 1 F) (z : Space n) (h : ℝ) (hh : 0 < h) :
    (∫ u : Fin n → ℝ, oddDifference F z h (WithLp.toLp 1 u) ∂productLaw n) = 0 := by
  apply product_odd_integral_zero
  · exact ((oddDifference_lipschitz F hF z h hh).continuous.comp
      (PiLp.continuous_toLp 1 _)).measurable
  · intro u
    exact oddDifference_neg F z h (WithLp.toLp 1 u)

theorem laplace_oddDifference_second_moment (n : ℕ) (F : Space n → ℝ)
    (hF : LipschitzWith 1 F) (z : Space n) (h : ℝ) (hh : 0 < h) :
    (∫ u : Fin n → ℝ, oddDifference F z h (WithLp.toLp 1 u) ^ 2 ∂productLaw n) ≤ 2 * n := by
  have hbound := oddDifference_second_moment_le n laplaceLaw laplace_id_memLp_two F hF z h hh
    (laplace_oddDifference_mean_zero n F hF z h hh)
  have hv : variance (id : ℝ → ℝ) laplaceLaw = 2 := laplace_variance_two
  simpa only [hv, mul_comm, productLaw] using hbound

theorem laplace_estimator_memLp (n : ℕ) (F : Space n → ℝ)
    (hF : LipschitzWith 1 F) (z : Space n) (h : ℝ) (hh : 0 < h) :
    MemLp (fun u : Fin n → ℝ => signEstimator (oddDifference F z h) (WithLp.toLp 1 u)) 2
      (productLaw n) :=
  signEstimator_memLp n laplaceLaw laplace_id_memLp_two _ (oddDifference_lipschitz F hF z h hh)

theorem laplace_estimator_second_moment (n : ℕ) (F : Space n → ℝ)
    (hF : LipschitzWith 1 F) (z : Space n) (h : ℝ) (hh : 0 < h) :
    (∫ u : Fin n → ℝ, ‖signEstimator (oddDifference F z h) (WithLp.toLp 1 u)‖ ^ 2
      ∂productLaw n) ≤ 2 * n := by
  have hbound := signEstimator_second_moment_le n laplaceLaw laplace_id_memLp_two
    (oddDifference F z h) (oddDifference_lipschitz F hF z h hh)
    (laplace_oddDifference_mean_zero n F hF z h hh)
  have hv : variance (id : ℝ → ℝ) laplaceLaw = 2 := laplace_variance_two
  simpa only [hv, mul_comm, productLaw] using hbound

theorem laplace_smoothing_abs_bias (n : ℕ) (F : Space n → ℝ)
    (hF : LipschitzWith 1 F) (z : Space n) (h : ℝ) (hh : 0 ≤ h) :
    |smoothing n laplaceLaw F z h - F z| ≤ h * n := by
  have hbound := smoothing_abs_bias_le n laplaceLaw laplace_id_memLp_two F hF z h hh
  rw [← product_norm_integral n]
  exact hbound

end PaperLaplaceEstimator


end
-- END LaplaceEstimator.lean

-- BEGIN ProjectorInnovations.lean
section

namespace PaperProjectorInnovations

open scoped InnerProductSpace
open InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def normalizedResidual (Q : E →L[ℝ] E) (v : E) : E :=
  ‖Q v‖⁻¹ • Q v

noncomputable def projectorUpdate (Q : E →L[ℝ] E) (w : E) : E →L[ℝ] E :=
  Q - (innerSL ℝ w).smulRight w

theorem normalizedResidual_norm {Q : E →L[ℝ] E} {v : E} (hr : Q v ≠ 0) :
    ‖normalizedResidual Q v‖ = 1 := by
  rw [normalizedResidual, norm_smul,
    Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
    inv_mul_cancel₀ (norm_ne_zero_iff.mpr hr)]

theorem normalizedResidual_fixed {Q : E →L[ℝ] E} (hQ : Q * Q = Q) (v : E) :
    Q (normalizedResidual Q v) = normalizedResidual Q v := by
  have hQQ : Q (Q v) = Q v := congrArg (fun T : E →L[ℝ] E => T v) hQ
  simp only [normalizedResidual, map_smul, hQQ]

theorem normalizedResidual_zero {Q : E →L[ℝ] E} {v : E} (hr : Q v = 0) :
    normalizedResidual Q v = 0 := by simp [normalizedResidual, hr]

theorem inner_projector_fixed {Q : E →L[ℝ] E} (hQ : Q.IsSymmetric) {w : E}
    (hw : Q w = w) (b : E) : ⟪w, Q b⟫_ℝ = ⟪w, b⟫_ℝ := by
  calc
    _ = ⟪Q w, b⟫_ℝ := (hQ w b).symm
    _ = _ := by rw [hw]

theorem projectorUpdate_kills {Q : E →L[ℝ] E} {w : E} (hw : ‖w‖ = 1)
    (hQw : Q w = w) : projectorUpdate Q w w = 0 := by
  change Q w - ⟪w, w⟫_ℝ • w = 0
  rw [hQw, real_inner_self_eq_norm_sq, hw]
  simp

theorem projectorUpdate_zero (Q : E →L[ℝ] E) : projectorUpdate Q (0 : E) = Q := by
  ext x
  simp [projectorUpdate]

theorem projectorUpdate_isSymmetricProjection {Q : E →L[ℝ] E}
    (hQ : Q.IsSymmetricProjection) {w : E} (hw : ‖w‖ = 1) (hQw : Q w = w) :
    (projectorUpdate Q w).IsSymmetricProjection := by
  have hp := isSymmetricProjection_rankOne_self (𝕜 := ℝ) hw
  have hrange : LinearMap.range (rankOne ℝ w w : E →L[ℝ] E).toLinearMap ≤
      LinearMap.range Q.toLinearMap := by
    rintro y ⟨x, rfl⟩
    refine ⟨⟪w, x⟫_ℝ • w, ?_⟩
    simp only [ContinuousLinearMap.coe_coe, map_smul, hQw, rankOne_apply]
  exact hp.sub_of_range_le_range hQ hrange

theorem symmetricProjection_of_selfAdjoint_idempotent [CompleteSpace E]
    {Q : E →L[ℝ] E} (hQ : IsSelfAdjoint Q) (hQQ : Q * Q = Q) :
    Q.IsSymmetricProjection := by
  refine ⟨?_, ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hQ⟩
  exact congrArg ContinuousLinearMap.toLinearMap hQQ

theorem projectorUpdate_selfAdjoint_idempotent [CompleteSpace E]
    {Q : E →L[ℝ] E} (hQ : IsSelfAdjoint Q) (hQQ : Q * Q = Q)
    {w : E} (hw : ‖w‖ = 1) (hQw : Q w = w) :
    IsSelfAdjoint (projectorUpdate Q w) ∧ projectorUpdate Q w * projectorUpdate Q w =
      projectorUpdate Q w := by
  have hu := projectorUpdate_isSymmetricProjection
    (symmetricProjection_of_selfAdjoint_idempotent hQ hQQ) hw hQw
  refine ⟨ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr hu.isSymmetric, ?_⟩
  ext x
  exact congrArg (fun T : E →ₗ[ℝ] E => T x) hu.isIdempotentElem

theorem innovationUpdate_kills_query {Q : E →L[ℝ] E} (hQ : Q.IsSymmetric)
    (hQQ : Q * Q = Q) (v : E) : projectorUpdate Q (normalizedResidual Q v) v = 0 := by
  by_cases hr : Q v = 0
  · rw [normalizedResidual_zero hr, projectorUpdate_zero]
    exact hr
  · have hn : ‖Q v‖ ≠ 0 := norm_ne_zero_iff.mpr hr
    have hfix := normalizedResidual_fixed hQQ v
    have hcoeff : ⟪normalizedResidual Q v, v⟫_ℝ = ‖Q v‖ := by
      rw [← inner_projector_fixed hQ hfix v, normalizedResidual, real_inner_smul_left,
        real_inner_self_eq_norm_sq]
      field_simp
    have hrw : ‖Q v‖ • normalizedResidual Q v = Q v := by
      rw [normalizedResidual, smul_smul, mul_inv_cancel₀ hn, one_smul]
    change Q v - ⟪normalizedResidual Q v, v⟫_ℝ • normalizedResidual Q v = 0
    rw [hcoeff, hrw, sub_self]

theorem active_innovation_properties [CompleteSpace E] {Q : E →L[ℝ] E}
    (hQ : IsSelfAdjoint Q) (hQQ : Q * Q = Q) (v : E) (hr : Q v ≠ 0) :
    ‖normalizedResidual Q v‖ = 1 ∧
      Q (normalizedResidual Q v) = normalizedResidual Q v ∧
      (∀ b, ⟪normalizedResidual Q v, Q b⟫_ℝ = ⟪normalizedResidual Q v, b⟫_ℝ) ∧
      IsSelfAdjoint (projectorUpdate Q (normalizedResidual Q v)) ∧
      projectorUpdate Q (normalizedResidual Q v) * projectorUpdate Q (normalizedResidual Q v) =
        projectorUpdate Q (normalizedResidual Q v) ∧
      projectorUpdate Q (normalizedResidual Q v) (normalizedResidual Q v) = 0 ∧
      projectorUpdate Q (normalizedResidual Q v) v = 0 := by
  have hw := normalizedResidual_norm hr
  have hfix := normalizedResidual_fixed hQQ v
  have hsym := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hQ
  have hup := projectorUpdate_selfAdjoint_idempotent hQ hQQ hw hfix
  exact ⟨hw, hfix, inner_projector_fixed hsym hfix, hup.1, hup.2,
    projectorUpdate_kills hw hfix, innovationUpdate_kills_query hsym hQQ v⟩

section Measurable

variable [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

theorem normalizedResidual_measurable :
    Measurable (fun p : (E →L[ℝ] E) × E => normalizedResidual p.1 p.2) := by
  have hm : Measurable (fun p : (E →L[ℝ] E) × E => p.1 p.2) :=
    (continuous_fst.clm_apply continuous_snd).measurable
  exact hm.norm.inv.smul hm

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
theorem projectorUpdate_continuous :
    Continuous (fun p : (E →L[ℝ] E) × E => projectorUpdate p.1 p.2) := by
  have hrank : Continuous (fun w : E => rankOne ℝ w w) :=
    (rankOne ℝ).continuous.clm_apply continuous_id
  exact continuous_fst.sub (hrank.comp continuous_snd)

theorem projectorUpdate_measurable :
    Measurable (fun p : (E →L[ℝ] E) × E => projectorUpdate p.1 p.2) :=
  projectorUpdate_continuous.measurable

theorem innovationUpdate_measurable :
    Measurable (fun p : (E →L[ℝ] E) × E =>
      projectorUpdate p.1 (normalizedResidual p.1 p.2)) := by
  exact projectorUpdate_measurable.comp (measurable_fst.prodMk normalizedResidual_measurable)

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
theorem innovationUpdate_zero {Q : E →L[ℝ] E} {v : E} (hr : Q v = 0) :
    projectorUpdate Q (normalizedResidual Q v) = Q := by
  rw [normalizedResidual_zero hr, projectorUpdate_zero]

end Measurable

end PaperProjectorInnovations


end
-- END ProjectorInnovations.lean

-- BEGIN GaussianOracleBridge.lean
section

/- Fixed-row Gaussian disintegration toward the adaptive raw-oracle bridge.
   No adaptive conditional Gaussian law is assumed or claimed here. -/
namespace PaperGaussianOracleBridge

open MeasureTheory ProbabilityTheory Set
open scoped RealInnerProductSpace NNReal ENNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

noncomputable def residualMap (w : E) : E →L[ℝ] E :=
  ContinuousLinearMap.id ℝ E - (innerSL ℝ w).smulRight w

lemma residualMap_apply (w x : E) :
    residualMap w x = x - ⟪w, x⟫ • w := rfl

/-- A fixed unit query extracts an actual N(0,1) observation. -/
theorem fixed_unit_row_standardGaussian_law (w : E) (hw : ‖w‖ = 1) :
    (stdGaussian E).map (fun x => ⟪w, x⟫) = gaussianReal 0 1 := by
  have hg : HasGaussianLaw (fun x : E => ⟪w, x⟫) (stdGaussian E) := by
    simpa using (IsGaussian.hasGaussianLaw_id (μ := stdGaussian E)).map (innerSL ℝ w)
  rw [hg.map_eq_gaussianReal]
  simp only [show (fun x : E => ⟪w, x⟫) = innerSL ℝ w from rfl,
    integral_strongDual_stdGaussian, variance_dual_stdGaussian, innerSL_apply_norm,
    hw, one_pow, Real.toNNReal_one]

/-- A fixed unit query and the orthogonal residual are independent under
the actual standard Gaussian vector law. -/
theorem fixed_unit_row_residual_independent (w : E) (hw : ‖w‖ = 1) :
    IndepFun (fun x : E => ⟪w, x⟫) (residualMap w) (stdGaussian E) := by
  have hg : HasGaussianLaw (fun x : E => (⟪w, x⟫, residualMap w x))
      (stdGaussian E) := by
    convert! (IsGaussian.hasGaussianLaw_id (μ := stdGaussian E)).map
      ((innerSL ℝ w).prod (residualMap w)) using 1
  apply hg.indepFun_of_covariance_inner
  intro a y
  have hleft : (fun x : E => ⟪a, ⟪w, x⟫⟫) = (fun x => ⟪a • w, x⟫) := by
    ext x
    simp only [RCLike.inner_apply, conj_trivial, real_inner_smul_left]
    ring
  have hright : (fun x : E => ⟪y, residualMap w x⟫) =
      (fun x => ⟪y - ⟪y, w⟫ • w, x⟫) := by
    ext x
    simp [residualMap_apply, inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right]
    ring
  rw [hleft, hright, ← covarianceBilin_apply_eq_cov IsGaussian.memLp_two_id,
    covarianceBilin_stdGaussian]
  change ⟪a • w, y - ⟪y, w⟫ • w⟫ = 0
  simp [residualMap_apply, inner_smul_left, inner_sub_right, inner_smul_right, real_inner_comm w y,
    inner_self_eq_norm_sq, hw]
  ring

/-- Exact joint law of a fixed Gaussian observation and its unobserved
orthogonal residual. This is a genuine product measure identity. -/
theorem fixed_unit_row_joint_decomposition (w : E) (hw : ‖w‖ = 1) :
    (stdGaussian E).map (fun x => (⟪w, x⟫, residualMap w x)) =
      (gaussianReal 0 1).prod ((stdGaussian E).map (residualMap w)) := by
  have h := (fixed_unit_row_residual_independent w hw).map_prod_eq_prod_map_map
    (by fun_prop) (by fun_prop)
  rwa [fixed_unit_row_standardGaussian_law w hw] at h

/-- The orthogonal residual's actual regular conditional distribution given
a fixed unit observation is its unconditional Gaussian residual law. -/
theorem fixed_unit_row_residual_conditional_kernel (w : E) (hw : ‖w‖ = 1) :
    ∀ᵐ y ∂gaussianReal 0 1,
      ((stdGaussian E).map (fun x => (⟪w, x⟫, residualMap w x))).condKernel y =
        (stdGaussian E).map (residualMap w) := by
  let residualLaw : Measure E := (stdGaussian E).map (residualMap w)
  letI : IsProbabilityMeasure residualLaw :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  let ρ : Measure (ℝ × E) :=
    (stdGaussian E).map (fun x => (⟪w, x⟫, residualMap w x))
  have hρ : ρ = (gaussianReal 0 1).prod residualLaw :=
    fixed_unit_row_joint_decomposition w hw
  have hfst : ρ.fst = gaussianReal 0 1 := by rw [hρ, Measure.fst_prod]
  have hdis : ρ = ρ.fst ⊗ₘ Kernel.const ℝ residualLaw := by
    rw [hfst, Measure.compProd_const, hρ]
  have h := eq_condKernel_of_measure_eq_compProd (ρ := ρ) (Kernel.const ℝ residualLaw) hdis
  rw [hfst] at h
  exact h.mono (fun _ hy => hy.symm)

/-- Reconstruct the Gaussian vector from its observed scalar and an
independent draw from the orthogonal residual law. -/
noncomputable def reconstructionKernel (w : E) (R : Measure E) : Kernel ℝ E :=
  (Kernel.id ×ₖ Kernel.const ℝ R).map (fun p : ℝ × E => p.2 + p.1 • w)

instance reconstructionKernel_isMarkov (w : E) (R : Measure E) [IsProbabilityMeasure R] :
    IsMarkovKernel (reconstructionKernel w R) := by
  apply Kernel.IsMarkovKernel.map
  fun_prop

/-- A reconstruction kernel's composition-product is the explicitly
reconstructed joint product law. -/
theorem reconstruction_compProd (w : E) (μ : Measure ℝ) (R : Measure E)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure R] :
    μ ⊗ₘ reconstructionKernel w R =
      (μ.prod R).map (fun p : ℝ × E => (p.1, p.2 + p.1 • w)) := by
  ext A hA
  have hrecon : Measurable (fun p : ℝ × E => p.2 + p.1 • w) := by fun_prop
  have hjoint : Measurable (fun p : ℝ × E => (p.1, p.2 + p.1 • w)) := by fun_prop
  rw [Measure.compProd_apply hA, Measure.map_apply hjoint hA,
    Measure.prod_apply (hjoint hA)]
  apply lintegral_congr
  intro y
  rw [reconstructionKernel, Kernel.map_apply' _ hrecon y (measurable_prodMk_left hA),
    Kernel.id_prod_apply' _ y (hrecon (measurable_prodMk_left hA)), Kernel.const_apply]
  rfl

/-- The actual full Gaussian vector has the displayed conditional kernel
after one fixed unit raw oracle query. No conditional-law premise is used. -/
theorem fixed_unit_row_full_vector_disintegration (w : E) (hw : ‖w‖ = 1) :
    (stdGaussian E).map (fun x => (⟪w, x⟫, x)) =
      gaussianReal 0 1 ⊗ₘ reconstructionKernel w
        ((stdGaussian E).map (residualMap w)) := by
  let R : Measure E := (stdGaussian E).map (residualMap w)
  letI : IsProbabilityMeasure R := Measure.isProbabilityMeasure_map (by fun_prop)
  calc
    (stdGaussian E).map (fun x => (⟪w, x⟫, x)) =
        ((stdGaussian E).map (fun x => (⟪w, x⟫, residualMap w x))).map
          (fun p : ℝ × E => (p.1, p.2 + p.1 • w)) := by
      rw [Measure.map_map (by fun_prop) (by fun_prop)]
      congr 1
      funext x
      apply Prod.ext
      · rfl
      · change x = x - ⟪w, x⟫ • w + ⟪w, x⟫ • w
        abel
    _ = ((gaussianReal 0 1).prod R).map
          (fun p : ℝ × E => (p.1, p.2 + p.1 • w)) := by
      rw [fixed_unit_row_joint_decomposition w hw]
    _ = gaussianReal 0 1 ⊗ₘ reconstructionKernel w R :=
      (reconstruction_compProd w (gaussianReal 0 1) R).symm

/-- Actual isotropic Gaussian source prior, constructed as an affine image
of independent standard coordinates. -/
noncomputable def sourcePrior (σ : ℝ) (θ : E) : Measure E :=
  (stdGaussian E).map (fun b => σ • b + θ)

instance sourcePrior_isProbability (σ : ℝ) (θ : E) :
    IsProbabilityMeasure (sourcePrior σ θ) :=
  Measure.isProbabilityMeasure_map (by fun_prop)

/-- Fixed raw query law under the shifted isotropic source Gaussian. -/
theorem fixed_unit_row_source_observation_law (w : E) (hw : ‖w‖ = 1)
    (σ : ℝ) (θ : E) :
    (sourcePrior σ θ).map (fun g => ⟪w, g⟫) =
      gaussianReal ⟪w, θ⟫ ⟨σ ^ 2, sq_nonneg σ⟩ := by
  have hlaw : HasLaw (fun b : E => ⟪w, b⟫) (gaussianReal 0 1) (stdGaussian E) :=
    ⟨by fun_prop, fixed_unit_row_standardGaussian_law w hw⟩
  have h := (gaussianReal_add_const (gaussianReal_const_mul hlaw σ) ⟪w, θ⟫).map_eq
  rw [sourcePrior, Measure.map_map (by fun_prop) (by fun_prop)]
  convert! h using 1 <;> simp [residualMap_apply, inner_add_right, inner_smul_right, mul_comm, Function.comp_def, NNReal.mk]

/-- Exact independence/product identity under the actual shifted source
prior, with no assumed posterior or conditional Gaussian distribution. -/
theorem fixed_unit_row_source_joint_decomposition (w : E) (hw : ‖w‖ = 1)
    (σ : ℝ) (θ : E) :
    (sourcePrior σ θ).map (fun g => (⟪w, g⟫, residualMap w g)) =
      (gaussianReal ⟪w, θ⟫ ⟨σ ^ 2, sq_nonneg σ⟩).prod
        ((sourcePrior σ θ).map (residualMap w)) := by
  have hi : IndepFun (fun b : E => ⟪w, σ • b + θ⟫)
      (fun b => residualMap w (σ • b + θ)) (stdGaussian E) := by
    convert! (fixed_unit_row_residual_independent w hw).comp
      (φ := fun z : ℝ => σ * z + ⟪w, θ⟫)
      (ψ := fun r : E => σ • r + residualMap w θ) (by fun_prop) (by fun_prop) using 1
    · funext b
      simp [residualMap_apply, inner_add_right, inner_smul_right, mul_comm, Function.comp_def]
    · funext b
      simp [residualMap_apply, map_add, map_smul, Function.comp_def]
  have hjoint := hi.map_prod_eq_prod_map_map (by fun_prop) (by fun_prop)
  have hobs := fixed_unit_row_source_observation_law w hw σ θ
  rw [sourcePrior, Measure.map_map (by fun_prop) (by fun_prop)] at hobs
  rw [sourcePrior, Measure.map_map (by fun_prop) (by fun_prop),
    Measure.map_map (by fun_prop) (by fun_prop)]
  rw [← hobs]
  exact hjoint

/-- A full-vector regular conditional kernel for one fixed raw query of
the source prior. The covariance degeneracy is encoded by residualMap. -/
theorem fixed_unit_row_source_disintegration (w : E) (hw : ‖w‖ = 1)
    (σ : ℝ) (θ : E) :
    (sourcePrior σ θ).map (fun g => (⟪w, g⟫, g)) =
      gaussianReal ⟪w, θ⟫ ⟨σ ^ 2, sq_nonneg σ⟩ ⊗ₘ
        reconstructionKernel w ((sourcePrior σ θ).map (residualMap w)) := by
  let R : Measure E := (sourcePrior σ θ).map (residualMap w)
  letI : IsProbabilityMeasure R := Measure.isProbabilityMeasure_map (by fun_prop)
  calc
    (sourcePrior σ θ).map (fun g => (⟪w, g⟫, g)) =
        ((sourcePrior σ θ).map (fun g => (⟪w, g⟫, residualMap w g))).map
          (fun p : ℝ × E => (p.1, p.2 + p.1 • w)) := by
      rw [Measure.map_map (by fun_prop) (by fun_prop)]
      congr 1
      funext g
      apply Prod.ext
      · rfl
      · change g = g - ⟪w, g⟫ • w + ⟪w, g⟫ • w
        abel
    _ = ((gaussianReal ⟪w, θ⟫ ⟨σ ^ 2, sq_nonneg σ⟩).prod R).map
          (fun p : ℝ × E => (p.1, p.2 + p.1 • w)) := by
      rw [fixed_unit_row_source_joint_decomposition w hw σ θ]
    _ = gaussianReal ⟪w, θ⟫ ⟨σ ^ 2, sq_nonneg σ⟩ ⊗ₘ reconstructionKernel w R :=
      (reconstruction_compProd w _ R).symm

/-- The source prior starts from the manuscript's independent coordinates. -/
theorem sourcePrior_eq_independent_coordinate_image {d : ℕ}
    (σ : ℝ) (θ : EuclideanSpace ℝ (Fin d)) :
    sourcePrior σ θ =
      (Measure.pi (fun _ : Fin d => gaussianReal 0 1)).map
        (fun z => σ • WithLp.toLp 2 z + θ) := by
  rw [sourcePrior, ← map_pi_eq_stdGaussian, Measure.map_map (by fun_prop) (by fun_prop)]
  rfl

/-- A possibly degenerate projected Gaussian prior. -/
noncomputable def projectedPrior (Q : E →L[ℝ] E) (σ : ℝ) (m : E) : Measure E :=
  (stdGaussian E).map (fun b => σ • Q b + m)

instance projectedPrior_isProbability (Q : E →L[ℝ] E) (σ : ℝ) (m : E) :
    IsProbabilityMeasure (projectedPrior Q σ m) :=
  Measure.isProbabilityMeasure_map (by fun_prop)

noncomputable def projectorUpdate (Q : E →L[ℝ] E) (w : E) : E →L[ℝ] E :=
  Q - (innerSL ℝ w).smulRight w

lemma projectorUpdate_apply (Q : E →L[ℝ] E) (w b : E) :
    projectorUpdate Q w b = Q b - ⟪w, b⟫ • w := rfl

/-- A unit direction retained by a symmetric projector has an ordinary
one-dimensional Gaussian observation law under its degenerate prior. -/
theorem projected_unit_row_observation_law
    (Q : E →L[ℝ] E) (w : E) (hw : ‖w‖ = 1)
    (hobs : ∀ b, ⟪w, Q b⟫ = ⟪w, b⟫) (σ : ℝ) (m : E) :
    (projectedPrior Q σ m).map (fun x => ⟪w, x⟫) =
      gaussianReal ⟪w, m⟫ ⟨σ ^ 2, sq_nonneg σ⟩ := by
  rw [← fixed_unit_row_source_observation_law w hw σ m, projectedPrior, sourcePrior,
    Measure.map_map (by fun_prop) (by fun_prop),
    Measure.map_map (by fun_prop) (by fun_prop)]
  congr 1
  funext b
  simp [residualMap_apply, projectorUpdate_apply, Function.comp_def, inner_add_right, inner_smul_right, hobs]

/-- The new orthogonal residual law is the actual projected Gaussian with
the rank-one direction removed; its mean is the old mean's residual. -/
theorem projected_unit_row_residual_law
    (Q : E →L[ℝ] E) (w : E)
    (hobs : ∀ b, ⟪w, Q b⟫ = ⟪w, b⟫) (σ : ℝ) (m : E) :
    (projectedPrior Q σ m).map (residualMap w) =
      projectedPrior (projectorUpdate Q w) σ (residualMap w m) := by
  rw [projectedPrior, Measure.map_map (by fun_prop) (by fun_prop), projectedPrior]
  congr 1
  funext b
  simp [residualMap_apply, projectorUpdate_apply, Function.comp_def, map_add, map_smul, smul_sub, hobs]

/-- Actual projected-Gaussian conditioning step. The algebraic hypotheses
are satisfied by an orthogonal projector Q and a unit w in its range.
There is no posterior or conditional-Gaussian-law premise. -/
theorem projected_unit_row_disintegration
    (Q : E →L[ℝ] E) (w : E) (hw : ‖w‖ = 1)
    (hQw : Q w = w) (hobs : ∀ b, ⟪w, Q b⟫ = ⟪w, b⟫)
    (σ : ℝ) (m : E) :
    (projectedPrior Q σ m).map (fun x => (⟪w, x⟫, x)) =
      gaussianReal ⟪w, m⟫ ⟨σ ^ 2, sq_nonneg σ⟩ ⊗ₘ
        reconstructionKernel w
          (projectedPrior (projectorUpdate Q w) σ (residualMap w m)) := by
  have hzero : residualMap w w = 0 := by
    simp [residualMap_apply, projectorUpdate_apply, inner_self_eq_norm_sq, hw]
  have hkill (b : E) : residualMap w (Q (residualMap w b)) = residualMap w (Q b) := by
    rw [show residualMap w b = b - ⟪w, b⟫ • w from rfl, map_sub, map_smul, hQw,
      map_sub, map_smul, hzero, smul_zero, sub_zero]
  have hi : IndepFun (fun b : E => ⟪w, σ • Q b + m⟫)
      (fun b => residualMap w (σ • Q b + m)) (stdGaussian E) := by
    convert! (fixed_unit_row_residual_independent w hw).comp
      (φ := fun z : ℝ => σ * z + ⟪w, m⟫)
      (ψ := fun r : E => σ • residualMap w (Q r) + residualMap w m)
      (by fun_prop) (by fun_prop) using 1
    · funext b
      simp [residualMap_apply, projectorUpdate_apply, inner_add_right, inner_smul_right, hobs, Function.comp_def]
    · funext b
      simp only [Function.comp_def, map_add, map_smul]
      rw [hkill]
  have hjoint := hi.map_prod_eq_prod_map_map (by fun_prop) (by fun_prop)
  have hprod : (projectedPrior Q σ m).map (fun x => (⟪w, x⟫, residualMap w x)) =
      ((projectedPrior Q σ m).map (fun x => ⟪w, x⟫)).prod
        ((projectedPrior Q σ m).map (residualMap w)) := by
    unfold projectedPrior
    rw [Measure.map_map (by fun_prop) (by fun_prop),
      Measure.map_map (by fun_prop) (by fun_prop),
      Measure.map_map (by fun_prop) (by fun_prop)]
    exact hjoint
  rw [projected_unit_row_observation_law Q w hw hobs σ m,
    projected_unit_row_residual_law Q w hobs σ m] at hprod
  rw [reconstruction_compProd]
  rw [← hprod, Measure.map_map (by fun_prop) (by fun_prop)]
  congr 1
  funext x
  apply Prod.ext
  · rfl
  · change x = x - ⟪w, x⟫ • w + ⟪w, x⟫ • w
    abel

/-- A jointly measurable family of projected Gaussians, represented as a
kernel rather than a collection of unspecified conditional distributions. -/
noncomputable def projectedKernel
    {H : Type*} [MeasurableSpace H]
    (Q : H → E →L[ℝ] E) (σ : ℝ) (m : H → E) : Kernel H E :=
  (Kernel.id ×ₖ Kernel.const H (stdGaussian E)).map
    (fun p : H × E => σ • Q p.1 p.2 + m p.1)

theorem projectedKernel_isMarkov
    {H : Type*} [MeasurableSpace H]
    (Q : H → E →L[ℝ] E) (σ : ℝ) (m : H → E)
    (hQ : Measurable Q) (hm : Measurable m) :
    IsMarkovKernel (projectedKernel Q σ m) := by
  apply Kernel.IsMarkovKernel.map
  have heval : Measurable (fun p : (E →L[ℝ] E) × E => p.1 p.2) :=
    (continuous_fst.clm_apply continuous_snd).measurable
  exact (heval.comp ((hQ.comp measurable_fst).prodMk measurable_snd)).const_smul σ |>.add
    (hm.comp measurable_fst)

/-- The explicit conditional-prior kernel evaluates to the actual affine
Gaussian measure at every fixed history. -/
theorem projectedKernel_apply
    {H : Type*} [MeasurableSpace H]
    (Q : H → E →L[ℝ] E) (σ : ℝ) (m : H → E)
    (hQ : Measurable Q) (hm : Measurable m) (h : H) :
    projectedKernel Q σ m h = projectedPrior (Q h) σ (m h) := by
  have heval : Measurable (fun p : (E →L[ℝ] E) × E => p.1 p.2) :=
    (continuous_fst.clm_apply continuous_snd).measurable
  have hf : Measurable (fun p : H × E => σ • Q p.1 p.2 + m p.1) :=
    (heval.comp ((hQ.comp measurable_fst).prodMk measurable_snd)).const_smul σ |>.add
      (hm.comp measurable_fst)
  rw [projectedKernel, Kernel.map_apply _ hf, Kernel.prod_apply,
    Kernel.id, Kernel.deterministic_apply, Kernel.const_apply, Measure.dirac_prod,
    Measure.map_map hf (by fun_prop)]
  rfl

lemma reconstructionKernel_apply (w : E) (R : Measure E) [IsProbabilityMeasure R] (y : ℝ) :
    reconstructionKernel w R y = R.map (fun r => r + y • w) := by
  rw [reconstructionKernel, Kernel.map_apply _ (by fun_prop), Kernel.prod_apply,
    Kernel.id, Kernel.deterministic_apply, Kernel.const_apply, Measure.dirac_prod,
    Measure.map_map (by fun_prop) (by fun_prop)]
  rfl

/-- Reparametrizing a genuinely disintegrated observation preserves the
joint law when the explicitly given kernels agree on corresponding values. -/
theorem reparametrize_observation
    {H S : Type*} [MeasurableSpace H] [MeasurableSpace S]
    (μ : Measure H) [IsProbabilityMeasure μ]
    (κ : Kernel H E) (η : Kernel S E) [IsMarkovKernel κ] [IsMarkovKernel η]
    (f : H → S) (hf : Measurable f) (hκ : ∀ h, η (f h) = κ h) :
    (μ ⊗ₘ κ).map (Prod.map f id) = (μ.map f) ⊗ₘ η := by
  ext A hA
  rw [Measure.map_apply (hf.prodMap measurable_id) hA,
    Measure.compProd_apply ((hf.prodMap measurable_id) hA), Measure.compProd_apply hA,
    lintegral_map (η.measurable_kernel_prodMk_left hA) hf]
  apply lintegral_congr
  intro h
  rw [hκ]
  rfl

/-- One normalized innovation and the full source vector, from an actual
projected Gaussian prior. The normalization has arbitrary known center c;
its mean is derived and its conditional noise variance is exactly one. -/
theorem projected_normalized_innovation_disintegration
    (Q : E →L[ℝ] E) (w : E) (hw : ‖w‖ = 1)
    (hQw : Q w = w) (hobs : ∀ b, ⟪w, Q b⟫ = ⟪w, b⟫)
    (σ : ℝ) (hσ : σ ≠ 0) (m : E) (c : ℝ) :
    (projectedPrior Q σ m).map (fun x => ((⟪w, x⟫ - c) / σ, x)) =
      gaussianReal ((⟪w, m⟫ - c) / σ) 1 ⊗ₘ
        projectedKernel (fun _ : ℝ => projectorUpdate Q w) σ
          (fun z : ℝ => residualMap w m + (σ * z + c) • w) := by
  let Q' := projectorUpdate Q w
  let R := projectedPrior Q' σ (residualMap w m)
  let κ := reconstructionKernel w R
  let η := projectedKernel (fun _ : ℝ => Q') σ
    (fun z : ℝ => residualMap w m + (σ * z + c) • w)
  letI : IsMarkovKernel η := projectedKernel_isMarkov _ σ _ measurable_const (by fun_prop)
  have heq (y : ℝ) : η ((y - c) / σ) = κ y := by
    dsimp [residualMap_apply, projectorUpdate_apply, η, κ, R]
    rw [projectedKernel_apply _ σ _ measurable_const (by fun_prop),
      reconstructionKernel_apply]
    unfold projectedPrior
    rw [Measure.map_map (by fun_prop) (by fun_prop)]
    congr 1
    funext b
    have hy : σ * ((y - c) / σ) + c = y := by field_simp [residualMap_apply, projectorUpdate_apply, hσ]; ring
    simp only [Function.comp_def, hy]
    abel
  have hrep := reparametrize_observation
    (gaussianReal ⟪w, m⟫ ⟨σ ^ 2, sq_nonneg σ⟩) κ η
    (fun y => (y - c) / σ) (by fun_prop) heq
  have hnormal : (gaussianReal ⟪w, m⟫ ⟨σ ^ 2, sq_nonneg σ⟩).map
      (fun y => (y - c) / σ) = gaussianReal ((⟪w, m⟫ - c) / σ) 1 := by
    have hf : (fun y : ℝ => (y - c) / σ) = (fun y => y / σ) ∘ (fun y => y - c) := rfl
    rw [hf, ← Measure.map_map (by fun_prop) (by fun_prop), gaussianReal_map_sub_const,
      gaussianReal_map_div_const]
    congr 1
    change NNReal.mk (σ ^ 2) (sq_nonneg σ) / NNReal.mk (σ ^ 2) (sq_nonneg σ) = 1
    apply div_self
    apply NNReal.coe_ne_zero.mp
    exact pow_ne_zero 2 hσ
  rw [hnormal] at hrep
  rw [← projected_unit_row_disintegration Q w hw hQw hobs σ m,
    Measure.map_map (by fun_prop) (by fun_prop)] at hrep
  exact hrep

/-- One signal innovation with the exact posterior update required for
iteration: the common center updates independently of the hidden signal. -/
theorem signal_innovation_disintegration
    (Q : E →L[ℝ] E) (w : E) (hw : ‖w‖ = 1)
    (hQw : Q w = w) (hobs : ∀ b, ⟪w, Q b⟫ = ⟪w, b⟫)
    (σ : ℝ) (hσ : σ ≠ 0) (δ : ℝ) (θ m₀ : E) :
    (projectedPrior Q σ (m₀ + δ • Q θ)).map
        (fun x => (⟪w, x - m₀⟫ / σ, x)) =
      gaussianReal ((δ / σ) * ⟪w, θ⟫) 1 ⊗ₘ
        projectedKernel (fun _ : ℝ => projectorUpdate Q w) σ
          (fun z : ℝ => m₀ + (σ * z) • w + δ • projectorUpdate Q w θ) := by
  have h := projected_normalized_innovation_disintegration Q w hw hQw hobs σ hσ
    (m₀ + δ • Q θ) ⟪w, m₀⟫
  have hsignal : (⟪w, m₀ + δ • Q θ⟫ - ⟪w, m₀⟫) / σ =
      (δ / σ) * ⟪w, θ⟫ := by
    simp only [inner_add_right, inner_smul_right, hobs]
    ring
  have hmean : (fun z : ℝ => residualMap w (m₀ + δ • Q θ) + (σ * z + ⟪w, m₀⟫) • w) =
      (fun z : ℝ => m₀ + (σ * z) • w + δ • projectorUpdate Q w θ) := by
    funext z
    simp only [residualMap_apply, projectorUpdate_apply,
      inner_add_right, inner_smul_right, hobs]
    module
  rw [hsignal, hmean] at h
  simpa only [inner_sub_right] using h

end PaperGaussianOracleBridge


end
-- END GaussianOracleBridge.lean

-- BEGIN AdaptiveGaussianOracleBridgeClean.lean
section
namespace PaperAdaptiveGaussianOracleBridge

open MeasureTheory ProbabilityTheory Set PaperGaussianOracleBridge PaperGaussianKL
open scoped RealInnerProductSpace NNReal ENNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- An exact measurable filtering update on joint history/state laws. Its
per-history disintegration input will be discharged by the proved Gaussian
innovation identity, rather than assumed in the finite source theorem. -/
theorem update_joint_disintegration
    {H : Type*} [MeasurableSpace H]
    (π : Measure H) [IsProbabilityMeasure π]
    (K : Kernel H E) [IsMarkovKernel K]
    (L : Kernel H ℝ) [IsMarkovKernel L]
    (P : Kernel (H × ℝ) E) [IsMarkovKernel P]
    (z : H × E → ℝ) (hz : Measurable z)
    (hdis : ∀ h, (K h).map (fun x => (z (h, x), x)) =
      (L h) ⊗ₘ P.comap (Prod.mk h) measurable_prodMk_left) :
    (π ⊗ₘ K).map (fun p => ((p.1, z p), p.2)) = (π ⊗ₘ L) ⊗ₘ P := by
  ext A hA
  have hf : Measurable (fun p : H × E => ((p.1, z p), p.2)) := by fun_prop
  rw [Measure.map_apply hf hA, Measure.compProd_apply (hf hA),
    Measure.compProd_apply hA, Measure.lintegral_compProd (P.measurable_kernel_prodMk_left hA)]
  apply lintegral_congr
  intro h
  let B : Set (ℝ × E) := {p | ((h, p.1), p.2) ∈ A}
  have hB : MeasurableSet B := hA.preimage (by fun_prop)
  have hh := congrArg (fun μ : Measure (ℝ × E) => μ B) (hdis h)
  rw [Measure.map_apply (by fun_prop) hB, Measure.compProd_apply hB] at hh
  simp only [Kernel.comap_apply] at hh
  convert! hh using 1

noncomputable def innovationProjection
    (rows : (t : ℕ) → History t → E) : (t : ℕ) → History t → E →L[ℝ] E
  | 0 => fun _ => ContinuousLinearMap.id ℝ E
  | t + 1 => fun h => PaperGaussianOracleBridge.projectorUpdate
      (innovationProjection rows t h.1) (rows t h.1)

noncomputable def innovationCenter
    (rows : (t : ℕ) → History t → E) (σ : ℝ) : (t : ℕ) → History t → E
  | 0 => fun _ => 0
  | t + 1 => fun h => innovationCenter rows σ t h.1 + (σ * h.2) • rows t h.1

theorem innovationProjection_measurable
    (rows : (t : ℕ) → History t → E) (hmeas : ∀ t, Measurable (rows t)) (t : ℕ) :
    Measurable (innovationProjection rows t) := by
  induction t with
  | zero => exact measurable_const
  | succ t ih =>
    exact PaperProjectorInnovations.projectorUpdate_measurable.comp
      ((ih.comp measurable_fst).prodMk ((hmeas t).comp measurable_fst))

theorem innovationCenter_measurable
    (rows : (t : ℕ) → History t → E) (hmeas : ∀ t, Measurable (rows t)) (σ : ℝ) (t : ℕ) :
    Measurable (innovationCenter rows σ t) := by
  induction t with
  | zero => exact measurable_const
  | succ t ih =>
    exact (ih.comp measurable_fst).add
      ((measurable_const.mul measurable_snd).smul ((hmeas t).comp measurable_fst))

/-- Actual observations of one fixed unknown source vector. The same g is
used throughout the full finite path. -/
noncomputable def sourceHistory
    (rows : (t : ℕ) → History t → E) (σ : ℝ) : (t : ℕ) → E → History t
  | 0 => fun _ => ()
  | t + 1 => fun g =>
      let h := sourceHistory rows σ t g
      (h, ⟪rows t h, g - innovationCenter rows σ t h⟫ / σ)

theorem sourceHistory_measurable
    (rows : (t : ℕ) → History t → E) (hmeas : ∀ t, Measurable (rows t)) (σ : ℝ) (t : ℕ) :
    Measurable (sourceHistory rows σ t) := by
  induction t with
  | zero => exact measurable_const
  | succ t ih =>
    exact ih.prodMk (((hmeas t).comp ih).inner
      (measurable_id.sub ((innovationCenter_measurable rows hmeas σ t).comp ih)) |>.div_const σ)

noncomputable def signalMeans
    (rows : (t : ℕ) → History t → E) (hmeas : ∀ t, Measurable (rows t))
    (σ δ : ℝ) (θ : E) : AdaptiveMean where
  mean t h := (δ / σ) * ⟪rows t h, θ⟫
  measurable_mean t := measurable_const.mul ((hmeas t).inner measurable_const)

noncomputable def sourcePosterior
    (rows : (t : ℕ) → History t → E) (σ δ : ℝ) (θ : E) (t : ℕ) :
    Kernel (History t) E :=
  projectedKernel (innovationProjection rows t) σ
    (fun h => innovationCenter rows σ t h + δ • innovationProjection rows t h θ)

theorem sourcePosterior_isMarkov
    (rows : (t : ℕ) → History t → E) (hmeas : ∀ t, Measurable (rows t))
    (σ δ : ℝ) (θ : E) (t : ℕ) :
    IsMarkovKernel (sourcePosterior rows σ δ θ t) := by
  apply projectedKernel_isMarkov _ σ _ (innovationProjection_measurable rows hmeas t)
  have heval : Measurable (fun p : (E →L[ℝ] E) × E => p.1 p.2) :=
    (continuous_fst.clm_apply continuous_snd).measurable
  exact (innovationCenter_measurable rows hmeas σ t).add
    ((heval.comp ((innovationProjection_measurable rows hmeas t).prodMk measurable_const)).const_smul δ)

theorem sourcePosterior_apply
    (rows : (t : ℕ) → History t → E) (hmeas : ∀ t, Measurable (rows t))
    (σ δ : ℝ) (θ : E) (t : ℕ) (h : History t) :
    sourcePosterior rows σ δ θ t h = projectedPrior (innovationProjection rows t h) σ
      (innovationCenter rows σ t h + δ • innovationProjection rows t h θ) := by
  apply projectedKernel_apply _ σ _ (innovationProjection_measurable rows hmeas t)
  have heval : Measurable (fun p : (E →L[ℝ] E) × E => p.1 p.2) :=
    (continuous_fst.clm_apply continuous_snd).measurable
  exact (innovationCenter_measurable rows hmeas σ t).add
    ((heval.comp ((innovationProjection_measurable rows hmeas t).prodMk measurable_const)).const_smul δ)

/-- The exact finite source joint law for measurable adaptive orthogonal
innovation rows. The source uses one fixed Gaussian vector along the entire
path, while the channel law is built recursively from Gaussian kernels.
All hypotheses are algebraic row/projector conditions on the finite horizon. -/
theorem finite_adaptive_source_joint_law
    (rows : (t : ℕ) → History t → E) (hmeas : ∀ t, Measurable (rows t))
    (σ δ : ℝ) (hσ : σ ≠ 0) (θ : E) :
    ∀ n,
      (∀ t < n, ∀ h : History t, ‖rows t h‖ = 1) →
      (∀ t < n, ∀ h : History t, innovationProjection rows t h (rows t h) = rows t h) →
      (∀ t < n, ∀ h : History t, ∀ b,
        ⟪rows t h, innovationProjection rows t h b⟫ = ⟪rows t h, b⟫) →
      (sourcePrior σ (δ • θ)).map (fun g => (sourceHistory rows σ n g, g)) =
        signalLaw (signalMeans rows hmeas σ δ θ) n ⊗ₘ sourcePosterior rows σ δ θ n := by
  intro n
  induction n with
  | zero =>
    intro _ _ _
    have hK : sourcePosterior rows σ δ θ 0 = Kernel.const Unit (sourcePrior σ (δ • θ)) := by
      ext h : 1
      rw [sourcePosterior_apply rows hmeas]
      change projectedPrior (innovationProjection rows 0 h) σ
        (innovationCenter rows σ 0 h + δ • innovationProjection rows 0 h θ) =
          sourcePrior σ (δ • θ)
      simp only [innovationProjection, innovationCenter, ContinuousLinearMap.id_apply, zero_add]
      rfl
    change (sourcePrior σ (δ • θ)).map (fun g => ((), g)) =
      Measure.dirac () ⊗ₘ sourcePosterior rows σ δ θ 0
    rw [hK, Measure.dirac_unit_compProd_const]
  | succ n ih =>
    intro hunit hfixed hinner
    have hp := ih (fun t ht => hunit t (by omega)) (fun t ht => hfixed t (by omega))
      (fun t ht => hinner t (by omega))
    let a := signalMeans rows hmeas σ δ θ
    let K := sourcePosterior rows σ δ θ n
    let L := gaussianKernel (a.mean n) (a.measurable_mean n)
    let P : Kernel (History n × ℝ) E := sourcePosterior rows σ δ θ (n + 1)
    let z : History n × E → ℝ :=
      fun p => ⟪rows n p.1, p.2 - innovationCenter rows σ n p.1⟫ / σ
    letI : IsMarkovKernel K := sourcePosterior_isMarkov rows hmeas σ δ θ n
    letI : IsMarkovKernel P := by
      change IsMarkovKernel (sourcePosterior rows σ δ θ (n + 1))
      exact sourcePosterior_isMarkov rows hmeas σ δ θ (n + 1)
    have hz : Measurable z :=
      ((hmeas n).comp measurable_fst).inner
        (measurable_snd.sub ((innovationCenter_measurable rows hmeas σ n).comp measurable_fst))
        |>.div_const σ
    have hdis : ∀ h, (K h).map (fun x => (z (h, x), x)) =
        (L h) ⊗ₘ P.comap (Prod.mk h) measurable_prodMk_left := by
      intro h
      have hpost : P.comap (Prod.mk h) measurable_prodMk_left =
          projectedKernel (fun _ : ℝ => PaperGaussianOracleBridge.projectorUpdate
            (innovationProjection rows n h) (rows n h)) σ
            (fun y : ℝ => innovationCenter rows σ n h + (σ * y) • rows n h +
              δ • PaperGaussianOracleBridge.projectorUpdate (innovationProjection rows n h) (rows n h) θ) := by
        ext y : 1
        rw [Kernel.comap_apply]
        have hpApply := sourcePosterior_apply rows hmeas σ δ θ (n + 1) (h, y)
        have heApply := projectedKernel_apply
          (fun _ : ℝ => PaperGaussianOracleBridge.projectorUpdate
            (innovationProjection rows n h) (rows n h)) σ
          (fun y : ℝ => innovationCenter rows σ n h + (σ * y) • rows n h +
            δ • PaperGaussianOracleBridge.projectorUpdate (innovationProjection rows n h) (rows n h) θ)
          measurable_const (by fun_prop) y
        exact hpApply.trans heApply.symm
      rw [hpost]
      change (sourcePosterior rows σ δ θ n h).map _ =
        gaussianReal ((δ / σ) * ⟪rows n h, θ⟫) 1 ⊗ₘ _
      rw [sourcePosterior_apply rows hmeas]
      exact signal_innovation_disintegration (innovationProjection rows n h) (rows n h)
        (hunit n (by omega) h) (hfixed n (by omega) h) (hinner n (by omega) h) σ hσ δ θ
          (innovationCenter rows σ n h)
    have hu := update_joint_disintegration (signalLaw a n) K L P z hz hdis
    change (sourcePrior σ (δ • θ)).map (fun g => (sourceHistory rows σ n g, g)) =
      signalLaw a n ⊗ₘ K at hp
    have hjmeas : Measurable (fun g : E => (sourceHistory rows σ n g, g)) :=
      (sourceHistory_measurable rows hmeas σ n).prodMk measurable_id
    have htmeas : Measurable (fun p : History n × E => ((p.1, z p), p.2)) := by fun_prop
    rw [← hp, Measure.map_map htmeas hjmeas] at hu
    exact hu

/-- Equality of the actual full finite adaptive source path law with the
Gaussian channel transcript law, obtained by taking the proved joint marginal. -/
theorem finite_adaptive_source_history_law
    (rows : (t : ℕ) → History t → E) (hmeas : ∀ t, Measurable (rows t))
    (σ δ : ℝ) (hσ : σ ≠ 0) (θ : E) (n : ℕ)
    (hunit : ∀ t < n, ∀ h : History t, ‖rows t h‖ = 1)
    (hfixed : ∀ t < n, ∀ h : History t, innovationProjection rows t h (rows t h) = rows t h)
    (hinner : ∀ t < n, ∀ h : History t, ∀ b,
      ⟪rows t h, innovationProjection rows t h b⟫ = ⟪rows t h, b⟫) :
    (sourcePrior σ (δ • θ)).map (sourceHistory rows σ n) =
      signalLaw (signalMeans rows hmeas σ δ θ) n := by
  letI := sourcePosterior_isMarkov rows hmeas σ δ θ n
  have h := congrArg Measure.fst
    (finite_adaptive_source_joint_law rows hmeas σ δ hσ θ n hunit hfixed hinner)
  rw [Measure.fst_compProd] at h
  rw [Measure.fst] at h
  have hjmeas : Measurable (fun g : E => (sourceHistory rows σ n g, g)) :=
    (sourceHistory_measurable rows hmeas σ n).prodMk measurable_id
  exact (Measure.map_map (μ := sourcePrior σ (δ • θ)) measurable_fst hjmeas).symm.trans h

/-- Gram--Schmidt projector generated by the actual measurable adaptive
query vectors, before any stochastic law is considered. -/
noncomputable def queryProjection
    (query : (t : ℕ) → History t → E) : (t : ℕ) → History t → E →L[ℝ] E
  | 0 => fun _ => ContinuousLinearMap.id ℝ E
  | t + 1 => fun h => PaperProjectorInnovations.projectorUpdate
      (queryProjection query t h.1)
      (PaperProjectorInnovations.normalizedResidual (queryProjection query t h.1) (query t h.1))

noncomputable def queryRows
    (query : (t : ℕ) → History t → E) (t : ℕ) (h : History t) : E :=
  PaperProjectorInnovations.normalizedResidual (queryProjection query t h) (query t h)

theorem queryProjection_measurable
    (query : (t : ℕ) → History t → E) (hmeas : ∀ t, Measurable (query t)) (t : ℕ) :
    Measurable (queryProjection query t) := by
  induction t with
  | zero => exact measurable_const
  | succ t ih =>
    exact PaperProjectorInnovations.innovationUpdate_measurable.comp
      ((ih.comp measurable_fst).prodMk ((hmeas t).comp measurable_fst))

theorem queryRows_measurable
    (query : (t : ℕ) → History t → E) (hmeas : ∀ t, Measurable (query t)) (t : ℕ) :
    Measurable (queryRows query t) :=
  PaperProjectorInnovations.normalizedResidual_measurable.comp
    ((queryProjection_measurable query hmeas t).prodMk (hmeas t))

theorem innovationProjection_queryRows
    (query : (t : ℕ) → History t → E) (t : ℕ) :
    innovationProjection (queryRows query) t = queryProjection query t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    funext h
    simp only [innovationProjection, queryProjection, queryRows, ih]
    rfl

theorem queryProjection_selfAdjoint_idempotent
    (query : (t : ℕ) → History t → E) :
    ∀ n, (∀ t < n, ∀ h : History t, queryProjection query t h (query t h) ≠ 0) →
      ∀ h : History n, IsSelfAdjoint (queryProjection query n h) ∧
        queryProjection query n h * queryProjection query n h = queryProjection query n h := by
  intro n
  induction n with
  | zero =>
    intro _ h
    change IsSelfAdjoint (1 : E →L[ℝ] E) ∧ (1 : E →L[ℝ] E) * 1 = 1
    exact ⟨IsSelfAdjoint.one _, one_mul _⟩
  | succ n ih =>
    intro hactive h
    have hp := ih (fun t ht => hactive t (by omega)) h.1
    exact PaperProjectorInnovations.projectorUpdate_selfAdjoint_idempotent hp.1 hp.2
      (PaperProjectorInnovations.normalizedResidual_norm (hactive n (by omega) h.1))
      (PaperProjectorInnovations.normalizedResidual_fixed hp.2 _)

/-- For a finite sequence of active adaptive source queries, the actual
normalized transcript law equals the Gaussian sensing channel. The only
extra condition is nonzero residual at each queried finite history; zero and
stopping branches require a separate compression/padding construction. -/
theorem finite_active_query_source_history_law
    (query : (t : ℕ) → History t → E) (hmeas : ∀ t, Measurable (query t))
    (σ δ : ℝ) (hσ : σ ≠ 0) (θ : E) (n : ℕ)
    (hactive : ∀ t < n, ∀ h : History t, queryProjection query t h (query t h) ≠ 0) :
    (sourcePrior σ (δ • θ)).map (sourceHistory (queryRows query) σ n) =
      signalLaw (signalMeans (queryRows query) (queryRows_measurable query hmeas) σ δ θ) n := by
  apply finite_adaptive_source_history_law _ (queryRows_measurable query hmeas) σ δ hσ θ n
  · intro t ht h
    exact PaperProjectorInnovations.normalizedResidual_norm (hactive t ht h)
  · intro t ht h
    rw [innovationProjection_queryRows]
    have hp := queryProjection_selfAdjoint_idempotent query t
      (fun s hs => hactive s (by omega)) h
    exact PaperProjectorInnovations.normalizedResidual_fixed hp.2 _
  · intro t ht h b
    rw [innovationProjection_queryRows]
    have hp := queryProjection_selfAdjoint_idempotent query t
      (fun s hs => hactive s (by omega)) h
    exact PaperProjectorInnovations.inner_projector_fixed
      (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hp.1)
      (PaperProjectorInnovations.normalizedResidual_fixed hp.2 _) b

end PaperAdaptiveGaussianOracleBridge


end
-- END AdaptiveGaussianOracleBridgeClean.lean

-- BEGIN EnrichedGaussianOracleBridge.lean
section
namespace PaperEnrichedGaussianOracleBridge

open MeasureTheory ProbabilityTheory Set PaperGaussianOracleBridge PaperGaussianKL
  PaperAdaptiveGaussianOracleBridge
open scoped RealInnerProductSpace NNReal ENNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- A stochastic observation update that retains the same source state.
The per-history law is later proved from the Gaussian disintegration. -/
theorem stochastic_joint_update
    {H : Type*} [MeasurableSpace H]
    (π : Measure H) [IsProbabilityMeasure π]
    (K : Kernel H E) [IsMarkovKernel K]
    (S : Kernel (H × E) ℝ) [IsMarkovKernel S]
    (L : Kernel H ℝ) [IsMarkovKernel L]
    (P : Kernel (H × ℝ) E) [IsMarkovKernel P]
    (hdis : ∀ h,
      ((K h) ⊗ₘ S.comap (Prod.mk h) measurable_prodMk_left).map Prod.swap =
        (L h) ⊗ₘ P.comap (Prod.mk h) measurable_prodMk_left) :
    (π ⊗ₘ K ⊗ₘ S).map (fun p => ((p.1.1, p.2), p.1.2)) = (π ⊗ₘ L) ⊗ₘ P := by
  ext A hA
  have hf : Measurable (fun p : (H × E) × ℝ => ((p.1.1, p.2), p.1.2)) := by fun_prop
  rw [Measure.map_apply hf hA, Measure.compProd_apply (hf hA),
    Measure.lintegral_compProd (S.measurable_kernel_prodMk_left (hf hA)),
    Measure.compProd_apply hA,
    Measure.lintegral_compProd (P.measurable_kernel_prodMk_left hA)]
  apply lintegral_congr
  intro h
  let B : Set (ℝ × E) := {p | ((h, p.1), p.2) ∈ A}
  have hB : MeasurableSet B := hA.preimage (by fun_prop)
  have hh := congrArg (fun μ : Measure (ℝ × E) => μ B) (hdis h)
  rw [Measure.map_apply measurable_swap hB, Measure.compProd_apply (measurable_swap hB),
    Measure.compProd_apply hB] at hh
  simp only [Kernel.comap_apply] at hh
  convert! hh using 1

noncomputable def innovationObservation
    (rows : (t : ℕ) → History t → E) (σ : ℝ) (t : ℕ) (p : History t × E) : ℝ :=
  ⟪rows t p.1, p.2 - innovationCenter rows σ t p.1⟫ / σ

theorem innovationObservation_measurable
    (rows : (t : ℕ) → History t → E) (hmeas : ∀ t, Measurable (rows t))
    (σ : ℝ) (t : ℕ) : Measurable (innovationObservation rows σ t) :=
  ((hmeas t).comp measurable_fst).inner
    (measurable_snd.sub ((innovationCenter_measurable rows hmeas σ t).comp measurable_fst))
    |>.div_const σ

/-- A zero row uses fresh independent private Gaussian noise. Every active
row returns the actual normalized observation of the current fixed g. -/
noncomputable def sourceObservationKernel
    (rows : (t : ℕ) → History t → E) (hmeas : ∀ t, Measurable (rows t))
    (σ : ℝ) (t : ℕ) : Kernel (History t × E) ℝ := by
  classical
  have hs : MeasurableSet {p : History t × E | rows t p.1 = 0} :=
    measurableSet_eq_fun ((hmeas t).comp measurable_fst) measurable_const
  exact Kernel.piecewise hs
    (Kernel.const (History t × E) (gaussianReal 0 1))
    (Kernel.deterministic (innovationObservation rows σ t)
      (innovationObservation_measurable rows hmeas σ t))

instance sourceObservationKernel_isMarkov
    (rows : (t : ℕ) → History t → E) (hmeas : ∀ t, Measurable (rows t))
    (σ : ℝ) (t : ℕ) : IsMarkovKernel (sourceObservationKernel rows hmeas σ t) := by
  unfold sourceObservationKernel
  infer_instance

/-- The source vector is sampled once at t=0. All subsequent steps retain
it and only sample private noise on the zero-row branch. -/
noncomputable def enrichedSourceJoint
    (rows : (t : ℕ) → History t → E) (hmeas : ∀ t, Measurable (rows t))
    (σ δ : ℝ) (θ : E) : (t : ℕ) → Measure (History t × E)
  | 0 => (sourcePrior σ (δ • θ)).map (fun g => ((), g))
  | t + 1 => ((enrichedSourceJoint rows hmeas σ δ θ t) ⊗ₘ
      sourceObservationKernel rows hmeas σ t).map
        (fun p : (History t × E) × ℝ => ((p.1.1, p.2), p.1.2))

instance enrichedSourceJoint_isProbability
    (rows : (t : ℕ) → History t → E) (hmeas : ∀ t, Measurable (rows t))
    (σ δ : ℝ) (θ : E) (t : ℕ) :
    IsProbabilityMeasure (enrichedSourceJoint rows hmeas σ δ θ t) := by
  induction t with
  | zero => exact Measure.isProbabilityMeasure_map (by fun_prop)
  | succ t ih =>
    letI : IsProbabilityMeasure (enrichedSourceJoint rows hmeas σ δ θ t) := ih
    exact Measure.isProbabilityMeasure_map (by fun_prop)

/-- The next posterior kernel, stated with the product history type so
that it can be used directly in composition-products. -/
theorem sourcePosterior_next_comap
    (rows : (t : ℕ) → History t → E) (hmeas : ∀ t, Measurable (rows t))
    (σ δ : ℝ) (θ : E) (t : ℕ) (h : History t) :
    (sourcePosterior rows σ δ θ (t + 1) : Kernel (History t × ℝ) E).comap
      (Prod.mk h) measurable_prodMk_left =
      projectedKernel (fun _ : ℝ => PaperGaussianOracleBridge.projectorUpdate
        (innovationProjection rows t h) (rows t h)) σ
        (fun z : ℝ => innovationCenter rows σ t h + (σ * z) • rows t h +
          δ • PaperGaussianOracleBridge.projectorUpdate (innovationProjection rows t h) (rows t h) θ) := by
  ext z : 1
  rw [Kernel.comap_apply]
  have hp := sourcePosterior_apply rows hmeas σ δ θ (t + 1) (h, z)
  have he := projectedKernel_apply
    (fun _ : ℝ => PaperGaussianOracleBridge.projectorUpdate
      (innovationProjection rows t h) (rows t h)) σ
    (fun z : ℝ => innovationCenter rows σ t h + (σ * z) • rows t h +
      δ • PaperGaussianOracleBridge.projectorUpdate (innovationProjection rows t h) (rows t h) θ)
    measurable_const (by fun_prop) z
  exact hp.trans he.symm

theorem sourceObservationKernel_zero
    (rows : (t : ℕ) → History t → E) (hmeas : ∀ t, Measurable (rows t))
    (σ : ℝ) (t : ℕ) (h : History t) (hzero : rows t h = 0) :
    (sourceObservationKernel rows hmeas σ t).comap (Prod.mk h) measurable_prodMk_left =
      Kernel.const E (gaussianReal 0 1) := by
  classical
  ext g : 1
  simp [sourceObservationKernel, Kernel.comap_apply, Kernel.piecewise_apply, hzero, Kernel.const_apply]

theorem sourceObservationKernel_active
    (rows : (t : ℕ) → History t → E) (hmeas : ∀ t, Measurable (rows t))
    (σ : ℝ) (t : ℕ) (h : History t) (hactive : rows t h ≠ 0) :
    (sourceObservationKernel rows hmeas σ t).comap (Prod.mk h) measurable_prodMk_left =
      Kernel.deterministic (fun g => innovationObservation rows σ t (h, g))
        ((innovationObservation_measurable rows hmeas σ t).comp measurable_prodMk_left) := by
  classical
  ext g : 1
  simp [sourceObservationKernel, Kernel.comap_apply, Kernel.piecewise_apply,
    hactive, Kernel.deterministic_apply]

theorem sourcePosterior_next_zero
    (rows : (t : ℕ) → History t → E) (hmeas : ∀ t, Measurable (rows t))
    (σ δ : ℝ) (θ : E) (t : ℕ) (h : History t) (hzero : rows t h = 0) :
    (sourcePosterior rows σ δ θ (t + 1) : Kernel (History t × ℝ) E).comap
      (Prod.mk h) measurable_prodMk_left = Kernel.const ℝ (sourcePosterior rows σ δ θ t h) := by
  rw [sourcePosterior_next_comap rows hmeas]
  ext z : 1
  rw [projectedKernel_apply _ σ _ measurable_const (by fun_prop)]
  change projectedPrior _ σ _ = sourcePosterior rows σ δ θ t h
  rw [sourcePosterior_apply rows hmeas]
  have hu : PaperGaussianOracleBridge.projectorUpdate (innovationProjection rows t h) (rows t h) =
      innovationProjection rows t h := by
    rw [hzero]
    ext b
    simp [PaperGaussianOracleBridge.projectorUpdate]
  rw [hu, hzero]
  simp

/-- The exact per-history Gaussian innovation identity, including zero
rows where a fresh independent private Gaussian is adjoined. -/
theorem enriched_innovation_disintegration
    (rows : (t : ℕ) → History t → E) (hmeas : ∀ t, Measurable (rows t))
    (σ δ : ℝ) (hσ : σ ≠ 0) (θ : E) (t : ℕ) (h : History t)
    (hunit : rows t h = 0 ∨ ‖rows t h‖ = 1)
    (hfixed : innovationProjection rows t h (rows t h) = rows t h)
    (hinner : ∀ b, ⟪rows t h, innovationProjection rows t h b⟫ = ⟪rows t h, b⟫) :
    ((sourcePosterior rows σ δ θ t h) ⊗ₘ
      (sourceObservationKernel rows hmeas σ t).comap (Prod.mk h) measurable_prodMk_left).map Prod.swap =
        gaussianReal ((δ / σ) * ⟪rows t h, θ⟫) 1 ⊗ₘ
          (sourcePosterior rows σ δ θ (t + 1) : Kernel (History t × ℝ) E).comap
            (Prod.mk h) measurable_prodMk_left := by
  letI := sourcePosterior_isMarkov rows hmeas σ δ θ t
  by_cases hz : rows t h = 0
  · rw [sourceObservationKernel_zero rows hmeas σ t h hz,
      sourcePosterior_next_zero rows hmeas σ δ θ t h hz,
      Measure.compProd_const, Measure.prod_swap, Measure.compProd_const]
    simp only [hz, inner_zero_left, mul_zero]
  · have hn : ‖rows t h‖ = 1 := hunit.resolve_left hz
    have hfm : Measurable (fun g : E => innovationObservation rows σ t (h, g)) :=
      (innovationObservation_measurable rows hmeas σ t).comp measurable_prodMk_left
    have hpair : Measurable (fun g : E => (g, innovationObservation rows σ t (h, g))) :=
      measurable_id.prodMk hfm
    rw [sourceObservationKernel_active rows hmeas σ t h hz,
      sourcePosterior_next_comap rows hmeas,
      Measure.compProd_deterministic hfm,
      Measure.map_map measurable_swap hpair, sourcePosterior_apply rows hmeas]
    exact signal_innovation_disintegration (innovationProjection rows t h) (rows t h)
      hn hfixed hinner σ hσ δ θ (innovationCenter rows σ t h)

/-- Full finite enriched source/channel joint-law equality. No actual
conditional Gaussian or transcript-law equality is assumed. Zero rows and
unused steps are included through the independently sampled noise branch. -/
theorem finite_enriched_source_joint_law
    (rows : (t : ℕ) → History t → E) (hmeas : ∀ t, Measurable (rows t))
    (σ δ : ℝ) (hσ : σ ≠ 0) (θ : E) :
    ∀ n,
      (∀ t < n, ∀ h : History t, rows t h = 0 ∨ ‖rows t h‖ = 1) →
      (∀ t < n, ∀ h : History t, innovationProjection rows t h (rows t h) = rows t h) →
      (∀ t < n, ∀ h : History t, ∀ b,
        ⟪rows t h, innovationProjection rows t h b⟫ = ⟪rows t h, b⟫) →
      enrichedSourceJoint rows hmeas σ δ θ n =
        signalLaw (signalMeans rows hmeas σ δ θ) n ⊗ₘ sourcePosterior rows σ δ θ n := by
  intro n
  induction n with
  | zero =>
    intro _ _ _
    have hK : sourcePosterior rows σ δ θ 0 = Kernel.const Unit (sourcePrior σ (δ • θ)) := by
      ext h : 1
      rw [sourcePosterior_apply rows hmeas]
      change projectedPrior (innovationProjection rows 0 h) σ
        (innovationCenter rows σ 0 h + δ • innovationProjection rows 0 h θ) =
          sourcePrior σ (δ • θ)
      simp only [innovationProjection, innovationCenter, ContinuousLinearMap.id_apply, zero_add]
      rfl
    change (sourcePrior σ (δ • θ)).map (fun g => ((), g)) =
      Measure.dirac () ⊗ₘ sourcePosterior rows σ δ θ 0
    rw [hK, Measure.dirac_unit_compProd_const]
  | succ n ih =>
    intro hunit hfixed hinner
    have hp := ih (fun t ht => hunit t (by omega)) (fun t ht => hfixed t (by omega))
      (fun t ht => hinner t (by omega))
    let a := signalMeans rows hmeas σ δ θ
    let K := sourcePosterior rows σ δ θ n
    let S := sourceObservationKernel rows hmeas σ n
    let L := gaussianKernel (a.mean n) (a.measurable_mean n)
    let P : Kernel (History n × ℝ) E := sourcePosterior rows σ δ θ (n + 1)
    letI : IsMarkovKernel K := sourcePosterior_isMarkov rows hmeas σ δ θ n
    letI : IsMarkovKernel P := by
      change IsMarkovKernel (sourcePosterior rows σ δ θ (n + 1))
      exact sourcePosterior_isMarkov rows hmeas σ δ θ (n + 1)
    have hd : ∀ h, ((K h) ⊗ₘ S.comap (Prod.mk h) measurable_prodMk_left).map Prod.swap =
        (L h) ⊗ₘ P.comap (Prod.mk h) measurable_prodMk_left := by
      intro h
      exact enriched_innovation_disintegration rows hmeas σ δ hσ θ n h
        (hunit n (by omega) h) (hfixed n (by omega) h) (hinner n (by omega) h)
    have hu := stochastic_joint_update (signalLaw a n) K S L P hd
    change enrichedSourceJoint rows hmeas σ δ θ n = signalLaw a n ⊗ₘ K at hp
    rw [← hp] at hu
    exact hu

/-- The stochastic observation transition preserves the source-vector
marginal for any observation kernel, including all private-noise steps. -/
theorem retain_source_state_marginal
    {H : Type*} [MeasurableSpace H]
    (μ : Measure (H × E)) [IsProbabilityMeasure μ]
    (S : Kernel (H × E) ℝ) [IsMarkovKernel S] :
    ((μ ⊗ₘ S).map (fun p : (H × E) × ℝ => ((p.1.1, p.2), p.1.2))).snd = μ.snd := by
  have hf : Measurable (fun p : (H × E) × ℝ => ((p.1.1, p.2), p.1.2)) := by fun_prop
  rw [Measure.snd, Measure.map_map measurable_snd hf]
  change (μ ⊗ₘ S).map (Prod.snd ∘ Prod.fst) = μ.snd
  rw [← Measure.map_map measurable_snd measurable_fst]
  change (μ ⊗ₘ S).fst.map Prod.snd = μ.snd
  rw [Measure.fst_compProd]
  rfl

/-- The same source vector, sampled exactly once, remains the state at
every finite time; it is never resampled by the posterior construction. -/
theorem enrichedSourceJoint_source_marginal
    (rows : (t : ℕ) → History t → E) (hmeas : ∀ t, Measurable (rows t))
    (σ δ : ℝ) (θ : E) (n : ℕ) :
    (enrichedSourceJoint rows hmeas σ δ θ n).snd = sourcePrior σ (δ • θ) := by
  induction n with
  | zero =>
    change ((sourcePrior σ (δ • θ)).map (fun g => ((), g))).snd = sourcePrior σ (δ • θ)
    rw [Measure.snd, Measure.map_map measurable_snd (by fun_prop)]
    exact Measure.map_id
  | succ n ih =>
    change (((enrichedSourceJoint rows hmeas σ δ θ n) ⊗ₘ
      sourceObservationKernel rows hmeas σ n).map
      (fun p : (History n × E) × ℝ => ((p.1.1, p.2), p.1.2))).snd = _
    rw [retain_source_state_marginal]
    exact ih

theorem finite_enriched_source_history_law
    (rows : (t : ℕ) → History t → E) (hmeas : ∀ t, Measurable (rows t))
    (σ δ : ℝ) (hσ : σ ≠ 0) (θ : E) (n : ℕ)
    (hunit : ∀ t < n, ∀ h : History t, rows t h = 0 ∨ ‖rows t h‖ = 1)
    (hfixed : ∀ t < n, ∀ h : History t, innovationProjection rows t h (rows t h) = rows t h)
    (hinner : ∀ t < n, ∀ h : History t, ∀ b,
      ⟪rows t h, innovationProjection rows t h b⟫ = ⟪rows t h, b⟫) :
    (enrichedSourceJoint rows hmeas σ δ θ n).fst =
      signalLaw (signalMeans rows hmeas σ δ θ) n := by
  letI := sourcePosterior_isMarkov rows hmeas σ δ θ n
  have h := congrArg Measure.fst
    (finite_enriched_source_joint_law rows hmeas σ δ hσ θ n hunit hfixed hinner)
  rw [Measure.fst_compProd] at h
  exact h

/-- The recursively normalized query projector remains an orthogonal
projector even when a zero residual leaves it unchanged. -/
theorem queryProjection_all_selfAdjoint_idempotent
    (query : (t : ℕ) → History t → E) (n : ℕ) (h : History n) :
    IsSelfAdjoint (queryProjection query n h) ∧
      queryProjection query n h * queryProjection query n h = queryProjection query n h := by
  induction n with
  | zero =>
    change IsSelfAdjoint (1 : E →L[ℝ] E) ∧ (1 : E →L[ℝ] E) * 1 = 1
    exact ⟨IsSelfAdjoint.one _, one_mul _⟩
  | succ n ih =>
    have hp := ih h.1
    by_cases hr : queryProjection query n h.1 (query n h.1) = 0
    · change IsSelfAdjoint (PaperProjectorInnovations.projectorUpdate _ _) ∧
        PaperProjectorInnovations.projectorUpdate _ _ * PaperProjectorInnovations.projectorUpdate _ _ =
          PaperProjectorInnovations.projectorUpdate (queryProjection query n h.1)
            (PaperProjectorInnovations.normalizedResidual (queryProjection query n h.1) (query n h.1))
      rw [PaperProjectorInnovations.normalizedResidual_zero hr,
        PaperProjectorInnovations.projectorUpdate_zero]
      exact hp
    · exact PaperProjectorInnovations.projectorUpdate_selfAdjoint_idempotent hp.1 hp.2
        (PaperProjectorInnovations.normalizedResidual_norm hr)
        (PaperProjectorInnovations.normalizedResidual_fixed hp.2 _)

/-- Full finite normalized source law for arbitrary measurable adaptive
query vectors, with zero/dependent/unused queries padded by private N(0,1).
This statement has no nonzero-residual restriction. -/
theorem finite_query_enriched_source_history_law
    (query : (t : ℕ) → History t → E) (hmeas : ∀ t, Measurable (query t))
    (σ δ : ℝ) (hσ : σ ≠ 0) (θ : E) (n : ℕ) :
    (enrichedSourceJoint (queryRows query) (queryRows_measurable query hmeas) σ δ θ n).fst =
      signalLaw (signalMeans (queryRows query) (queryRows_measurable query hmeas) σ δ θ) n := by
  apply finite_enriched_source_history_law _ (queryRows_measurable query hmeas) σ δ hσ θ n
  · intro t ht h
    by_cases hr : queryProjection query t h (query t h) = 0
    · exact Or.inl (PaperProjectorInnovations.normalizedResidual_zero hr)
    · exact Or.inr (PaperProjectorInnovations.normalizedResidual_norm hr)
  · intro t ht h
    rw [innovationProjection_queryRows]
    have hp := queryProjection_all_selfAdjoint_idempotent query t h
    exact PaperProjectorInnovations.normalizedResidual_fixed hp.2 _
  · intro t ht h b
    rw [innovationProjection_queryRows]
    have hp := queryProjection_all_selfAdjoint_idempotent query t h
    exact PaperProjectorInnovations.inner_projector_fixed
      (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hp.1)
      (PaperProjectorInnovations.normalizedResidual_fixed hp.2 _) b

/-- The only source-observation randomness is the independent zero-row
branch. On an active row, the observation equals the raw source function
almost surely, in fact under a Dirac conditional measure. -/
theorem sourceObservationKernel_support
    (rows : (t : ℕ) → History t → E) (hmeas : ∀ t, Measurable (rows t))
    (σ : ℝ) (t : ℕ) (h : History t) (g : E) :
    ∀ᵐ z ∂sourceObservationKernel rows hmeas σ t (h, g),
      rows t h = 0 ∨ z = innovationObservation rows σ t (h, g) := by
  classical
  by_cases hz : rows t h = 0
  · exact ae_of_all _ (fun _ => Or.inl hz)
  · have hS : sourceObservationKernel rows hmeas σ t (h, g) =
        Measure.dirac (innovationObservation rows σ t (h, g)) := by
      simp [sourceObservationKernel, Kernel.piecewise_apply, hz, Kernel.deterministic_apply]
    rw [hS]
    simp only [hz, false_or]
    exact (ae_dirac_iff (measurableSet_eq_fun measurable_id measurable_const)).mpr rfl

/-- A general almost-sure invariant principle for the actual enriched
source process. It is useful for proving raw-policy decoder agreement and
support identities, without assuming those properties as probability bounds. -/
theorem enrichedSourceJoint_ae_invariant
    (rows : (t : ℕ) → History t → E) (hmeas : ∀ t, Measurable (rows t))
    (σ δ : ℝ) (θ : E)
    (P : (t : ℕ) → History t × E → Prop)
    (hP : ∀ t, MeasurableSet {p | P t p})
    (hzero : ∀ᵐ g ∂sourcePrior σ (δ • θ), P 0 ((), g))
    (hstep : ∀ t (h : History t) (g : E), P t (h, g) →
      ∀ᵐ z ∂sourceObservationKernel rows hmeas σ t (h, g), P (t + 1) ((h, z), g)) :
    ∀ t, ∀ᵐ p ∂enrichedSourceJoint rows hmeas σ δ θ t, P t p := by
  intro t
  induction t with
  | zero =>
    change ∀ᵐ p ∂(sourcePrior σ (δ • θ)).map (fun g => ((), g)), P 0 p
    exact (ae_map_iff (by fun_prop) (hP 0)).mpr hzero
  | succ t ih =>
    have hf : Measurable (fun p : (History t × E) × ℝ => ((p.1.1, p.2), p.1.2)) := by fun_prop
    change ∀ᵐ p ∂((enrichedSourceJoint rows hmeas σ δ θ t) ⊗ₘ
      sourceObservationKernel rows hmeas σ t).map
      (fun p : (History t × E) × ℝ => ((p.1.1, p.2), p.1.2)), P (t + 1) p
    apply (ae_map_iff hf.aemeasurable (hP (t + 1))).mpr
    apply Measure.ae_compProd_of_ae_ae ((hP (t + 1)).preimage hf)
    exact ih.mono (fun p hp => hstep t p.1 p.2 hp)

end PaperEnrichedGaussianOracleBridge


end
-- END EnrichedGaussianOracleBridge.lean

-- BEGIN LaplaceDensity.lean
section

/- Concatenation dependency: LaplaceMoments.lean. -/
namespace PaperLaplaceDensity

open MeasureTheory ProbabilityTheory Set PaperLaplace
open scoped ENNReal

theorem map_withDensity_involution
    {X : Type*} [MeasurableSpace X] (μ : Measure X) (T : X → X)
    (hT : Measurable T) (hInv : ∀ x, T (T x) = x) (hPres : μ.map T = μ)
    (f : X → ℝ≥0∞) (hf : Measurable f) :
    (μ.withDensity f).map T = μ.withDensity (fun x => f (T x)) := by
  apply Measure.ext
  intro E hE
  rw [Measure.map_apply hT hE, withDensity_apply _ (hE.preimage hT),
    withDensity_apply _ hE]
  rw [← lintegral_indicator (hE.preimage hT) f,
    ← lintegral_indicator hE (fun x => f (T x))]
  have hm := lintegral_map ((hf.comp hT).indicator hE) hT (μ := μ)
  rw [hPres] at hm
  change (∫⁻ x, E.indicator (fun y => f (T y)) x ∂μ) =
    ∫⁻ x, E.indicator (fun y => f (T y)) (T x) ∂μ at hm
  have heq : (fun x => E.indicator (fun y => f (T y)) (T x)) =
      (T ⁻¹' E).indicator f := by
    funext x
    by_cases hx : T x ∈ E <;> simp [Set.indicator, hx, hInv]
  rw [heq] at hm
  exact hm.symm

noncomputable def density (x : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal ((1 / 2 : ℝ) * Real.exp (-|x|))

theorem density_measurable : Measurable density := by
  unfold density
  fun_prop

theorem laplace_density : laplaceLaw = volume.withDensity density := by
  have hp : Measurable (gammaPDF 1 1) := (measurable_gammaPDFReal 1 1).ennreal_ofReal
  have hnp : Measurable (fun x : ℝ => gammaPDF 1 1 (-x)) := hp.comp measurable_neg
  have hhalf : Measurable ((1/2 : ℝ≥0∞) • gammaPDF 1 1) := by fun_prop
  have hneg : (expMeasure 1).map (fun x : ℝ => -x) =
      volume.withDensity (fun x => gammaPDF 1 1 (-x)) := by
    exact map_withDensity_involution volume (fun x : ℝ => -x) measurable_neg
      (fun x => neg_neg x) (Measure.map_neg_eq_self volume) (gammaPDF 1 1) hp
  rw [laplaceLaw, hneg]
  change (1/2 : ℝ≥0∞) • volume.withDensity (gammaPDF 1 1) +
    (1/2 : ℝ≥0∞) • volume.withDensity (fun x => gammaPDF 1 1 (-x)) = _
  rw [← withDensity_smul (1/2) hp,
    ← withDensity_smul (1/2) hnp,
    ← withDensity_add_left hhalf]
  apply withDensity_congr_ae
  filter_upwards [(volume : Measure ℝ).ae_ne 0] with x hx
  have hpdf (y : ℝ) : gammaPDF 1 1 y =
      ENNReal.ofReal (if 0 ≤ y then Real.exp (-y) else 0) := by
    simp [gammaPDF, gammaPDFReal, Real.Gamma_one]
  change (1/2 : ℝ≥0∞) * gammaPDF 1 1 x + (1/2 : ℝ≥0∞) * gammaPDF 1 1 (-x) = density x
  rw [hpdf x, hpdf (-x)]
  obtain hn | hp := hx.lt_or_gt
  · simp [density, hn.le, show ¬0 ≤ x by linarith, show 0 ≤ -x by linarith,
      abs_of_neg hn, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1/2)]
  · simp [density, hp.le, show ¬0 ≤ -x by linarith, abs_of_pos hp,
      ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1/2)]

end PaperLaplaceDensity


end
-- END LaplaceDensity.lean

-- BEGIN LaplaceScore.lean
section

namespace PaperLaplaceScore

open MeasureTheory Set Filter
open scoped Topology

noncomputable def kernel (h z v : ℝ) : ℝ := Real.exp (-|v - z| / h)

theorem kernel_pos (h z v : ℝ) : 0 < kernel h z v := Real.exp_pos _

theorem kernel_continuous (h : ℝ) : Continuous (fun p : ℝ × ℝ => kernel h p.1 p.2) := by
  unfold kernel
  fun_prop

theorem kernel_hasDerivAt (h z v : ℝ) (hv : v ≠ z) :
    HasDerivAt (fun x => kernel h x v) (kernel h z v * Real.sign (v - z) / h) z := by
  have hs : (SignType.sign (v - z) : ℝ) = Real.sign (v - z) := by
    rcases lt_trichotomy (v - z) 0 with ht | ht | ht
    · simp [sign_neg ht, Real.sign_of_neg ht]
    · simp [ht]
    · simp [sign_pos ht, Real.sign_of_pos ht]
  have ha := (hasDerivAt_abs (sub_ne_zero.mpr hv)).comp z ((hasDerivAt_const z v).sub (hasDerivAt_id z))
  have he := ((ha.neg).div_const h).exp
  simpa only [kernel, hs, Function.comp_def, Pi.neg_apply, zero_sub, mul_neg,
    mul_one, neg_neg, mul_div_assoc] using he

theorem log_kernel_distance_bound (h z z₀ v : ℝ) (hh : 0 < h) :
    |(-|v - z| / h) - (-|v - z₀| / h)| ≤ |z - z₀| / h := by
  have ha := abs_abs_sub_abs_le_abs_sub (v - z) (v - z₀)
  have he : |(v - z) - (v - z₀)| = |z - z₀| := by
    have he' : (v - z) - (v - z₀) = -(z - z₀) := by ring
    rw [he', abs_neg]
  rw [he] at ha
  have he' : (-|v - z| / h) - (-|v - z₀| / h) =
      -((|v - z| - |v - z₀|) / h) := by ring
  rw [he', abs_neg, abs_div, abs_of_pos hh]
  exact div_le_div_of_nonneg_right ha hh.le

theorem exp_lipschitzOn_Iic (B : ℝ) :
    LipschitzOnWith ⟨Real.exp B, (Real.exp_pos B).le⟩ Real.exp (Iic B) := by
  apply (convex_Iic B).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
    (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt)
  intro x hx
  change ‖Real.exp x‖ ≤ Real.exp B
  rw [Real.norm_of_nonneg (Real.exp_pos x).le]
  exact Real.exp_le_exp.mpr hx

theorem kernel_local_difference (h z z₀ v : ℝ) (hh : 0 < h)
    (hz : z ∈ Metric.ball z₀ h) :
    |kernel h z v - kernel h z₀ v| ≤
      (Real.exp 1 / h) * kernel h z₀ v * |z - z₀| := by
  let a : ℝ := -|v - z| / h
  let b : ℝ := -|v - z₀| / h
  have hab : |a - b| ≤ |z - z₀| / h := log_kernel_distance_bound h z z₀ v hh
  have hz' : |z - z₀| < h := by simpa [Metric.mem_ball, Real.dist_eq] using hz
  have hab1 : |a - b| < 1 := hab.trans_lt ((div_lt_one hh).mpr hz')
  have hbound := (exp_lipschitzOn_Iic 1).dist_le_mul
    (a - b) (show a - b ∈ Iic (1 : ℝ) from (le_abs_self _).trans hab1.le)
    0 (by norm_num)
  simp only [Real.dist_eq, sub_zero, Real.exp_zero] at hbound
  have heq : kernel h z v - kernel h z₀ v = kernel h z₀ v * (Real.exp (a - b) - 1) := by
    change Real.exp a - Real.exp b = Real.exp b * (Real.exp (a - b) - 1)
    rw [Real.exp_sub]
    field_simp
  rw [heq, abs_mul, abs_of_pos (kernel_pos h z₀ v)]
  calc
    kernel h z₀ v * |Real.exp (a - b) - 1| ≤
        kernel h z₀ v * (Real.exp 1 * |a - b|) :=
      mul_le_mul_of_nonneg_left hbound (kernel_pos h z₀ v).le
    _ ≤ kernel h z₀ v * (Real.exp 1 * (|z - z₀| / h)) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hab (Real.exp_pos 1).le) (kernel_pos h z₀ v).le
    _ = _ := by ring

theorem real_sign_measurable : Measurable (Real.sign : ℝ → ℝ) := by
  unfold Real.sign
  exact Measurable.ite (measurableSet_lt measurable_id measurable_const) measurable_const
    (Measurable.ite (measurableSet_lt measurable_const measurable_id) measurable_const measurable_const)

theorem kernelIntegral_hasDerivAt (F : ℝ → ℝ) (hF : Measurable F)
    (h z₀ : ℝ) (hh : 0 < h) (hweighted : Integrable (fun v => F v * kernel h z₀ v)) :
    Integrable (fun v => F v * kernel h z₀ v * Real.sign (v - z₀) / h) ∧
      HasDerivAt (fun z => ∫ v, F v * kernel h z v)
        (∫ v, F v * kernel h z₀ v * Real.sign (v - z₀) / h) z₀ := by
  let d : ℝ → ℝ := fun v => F v * kernel h z₀ v * Real.sign (v - z₀) / h
  let L : ℝ →L[ℝ] ℝ →L[ℝ] ℝ := ContinuousLinearMap.smulRightL ℝ ℝ ℝ 1
  let bound : ℝ → ℝ := fun v => (Real.exp 1 / h) * |F v * kernel h z₀ v|
  have hkernel : ∀ z, Measurable (fun v => kernel h z v) := fun z =>
    (kernel_continuous h).measurable.comp (measurable_const.prodMk measurable_id)
  have hdmeas : Measurable d :=
    (((hF.mul (hkernel z₀)).mul
      (real_sign_measurable.comp (measurable_id.sub_const z₀))).div_const h)
  have hbound : Integrable bound := by
    exact hweighted.norm.const_mul (Real.exp 1 / h)
  have hdiff : ∀ᵐ v : ℝ, HasFDerivAt (fun z => F v * kernel h z v) (L (d v)) z₀ := by
    filter_upwards [volume.ae_ne z₀] with v hv
    have hdv : HasDerivAt (fun z => F v * kernel h z v) (d v) z₀ := by
      have hdv' := (kernel_hasDerivAt h z₀ v hv).const_mul (F v)
      have he : F v * (kernel h z₀ v * Real.sign (v - z₀) / h) = d v := by
        dsimp [d]
        ring
      rw [he] at hdv'
      exact hdv'
    exact hdv.hasFDerivAt
  have hlocal : ∀ᵐ v : ℝ, ∀ z ∈ Metric.ball z₀ h,
      ‖F v * kernel h z v - F v * kernel h z₀ v‖ ≤ bound v * ‖z - z₀‖ := by
    apply Filter.Eventually.of_forall
    intro v z hz
    rw [Real.norm_eq_abs, ← mul_sub, abs_mul, Real.norm_eq_abs]
    calc
      |F v| * |kernel h z v - kernel h z₀ v| ≤
          |F v| * ((Real.exp 1 / h) * kernel h z₀ v * |z - z₀|) :=
        mul_le_mul_of_nonneg_left (kernel_local_difference h z z₀ v hh hz) (abs_nonneg _)
      _ = bound v * |z - z₀| := by
        dsimp [bound]
        rw [abs_mul, abs_of_pos (kernel_pos h z₀ v)]
        ring
  obtain ⟨hdint, hderiv⟩ := hasFDerivAt_integral_of_dominated_loc_of_lip'
    (μ := (volume : Measure ℝ)) (F := fun z v => F v * kernel h z v)
    (F' := fun v => L (d v)) (bound := bound) (Metric.ball_mem_nhds z₀ hh)
    (fun z _ => (hF.mul (hkernel z)).aestronglyMeasurable) hweighted
    (L.continuous.measurable.comp hdmeas).aestronglyMeasurable hlocal hbound hdiff
  have hdreal : Integrable d := by
    simpa [L] using (ContinuousLinearMap.apply ℝ ℝ (1 : ℝ)).integrable_comp hdint
  refine ⟨hdreal, ?_⟩
  have hscalar := hderiv.hasDerivAt
  rw [ContinuousLinearMap.integral_apply hdint 1] at hscalar
  simpa [L] using hscalar

theorem integral_affine_change (g : ℝ → ℝ) (h z : ℝ) (hh : 0 < h) :
    (∫ v, g v) = h * ∫ u, g (z + h * u) := by
  symm
  rw [Measure.integral_comp_mul_left (fun v => g (z + v)) h,
    integral_add_left_eq_self g z, smul_eq_mul, abs_of_pos (inv_pos.mpr hh)]
  rw [← mul_assoc, mul_inv_cancel₀ hh.ne', one_mul]

theorem integrable_affine_change_iff (g : ℝ → ℝ) (h z : ℝ) (hh : 0 < h) :
    Integrable (fun u => g (z + h * u)) ↔ Integrable g := by
  constructor
  · intro hg
    have ht := (integrable_comp_mul_left_iff (fun v => g (z + v)) hh.ne').mp hg
    have hr := ht.comp_add_left (-z)
    simpa only [add_neg_cancel_left] using hr
  · intro hg
    exact (hg.comp_add_left z).comp_mul_left' hh.ne'

theorem kernel_affine (h z u : ℝ) (hh : 0 < h) :
    kernel h z (z + h * u) = Real.exp (-|u|) := by
  unfold kernel
  have he : z + h * u - z = h * u := by ring
  rw [he, abs_mul, abs_of_pos hh]
  congr 1
  field_simp

end PaperLaplaceScore


end
-- END LaplaceScore.lean

-- BEGIN LaplaceScoreBridge.lean
section

namespace PaperLaplaceScoreBridge

open MeasureTheory ProbabilityTheory PaperLaplace PaperLaplaceDensity PaperLaplaceScore PaperProductVariance
open scoped ENNReal

theorem density_toReal (u : ℝ) : (density u).toReal = (1 / 2 : ℝ) * Real.exp (-|u|) := by
  unfold density
  exact ENNReal.toReal_ofReal (by positivity)

theorem law_integral (g : ℝ → ℝ) :
    (∫ u, g u ∂laplaceLaw) = ∫ u, ((1 / 2 : ℝ) * Real.exp (-|u|)) * g u := by
  rw [laplace_density]
  have ht : ∀ᵐ u : ℝ, density u < ∞ :=
    Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)
  rw [integral_withDensity_eq_integral_toReal_smul density_measurable ht]
  simp only [smul_eq_mul, density_toReal]

theorem law_integrable_iff (g : ℝ → ℝ) :
    Integrable g laplaceLaw ↔
      Integrable (fun u => ((1 / 2 : ℝ) * Real.exp (-|u|)) * g u) := by
  rw [laplace_density]
  have ht : ∀ᵐ u : ℝ, density u < ∞ :=
    Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)
  rw [integrable_withDensity_iff_integrable_smul' density_measurable ht]
  simp only [smul_eq_mul, density_toReal]

theorem raw_weight_integral (g : ℝ → ℝ) :
    (∫ u, Real.exp (-|u|) * g u) = 2 * ∫ u, g u ∂laplaceLaw := by
  have he : (fun u => ((1 / 2 : ℝ) * Real.exp (-|u|)) * g u) =
      fun u => (1 / 2 : ℝ) * (Real.exp (-|u|) * g u) := by ext u; ring
  have hi := law_integral g
  rw [he, integral_const_mul] at hi
  linarith

theorem affine_value_memLp (F : ℝ → ℝ) (hF : LipschitzWith 1 F) (h z : ℝ) :
    MemLp (fun u : ℝ => F (z + h * u)) 2 laplaceLaw := by
  have hX : MemLp (fun u : ℝ => z + h * u) 2 laplaceLaw :=
    (memLp_const z).add (laplace_id_memLp_two.const_smul h)
  exact lipschitz_memLp_two laplaceLaw _ hX F hF

theorem kernel_weight_integrable_of_lipschitz (F : ℝ → ℝ) (hF : LipschitzWith 1 F)
    (h z : ℝ) (hh : 0 < h) : Integrable (fun v => F v * kernel h z v) := by
  have hi := (law_integrable_iff (fun u => F (z + h * u))).mp
    ((affine_value_memLp F hF h z).integrable (by norm_num))
  have hraw := hi.const_mul (2 : ℝ)
  have ht : Integrable (fun u => F (z + h * u) * kernel h z (z + h * u)) := by
    convert hraw using 1
    ext u
    rw [kernel_affine h z u hh]
    ring
  exact (integrable_affine_change_iff _ h z hh).mp ht

theorem kernel_integral_eq_expectation (F : ℝ → ℝ) (h z : ℝ) (hh : 0 < h) :
    (∫ v, F v * kernel h z v) = 2 * h * ∫ u, F (z + h * u) ∂laplaceLaw := by
  rw [integral_affine_change _ h z hh]
  simp_rw [kernel_affine h z _ hh]
  have he : (fun u => F (z + h * u) * Real.exp (-|u|)) =
      fun u => Real.exp (-|u|) * F (z + h * u) := by ext u; ring
  rw [he, raw_weight_integral]
  ring

theorem sign_affine (h z u : ℝ) (hh : 0 < h) :
    Real.sign (z + h * u - z) = Real.sign u := by
  have he : z + h * u - z = h * u := by ring
  rw [he]
  rcases lt_trichotomy u 0 with hu | hu | hu
  · rw [Real.sign_of_neg (mul_neg_of_pos_of_neg hh hu), Real.sign_of_neg hu]
  · simp [hu]
  · rw [Real.sign_of_pos (mul_pos hh hu), Real.sign_of_pos hu]

theorem kernel_score_integral_eq_expectation (F : ℝ → ℝ) (h z : ℝ) (hh : 0 < h) :
    (∫ v, F v * kernel h z v * Real.sign (v - z) / h) =
      2 * ∫ u, F (z + h * u) * Real.sign u ∂laplaceLaw := by
  rw [integral_affine_change _ h z hh]
  simp_rw [kernel_affine h z _ hh, sign_affine h z _ hh]
  rw [integral_div]
  have he : (fun u => F (z + h * u) * Real.exp (-|u|) * Real.sign u) =
      fun u => Real.exp (-|u|) * (F (z + h * u) * Real.sign u) := by ext u; ring
  rw [he, raw_weight_integral]
  field_simp

theorem laplace_smoothing_hasDerivAt (F : ℝ → ℝ) (hF : LipschitzWith 1 F)
    (h z : ℝ) (hh : 0 < h) :
    HasDerivAt (fun x => ∫ u, F (x + h * u) ∂laplaceLaw)
      ((∫ u, F (z + h * u) * Real.sign u ∂laplaceLaw) / h) z := by
  have hc := kernelIntegral_hasDerivAt F hF.continuous.measurable h z hh
    (kernel_weight_integrable_of_lipschitz F hF h z hh)
  have hd := hc.2.div_const (2 * h)
  rw [kernel_score_integral_eq_expectation F h z hh] at hd
  have hSlope : (2 * ∫ u, F (z + h * u) * Real.sign u ∂laplaceLaw) / (2 * h) =
      (∫ u, F (z + h * u) * Real.sign u ∂laplaceLaw) / h := by field_simp
  rw [hSlope] at hd
  have hfun : (fun x => ∫ u, F (x + h * u) ∂laplaceLaw) =
      fun x => (∫ v, F v * kernel h x v) / (2 * h) := by
    funext x
    rw [kernel_integral_eq_expectation F h x hh]
    field_simp
  rw [hfun]
  exact hd

theorem abs_sign_le_one (u : ℝ) : |Real.sign u| ≤ 1 := by
  rcases Real.sign_apply_eq u with hu | hu | hu <;> rw [hu] <;> norm_num

theorem affine_score_integrable (F : ℝ → ℝ) (hF : LipschitzWith 1 F) (h z : ℝ) :
    Integrable (fun u => F (z + h * u) * Real.sign u) laplaceLaw := by
  exact ((affine_value_memLp F hF h z).integrable (by norm_num)).mul_bdd
    real_sign_measurable.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun u => by simpa only [Real.norm_eq_abs] using abs_sign_le_one u))

theorem reflected_score_integral (F : ℝ → ℝ) (hF : LipschitzWith 1 F) (h z : ℝ) :
    (∫ u, F (z - h * u) * Real.sign u ∂laplaceLaw) =
      -(∫ u, F (z + h * u) * Real.sign u ∂laplaceLaw) := by
  have hgm : Measurable (fun u => F (z - h * u) * Real.sign u) :=
    (hF.continuous.measurable.comp
      (measurable_const.sub (measurable_const.mul measurable_id))).mul real_sign_measurable
  calc
    _ = ∫ u, F (z - h * u) * Real.sign u ∂laplaceLaw.map (fun u : ℝ => -u) := by
      rw [laplace_reflection]
    _ = ∫ u, F (z - h * (-u)) * Real.sign (-u) ∂laplaceLaw := by
      rw [integral_map measurable_neg.aemeasurable hgm.aestronglyMeasurable]
    _ = _ := by
      simp only [mul_neg, sub_neg_eq_add, Real.sign_neg]
      rw [integral_neg]

noncomputable def centralEstimator (F : ℝ → ℝ) (z h u : ℝ) : ℝ :=
  (F (z + h * u) - F (z - h * u)) / (2 * h) * Real.sign u

theorem centralEstimator_integrable (F : ℝ → ℝ) (hF : LipschitzWith 1 F) (h z : ℝ) :
    Integrable (centralEstimator F z h) laplaceLaw := by
  have hp := affine_score_integrable F hF h z
  have hn := affine_score_integrable F hF (-h) z
  have hi := (hp.sub hn).div_const (2 * h)
  convert hi using 1
  ext u
  simp only [centralEstimator, Pi.sub_apply, neg_mul, sub_eq_add_neg]
  ring

theorem centralEstimator_integral (F : ℝ → ℝ) (hF : LipschitzWith 1 F)
    (h z : ℝ) (hh : 0 < h) :
    (∫ u, centralEstimator F z h u ∂laplaceLaw) =
      (∫ u, F (z + h * u) * Real.sign u ∂laplaceLaw) / h := by
  have hp := affine_score_integrable F hF h z
  have hn : Integrable (fun u => F (z - h * u) * Real.sign u) laplaceLaw := by
    simpa only [neg_mul, sub_eq_add_neg] using affine_score_integrable F hF (-h) z
  have he : (fun u => centralEstimator F z h u) =
      fun u => (F (z + h * u) * Real.sign u - F (z - h * u) * Real.sign u) / (2 * h) := by
    ext u
    unfold centralEstimator
    ring
  rw [he, integral_div, integral_sub hp hn, reflected_score_integral F hF h z]
  field_simp
  ring

theorem laplace_smoothing_hasDerivAt_centralEstimator (F : ℝ → ℝ) (hF : LipschitzWith 1 F)
    (h z : ℝ) (hh : 0 < h) :
    HasDerivAt (fun x => ∫ u, F (x + h * u) ∂laplaceLaw)
      (∫ u, centralEstimator F z h u ∂laplaceLaw) z := by
  rw [centralEstimator_integral F hF h z hh]
  exact laplace_smoothing_hasDerivAt F hF h z hh

end PaperLaplaceScoreBridge


end
-- END LaplaceScoreBridge.lean

-- BEGIN ProductDensity.lean
section

namespace PaperProductDensity

open MeasureTheory Set
open scoped ENNReal

theorem pi_withDensity_ofReal {ι X : Type*} [Fintype ι] [MeasurableSpace X]
    (μ : ι → Measure X) [∀ i, SigmaFinite (μ i)] (w : ι → X → ℝ)
    (hw : ∀ i, Integrable (w i) (μ i)) (hwnonneg : ∀ i x, 0 ≤ w i x) :
    Measure.pi (fun i => (μ i).withDensity (fun x => ENNReal.ofReal (w i x))) =
      (Measure.pi μ).withDensity (fun x => ENNReal.ofReal (∏ i, w i (x i))) := by
  classical
  haveI : ∀ i, IsFiniteMeasure ((μ i).withDensity (fun x => ENNReal.ofReal (w i x))) := by
    intro i
    apply isFiniteMeasure_withDensity
    rw [← ofReal_integral_eq_lintegral_ofReal (hw i)
      (Filter.Eventually.of_forall (hwnonneg i))]
    exact ENNReal.ofReal_ne_top
  apply Measure.pi_eq
  intro s hs
  let φ : ι → X → ℝ := fun i => (s i).indicator (w i)
  have hφ : ∀ i, Integrable (φ i) (μ i) := fun i => (hw i).indicator (hs i)
  have hφnonneg : ∀ i x, 0 ≤ φ i x := by
    intro i x
    by_cases hx : x ∈ s i <;> simp [φ, hx, hwnonneg]
  have hprod : Integrable (fun x : ι → X => ∏ i, φ i (x i)) (Measure.pi μ) :=
    Integrable.fintype_prod hφ
  have hbox : MeasurableSet (Set.pi Set.univ s) := MeasurableSet.univ_pi hs
  rw [withDensity_apply _ hbox, ← lintegral_indicator hbox]
  have hind : (Set.pi Set.univ s).indicator
      (fun x : ι → X => ENNReal.ofReal (∏ i, w i (x i))) =
      fun x => ENNReal.ofReal (∏ i, φ i (x i)) := by
    ext x
    by_cases hx : x ∈ Set.pi Set.univ s
    · rw [Set.indicator_of_mem hx]
      congr 1
      apply Finset.prod_congr rfl
      intro i _
      rw [show φ i (x i) = w i (x i) from Set.indicator_of_mem (hx i (Set.mem_univ i)) _]
    · rw [Set.indicator_of_notMem hx]
      have hex : ∃ i, x i ∉ s i := by
        by_contra h
        push Not at h
        exact hx (fun i _ => h i)
      obtain ⟨i, hi⟩ := hex
      have hz : ∏ j, φ j (x j) = 0 := by
        apply Finset.prod_eq_zero (Finset.mem_univ i)
        exact Set.indicator_of_notMem hi _
      rw [hz, ENNReal.ofReal_zero]
  rw [hind, ← ofReal_integral_eq_lintegral_ofReal hprod
    (Filter.Eventually.of_forall (fun x => Finset.prod_nonneg (fun i _ => hφnonneg i (x i)))),
    integral_fintype_prod_eq_prod,
    ENNReal.ofReal_prod_of_nonneg (fun i _ => integral_nonneg (hφnonneg i))]
  apply Finset.prod_congr rfl
  intro i _
  rw [withDensity_apply _ (hs i),
    ← ofReal_integral_eq_lintegral_ofReal ((hw i).restrict)
      (Filter.Eventually.of_forall (hwnonneg i))]
  congr 1
  exact integral_indicator (hs i)

end PaperProductDensity


end
-- END ProductDensity.lean

-- BEGIN ProductLaplaceDensity.lean
section

/-! The genuine finite product Laplace density and its exact translation ratio.
Dependencies by concatenation: LaplaceMoments, LaplaceDensity, ProductDensity.
The law remains the existing product of independent one-dimensional Laplace laws.
-/
noncomputable section
namespace PaperProductLaplaceDensity
open MeasureTheory Set
open scoped ENNReal
open PaperLaplace PaperLaplaceDensity PaperProductDensity

def mass {n : ℕ} (u : Fin n → ℝ) : ℝ := ∑ i, |u i|

def rho (n : ℕ) (u : Fin n → ℝ) : ℝ := (1/2 : ℝ)^n * Real.exp (-mass u)

def ratio {n : ℕ} (c u : Fin n → ℝ) : ℝ := Real.exp (mass u - mass (u-c))

def scalarDensity (x : ℝ) : ℝ := (1/2 : ℝ) * Real.exp (-|x|)

theorem scalarDensity_pos (x : ℝ) : 0 < scalarDensity x := by unfold scalarDensity; positivity

theorem density_toReal (x : ℝ) : (density x).toReal = scalarDensity x := by
  unfold density
  exact ENNReal.toReal_ofReal (scalarDensity_pos x).le

theorem scalarDensity_integrable : Integrable scalarDensity (volume : Measure ℝ) := by
  have hi : Integrable (fun _ : ℝ => (1:ℝ)) laplaceLaw := integrable_const 1
  rw [laplace_density] at hi
  have ht : ∀ᵐ x : ℝ, density x < ∞ := Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)
  rw [integrable_withDensity_iff_integrable_smul' density_measurable ht] at hi
  simpa only [smul_eq_mul, density_toReal, mul_one] using hi

theorem scalarDensity_prod (n : ℕ) (u : Fin n → ℝ) :
    (∏ i, scalarDensity (u i)) = rho n u := by
  simp only [scalarDensity, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin, ← Real.exp_sum, Finset.sum_neg_distrib, rho, mass]

theorem rho_continuous (n : ℕ) : Continuous (rho n) := by
  unfold rho mass
  fun_prop

theorem ratio_continuous {n : ℕ} (c : Fin n → ℝ) : Continuous (ratio c) := by
  unfold ratio mass
  fun_prop

theorem rho_pos (n : ℕ) (u : Fin n → ℝ) : 0 < rho n u := by unfold rho; positivity

theorem ratio_pos {n : ℕ} (c u : Fin n → ℝ) : 0 < ratio c u := Real.exp_pos _

/-- Independent coordinate laws have exactly the normalized product density. -/
theorem productLaw_density (n : ℕ) :
    productLaw n = (volume : Measure (Fin n → ℝ)).withDensity (fun u => ENNReal.ofReal (rho n u)) := by
  unfold productLaw
  simp_rw [laplace_density]
  change Measure.pi (fun _ : Fin n => (volume : Measure ℝ).withDensity
      (fun x => ENNReal.ofReal (scalarDensity x))) =
    (Measure.pi (fun _ : Fin n => (volume : Measure ℝ))).withDensity (fun u => ENNReal.ofReal (rho n u))
  rw [pi_withDensity_ofReal (fun _ : Fin n => (volume : Measure ℝ))
    (fun _ => scalarDensity) (fun _ => scalarDensity_integrable) (fun _ x => (scalarDensity_pos x).le)]
  congr 1
  funext u
  rw [scalarDensity_prod]

theorem law_integral (n : ℕ) (g : (Fin n → ℝ) → ℝ) :
    (∫ u, g u ∂productLaw n) = ∫ u, rho n u * g u := by
  rw [productLaw_density]
  have hm := (rho_continuous n).measurable.ennreal_ofReal
  have ht : ∀ᵐ u : Fin n → ℝ, ENNReal.ofReal (rho n u) < ∞ :=
    Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)
  rw [integral_withDensity_eq_integral_toReal_smul hm ht]
  simp only [smul_eq_mul, ENNReal.toReal_ofReal (rho_pos n _).le]

theorem law_integrable_iff (n : ℕ) (g : (Fin n → ℝ) → ℝ) :
    Integrable g (productLaw n) ↔ Integrable (fun u => rho n u * g u) := by
  rw [productLaw_density]
  have hm := (rho_continuous n).measurable.ennreal_ofReal
  have ht : ∀ᵐ u : Fin n → ℝ, ENNReal.ofReal (rho n u) < ∞ :=
    Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)
  rw [integrable_withDensity_iff_integrable_smul' hm ht]
  simp only [smul_eq_mul, ENNReal.toReal_ofReal (rho_pos n _).le]

theorem rho_mul_ratio {n : ℕ} (c u : Fin n → ℝ) : rho n u * ratio c u = rho n (u-c) := by
  unfold rho ratio
  rw [mul_assoc, ← Real.exp_add]
  congr 1
  congr 1
  ring

/-- Translation of a Haar-density measure in the actual finite coordinate space. -/
theorem map_withDensity_add (n : ℕ) (f : (Fin n → ℝ) → ℝ≥0∞) (c : Fin n → ℝ) :
    ((volume : Measure (Fin n → ℝ)).withDensity f).map (fun u => u+c) =
      volume.withDensity (fun u => f (u-c)) := by
  have hAdd : Measurable (fun u : Fin n → ℝ => u+c) := measurable_id.add_const c
  apply Measure.ext
  intro E hE
  rw [Measure.map_apply hAdd hE, withDensity_apply _ (hE.preimage hAdd), withDensity_apply _ hE]
  rw [← lintegral_indicator (hE.preimage hAdd) f,
    ← lintegral_indicator hE (fun u => f (u-c))]
  have hh := lintegral_add_right_eq_self (μ:= (volume : Measure (Fin n → ℝ)))
    (E.indicator (fun u => f (u-c))) c
  have he : (fun u => E.indicator (fun v => f (v-c)) (u+c)) =
      ((fun u => u+c) ⁻¹' E).indicator f := by
    funext u
    by_cases hu : u+c ∈ E <;> simp [Set.indicator, hu]
  rw [he] at hh
  exact hh

/-- The likelihood ratio has the sign appropriate to the pushforward U ↦ U+c. -/
theorem productLaw_map_add {n : ℕ} (c : Fin n → ℝ) :
    (productLaw n).map (fun u => u+c) =
      (productLaw n).withDensity (fun u => ENNReal.ofReal (ratio c u)) := by
  rw [productLaw_density, map_withDensity_add]
  rw [← withDensity_mul _ (rho_continuous n).measurable.ennreal_ofReal
    (ratio_continuous c).measurable.ennreal_ofReal]
  congr 1
  funext u
  change ENNReal.ofReal (rho n (u-c)) = ENNReal.ofReal (rho n u) * ENNReal.ofReal (ratio c u)
  rw [← ENNReal.ofReal_mul (rho_pos n u).le, rho_mul_ratio]

/-- Exact relative-shift identity. It is valid for every real-valued g; Bochner
integrals use their usual zero convention when not integrable. -/
theorem relative_shift_integral {n : ℕ} (c : Fin n → ℝ) (g : (Fin n → ℝ) → ℝ) :
    (∫ u, g (u+c) ∂productLaw n) = ∫ u, g u * ratio c u ∂productLaw n := by
  rw [law_integral, law_integral]
  have hL : (fun u => rho n u * g (u+c)) =
      fun u => (g (u+c) * rho n ((u+c)-c)) := by
    funext u; simp only [add_sub_cancel_right]; ring
  have hR : (fun u => rho n u * (g u * ratio c u)) =
      fun u => g u * rho n (u-c) := by
    funext u; rw [← rho_mul_ratio c u]; ring
  rw [hL, hR]
  exact integral_add_right_eq_self (fun u => g u * rho n (u-c)) c

def smoothing {n : ℕ} (F : (Fin n → ℝ) → ℝ) (h : ℝ) (z : Fin n → ℝ) : ℝ :=
  ∫ u, F (z + h • u) ∂productLaw n

/-- The smoothing shift and the density ratio share the same positive t/h sign. -/
theorem smoothing_shift {n : ℕ} (F : (Fin n → ℝ) → ℝ)
    (h : ℝ) (hh : h ≠ 0) (z v : Fin n → ℝ) (t : ℝ) :
    smoothing F h (z + t • v) =
      ∫ u, F (z + h • u) * ratio ((t/h) • v) u ∂productLaw n := by
  have he : (fun u : Fin n → ℝ => F ((z + t • v) + h • u)) =
      fun u => F (z + h • (u + (t/h) • v)) := by
    funext u
    congr 1
    ext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    field_simp [hh]
    ring
  unfold smoothing
  rw [he]
  exact relative_shift_integral ((t/h) • v) (fun u => F (z + h • u))

abbrev L1Point (n : ℕ) := PiLp 1 (fun _ : Fin n => ℝ)

def smoothingL1 {n : ℕ} (F : L1Point n → ℝ) (h : ℝ) (z : L1Point n) : ℝ :=
  ∫ u : Fin n → ℝ, F (z + h • WithLp.toLp 1 u) ∂productLaw n

/-- The same identity directly at the actual l1 target objective type. -/
theorem smoothingL1_shift {n : ℕ} (F : L1Point n → ℝ)
    (h : ℝ) (hh : h ≠ 0) (z v : L1Point n) (t : ℝ) :
    smoothingL1 F h (z + t • v) =
      ∫ u : Fin n → ℝ, F (z + h • WithLp.toLp 1 u) *
        ratio (fun i => (t/h) * v i) u ∂productLaw n := by
  have he : (fun u : Fin n → ℝ => F ((z + t • v) + h • WithLp.toLp 1 u)) =
      fun u => F (z + h • WithLp.toLp 1 (u + fun i => (t/h) * v i)) := by
    funext u
    congr 1
    ext i
    change (z i + t*v i) + h*u i = z i + h*(u i + (t/h)*v i)
    field_simp [hh]
    ring
  unfold smoothingL1
  rw [he]
  exact relative_shift_integral (fun i => (t/h)*v i) (fun u => F (z + h • WithLp.toLp 1 u))

end PaperProductLaplaceDensity

end
end
-- END ProductLaplaceDensity.lean

-- BEGIN ProductLaplaceAE.lean
section

/-! Atomlessness and the true almost-sure nonzero-coordinate condition for the
product Laplace law. Dependencies: LaplaceMoments and LaplaceDensity. -/
namespace PaperProductLaplaceAE
open MeasureTheory
open PaperLaplace PaperLaplaceDensity

instance laplace_nullSingleton : NullSingletonClass laplaceLaw := by
  rw [laplace_density]
  infer_instance

theorem laplace_singleton_zero (x : ℝ) : laplaceLaw {x} = 0 := measure_singleton x

theorem coordinate_zero_measure (n : ℕ) (i : Fin n) :
    (productLaw n) {u : Fin n → ℝ | u i = 0} = 0 := by
  have hp : MeasurePreserving (Function.eval i) (productLaw n) laplaceLaw :=
    measurePreserving_eval (μ := fun _ : Fin n => laplaceLaw) i
  have hh := congrArg (fun μ : Measure ℝ => μ {0}) hp.map_eq
  rw [Measure.map_apply (measurable_pi_apply i) (measurableSet_singleton 0), measure_singleton] at hh
  exact hh

theorem ae_coordinates_ne_zero (n : ℕ) :
    ∀ᵐ u ∂productLaw n, ∀ i : Fin n, u i ≠ 0 := by
  rw [ae_all_iff]
  intro i
  apply ae_iff.2
  simpa only [not_not] using coordinate_zero_measure n i

end PaperProductLaplaceAE


end
-- END ProductLaplaceAE.lean

-- BEGIN UpperEnvelope.lean
section

/- Dependencies: Composition.lean and OracleModel.lean.
This closes the quantitative upper-envelope assembly from actual admissible
algorithm budgets. It does not postulate or prove the two component algorithms.
The second is the manuscript's external Protasov input; the first still needs
the constructed two-query Laplace policy and its error analysis. -/
namespace Task003.UpperEnvelope

open Task003.OracleModel CompositionAudit

theorem upper_log_bounds {d α : ℝ} (hd : 1 ≤ d) (ha : 0 < α) (ha1 : α ≤ 1) :
    1 ≤ Lambda d α ∧ Real.log (2*d) ≤ Lambda d α ∧
    Real.log (d+1) ≤ Lambda d α ∧ Real.log (4/α) ≤ 2*Lambda d α := by
  have hdpos : 0 < d := by linarith
  have he : ell d = 1 + Real.log d := log_e_mul hdpos
  have hl : Lambda d α = ell d + (1 + Real.log (A α)) := by
    unfold Lambda
    rw [log_e_div ha]
  have hdlog : 0 ≤ Real.log d := Real.log_nonneg hd
  have haInv : 1 ≤ A α := (one_le_inv₀ ha).mpr ha1
  have halog : 0 ≤ Real.log (A α) := Real.log_nonneg haInv
  have htlog : Real.log (2:ℝ) ≤ 1 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
    linarith
  have htd : Real.log (2*d) = Real.log 2 + Real.log d :=
    Real.log_mul (by norm_num) hdpos.ne'
  have he2 : (2:ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1:ℝ)]
  have hdadd : d+1 ≤ Real.exp 1 * d := by nlinarith
  have hsmall : Real.log (d+1) ≤ ell d :=
    Real.log_le_log (by linarith) hdadd
  have hfour : Real.log (4/α) = 2*Real.log 2 + Real.log (A α) := by
    rw [div_eq_mul_inv, Real.log_mul (by norm_num) (inv_ne_zero ha.ne'),
      show (4:ℝ)=2^2 by norm_num, Real.log_pow]
    rfl
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

/-- A concrete fixed constant controls the exact natural ceiling budget. -/
theorem coarse_ceiling_bound {d α : ℝ} (hd : 1 ≤ d) (ha : 0 < α) (ha1 : α ≤ 1)
    (hcoarse : A α ^ 2 ≤ d) :
    ((2 * ⌈576*d*(A α)^2*Real.log (2*d)⌉₊ : ℕ) : ℝ) ≤
      1154 * q d α * (Lambda d α)^2 := by
  have hdpos : 0 < d := by linarith
  obtain ⟨hl1,hlog,_,_⟩ := upper_log_bounds hd ha ha1
  have hlogs : 0 ≤ Real.log (2*d) := Real.log_nonneg (by linarith)
  have hA : 1 ≤ A α := (one_le_inv₀ ha).mpr ha1
  have hq : q d α = d * (A α)^2 := by simp [q,M,min_eq_right hcoarse]
  have hq1 : 1 ≤ q d α := by rw [hq]; nlinarith
  have hnneg : 0 ≤ 576*d*(A α)^2*Real.log (2*d) := by positivity
  have hceil : (⌈576*d*(A α)^2*Real.log (2*d)⌉₊ : ℝ) ≤
      576*d*(A α)^2*Real.log (2*d)+1 :=
    le_of_lt (Nat.ceil_lt_add_one hnneg)
  have hLsq : Lambda d α ≤ (Lambda d α)^2 := by nlinarith
  have hqL : 1 ≤ q d α * (Lambda d α)^2 := by nlinarith
  have hlogMul := mul_le_mul_of_nonneg_left (hlog.trans hLsq)
    (show 0 ≤ q d α by linarith)
  push_cast
  have hscale : 576*d*(A α)^2*Real.log (2*d) = 576*q d α*Real.log (2*d) := by
    rw [hq]
    ring
  rw [hscale] at hceil ⊢
  nlinarith

/-- Proposition1 in actual admissible-budget form, from the two explicit
component budget witnesses. Neither a minimax upper bracket nor the conclusion
of Proposition1 is assumed. -/
theorem admissible_upper_envelope (C2 : ℝ) (hC2 : 0 ≤ C2)
    (hU1 : ∀ (d : ℕ) (α : ℝ), 1 ≤ d → 0 < α → α ≤ 1 →
      AdmissibleBudget d (2 * ⌈576*(d:ℝ)*(A α)^2*Real.log (2*(d:ℝ))⌉₊) 1 1 α)
    (hU2 : ∀ (d : ℕ) (α : ℝ), 1 ≤ d → 0 < α → α ≤ 1 →
      ∃ m : ℕ, AdmissibleBudget d m 1 1 α ∧
        (m:ℝ) ≤ C2*(d:ℝ)^2*Real.log ((d:ℝ)+1)*Real.log (4/α)) :
    ∃ b : ℝ, 0 < b ∧ ∀ (d : ℕ) (α : ℝ), 1 ≤ d → 0 < α → α ≤ 1 →
      ∃ m : ℕ, AdmissibleBudget d m 1 1 α ∧
        (m:ℝ) ≤ b*profileQ d α*(profileLambda d α)^2 := by
  refine ⟨1154+2*C2, by linarith, ?_⟩
  intro d α hd ha ha1
  have hdR : (1:ℝ) ≤ d := by exact_mod_cast hd
  have hdpos : (0:ℝ) < d := by linarith
  have hmQ : profileQ d α = q d α := rfl
  have hmL : profileLambda d α = Lambda d α := rfl
  rw [hmQ,hmL]
  obtain ⟨hl1,hlog2,hlogd,hlogA⟩ := upper_log_bounds hdR ha ha1
  have hqnonneg := q_nonneg (α:=α) (show (0:ℝ)≤d by positivity)
  by_cases hc : (A α)^2 ≤ (d:ℝ)
  · refine ⟨2 * ⌈576*(d:ℝ)*(A α)^2*Real.log (2*(d:ℝ))⌉₊,hU1 d α hd ha ha1,?_⟩
    have hb := coarse_ceiling_bound hdR ha ha1 hc
    have hmul := mul_nonneg hC2 (mul_nonneg hqnonneg (sq_nonneg (Lambda d α)))
    nlinarith
  · obtain ⟨m,hm,hbound⟩ := hU2 d α hd ha ha1
    refine ⟨m,hm,?_⟩
    have hq : q d α = (d:ℝ)^2 := by
      unfold q M
      rw [min_eq_left (le_of_lt (lt_of_not_ge hc))]
      ring
    have hln : 0 ≤ Real.log ((d:ℝ)+1) := Real.log_nonneg (by linarith)
    have hlnA : 0 ≤ Real.log (4/α) := by
      apply Real.log_nonneg
      exact (le_div_iff₀ ha).mpr (by linarith)
    have hprod : Real.log ((d:ℝ)+1)*Real.log (4/α) ≤ 2*(Lambda d α)^2 := by
      have hh := mul_le_mul hlogd hlogA hlnA (show 0≤Lambda d α by linarith)
      nlinarith
    have hmul := mul_le_mul_of_nonneg_left hprod (mul_nonneg hC2 (sq_nonneg (d:ℝ)))
    rw [hq]
    nlinarith [sq_nonneg (d:ℝ),sq_nonneg (Lambda d α)]

end Task003.UpperEnvelope


end
-- END UpperEnvelope.lean

-- BEGIN OracleStateMachine.lean
section

/- Dependencies: OracleModel. Finite public-state machines compile to actual
scalar-reply policies; neither transitions nor query/output maps receive f. -/
namespace Task003.OracleStateMachine
open MeasureTheory Task003.OracleModel

variable {d : ℕ} {R : ℝ} {Ω S : Type*} [MeasurableSpace Ω] [MeasurableSpace S]

structure Machine (d : ℕ) (R : ℝ) (Ω S : Type*) [MeasurableSpace Ω] [MeasurableSpace S] where
  initial : Ω → S
  initial_measurable : Measurable initial
  step : ℕ → Ω × S × ℝ → S
  step_measurable : ∀ n, Measurable (step n)
  query : ℕ → Ω × S → Point d
  query_measurable : ∀ n, Measurable (query n)
  output : ℕ → Ω × S → Point d
  output_measurable : ∀ n, Measurable (output n)
  output_feasible : ∀ n p, Feasible R (output n p)

noncomputable def historyState (a : Machine d R Ω S) :
    (n : ℕ) → Ω × (Fin n → ℝ) → S
  | 0 => fun h => a.initial h.1
  | n+1 => fun h => a.step n (h.1, historyState a n (h.1,Fin.init h.2), h.2 (Fin.last n))

theorem historyState_measurable (a : Machine d R Ω S) (n : ℕ) :
    Measurable (historyState a n) := by
  induction n with
  | zero => exact a.initial_measurable.comp measurable_fst
  | succ n ih =>
    have hi : Measurable (fun h : Ω × (Fin (n+1) → ℝ) => (h.1,Fin.init h.2)) := by
      apply measurable_fst.prodMk
      exact measurable_pi_lambda _ (fun i => (measurable_pi_apply i.castSucc).comp measurable_snd)
    exact (a.step_measurable n).comp
      (measurable_fst.prodMk ((ih.comp hi).prodMk ((measurable_pi_apply (Fin.last n)).comp measurable_snd)))

noncomputable def toPolicy (a : Machine d R Ω S) : Policy d R Ω where
  query := fun n h => a.query n (h.1,historyState a n h)
  query_measurable := fun n => (a.query_measurable n).comp
    (measurable_fst.prodMk (historyState_measurable a n))
  stop := fun _ _ => false
  stop_measurable := fun _ => measurable_const
  output := fun n h => a.output n (h.1,historyState a n h)
  output_measurable := fun n => (a.output_measurable n).comp
    (measurable_fst.prodMk (historyState_measurable a n))
  output_feasible := fun n h => a.output_feasible n (h.1,historyState a n h)

theorem historyState_nextHistory (a : Machine d R Ω S) (f : Point d → ℝ)
    (n : ℕ) (h : Ω × (Fin n → ℝ)) :
    historyState a (n+1) (nextHistory (toPolicy a) f n h) =
      a.step n (h.1,historyState a n h,f (a.query n (h.1,historyState a n h))) := by
  simp [historyState,nextHistory,toPolicy,Fin.init_snoc]

noncomputable def evolution (a : Machine d R Ω S) (f : Point d → ℝ)
    (ω : Ω) (n : ℕ) (s : S) : ℕ → S
  | 0 => s
  | k+1 => evolution a f ω (n+1)
      (a.step n (ω,s,f (a.query n (ω,s)))) k

theorem evolution_add (a : Machine d R Ω S) (f : Point d → ℝ)
    (ω : Ω) (n : ℕ) (s : S) (k l : ℕ) :
    evolution a f ω n s (k+l) =
      evolution a f ω (n+k) (evolution a f ω n s k) l := by
  induction k generalizing n s with
  | zero => simp only [Nat.zero_add,Nat.add_zero,evolution]
  | succ k ih =>
    simp only [Nat.succ_add,evolution]
    rw [ih]
    have he : n+1+k=n+(k+1) := by omega
    rw [he]

theorem execute_toPolicy (a : Machine d R Ω S) (f : Point d → ℝ)
    (k n : ℕ) (h : Ω × (Fin n → ℝ)) :
    execute (toPolicy a) f k n h = a.output (n+k)
      (h.1,evolution a f h.1 n (historyState a n h) k) := by
  induction k generalizing n with
  | zero => rfl
  | succ k ih =>
    change execute (toPolicy a) f k (n+1) (nextHistory (toPolicy a) f n h) = _
    rw [ih]
    have hs := historyState_nextHistory a f n h
    change historyState a (n+1) (h.1,Fin.snoc h.2 (f ((toPolicy a).query n h))) = _ at hs
    simp only [nextHistory]
    rw [hs]
    have hn : n+1+k = n+(k+1) := by omega
    rw [hn]
    rfl

theorem run_toPolicy (a : Machine d R Ω S) (f : Point d → ℝ)
    (k : ℕ) (ω : Ω) :
    run (toPolicy a) f k ω = a.output k
      (ω,evolution a f ω 0 (a.initial ω) k) := by
  simpa only [run,execute_toPolicy,historyState,Nat.zero_add] using
    execute_toPolicy a f k 0 (ω,Fin.elim0)

end Task003.OracleStateMachine


end
-- END OracleStateMachine.lean

-- BEGIN SimplexAlgorithm.lean
section

/- Dependencies: EntropyRegret. Public positive-simplex states and measurable
multiplicative updates for arbitrary scalar oracle replies. -/
namespace PaperSimplexAlgorithm
open MeasureTheory
open scoped BigOperators
open PaperEntropyRegret

abbrev PositiveSimplex (n : ℕ) := {z : Fin n → ℝ // (∀ i, 0 < z i) ∧ ∑ i, z i = 1}

noncomputable def uniform (n : ℕ) (hn : 0 < n) : PositiveSimplex n :=
  ⟨fun _ => (n : ℝ)⁻¹, (by intro i; exact inv_pos.mpr (by exact_mod_cast hn)), by
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    exact mul_inv_cancel₀ (by exact_mod_cast (Nat.ne_of_gt hn))⟩

noncomputable def updated {n : ℕ} (z : PositiveSimplex n) (g : Fin n → ℝ)
    (η : ℝ) : PositiveSimplex n :=
  ⟨update z g η,update_pos z g η z.property.1 z.property.2,
    update_sum z g η z.property.1 z.property.2⟩

theorem updated_measurable (n : ℕ) (η : ℝ) :
    Measurable (fun p : PositiveSimplex n × (Fin n → ℝ) => updated p.1 p.2 η) := by
  apply Measurable.subtype_mk
  apply measurable_pi_lambda
  intro i
  change Measurable (fun p : PositiveSimplex n × (Fin n → ℝ) =>
    p.1.val i * Real.exp (-η*p.2 i) / ∑ j, p.1.val j * Real.exp (-η*p.2 j))
  have hz (j : Fin n) : Measurable (fun p : PositiveSimplex n × (Fin n → ℝ) => p.1.val j) :=
    (measurable_pi_apply j).comp (measurable_subtype_coe.comp measurable_fst)
  have hg (j : Fin n) : Measurable (fun p : PositiveSimplex n × (Fin n → ℝ) => p.2 j) :=
    (measurable_pi_apply j).comp measurable_snd
  have he (j : Fin n) := (hz j).mul (((hg j).const_mul (-η)).exp)
  exact (he i).div (Finset.measurable_sum _ (fun j _ => he j))

noncomputable def averaged {n : ℕ} (t : ℕ) (a z : PositiveSimplex n) : PositiveSimplex n :=
  ⟨fun i => ((t : ℝ) * a.val i + z.val i) / (t+1), by
    intro i
    apply div_pos
    · exact add_pos_of_nonneg_of_pos (mul_nonneg (by positivity) (a.property.1 i).le) (z.property.1 i)
    · positivity
   ,by
    rw [← Finset.sum_div,Finset.sum_add_distrib,← Finset.mul_sum,a.property.2,z.property.2]
    simpa only [mul_one] using (div_self (show (t : ℝ)+1 ≠ 0 by positivity))⟩

theorem averaged_measurable (n t : ℕ) :
    Measurable (fun p : PositiveSimplex n × PositiveSimplex n => averaged t p.1 p.2) := by
  apply Measurable.subtype_mk
  apply measurable_pi_lambda
  intro i
  change Measurable (fun p : PositiveSimplex n × PositiveSimplex n =>
    ((t : ℝ)*p.1.val i+p.2.val i)/(t+1))
  have ha : Measurable (fun p : PositiveSimplex n × PositiveSimplex n => p.1.val i) :=
    (measurable_pi_apply i).comp (measurable_subtype_coe.comp measurable_fst)
  have hz : Measurable (fun p : PositiveSimplex n × PositiveSimplex n => p.2.val i) :=
    (measurable_pi_apply i).comp (measurable_subtype_coe.comp measurable_snd)
  exact ((ha.const_mul (t : ℝ)).add hz).div_const (t+1)

abbrev State (n : ℕ) := PositiveSimplex n × PositiveSimplex n × ℝ

noncomputable def initial (n : ℕ) (hn : 0 < n) : State n :=
  (uniform n hn,uniform n hn,0)

/-- At the first reply of a pair, save the plus value; at the second,
form the central difference, update z, and average the pre-update z.
There is no objective parameter in this transition. -/
noncomputable def step {n : ℕ} (η h : ℝ) (u : ℕ → Fin n → ℝ)
    (m : ℕ) (s : State n) (y : ℝ) : State n :=
  if m % 2 = 0 then (s.1,s.2.1,y) else
    (updated s.1 (fun i => ((s.2.2-y)/(2*h))*Real.sign (u (m/2) i)) η,
      averaged (m/2) s.2.1 s.1,0)

theorem step_measurable {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (η h : ℝ) (u : Ω → ℕ → Fin n → ℝ)
    (hu : ∀ t, Measurable (fun ω => u ω t)) (m : ℕ) :
    Measurable (fun p : Ω × State n × ℝ => step η h (u p.1) m p.2.1 p.2.2) := by
  by_cases hm : m%2=0
  · simpa only [step,if_pos hm] using
      (measurable_snd.fst.fst.prodMk (measurable_snd.fst.snd.fst.prodMk measurable_snd.snd))
  · simp only [step,if_neg hm]
    have hg : Measurable (fun p : Ω × State n × ℝ =>
        fun i => ((p.2.1.2.2-p.2.2)/(2*h))*Real.sign (u p.1 (m/2) i)) := by
      apply measurable_pi_lambda
      intro i
      have hi : Measurable (fun p : Ω × State n × ℝ => u p.1 (m/2) i) :=
        (measurable_pi_apply i).comp ((hu (m/2)).comp measurable_fst)
      have hsign := PaperOddDifference.real_sign_measurable.comp hi
      exact (((measurable_snd.fst.snd.snd.sub measurable_snd.snd).div_const (2*h))).mul hsign
    exact ((updated_measurable n η).comp (measurable_snd.fst.fst.prodMk hg)).prodMk
      (((averaged_measurable n (m/2)).comp
        (measurable_snd.fst.snd.fst.prodMk measurable_snd.fst.fst)).prodMk measurable_const)

end PaperSimplexAlgorithm


end
-- END SimplexAlgorithm.lean

-- BEGIN TwoPointPolicy.lean
section

/- Dependencies: OracleModel, OracleStateMachine, SimplexAlgorithm.
A real two-scalar-value public policy; perturbations are part of the private
seed and the objective is absent from all public machine maps. -/
namespace Task003.TwoPointPolicy
open MeasureTheory Task003.OracleModel Task003.OracleStateMachine PaperSimplexAlgorithm

variable {d n : ℕ} {Ω : Type*} [MeasurableSpace Ω]

noncomputable def machine (hn : 0 < n) (η h : ℝ)
    (u : Ω → ℕ → Fin n → ℝ) (hu : ∀ t, Measurable (fun ω => u ω t))
    (V : (Fin n → ℝ) → Point d) (hVm : Measurable V)
    (hV : ∀ z : PositiveSimplex n, Feasible 1 (V z.val)) :
    Machine d 1 Ω (PaperSimplexAlgorithm.State n) where
  initial := fun _ => PaperSimplexAlgorithm.initial n hn
  initial_measurable := measurable_const
  step := fun m p => PaperSimplexAlgorithm.step η h (u p.1) m p.2.1 p.2.2
  step_measurable := step_measurable η h u hu
  query := fun m p => V (fun i => p.2.1.val i +
    if m%2=0 then h*u p.1 (m/2) i else -(h*u p.1 (m/2) i))
  query_measurable := fun m => by
    apply hVm.comp
    apply measurable_pi_lambda
    intro i
    have hz : Measurable (fun p : Ω × PaperSimplexAlgorithm.State n => p.2.1.val i) :=
      (measurable_pi_apply i).comp (measurable_subtype_coe.comp measurable_snd.fst)
    have hu' : Measurable (fun p : Ω × PaperSimplexAlgorithm.State n => u p.1 (m/2) i) :=
      (measurable_pi_apply i).comp ((hu (m/2)).comp measurable_fst)
    by_cases hm : m%2=0
    · simp only [if_pos hm]
      convert hz.add (hu'.const_mul h) using 1
      funext p
      rfl
    · simp only [if_neg hm]
      convert hz.add (hu'.const_mul h).neg using 1
      funext p
      rfl
  output := fun _ p => V p.2.2.1.val
  output_measurable := fun _ => hVm.comp (measurable_subtype_coe.comp measurable_snd.snd.fst)
  output_feasible := fun _ p => hV p.2.2.1

noncomputable def policy (hn : 0 < n) (η h : ℝ)
    (u : Ω → ℕ → Fin n → ℝ) (hu : ∀ t, Measurable (fun ω => u ω t))
    (V : (Fin n → ℝ) → Point d) (hVm : Measurable V)
    (hV : ∀ z : PositiveSimplex n, Feasible 1 (V z.val)) : Policy d 1 Ω :=
  toPolicy (machine hn η h u hu V hVm hV)

noncomputable def round (F : (Fin n → ℝ) → ℝ) (η h : ℝ)
    (u : ℕ → Fin n → ℝ) (t : ℕ) (s : PaperSimplexAlgorithm.State n) :
    PaperSimplexAlgorithm.State n :=
  (updated s.1 (fun i =>
    ((F (fun j => s.1.val j+h*u t j)-F (fun j => s.1.val j-h*u t j))/(2*h))*
      Real.sign (u t i)) η, averaged t s.2.1 s.1,0)

theorem evolution_two (hn : 0 < n) (η h : ℝ)
    (u : Ω → ℕ → Fin n → ℝ) (hu : ∀ t, Measurable (fun ω => u ω t))
    (V : (Fin n → ℝ) → Point d) (hVm : Measurable V)
    (hV : ∀ z : PositiveSimplex n, Feasible 1 (V z.val))
    (f : Point d → ℝ) (ω : Ω) (t : ℕ) (s : PaperSimplexAlgorithm.State n) :
    evolution (machine hn η h u hu V hVm hV) f ω (2*t) s 2 =
      round (f ∘ V) η h (u ω) t s := by
  have h0 : 2*t%2=0 := by omega
  have h1 : ¬ (2*t+1)%2=0 := by omega
  have hd0 : 2*t/2=t := by omega
  have hd1 : (2*t+1)/2=t := by omega
  simp only [evolution,machine,PaperSimplexAlgorithm.step,h0,if_pos,h1,if_neg,hd0,hd1]
  rfl

noncomputable def rounds (hn : 0 < n) (F : (Fin n → ℝ) → ℝ) (η h : ℝ)
    (u : ℕ → Fin n → ℝ) : ℕ → PaperSimplexAlgorithm.State n
  | 0 => PaperSimplexAlgorithm.initial n hn
  | t+1 => round F η h u t (rounds hn F η h u t)

theorem evolution_rounds (hn : 0 < n) (η h : ℝ)
    (u : Ω → ℕ → Fin n → ℝ) (hu : ∀ t, Measurable (fun ω => u ω t))
    (V : (Fin n → ℝ) → Point d) (hVm : Measurable V)
    (hV : ∀ z : PositiveSimplex n, Feasible 1 (V z.val))
    (f : Point d → ℝ) (ω : Ω) (T : ℕ) :
    evolution (machine hn η h u hu V hVm hV) f ω 0
      (PaperSimplexAlgorithm.initial n hn) (2*T) = rounds hn (f ∘ V) η h (u ω) T := by
  induction T with
  | zero => rfl
  | succ T ih =>
    rw [show 2*(T+1)=2*T+2 by omega,evolution_add,ih,Nat.zero_add,evolution_two]
    rfl

theorem run_policy_even (hn : 0 < n) (η h : ℝ)
    (u : Ω → ℕ → Fin n → ℝ) (hu : ∀ t, Measurable (fun ω => u ω t))
    (V : (Fin n → ℝ) → Point d) (hVm : Measurable V)
    (hV : ∀ z : PositiveSimplex n, Feasible 1 (V z.val))
    (f : Point d → ℝ) (ω : Ω) (T : ℕ) :
    run (policy hn η h u hu V hVm hV) f (2*T) ω =
      V (rounds hn (f ∘ V) η h (u ω) T).2.1.val := by
  unfold policy
  rw [run_toPolicy]
  change V (evolution (machine hn η h u hu V hVm hV) f ω 0
    (PaperSimplexAlgorithm.initial n hn) (2*T)).2.1.val = _
  rw [evolution_rounds]

theorem rounds_average_sum (hn : 0 < n) (F : (Fin n → ℝ) → ℝ) (η h : ℝ)
    (u : ℕ → Fin n → ℝ) (T : ℕ) (i : Fin n) :
    (T : ℝ)*(rounds hn F η h u T).2.1.val i =
      ∑ t ∈ Finset.range T, (rounds hn F η h u t).1.val i := by
  induction T with
  | zero => simp
  | succ T ih =>
    change ((T+1 : ℕ) : ℝ)*(((T : ℝ)*(rounds hn F η h u T).2.1.val i+
      (rounds hn F η h u T).1.val i)/(T+1)) = _
    rw [Nat.cast_add,Nat.cast_one,mul_div_cancel₀ _ (show (T : ℝ)+1 ≠ 0 by positivity),
      Finset.sum_range_succ,ih]

theorem rounds_average_eq (hn : 0 < n) (F : (Fin n → ℝ) → ℝ) (η h : ℝ)
    (u : ℕ → Fin n → ℝ) (T : ℕ) (hT : 0 < T) :
    (rounds hn F η h u T).2.1.val =
      ∑ t ∈ Finset.range T, (T : ℝ)⁻¹ • (rounds hn F η h u t).1.val := by
  funext i
  have hTi : (T : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hT)
  have hs := rounds_average_sum hn F η h u T i
  simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
  rw [← Finset.mul_sum]
  calc
    _ = (T : ℝ)⁻¹ * ((T : ℝ)*(rounds hn F η h u T).2.1.val i) := by
      rw [inv_mul_cancel_left₀ hTi]
    _ = _ := by rw [hs]

theorem rounds_jensen (hn : 0 < n) (F : (Fin n → ℝ) → ℝ)
    (hF : ConvexOn ℝ Set.univ F) (η h : ℝ)
    (u : ℕ → Fin n → ℝ) (T : ℕ) (hT : 0 < T) :
    F (rounds hn F η h u T).2.1.val ≤
      (∑ t ∈ Finset.range T, F (rounds hn F η h u t).1.val)/(T : ℝ) := by
  have hTi : (T : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hT)
  have hw : ∑ _t ∈ Finset.range T, (T : ℝ)⁻¹ = 1 := by
    simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul]
    exact mul_inv_cancel₀ hTi
  have hh := hF.map_sum_le (t := Finset.range T)
    (w := fun _ : ℕ => (T : ℝ)⁻¹)
    (p := fun t => (rounds hn F η h u t).1.val)
    (fun _ _ => by positivity) hw (fun _ _ => Set.mem_univ _)
  rw [← rounds_average_eq hn F η h u T hT] at hh
  simpa only [smul_eq_mul,← Finset.mul_sum,div_eq_mul_inv,mul_comm] using hh

end Task003.TwoPointPolicy


end
-- END TwoPointPolicy.lean

-- BEGIN DirectionalKernel.lean
section

namespace PaperDirectionalKernel

open MeasureTheory Set Filter
open scoped Topology

def mass {n : ℕ} (u : Fin n → ℝ) : ℝ := ∑ i, |u i|

noncomputable def ratio {n : ℕ} (h : ℝ) (v : Fin n → ℝ) (t : ℝ) (u : Fin n → ℝ) : ℝ :=
  Real.exp (mass u - mass (fun i => u i - t * (v i / h)))

noncomputable def score {n : ℕ} (h : ℝ) (v u : Fin n → ℝ) : ℝ :=
  ∑ i, Real.sign (u i) * (v i / h)

theorem mass_nonneg {n : ℕ} (u : Fin n → ℝ) : 0 ≤ mass u :=
  Finset.sum_nonneg (fun _ _ => abs_nonneg _)

theorem mass_continuous (n : ℕ) : Continuous (@mass n) := by
  unfold mass
  fun_prop

theorem mass_difference_le {n : ℕ} (u q : Fin n → ℝ) :
    |mass u - mass q| ≤ mass (fun i => u i - q i) := by
  rw [mass, mass, ← Finset.sum_sub_distrib]
  exact (Finset.abs_sum_le_sum_abs _ _).trans
    (Finset.sum_le_sum (fun i _ => abs_abs_sub_abs_le_abs_sub (u i) (q i)))

theorem logRatio_bound {n : ℕ} (h : ℝ) (hh : 0 < h) (v u : Fin n → ℝ) (t : ℝ) :
    |mass u - mass (fun i => u i - t * (v i / h))| ≤ (mass v / h) * |t| := by
  have hb := mass_difference_le u (fun i => u i - t * (v i / h))
  have he : (fun i => u i - (u i - t * (v i / h))) = fun i => t * (v i / h) := by
    ext i
    ring
  rw [he] at hb
  have hm : mass (fun i => t * (v i / h)) = (mass v / h) * |t| := by
    simp only [mass, abs_mul, abs_div, abs_of_pos hh]
    rw [← Finset.mul_sum, ← Finset.sum_div]
    ring
  rwa [hm] at hb

theorem signType_eq_realSign (x : ℝ) : (SignType.sign x : ℝ) = Real.sign x := by
  rcases lt_trichotomy x 0 with hx | hx | hx
  · simp [sign_neg hx, Real.sign_of_neg hx]
  · simp [hx]
  · simp [sign_pos hx, Real.sign_of_pos hx]

theorem ratio_zero {n : ℕ} (h : ℝ) (v u : Fin n → ℝ) : ratio h v 0 u = 1 := by
  simp [ratio]

theorem ratio_hasDerivAt_zero {n : ℕ} (h : ℝ) (v u : Fin n → ℝ)
    (hu : ∀ i, u i ≠ 0) : HasDerivAt (fun t => ratio h v t u) (score h v u) 0 := by
  have hi : ∀ i, HasDerivAt (fun t => |u i - t * (v i / h)|)
      (-(Real.sign (u i) * (v i / h))) 0 := by
    intro i
    have hl : HasDerivAt (fun t : ℝ => u i - t * (v i / h)) (-(v i / h)) 0 := by
      convert! (hasDerivAt_const 0 (u i)).sub ((hasDerivAt_id 0).mul_const (v i / h)) using 1
      ring
    have ha := hasDerivAt_abs (show u i - 0 * (v i / h) ≠ 0 by simpa using hu i)
    have hc := ha.comp 0 hl
    simpa only [Function.comp_def, zero_mul, sub_zero, zero_sub, one_mul,
      signType_eq_realSign, mul_neg] using hc
  have hm := HasDerivAt.fun_sum (u := Finset.univ) (fun i _ => hi i)
  have he := (hm.const_sub (mass u)).exp
  simpa [ratio, mass, score, Finset.sum_neg_distrib] using he

theorem ratio_local_difference {n : ℕ} (h : ℝ) (hh : 0 < h) (v u : Fin n → ℝ)
    (t : ℝ) (ht : t ∈ Metric.ball 0 (mass v / h + 1)⁻¹) :
    |ratio h v t u - 1| ≤ Real.exp 1 * (mass v / h) * |t| := by
  let a : ℝ := mass u - mass (fun i => u i - t * (v i / h))
  have hK : 0 ≤ mass v / h := div_nonneg (mass_nonneg v) hh.le
  have hb : |a| ≤ (mass v / h) * |t| := logRatio_bound h hh v u t
  have ht' : |t| < (mass v / h + 1)⁻¹ := by simpa [Metric.mem_ball, Real.dist_eq] using ht
  have hprod : (mass v / h + 1) * |t| < 1 := by
    rw [inv_eq_one_div] at ht'
    have hx := (lt_div_iff₀ (show 0 < mass v / h + 1 by positivity)).mp ht'
    simpa only [mul_comm] using hx
  have ha1 : a ≤ 1 := by nlinarith [abs_nonneg t, le_abs_self a]
  have hexp := (PaperLaplaceScore.exp_lipschitzOn_Iic 1).dist_le_mul a ha1 0 (by norm_num)
  simp only [Real.dist_eq, sub_zero, Real.exp_zero] at hexp
  change |Real.exp a - 1| ≤ _
  calc
    _ ≤ Real.exp 1 * |a| := hexp
    _ ≤ Real.exp 1 * ((mass v / h) * |t|) :=
      mul_le_mul_of_nonneg_left hb (Real.exp_pos 1).le
    _ = _ := by ring

theorem ratio_measurable {n : ℕ} (h : ℝ) (v : Fin n → ℝ) (t : ℝ) :
    Measurable (ratio h v t) := by
  unfold ratio mass
  fun_prop

theorem score_measurable {n : ℕ} (h : ℝ) (v : Fin n → ℝ) : Measurable (score h v) := by
  unfold score
  apply Finset.measurable_sum
  intro i _
  exact (PaperLaplaceScore.real_sign_measurable.comp (measurable_pi_apply i)).mul_const (v i / h)

theorem ratioIntegral_hasDerivAt_zero {n : ℕ} (μ : Measure (Fin n → ℝ))
    (G : (Fin n → ℝ) → ℝ) (hG : Measurable G) (hGint : Integrable G μ)
    (hAE : ∀ᵐ u ∂μ, ∀ i, u i ≠ 0) (h : ℝ) (hh : 0 < h) (v : Fin n → ℝ) :
    Integrable (fun u => G u * score h v u) μ ∧
      HasDerivAt (fun t => ∫ u, G u * ratio h v t u ∂μ)
        (∫ u, G u * score h v u ∂μ) 0 := by
  let L : ℝ →L[ℝ] ℝ →L[ℝ] ℝ := ContinuousLinearMap.smulRightL ℝ ℝ ℝ 1
  let bound : (Fin n → ℝ) → ℝ := fun u => Real.exp 1 * (mass v / h) * |G u|
  have hK : 0 ≤ mass v / h := div_nonneg (mass_nonneg v) hh.le
  have hbound : Integrable bound μ := hGint.norm.const_mul (Real.exp 1 * (mass v / h))
  have hdiff : ∀ᵐ u ∂μ, HasFDerivAt (fun t => G u * ratio h v t u) (L (G u * score h v u)) 0 := by
    filter_upwards [hAE] with u hu
    exact ((ratio_hasDerivAt_zero h v u hu).const_mul (G u)).hasFDerivAt
  have hlocal : ∀ᵐ u ∂μ, ∀ t ∈ Metric.ball 0 (mass v / h + 1)⁻¹,
      ‖G u * ratio h v t u - G u * ratio h v 0 u‖ ≤ bound u * ‖t - 0‖ := by
    apply Filter.Eventually.of_forall
    intro u t ht
    rw [ratio_zero, mul_one, sub_zero, Real.norm_eq_abs, Real.norm_eq_abs]
    have he : G u * ratio h v t u - G u = G u * (ratio h v t u - 1) := by ring
    rw [he, abs_mul]
    calc
      |G u| * |ratio h v t u - 1| ≤ |G u| * (Real.exp 1 * (mass v / h) * |t|) :=
        mul_le_mul_of_nonneg_left (ratio_local_difference h hh v u t ht) (abs_nonneg _)
      _ = bound u * |t| := by dsimp [bound]; ring
  have hzero : Integrable (fun u => G u * ratio h v 0 u) μ := by
    simpa only [ratio_zero, mul_one] using hGint
  obtain ⟨hdint, hd⟩ := hasFDerivAt_integral_of_dominated_loc_of_lip'
    (μ := μ) (F := fun t u => G u * ratio h v t u)
    (F' := fun u => L (G u * score h v u)) (bound := bound)
    (Metric.ball_mem_nhds 0 (by positivity))
    (fun t _ => (hG.mul (ratio_measurable h v t)).aestronglyMeasurable) hzero
    (L.continuous.measurable.comp (hG.mul (score_measurable h v))).aestronglyMeasurable
    hlocal hbound hdiff
  have hdreal : Integrable (fun u => G u * score h v u) μ := by
    simpa [L] using (ContinuousLinearMap.apply ℝ ℝ (1 : ℝ)).integrable_comp hdint
  refine ⟨hdreal, ?_⟩
  have hs := hd.hasDerivAt
  rw [ContinuousLinearMap.integral_apply hdint 1] at hs
  simpa [L] using hs

end PaperDirectionalKernel


end
-- END DirectionalKernel.lean

-- BEGIN ProductLaplaceScore.lean
section

namespace PaperProductLaplaceScore

open MeasureTheory ProbabilityTheory PaperLaplace PaperProductVariance PaperOddDifference

theorem smoothingL1_eq_smoothing {n : ℕ} (F : Space n → ℝ) (h : ℝ) (z : Space n) :
    PaperProductLaplaceDensity.smoothingL1 F h z = PaperSmoothingBias.smoothing n laplaceLaw F z h := rfl

theorem smoothing_direction_hasDerivAt {n : ℕ} (F : Space n → ℝ) (hF : LipschitzWith 1 F)
    (h : ℝ) (hh : 0 < h) (z v : Space n) :
    HasDerivAt (fun t : ℝ => PaperProductLaplaceDensity.smoothingL1 F h (z + t • v))
      (∫ u : Fin n → ℝ, F (z + h • WithLp.toLp 1 u) *
        PaperDirectionalKernel.score h (WithLp.ofLp v) u ∂productLaw n) 0 := by
  let G : (Fin n → ℝ) → ℝ := fun u => F (z + h • WithLp.toLp 1 u)
  have hG : Measurable G := by
    exact hF.continuous.measurable.comp
      (measurable_const.add ((PiLp.continuous_toLp 1 _).measurable.const_smul h))
  have hGint : Integrable G (productLaw n) :=
    (PaperSmoothingBias.perturbed_value_memLp n laplaceLaw laplace_id_memLp_two F hF z h).integrable
      (by norm_num)
  have hd := PaperDirectionalKernel.ratioIntegral_hasDerivAt_zero (productLaw n) G hG hGint
    (PaperProductLaplaceAE.ae_coordinates_ne_zero n) h hh (WithLp.ofLp v)
  have hrat : ∀ t u, PaperProductLaplaceDensity.ratio (fun i => (t / h) * v i) u =
      PaperDirectionalKernel.ratio h (WithLp.ofLp v) t u := by
    intro t u
    unfold PaperProductLaplaceDensity.ratio PaperProductLaplaceDensity.mass
      PaperDirectionalKernel.ratio PaperDirectionalKernel.mass
    congr 2
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    change u i - (t / h) * v i = u i - t * (v i / h)
    ring
  have hfun : (fun t : ℝ => PaperProductLaplaceDensity.smoothingL1 F h (z + t • v)) =
      fun t => ∫ u, G u * PaperDirectionalKernel.ratio h (WithLp.ofLp v) t u ∂productLaw n := by
    funext t
    rw [PaperProductLaplaceDensity.smoothingL1_shift F h hh.ne' z v t]
    simp only [hrat]
    rfl
  have hd' := hd.2
  rw [← hfun] at hd'
  exact hd'

noncomputable def signDot {n : ℕ} (v : Space n) (u : Fin n → ℝ) : ℝ :=
  ∑ i, Real.sign (u i) * v i

theorem signDot_measurable {n : ℕ} (v : Space n) : Measurable (signDot v) := by
  unfold signDot
  apply Finset.measurable_sum
  intro i _
  exact (PaperLaplaceScore.real_sign_measurable.comp (measurable_pi_apply i)).mul_const _

theorem signDot_abs_le {n : ℕ} (v : Space n) (u : Fin n → ℝ) : |signDot v u| ≤ ‖v‖ := by
  rw [norm_eq_sum_abs]
  calc
    |∑ i, Real.sign (u i) * v i| ≤ ∑ i, |Real.sign (u i) * v i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, |v i| := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul]
      nlinarith [PaperLaplaceScoreBridge.abs_sign_le_one (u i), abs_nonneg (v i)]

theorem signDot_neg {n : ℕ} (v : Space n) (u : Fin n → ℝ) :
    signDot v (fun i => -u i) = -signDot v u := by
  simp [signDot, Real.sign_neg, Finset.sum_neg_distrib]

theorem score_eq_signDot {n : ℕ} (h : ℝ) (v : Space n) (u : Fin n → ℝ) :
    PaperDirectionalKernel.score h (WithLp.ofLp v) u = signDot v u / h := by
  unfold PaperDirectionalKernel.score signDot
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem value_signDot_integrable {n : ℕ} (F : Space n → ℝ) (hF : LipschitzWith 1 F)
    (h : ℝ) (z v : Space n) :
    Integrable (fun u : Fin n → ℝ => F (z + h • WithLp.toLp 1 u) * signDot v u) (productLaw n) := by
  have hv := (PaperSmoothingBias.perturbed_value_memLp n laplaceLaw laplace_id_memLp_two F hF z h).integrable
    (by norm_num)
  exact hv.mul_bdd (signDot_measurable v).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun u => by simpa only [Real.norm_eq_abs] using signDot_abs_le v u))

theorem reflected_value_signDot_integral {n : ℕ} (F : Space n → ℝ) (hF : LipschitzWith 1 F)
    (h : ℝ) (z v : Space n) :
    (∫ u : Fin n → ℝ, F (z - h • WithLp.toLp 1 u) * signDot v u ∂productLaw n) =
      -(∫ u : Fin n → ℝ, F (z + h • WithLp.toLp 1 u) * signDot v u ∂productLaw n) := by
  have hm : Measurable (fun u : Fin n → ℝ => F (z - h • WithLp.toLp 1 u) * signDot v u) :=
    (hF.continuous.measurable.comp
      (measurable_const.sub ((PiLp.continuous_toLp 1 _).measurable.const_smul h))).mul
        (signDot_measurable v)
  have hp := productLaw_reflection n
  calc
    _ = ∫ u, F (z - h • WithLp.toLp 1 u) * signDot v u
        ∂(productLaw n).map (fun u : Fin n → ℝ => fun i => -u i) := by rw [hp.map_eq]
    _ = ∫ u, F (z - h • WithLp.toLp 1 (fun i => -u i)) *
        signDot v (fun i => -u i) ∂productLaw n := by
      rw [integral_map hp.measurable.aemeasurable hm.aestronglyMeasurable]
    _ = _ := by
      have he : ∀ u : Fin n → ℝ, (WithLp.toLp 1 (fun i => -u i) : Space n) = -WithLp.toLp 1 u :=
        fun _ => rfl
      simp_rw [he, smul_neg, sub_neg_eq_add, signDot_neg, mul_neg]
      rw [integral_neg]

noncomputable def centralDot {n : ℕ} (F : Space n → ℝ) (z : Space n) (h : ℝ)
    (v : Space n) (u : Fin n → ℝ) : ℝ :=
  oddDifference F z h (WithLp.toLp 1 u) * signDot v u

theorem centralDot_eq_estimatorDot {n : ℕ} (F : Space n → ℝ) (z : Space n) (h : ℝ)
    (v : Space n) (u : Fin n → ℝ) :
    centralDot F z h v u =
      ∑ i, signEstimator (oddDifference F z h) (WithLp.toLp 1 u) i * v i := by
  unfold centralDot signDot signEstimator
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem centralDot_integrable {n : ℕ} (F : Space n → ℝ) (hF : LipschitzWith 1 F)
    (h : ℝ) (z v : Space n) : Integrable (centralDot F z h v) (productLaw n) := by
  have hp := value_signDot_integrable F hF h z v
  have hn := value_signDot_integrable F hF (-h) z v
  have hi := (hp.sub hn).div_const (2 * h)
  convert hi using 1
  ext u
  simp only [centralDot, oddDifference, Pi.sub_apply, neg_smul, sub_eq_add_neg]
  ring

theorem centralDot_integral_eq_score {n : ℕ} (F : Space n → ℝ) (hF : LipschitzWith 1 F)
    (h : ℝ) (hh : 0 < h) (z v : Space n) :
    (∫ u, centralDot F z h v u ∂productLaw n) =
      ∫ u : Fin n → ℝ, F (z + h • WithLp.toLp 1 u) *
        PaperDirectionalKernel.score h (WithLp.ofLp v) u ∂productLaw n := by
  have hp := value_signDot_integrable F hF h z v
  have hn : Integrable (fun u : Fin n → ℝ => F (z - h • WithLp.toLp 1 u) * signDot v u)
      (productLaw n) := by
    simpa only [neg_smul, sub_eq_add_neg] using value_signDot_integrable F hF (-h) z v
  have he : (fun u => centralDot F z h v u) = fun u : Fin n → ℝ =>
      (F (z + h • WithLp.toLp 1 u) * signDot v u -
        F (z - h • WithLp.toLp 1 u) * signDot v u) / (2 * h) := by
    ext u
    unfold centralDot oddDifference
    ring
  have heScore : (fun u : Fin n → ℝ => F (z + h • WithLp.toLp 1 u) *
      PaperDirectionalKernel.score h (WithLp.ofLp v) u) = fun u =>
      (F (z + h • WithLp.toLp 1 u) * signDot v u) / h := by
    ext u
    rw [score_eq_signDot]
    ring
  rw [he, integral_div, integral_sub hp hn, reflected_value_signDot_integral F hF h z v,
    heScore, integral_div]
  field_simp
  ring

theorem smoothing_direction_hasDerivAt_centralDot {n : ℕ} (F : Space n → ℝ)
    (hF : LipschitzWith 1 F) (h : ℝ) (hh : 0 < h) (z v : Space n) :
    HasDerivAt (fun t : ℝ => PaperProductLaplaceDensity.smoothingL1 F h (z + t • v))
      (∫ u, centralDot F z h v u ∂productLaw n) 0 := by
  rw [centralDot_integral_eq_score F hF h hh z v]
  exact smoothing_direction_hasDerivAt F hF h hh z v

theorem smoothing_line_convex {n : ℕ} (F : Space n → ℝ) (hF : LipschitzWith 1 F)
    (hconvex : ConvexOn ℝ Set.univ F) (h : ℝ) (z v : Space n) :
    ConvexOn ℝ Set.univ (fun t : ℝ => PaperProductLaplaceDensity.smoothingL1 F h (z + t • v)) := by
  have hs : ConvexOn ℝ Set.univ (fun x => PaperProductLaplaceDensity.smoothingL1 F h x) := by
    simpa only [smoothingL1_eq_smoothing] using
      PaperSmoothingBias.smoothing_convex n laplaceLaw laplace_id_memLp_two F hF hconvex h
  refine ⟨convex_univ, ?_⟩
  intro s _ t _ a b ha hb hab
  change PaperProductLaplaceDensity.smoothingL1 F h (z + (a * s + b * t) • v) ≤
    a • PaperProductLaplaceDensity.smoothingL1 F h (z + s • v) +
      b • PaperProductLaplaceDensity.smoothingL1 F h (z + t • v)
  have he : z + (a * s + b * t) • v =
      a • (z + s • v) + b • (z + t • v) := by
    calc
      _ = (a + b) • z + (a * s + b * t) • v := by rw [hab, one_smul]
      _ = _ := by module
  rw [he]
  exact hs.2 (Set.mem_univ _) (Set.mem_univ _) ha hb hab

theorem centralDot_tangent_le {n : ℕ} (F : Space n → ℝ) (hF : LipschitzWith 1 F)
    (hconvex : ConvexOn ℝ Set.univ F) (h : ℝ) (hh : 0 < h) (z v : Space n) :
    (∫ u, centralDot F z h v u ∂productLaw n) ≤
      PaperProductLaplaceDensity.smoothingL1 F h (z + v) -
        PaperProductLaplaceDensity.smoothingL1 F h z := by
  have ht := (smoothing_line_convex F hF hconvex h z v).le_slope_of_hasDerivAt
    (Set.mem_univ (0 : ℝ)) (Set.mem_univ (1 : ℝ)) (by norm_num)
    (smoothing_direction_hasDerivAt_centralDot F hF h hh z v)
  simpa [slope_def_field] using ht

theorem expected_estimator_supports_smoothing {n : ℕ} (F : Space n → ℝ)
    (hF : LipschitzWith 1 F) (hconvex : ConvexOn ℝ Set.univ F)
    (h : ℝ) (hh : 0 < h) (z x : Space n) :
    PaperProductLaplaceDensity.smoothingL1 F h z - PaperProductLaplaceDensity.smoothingL1 F h x ≤
      ∫ u : Fin n → ℝ, ∑ i,
        signEstimator (oddDifference F z h) (WithLp.toLp 1 u) i * (z i - x i) ∂productLaw n := by
  have ht := centralDot_tangent_le F hF hconvex h hh z (x - z)
  have hlinear : (fun u : Fin n → ℝ => ∑ i,
      signEstimator (oddDifference F z h) (WithLp.toLp 1 u) i * (z i - x i)) =
      fun u => -centralDot F z h (x - z) u := by
    funext u
    rw [centralDot_eq_estimatorDot, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    change _ * (z i - x i) = -(_ * (x i - z i))
    ring
  rw [hlinear, integral_neg]
  have he : z + (x - z) = x := by abel
  rw [he] at ht
  linarith

theorem estimatorDot_integrable {n : ℕ} (F : Space n → ℝ) (hF : LipschitzWith 1 F)
    (h : ℝ) (z v : Space n) : Integrable (fun u : Fin n → ℝ => ∑ i,
      signEstimator (oddDifference F z h) (WithLp.toLp 1 u) i * v i) (productLaw n) := by
  have he : (fun u : Fin n → ℝ => ∑ i,
      signEstimator (oddDifference F z h) (WithLp.toLp 1 u) i * v i) = centralDot F z h v := by
    funext u
    exact (centralDot_eq_estimatorDot F z h v u).symm
  rw [he]
  exact centralDot_integrable F hF h z v

theorem estimator_gap_integrable {n : ℕ} (F : Space n → ℝ) (hF : LipschitzWith 1 F)
    (h : ℝ) (z x : Space n) : Integrable (fun u : Fin n → ℝ => ∑ i,
      signEstimator (oddDifference F z h) (WithLp.toLp 1 u) i * (z i - x i)) (productLaw n) :=
  estimatorDot_integrable F hF h z (z - x)

theorem estimator_norm_le_noise_norm {n : ℕ} (F : Space n → ℝ) (hF : LipschitzWith 1 F)
    (h : ℝ) (hh : 0 < h) (z : Space n) (u : Fin n → ℝ) :
    ‖signEstimator (oddDifference F z h) (WithLp.toLp 1 u)‖ ≤ ‖(WithLp.toLp 1 u : Space n)‖ := by
  have hd := (oddDifference_lipschitz F hF z h hh).dist_le_mul (WithLp.toLp 1 u) 0
  have habs : |oddDifference F z h (WithLp.toLp 1 u)| ≤ ‖(WithLp.toLp 1 u : Space n)‖ := by
    simpa [oddDifference_zero, dist_eq_norm, Real.norm_eq_abs] using hd
  exact (signEstimator_norm_le _ _).trans habs

theorem estimator_joint_measurable {n : ℕ} (F : Space n → ℝ) (hF : LipschitzWith 1 F) (h : ℝ) :
    Measurable (fun p : Space n × (Fin n → ℝ) =>
      signEstimator (oddDifference F p.1 h) (WithLp.toLp 1 p.2)) := by
  have hU : Measurable (fun p : Space n × (Fin n → ℝ) => (WithLp.toLp 1 p.2 : Space n)) :=
    (PiLp.continuous_toLp 1 _).measurable.comp measurable_snd
  have hp := hF.continuous.measurable.comp (measurable_fst.add (hU.const_smul h))
  have hn := hF.continuous.measurable.comp (measurable_fst.sub (hU.const_smul h))
  have hD := (hp.sub hn).div_const (2 * h)
  apply measurable_pi_iff.mpr
  intro i
  exact hD.mul (PaperLaplaceScore.real_sign_measurable.comp
    ((measurable_pi_apply i).comp measurable_snd))

theorem smoothingL1_lipschitz {n : ℕ} (F : Space n → ℝ) (hF : LipschitzWith 1 F) (h : ℝ) :
    LipschitzWith 1 (PaperProductLaplaceDensity.smoothingL1 F h) := by
  have he : PaperProductLaplaceDensity.smoothingL1 F h =
      fun z => PaperSmoothingBias.smoothing n laplaceLaw F z h :=
    funext (fun z => smoothingL1_eq_smoothing F h z)
  rw [he]
  exact PaperSmoothingBias.smoothing_lipschitz n laplaceLaw laplace_id_memLp_two F hF h

end PaperProductLaplaceScore


end
-- END ProductLaplaceScore.lean

-- BEGIN FreshSeedIntegration.lean
section

/-! Fresh-coordinate integration in an actual finite product seed law. No
conditional-expectation or regret conclusion is assumed. The sole causality
condition states that the current state ignores the current fresh coordinate. -/
noncomputable section
namespace PaperFreshSeedIntegration
open MeasureTheory

/-- Exact finite-product decomposition and Fubini for an adaptive state that is
unchanged when the selected fresh coordinate is replaced. -/
theorem fresh_integral {Noise State : Type*} [MeasurableSpace Noise]
    (ν : Measure Noise) [IsProbabilityMeasure ν] {T : ℕ} (i : Fin (T+1))
    (x0 : Noise) (Z : (Fin (T+1) → Noise) → State) (H : State → Noise → ℝ)
    (hcausal : ∀ rest : Fin T → Noise, ∀ u : Noise,
      Z (i.insertNth u rest) = Z (i.insertNth x0 rest))
    (hint : Integrable (fun seed : Fin (T+1) → Noise => H (Z seed) (seed i))
      (Measure.pi (fun _ : Fin (T+1) => ν))) :
    Integrable (fun rest : Fin T → Noise => ∫ u, H (Z (i.insertNth x0 rest)) u ∂ν)
      (Measure.pi (fun _ : Fin T => ν)) ∧
    (∫ seed : Fin (T+1) → Noise, H (Z seed) (seed i)
      ∂Measure.pi (fun _ : Fin (T+1) => ν)) =
      ∫ rest : Fin T → Noise, (∫ u, H (Z (i.insertNth x0 rest)) u ∂ν)
        ∂Measure.pi (fun _ : Fin T => ν) := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (T+1) => Noise) i
  have hp := (measurePreserving_piFinSuccAbove (fun _ : Fin (T+1) => ν) i).symm
  let φ := fun seed : Fin (T+1) → Noise => H (Z seed) (seed i)
  have hi : Integrable (fun p : Noise × (Fin T → Noise) => φ (e.symm p))
      (ν.prod (Measure.pi (fun _ : Fin T => ν))) :=
    (hp.integrable_comp_emb e.symm.measurableEmbedding).2 hint
  have he : (fun p : Noise × (Fin T → Noise) => φ (e.symm p)) =
      fun p => H (Z (i.insertNth x0 p.2)) p.1 := by
    funext p
    change H (Z (i.insertNth p.1 p.2)) (Fin.insertNth (α:=fun _ : Fin (T+1) => Noise) i p.1 p.2 i) = _
    rw [Fin.insertNth_apply_same, hcausal p.2 p.1]
  have hEq := hp.integral_comp e.symm.measurableEmbedding φ
  rw [he] at hi hEq
  refine ⟨hi.integral_prod_right, ?_⟩
  rw [← hEq, integral_prod_symm _ hi]

theorem fresh_integral_le {Noise State : Type*} [MeasurableSpace Noise]
    (ν : Measure Noise) [IsProbabilityMeasure ν] {T : ℕ} (i : Fin (T+1))
    (x0 : Noise) (Z : (Fin (T+1) → Noise) → State) (H : State → Noise → ℝ)
    (hcausal : ∀ rest : Fin T → Noise, ∀ u : Noise,
      Z (i.insertNth u rest) = Z (i.insertNth x0 rest))
    (hint : Integrable (fun seed : Fin (T+1) → Noise => H (Z seed) (seed i))
      (Measure.pi (fun _ : Fin (T+1) => ν))) (C : ℝ)
    (hbound : ∀ z : State, (∫ u, H z u ∂ν) ≤ C) :
    (∫ seed : Fin (T+1) → Noise, H (Z seed) (seed i)
      ∂Measure.pi (fun _ : Fin (T+1) => ν)) ≤ C := by
  obtain ⟨hi, he⟩ := fresh_integral ν i x0 Z H hcausal hint
  rw [he]
  have hh := integral_mono hi (integrable_const C)
    (fun rest : Fin T → Noise => hbound (Z (i.insertNth x0 rest)))
  simpa only [integral_const, probReal_univ, one_smul] using hh

end PaperFreshSeedIntegration

end
end
-- END FreshSeedIntegration.lean

-- BEGIN StochasticEntropy.lean
section

/-! Actual adaptive two-value Laplace entropy iterates on a finite independent
seed. Dependencies: EntropyRegret, LaplaceEstimator and its dependencies. Fresh
seed integration and the analytic supporting theorem are assembled separately. -/
noncomputable section
namespace PaperStochasticEntropy
open MeasureTheory
open PaperEntropyRegret PaperLaplace PaperProductVariance PaperOddDifference

abbrev Raw (n : ℕ) := Fin n → ℝ
abbrev Seed (n T : ℕ) := Fin T → Raw n

def seedLaw (n T : ℕ) : Measure (Seed n T) := Measure.pi (fun _ : Fin T => productLaw n)

instance seedLaw_probability (n T : ℕ) : IsProbabilityMeasure (seedLaw n T) := by
  unfold seedLaw
  infer_instance

def uniform (n : ℕ) : Raw n := fun _ => (n:ℝ)⁻¹

/-- Exactly the central estimator computed from the two scalar oracle values. -/
def gradient {n : ℕ} (F : Space n → ℝ) (h : ℝ) (z u : Raw n) : Raw n :=
  signEstimator (oddDifference F (WithLp.toLp 1 z) h) (WithLp.toLp 1 u)

def sampleNoise {n T : ℕ} (seed : Seed n T) (t : ℕ) : Raw n :=
  if ht : t < T then seed ⟨t, ht⟩ else 0

/-- The specified update, not an arbitrary adapted sequence. -/
def state {n : ℕ} (F : Space n → ℝ) (eta h : ℝ) (U : ℕ → Raw n) : ℕ → Raw n
  | 0 => uniform n
  | t+1 => update (state F eta h U t) (gradient F h (state F eta h U t) (U t)) eta

def actualState {n T : ℕ} (F : Space n → ℝ) (eta h : ℝ)
    (seed : Seed n T) (t : ℕ) : Raw n := state F eta h (sampleNoise seed) t

def actualGradient {n T : ℕ} (F : Space n → ℝ) (eta h : ℝ)
    (seed : Seed n T) (t : ℕ) : Raw n :=
  gradient F h (actualState F eta h seed t) (sampleNoise seed t)

def actualK {n T : ℕ} (F : Space n → ℝ) (eta h : ℝ)
    (seed : Seed n T) (t : ℕ) : ℝ :=
  |oddDifference F (WithLp.toLp 1 (actualState F eta h seed t)) h
    (WithLp.toLp 1 (sampleNoise seed t))|

theorem uniform_pos {n : ℕ} (hn : 0 < n) (i : Fin n) : 0 < uniform n i := by
  unfold uniform
  positivity

theorem uniform_sum {n : ℕ} (hn : 0 < n) : (∑ i, uniform n i) = 1 := by
  have hnR : (n:ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  simp [uniform, hnR]

theorem gradient_measurable {n : ℕ} (F : Space n → ℝ) (hF : Measurable F) (h : ℝ) :
    Measurable (fun p : Raw n × Raw n => gradient F h p.1 p.2) := by
  have hz : Measurable (fun p : Raw n × Raw n => (WithLp.toLp 1 p.1 : Space n)) :=
    (PiLp.continuous_toLp 1 _).measurable.comp measurable_fst
  have hu : Measurable (fun p : Raw n × Raw n => (WithLp.toLp 1 p.2 : Space n)) :=
    (PiLp.continuous_toLp 1 _).measurable.comp measurable_snd
  apply measurable_pi_lambda
  intro i
  exact (((hF.comp (hz.add (hu.const_smul h))).sub
    (hF.comp (hz.sub (hu.const_smul h)))).div_const (2*h)).mul
      (real_sign_measurable.comp ((measurable_pi_apply i).comp measurable_snd))

theorem update_measurable (n : ℕ) (eta : ℝ) :
    Measurable (fun p : Raw n × Raw n => update p.1 p.2 eta) := by
  apply measurable_pi_lambda
  intro i
  unfold update normalizer
  fun_prop

theorem sampleNoise_measurable (n T t : ℕ) :
    Measurable (fun seed : Seed n T => sampleNoise seed t) := by
  by_cases ht : t < T
  · simpa only [sampleNoise, dif_pos ht] using (measurable_pi_apply (⟨t, ht⟩ : Fin T))
  · simpa only [sampleNoise, dif_neg ht] using
      (measurable_const : Measurable (fun _ : Seed n T => (0 : Raw n)))

theorem state_measurable {n Ω} [MeasurableSpace Ω] (F : Space n → ℝ)
    (hF : Measurable F) (eta h : ℝ) (U : Ω → ℕ → Raw n)
    (hU : ∀ t, Measurable (fun ω => U ω t)) (t : ℕ) :
    Measurable (fun ω => state F eta h (U ω) t) := by
  induction t with
  | zero => exact measurable_const
  | succ t ih =>
    exact (update_measurable n eta).comp (ih.prodMk
      ((gradient_measurable F hF h).comp (ih.prodMk (hU t))))

theorem actualState_measurable {n T : ℕ} (F : Space n → ℝ) (hF : Measurable F)
    (eta h : ℝ) (t : ℕ) : Measurable (fun seed : Seed n T => actualState F eta h seed t) :=
  state_measurable F hF eta h sampleNoise (sampleNoise_measurable n T) t

theorem actualGradient_measurable {n T : ℕ} (F : Space n → ℝ) (hF : Measurable F)
    (eta h : ℝ) (t : ℕ) : Measurable (fun seed : Seed n T => actualGradient F eta h seed t) :=
  (gradient_measurable F hF h).comp
    ((actualState_measurable F hF eta h t).prodMk (sampleNoise_measurable n T t))

theorem state_causal {n : ℕ} (F : Space n → ℝ) (eta h : ℝ)
    (U V : ℕ → Raw n) (t : ℕ) (hUV : ∀ j < t, U j = V j) :
    state F eta h U t = state F eta h V t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    have hpast : ∀ j < t, U j = V j := fun j hj => hUV j (by omega)
    simp only [state, ih hpast, hUV t (by omega)]

theorem actualState_simplex {n T : ℕ} (hn : 0 < n) (F : Space n → ℝ)
    (eta h : ℝ) (seed : Seed n T) (t : ℕ) :
    (∀ i, 0 < actualState F eta h seed t i) ∧
      (∑ i, actualState F eta h seed t i) = 1 := by
  induction t with
  | zero => exact ⟨uniform_pos hn, uniform_sum hn⟩
  | succ t ih => exact ⟨update_pos _ _ _ ih.1 ih.2, update_sum _ _ _ ih.1 ih.2⟩

theorem actualK_nonneg {n T : ℕ} (F : Space n → ℝ) (eta h : ℝ)
    (seed : Seed n T) (t : ℕ) : 0 ≤ actualK F eta h seed t := abs_nonneg _

theorem actualGradient_bound {n T : ℕ} (F : Space n → ℝ) (eta h : ℝ)
    (seed : Seed n T) (t : ℕ) (i : Fin n) :
    |actualGradient F eta h seed t i| ≤ actualK F eta h seed t := by
  change |oddDifference F (WithLp.toLp 1 (actualState F eta h seed t)) h
    (WithLp.toLp 1 (sampleNoise seed t)) * Real.sign (sampleNoise seed t i)| ≤ _
  rw [abs_mul]
  have hs : |Real.sign (sampleNoise seed t i)| ≤ 1 := by
    rcases Real.sign_apply_eq (sampleNoise seed t i) with hh | hh | hh <;> rw [hh] <;> norm_num
  exact mul_le_of_le_one_right (abs_nonneg _) hs

end PaperStochasticEntropy

end
end
-- END StochasticEntropy.lean

-- BEGIN StochasticMoments.lean
section

/-! Actual adaptive estimator moments under a finite independent product seed.
Dependencies: StochasticEntropy, FreshSeedIntegration and their dependencies.
The state is the actual recursive entropy update. The fresh-noise moment bound
comes from the proved Laplace second-moment theorem and actual Pi-law Fubini. -/
noncomputable section
namespace PaperStochasticMoments
open MeasureTheory
open PaperStochasticEntropy PaperEntropyRegret PaperLaplace PaperProductVariance PaperOddDifference
open PaperLaplaceEstimator PaperFreshSeedIntegration

theorem actualState_insertNth {n T : ℕ} (F : Space n → ℝ) (eta h : ℝ)
    (i : Fin (T+1)) (rest : Fin T → Raw n) (u v : Raw n) :
    actualState F eta h (i.insertNth u rest) i.val =
      actualState F eta h (i.insertNth v rest) i.val := by
  unfold actualState
  apply state_causal
  intro j hj
  have hjT : j < T+1 := lt_trans hj i.isLt
  have hji : (⟨j, hjT⟩ : Fin (T+1)) < i := hj
  simp only [sampleNoise, dif_pos hjT]
  rw [Fin.insertNth_apply_below hji, Fin.insertNth_apply_below hji]

theorem actualK_measurable {n T : ℕ} (F : Space n → ℝ) (hF : Measurable F)
    (eta h : ℝ) (t : ℕ) : Measurable (fun seed : Seed n T => actualK F eta h seed t) := by
  have hz : Measurable (fun seed : Seed n T => (WithLp.toLp 1 (actualState F eta h seed t) : Space n)) :=
    (PiLp.continuous_toLp 1 _).measurable.comp (actualState_measurable F hF eta h t)
  have hu : Measurable (fun seed : Seed n T => (WithLp.toLp 1 (sampleNoise seed t) : Space n)) :=
    (PiLp.continuous_toLp 1 _).measurable.comp (sampleNoise_measurable n T t)
  exact (((hF.comp (hz.add (hu.const_smul h))).sub
    (hF.comp (hz.sub (hu.const_smul h)))).div_const (2*h)).abs

theorem actualK_le_noise_norm {n T : ℕ} (F : Space n → ℝ) (hF : LipschitzWith 1 F)
    (eta h : ℝ) (hh : 0 < h) (seed : Seed n T) (t : ℕ) :
    actualK F eta h seed t ≤ ‖(WithLp.toLp 1 (sampleNoise seed t) : Space n)‖ := by
  have hd := (oddDifference_lipschitz F hF (WithLp.toLp 1 (actualState F eta h seed t)) h hh).dist_le_mul
    (WithLp.toLp 1 (sampleNoise seed t)) 0
  simpa only [actualK, NNReal.coe_one, one_mul, oddDifference_zero, Real.dist_eq,
    sub_zero, dist_zero_right, Real.norm_eq_abs] using hd

theorem noise_norm_sq_integrable (n : ℕ) :
    Integrable (fun u : Raw n => ‖(WithLp.toLp 1 u : Space n)‖^2) (productLaw n) :=
  (product_vector_memLp n laplaceLaw laplace_id_memLp_two).norm.integrable_sq

theorem actualK_sq_integrable {n T : ℕ} (F : Space n → ℝ) (hF : LipschitzWith 1 F)
    (eta h : ℝ) (hh : 0 < h) (t : ℕ) (ht : t < T) :
    Integrable (fun seed : Seed n T => (actualK F eta h seed t)^2) (seedLaw n T) := by
  have hp : MeasurePreserving (Function.eval (⟨t, ht⟩ : Fin T)) (seedLaw n T) (productLaw n) :=
    measurePreserving_eval (μ := fun _ : Fin T => productLaw n) ⟨t, ht⟩
  have hn := hp.integrable_comp_of_integrable (noise_norm_sq_integrable n)
  have hn' : Integrable (fun seed : Seed n T =>
      ‖(WithLp.toLp 1 (sampleNoise seed t) : Space n)‖^2) (seedLaw n T) := by
    simpa only [sampleNoise, dif_pos ht, Function.comp_def] using hn
  apply hn'.mono' ((actualK_measurable F hF.continuous.measurable eta h t).pow_const 2).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun seed => by
    have hk := actualK_le_noise_norm F hF eta h hh seed t
    have hk0 := actualK_nonneg F eta h seed t
    change |(actualK F eta h seed t)^2| ≤ _
    rw [abs_of_nonneg (sq_nonneg _)]
    nlinarith [norm_nonneg (WithLp.toLp 1 (sampleNoise seed t) : Space n)])

/-- The variance bound is applied after conditioning on every actual past state,
then integrated over the independent current product-law noise coordinate. -/
theorem actualK_second_moment {n T : ℕ} (F : Space n → ℝ) (hF : LipschitzWith 1 F)
    (eta h : ℝ) (hh : 0 < h) (t : ℕ) (ht : t < T) :
    (∫ seed : Seed n T, (actualK F eta h seed t)^2 ∂seedLaw n T) ≤ 2*n := by
  cases T with
  | zero => omega
  | succ T =>
    let i : Fin (T+1) := ⟨t, ht⟩
    let H : Raw n → Raw n → ℝ := fun z u =>
      (oddDifference F (WithLp.toLp 1 z) h (WithLp.toLp 1 u))^2
    have he : (fun seed : Seed n (T+1) => (actualK F eta h seed t)^2) =
        fun seed => H (actualState F eta h seed t) (seed i) := by
      funext seed
      simp only [actualK, H, sampleNoise, dif_pos ht, sq_abs, i]
    change (∫ seed : Seed n (T+1), (actualK F eta h seed t)^2
      ∂Measure.pi (fun _ : Fin (T+1) => productLaw n)) ≤ 2*n
    rw [he]
    apply fresh_integral_le (productLaw n) i (0 : Raw n)
      (fun seed : Seed n (T+1) => actualState F eta h seed t) H
    · intro rest u
      exact actualState_insertNth F eta h i rest u 0
    · rw [← he]
      exact actualK_sq_integrable F hF eta h hh t ht
    · intro z
      exact laplace_oddDifference_second_moment n F hF (WithLp.toLp 1 z) h hh

theorem actualK_second_moment_four {n T : ℕ} (F : Space n → ℝ) (hF : LipschitzWith 1 F)
    (eta h : ℝ) (hh : 0 < h) (t : ℕ) (ht : t < T) :
    (∫ seed : Seed n T, (actualK F eta h seed t)^2 ∂seedLaw n T) ≤ 4*n := by
  apply (actualK_second_moment F hF eta h hh t ht).trans
  have hn : (0:ℝ) ≤ n := by positivity
  linarith

end PaperStochasticMoments

end
end
-- END StochasticMoments.lean

-- BEGIN StochasticRegret.lean
section

/-! Integrability and expected entropy regret for the actual adaptive Laplace
trajectory. Dependencies: StochasticMoments and its dependencies. There are no
assumed moment or expected-regret conclusions in this file. -/
noncomputable section
namespace PaperStochasticRegret
open MeasureTheory
open PaperEntropyRegret PaperLaplace PaperProductVariance PaperOddDifference
open PaperStochasticEntropy PaperStochasticMoments

theorem simplex_norm_one {n : ℕ} (z : Raw n) (hz : ∀ i, 0 ≤ z i) (hs : ∑ i, z i = 1) :
    ‖(WithLp.toLp 1 z : Space n)‖ = 1 := by
  simp only [PiLp.norm_eq_of_L1, Real.norm_eq_abs]
  calc
    (∑ i, |z i|) = ∑ i, z i := Finset.sum_congr rfl (fun i _ => abs_of_nonneg (hz i))
    _ = 1 := hs

theorem actualState_memLp {n T : ℕ} (hn : 0 < n) (F : Space n → ℝ)
    (hF : LipschitzWith 1 F) (eta h : ℝ) (t : ℕ) :
    MemLp (fun seed : Seed n T => (WithLp.toLp 1 (actualState F eta h seed t) : Space n)) 2
      (seedLaw n T) := by
  have hm : Measurable (fun seed : Seed n T => (WithLp.toLp 1 (actualState F eta h seed t) : Space n)) :=
    (PiLp.continuous_toLp 1 _).measurable.comp
      (actualState_measurable F hF.continuous.measurable eta h t)
  apply (memLp_const (1:ℝ)).of_le hm.aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun seed => by
    obtain ⟨hz, hs⟩ := actualState_simplex hn F eta h seed t
    rw [simplex_norm_one _ (fun i => (hz i).le) hs]
    norm_num)

theorem actualValue_memLp {n T : ℕ} (hn : 0 < n) (F : Space n → ℝ)
    (hF : LipschitzWith 1 F) (eta h : ℝ) (t : ℕ)
    (φ : Space n → ℝ) (hφ : LipschitzWith 1 φ) :
    MemLp (fun seed : Seed n T => φ (WithLp.toLp 1 (actualState F eta h seed t))) 2
      (seedLaw n T) :=
  lipschitz_memLp_two (seedLaw n T) _ (actualState_memLp hn F hF eta h t) φ hφ

theorem actualK_integrable {n T : ℕ} (F : Space n → ℝ) (hF : LipschitzWith 1 F)
    (eta h : ℝ) (hh : 0 < h) (t : ℕ) (ht : t < T) :
    Integrable (fun seed : Seed n T => actualK F eta h seed t) (seedLaw n T) := by
  have hm : MemLp (fun seed : Seed n T => actualK F eta h seed t) 2 (seedLaw n T) :=
    (memLp_two_iff_integrable_sq (actualK_measurable F hF.continuous.measurable eta h t).aestronglyMeasurable).2
      (actualK_sq_integrable F hF eta h hh t ht)
  exact hm.integrable (by norm_num)

theorem regret_round_integrable {n T : ℕ} (hn : 0 < n) (F : Space n → ℝ)
    (hF : LipschitzWith 1 F) (eta h : ℝ) (hh : 0 < h)
    (x : Raw n) (hx : ∀ i, 0 ≤ x i) (hsx : ∑ i, x i = 1) (t : ℕ) (ht : t < T) :
    Integrable (fun seed : Seed n T => ∑ i,
      actualGradient F eta h seed t i * (actualState F eta h seed t i - x i)) (seedLaw n T) := by
  apply integrable_finsetSum
  intro i _
  have hGi : Integrable (fun seed : Seed n T => actualGradient F eta h seed t i) (seedLaw n T) := by
    apply (actualK_integrable F hF eta h hh t ht).mono'
      (((measurable_pi_apply i).comp
        (actualGradient_measurable F hF.continuous.measurable eta h t)).aestronglyMeasurable)
    exact Filter.Eventually.of_forall (fun seed => by
      simpa only [Real.norm_eq_abs, Function.comp_def] using actualGradient_bound F eta h seed t i)
  apply hGi.mul_bdd
  · exact (((measurable_pi_apply i).comp
      (actualState_measurable F hF.continuous.measurable eta h t)).sub_const (x i)).aestronglyMeasurable
  · exact Filter.Eventually.of_forall (fun seed => by
      obtain ⟨hz, hsz⟩ := actualState_simplex hn F eta h seed t
      have hzi : actualState F eta h seed t i ≤ 1 := by
        rw [← hsz]
        exact Finset.single_le_sum (fun j _ => (hz j).le) (Finset.mem_univ i)
      have hxi : x i ≤ 1 := by
        rw [← hsx]
        exact Finset.single_le_sum (fun j _ => hx j) (Finset.mem_univ i)
      change |actualState F eta h seed t i - x i| ≤ (1:ℝ)
      exact abs_le.2 ⟨by linarith [hz i, hx i], by linarith [hz i, hx i]⟩)

theorem regret_sum_integrable {n T : ℕ} (hn : 0 < n) (F : Space n → ℝ)
    (hF : LipschitzWith 1 F) (eta h : ℝ) (hh : 0 < h)
    (x : Raw n) (hx : ∀ i, 0 ≤ x i) (hsx : ∑ i, x i = 1) :
    Integrable (fun seed : Seed n T => ∑ t ∈ Finset.range T, ∑ i,
      actualGradient F eta h seed t i * (actualState F eta h seed t i - x i)) (seedLaw n T) :=
  integrable_finsetSum _ (fun t ht => regret_round_integrable hn F hF eta h hh x hx hsx t (Finset.mem_range.1 ht))

/-- The proved abstract entropy trajectory is exactly the actual feedback
trajectory when its gradients are computed from this same trajectory's queries. -/
theorem actualState_eq_trajectory {n T : ℕ} (F : Space n → ℝ)
    (eta h : ℝ) (seed : Seed n T) (t : ℕ) :
    actualState F eta h seed t =
      trajectory (uniform n) (fun s => actualGradient F eta h seed s) eta t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    change update (actualState F eta h seed t) (actualGradient F eta h seed t) eta =
      update (trajectory (uniform n) (fun s => actualGradient F eta h seed s) eta t)
        (actualGradient F eta h seed t) eta
    rw [ih]

/-- Expected regret now follows from actual finite-product Laplace randomness,
actual queries, actual updates and the proved estimator second moment. -/
theorem expected_actual_regret {n T : ℕ} (hn : 0 < n) (F : Space n → ℝ)
    (hF : LipschitzWith 1 F) (eta h : ℝ) (heta : 0 < eta) (hh : 0 < h)
    (x : Raw n) (hx : ∀ i, 0 ≤ x i) (hsx : ∑ i, x i = 1) :
    (∫ seed : Seed n T, (∑ t ∈ Finset.range T, ∑ i,
      actualGradient F eta h seed t i * (actualState F eta h seed t i - x i)) ∂seedLaw n T) ≤
      Real.log n / eta + 2*eta*n*T := by
  have hRi : Integrable (fun seed : Seed n T => ∑ t ∈ Finset.range T, ∑ i,
      actualGradient F eta h seed t i *
        (trajectory (uniform n) (fun s => actualGradient F eta h seed s) eta t i - x i)) (seedLaw n T) := by
    simpa only [actualState_eq_trajectory] using regret_sum_integrable hn F hF eta h hh x hx hsx
  have hbound := expected_trajectory_regret (seedLaw n T) x (uniform n)
    (fun seed t => actualGradient F eta h seed t) eta (fun seed t => actualK F eta h seed t)
    hx hsx (uniform_pos hn) (uniform_sum hn) T heta
    (fun seed _ _ => actualK_nonneg F eta h seed _) (fun seed _ _ i => actualGradient_bound F eta h seed _ i)
    (fun t ht => actualK_sq_integrable F hF eta h hh t ht)
    (fun t ht => actualK_second_moment_four F hF eta h hh t ht) hRi
  have hbound' : (∫ seed : Seed n T, (∑ t ∈ Finset.range T, ∑ i,
      actualGradient F eta h seed t i * (actualState F eta h seed t i - x i)) ∂seedLaw n T) ≤
      entropy x (uniform n) / eta + 2*eta*n*T := by
    simpa only [← actualState_eq_trajectory] using hbound
  have hEnt : entropy x (uniform n) ≤ Real.log n := entropy_uniform_bound hn x hx hsx
  have hdiv := div_le_div_of_nonneg_right hEnt heta.le
  linarith

end PaperStochasticRegret

end
end
-- END StochasticRegret.lean

-- BEGIN StochasticSupport.lean
section

/-! True fresh-noise supporting inequalities along the actual adaptive iterates.
Dependencies: StochasticRegret and ProductLaplaceScore with their dependencies.
The supporting inequality is the proved high-dimensional Laplace score theorem;
the actual finite seed law is disintegrated by the proved fresh Pi-coordinate
Fubini lemma. No unbiasedness or expected-regret conclusion is a hypothesis. -/
noncomputable section
namespace PaperStochasticSupport
open MeasureTheory
open PaperEntropyRegret PaperLaplace PaperProductVariance PaperOddDifference PaperLaplaceEstimator
open PaperStochasticEntropy PaperStochasticMoments PaperStochasticRegret PaperFreshSeedIntegration
open PaperProductLaplaceDensity PaperProductLaplaceScore

theorem smoothing_gap_integrable {n T : ℕ} (hn : 0 < n) (F : Space n → ℝ)
    (hF : LipschitzWith 1 F) (eta h : ℝ) (x : Raw n) (t : ℕ) :
    Integrable (fun seed : Seed n T =>
      smoothingL1 F h (WithLp.toLp 1 (actualState F eta h seed t)) - smoothingL1 F h (WithLp.toLp 1 x))
      (seedLaw n T) :=
  ((actualValue_memLp hn F hF eta h t (smoothingL1 F h) (smoothingL1_lipschitz F hF h)).integrable
    (by norm_num)).sub (integrable_const _)

/-- The analytic fixed-state supporting inequality remains valid in expectation
for the actual state computed before the independent current Laplace vector. -/
theorem expected_smoothing_gap_le_regret {n T : ℕ} (hn : 0 < n) (F : Space n → ℝ)
    (hF : LipschitzWith 1 F) (hconvex : ConvexOn ℝ Set.univ F)
    (eta h : ℝ) (hh : 0 < h) (x : Raw n) (hx : ∀ i, 0 ≤ x i) (hsx : ∑ i, x i = 1)
    (t : ℕ) (ht : t < T) :
    (∫ seed : Seed n T,
      (smoothingL1 F h (WithLp.toLp 1 (actualState F eta h seed t)) -
        smoothingL1 F h (WithLp.toLp 1 x)) ∂seedLaw n T) ≤
      ∫ seed : Seed n T, (∑ i, actualGradient F eta h seed t i *
        (actualState F eta h seed t i - x i)) ∂seedLaw n T := by
  cases T with
  | zero => omega
  | succ T =>
    let i : Fin (T+1) := ⟨t, ht⟩
    let H : Raw n → Raw n → ℝ := fun z u =>
      smoothingL1 F h (WithLp.toLp 1 z) - smoothingL1 F h (WithLp.toLp 1 x) -
        ∑ j, gradient F h z u j * (z j - x j)
    have hGap := smoothing_gap_integrable (T:=T+1) hn F hF eta h x t
    have hReg := regret_round_integrable (T:=T+1) hn F hF eta h hh x hx hsx t ht
    have he : (fun seed : Seed n (T+1) => H (actualState F eta h seed t) (seed i)) =
        fun seed =>
          (smoothingL1 F h (WithLp.toLp 1 (actualState F eta h seed t)) -
            smoothingL1 F h (WithLp.toLp 1 x)) -
          (∑ j, actualGradient F eta h seed t j * (actualState F eta h seed t j - x j)) := by
      funext seed
      simp only [H, actualGradient, sampleNoise, dif_pos ht, i]
    have hInt : Integrable (fun seed : Seed n (T+1) => H (actualState F eta h seed t) (seed i))
        (seedLaw n (T+1)) := by
      rw [he]
      exact hGap.sub hReg
    have hBound : ∀ z : Raw n, (∫ u, H z u ∂productLaw n) ≤ (0:ℝ) := by
      intro z
      have hi := estimator_gap_integrable F hF h (WithLp.toLp 1 z) (WithLp.toLp 1 x)
      have hs := expected_estimator_supports_smoothing F hF hconvex h hh
        (WithLp.toLp 1 z) (WithLp.toLp 1 x)
      change Integrable (fun u : Raw n => ∑ j, gradient F h z u j * (z j - x j)) (productLaw n) at hi
      change smoothingL1 F h (WithLp.toLp 1 z) - smoothingL1 F h (WithLp.toLp 1 x) ≤
        ∫ u : Raw n, ∑ j, gradient F h z u j * (z j - x j) ∂productLaw n at hs
      change (∫ u : Raw n, (smoothingL1 F h (WithLp.toLp 1 z) - smoothingL1 F h (WithLp.toLp 1 x)) -
        (∑ j, gradient F h z u j * (z j - x j)) ∂productLaw n) ≤ 0
      rw [integral_sub (integrable_const _) hi, integral_const]
      simp only [probReal_univ, one_smul]
      linarith
    have hh' := fresh_integral_le (productLaw n) i (0 : Raw n)
      (fun seed : Seed n (T+1) => actualState F eta h seed t) H
      (fun rest u => actualState_insertNth F eta h i rest u 0) hInt 0 hBound
    rw [he] at hh'
    have hsub := integral_sub hGap hReg
    simp only [seedLaw, Pi.sub_apply] at hsub
    rw [hsub] at hh'
    simpa only [seedLaw] using (sub_nonpos.1 hh')

theorem value_gap_integrable {n T : ℕ} (hn : 0 < n) (F : Space n → ℝ)
    (hF : LipschitzWith 1 F) (eta h : ℝ) (x : Raw n) (t : ℕ) :
    Integrable (fun seed : Seed n T => F (WithLp.toLp 1 (actualState F eta h seed t)) - F (WithLp.toLp 1 x))
      (seedLaw n T) :=
  ((actualValue_memLp hn F hF eta h t F hF).integrable (by norm_num)).sub (integrable_const _)

theorem expected_value_gap_le_regret {n T : ℕ} (hn : 0 < n) (F : Space n → ℝ)
    (hF : LipschitzWith 1 F) (hconvex : ConvexOn ℝ Set.univ F)
    (eta h : ℝ) (hh : 0 < h) (x : Raw n) (hx : ∀ i, 0 ≤ x i) (hsx : ∑ i, x i = 1)
    (t : ℕ) (ht : t < T) :
    (∫ seed : Seed n T,
      (F (WithLp.toLp 1 (actualState F eta h seed t)) - F (WithLp.toLp 1 x)) ∂seedLaw n T) ≤
      (∫ seed : Seed n T, (∑ i, actualGradient F eta h seed t i *
        (actualState F eta h seed t i - x i)) ∂seedLaw n T) + 2*h*n := by
  have hGap := value_gap_integrable (T:=T) hn F hF eta h x t
  have hS := smoothing_gap_integrable (T:=T) hn F hF eta h x t
  have hbias : ∀ seed : Seed n T,
      F (WithLp.toLp 1 (actualState F eta h seed t)) - F (WithLp.toLp 1 x) ≤
        (smoothingL1 F h (WithLp.toLp 1 (actualState F eta h seed t)) -
          smoothingL1 F h (WithLp.toLp 1 x)) + 2*h*n := by
    intro seed
    have hz := laplace_smoothing_abs_bias n F hF (WithLp.toLp 1 (actualState F eta h seed t)) h hh.le
    have hx' := laplace_smoothing_abs_bias n F hF (WithLp.toLp 1 x) h hh.le
    have hz' := abs_le.1 hz
    have hx'' := abs_le.1 hx'
    change |smoothingL1 F h (WithLp.toLp 1 (actualState F eta h seed t)) -
      F (WithLp.toLp 1 (actualState F eta h seed t))| ≤ h*n at hz
    change |smoothingL1 F h (WithLp.toLp 1 x) - F (WithLp.toLp 1 x)| ≤ h*n at hx'
    linarith [abs_le.1 hz, abs_le.1 hx']
  have hi := integral_mono hGap (hS.add (integrable_const (2*h*n))) hbias
  simp only [Pi.add_apply] at hi
  rw [integral_add hS (integrable_const (2*h*n)), integral_const] at hi
  simp only [probReal_univ, one_smul] at hi
  have hs := expected_smoothing_gap_le_regret hn F hF hconvex eta h hh x hx hsx t ht
  linarith

end PaperStochasticSupport

end
end
-- END StochasticSupport.lean

-- BEGIN StochasticUpper.lean
section

/-! The actual finite-round expected objective bound. Dependencies:
StochasticSupport, whose support inequality is proved from the actual Laplace
score identity, and all preceding stochastic construction/moment files. -/
noncomputable section
namespace PaperStochasticUpper
open MeasureTheory
open PaperLaplace PaperProductVariance PaperStochasticEntropy PaperStochasticMoments
open PaperStochasticRegret PaperStochasticSupport

/-- Mean objective gap of the actual T pre-update simplex iterates. Convexity
turns this into the error of their arithmetic mean (the policy's returned point). -/
def averageValueGap {n T : ℕ} (F : Space n → ℝ) (eta h : ℝ) (x : Raw n)
    (seed : Seed n T) : ℝ :=
  (∑ t ∈ Finset.range T,
    (F (WithLp.toLp 1 (actualState F eta h seed t)) - F (WithLp.toLp 1 x))) / (T:ℝ)

theorem averageValueGap_integrable {n T : ℕ} (hn : 0 < n) (F : Space n → ℝ)
    (hF : LipschitzWith 1 F) (eta h : ℝ) (x : Raw n) :
    Integrable (averageValueGap (T:=T) F eta h x) (seedLaw n T) :=
  (integrable_finsetSum _ (fun t _ => value_gap_integrable hn F hF eta h x t)).div_const _

/-- Manuscript MD 177--180 for the actual randomized adaptive algorithm:
no assumed conditional unbiasedness, second moment, or desired regret remains. -/
theorem expected_average_value_gap {n T : ℕ} (hn : 0 < n) (hT : 0 < T)
    (F : Space n → ℝ) (hF : LipschitzWith 1 F) (hconvex : ConvexOn ℝ Set.univ F)
    (eta h : ℝ) (heta : 0 < eta) (hh : 0 < h)
    (x : Raw n) (hx : ∀ i, 0 ≤ x i) (hsx : ∑ i, x i = 1) :
    (∫ seed : Seed n T, averageValueGap F eta h x seed ∂seedLaw n T) ≤
      Real.log n / (eta*T) + 2*eta*n + 2*h*n := by
  have hVint : ∀ t ∈ Finset.range T, Integrable (fun seed : Seed n T =>
      F (WithLp.toLp 1 (actualState F eta h seed t)) - F (WithLp.toLp 1 x)) (seedLaw n T) :=
    fun t _ => value_gap_integrable hn F hF eta h x t
  have hRint : ∀ t ∈ Finset.range T, Integrable (fun seed : Seed n T =>
      ∑ i, actualGradient F eta h seed t i * (actualState F eta h seed t i - x i)) (seedLaw n T) :=
    fun t ht => regret_round_integrable hn F hF eta h hh x hx hsx t (Finset.mem_range.1 ht)
  have hs := Finset.sum_le_sum (fun t (ht : t ∈ Finset.range T) =>
    expected_value_gap_le_regret hn F hF hconvex eta h hh x hx hsx t (Finset.mem_range.1 ht))
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hs
  have hR := expected_actual_regret (T:=T) hn F hF eta h heta hh x hx hsx
  rw [integral_finsetSum (Finset.range T) hRint] at hR
  have hTotal : (∑ t ∈ Finset.range T, ∫ seed : Seed n T,
      F (WithLp.toLp 1 (actualState F eta h seed t)) - F (WithLp.toLp 1 x) ∂seedLaw n T) ≤
      Real.log n / eta + 2*eta*n*T + (T:ℝ)*(2*h*n) := by linarith
  have hTR : (0:ℝ) < T := by exact_mod_cast hT
  unfold averageValueGap
  rw [integral_div, integral_finsetSum (Finset.range T) hVint]
  apply (div_le_iff₀ hTR).2
  have halgebra : (Real.log n / (eta*T) + 2*eta*n + 2*h*n) * (T:ℝ) =
      Real.log n / eta + 2*eta*n*T + (T:ℝ)*(2*h*n) := by
    field_simp [heta.ne', hTR.ne'] <;> ring
  rw [halgebra]
  exact hTotal

end PaperStochasticUpper

end
end
-- END StochasticUpper.lean

-- BEGIN SimplexLift.lean
section

/- Dependencies: Geometry, OracleModel, SimplexAlgorithm.
Two contiguous signed coordinate blocks avoid any unrecorded dimension change. -/
namespace Task003.SimplexLift
open MeasureTheory PaperGeometry Task003.OracleModel PaperSimplexAlgorithm

noncomputable def lift (d : ℕ) (z : Point (d+d)) : Point d :=
  WithLp.toLp 1 (fun i => z (Fin.castAdd d i) - z (Fin.natAdd d i))

theorem lift_add (d : ℕ) (z w : Point (d+d)) : lift d (z+w)=lift d z+lift d w := by
  apply PiLp.ext
  intro i
  change (z (Fin.castAdd d i)+w (Fin.castAdd d i)) -
    (z (Fin.natAdd d i)+w (Fin.natAdd d i)) = _
  change _ = (z (Fin.castAdd d i)-z (Fin.natAdd d i)) +
    (w (Fin.castAdd d i)-w (Fin.natAdd d i))
  ring

theorem lift_smul (d : ℕ) (a : ℝ) (z : Point (d+d)) : lift d (a • z)=a • lift d z := by
  apply PiLp.ext
  intro i
  change a*z (Fin.castAdd d i)-a*z (Fin.natAdd d i)=a*(z (Fin.castAdd d i)-z (Fin.natAdd d i))
  ring

theorem lift_contraction (d : ℕ) (z w : Point (d+d)) :
    ‖lift d z-lift d w‖ ≤ ‖z-w‖ := by
  rw [l1_norm_eq_sum_abs,l1_norm_eq_sum_abs,Fin.sum_univ_add]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  change |(z (Fin.castAdd d i)-z (Fin.natAdd d i))-
    (w (Fin.castAdd d i)-w (Fin.natAdd d i))| ≤
    |z (Fin.castAdd d i)-w (Fin.castAdd d i)|+|z (Fin.natAdd d i)-w (Fin.natAdd d i)|
  convert abs_sub (z (Fin.castAdd d i)-w (Fin.castAdd d i))
    (z (Fin.natAdd d i)-w (Fin.natAdd d i)) using 1 <;> congr 1 <;> ring

theorem lift_lipschitz (d : ℕ) : LipschitzWith 1 (lift d) := by
  apply LipschitzWith.of_dist_le_mul
  intro z w
  simpa only [dist_eq_norm,NNReal.coe_one,one_mul] using lift_contraction d z w

theorem lift_simplex_feasible (d : ℕ) (z : Point (d+d))
    (hz : ∀ i, 0 ≤ z i) (hs : ∑ i, z i = 1) : Feasible 1 (lift d z) := by
  change ‖lift d z‖ ≤ 1
  rw [l1_norm_eq_sum_abs]
  calc
    _ ≤ ∑ i : Fin d, (z (Fin.castAdd d i)+z (Fin.natAdd d i)) := by
      apply Finset.sum_le_sum
      intro i _
      change |z (Fin.castAdd d i)-z (Fin.natAdd d i)| ≤ _
      exact (abs_sub _ _).trans_eq (by rw [abs_of_nonneg (hz _),abs_of_nonneg (hz _)])
    _ = 1 := by rw [Finset.sum_add_distrib,← Fin.sum_univ_add]; exact hs

theorem lift_positiveSimplex_feasible (d : ℕ) (z : PositiveSimplex (d+d)) :
    Feasible 1 (lift d (WithLp.toLp 1 z.val)) :=
  lift_simplex_feasible d _ (fun i => (z.property.1 i).le) z.property.2

theorem lift_simplex_surjective (d : ℕ) (hd : 0 < d) (x : Point d)
    (hx : Feasible 1 x) : ∃ z : Point (d+d),
      (∀ i, 0 ≤ z i) ∧ (∑ i, z i = 1) ∧ lift d z=x := by
  letI : NeZero d := ⟨Nat.ne_of_gt hd⟩
  obtain ⟨s,hs,he⟩ := signedLift_simplex_surjective x hx
  let z : Point (d+d) := WithLp.toLp 1 (Fin.addCases (fun i => s (i,false)) (fun i => s (i,true)))
  refine ⟨z,?_,?_,?_⟩
  · intro i
    refine Fin.addCases (motive := fun i : Fin (d+d) => 0 ≤ z i) (fun j => ?_) (fun j => ?_) i
    · simpa only [z,WithLp.toLp_ofLp,Fin.addCases_left] using hs.1 (j,false)
    · simpa only [z,WithLp.toLp_ofLp,Fin.addCases_right] using hs.1 (j,true)
  · change (∑ i : Fin (d+d), (Fin.addCases (motive := fun _ : Fin (d+d) => ℝ) (fun i : Fin d => s (i,false)) (fun i : Fin d => s (i,true))) i)=1
    rw [Fin.sum_univ_add]
    simp only [Fin.addCases_left,Fin.addCases_right]
    have h := hs.2
    rw [Fintype.sum_prod_type] at h
    simpa only [Fintype.sum_bool,Finset.sum_add_distrib,add_comm] using h
  · rw [← he]
    apply PiLp.ext
    intro i
    change z (Fin.castAdd d i)-z (Fin.natAdd d i)=s (i,false)-s (i,true)
    simp [z]

theorem lifted_objective_convex (d : ℕ) (f : Objective d 1) :
    ConvexOn ℝ Set.univ (f ∘ lift d) := by
  refine ⟨convex_univ,?_⟩
  intro x hx y hy a b ha hb hab
  simpa only [Function.comp_apply,lift_add,lift_smul] using
    f.convex.2 (Set.mem_univ _) (Set.mem_univ _) ha hb hab

theorem lifted_objective_lipschitz (d : ℕ) (f : Objective d 1) :
    LipschitzWith 1 (f ∘ lift d) := by
  simpa only [Real.toNNReal_one,one_mul] using f.lip.comp (lift_lipschitz d)

end Task003.SimplexLift


end
-- END SimplexLift.lean

-- BEGIN PolicyStochasticBridge.lean
section

/- Dependencies: TwoPointPolicy, SimplexLift, StochasticEntropy.
This identifies the actual capped scalar-oracle policy with the independently
analysed finite-product Laplace recursion. -/
namespace Task003.PolicyStochasticBridge
open MeasureTheory Task003.OracleModel Task003.TwoPointPolicy
open PaperSimplexAlgorithm PaperProductVariance

variable {n : ℕ}

theorem rounds_state (hn : 0 < n) (F : Space n → ℝ) (η h : ℝ)
    (u : ℕ → Fin n → ℝ) (t : ℕ) :
    (rounds hn (fun z => F (WithLp.toLp 1 z)) η h u t).1.val =
      PaperStochasticEntropy.state F η h u t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    change PaperEntropyRegret.update
      (rounds hn (fun z => F (WithLp.toLp 1 z)) η h u t).1.val
      (fun i => _ ) η = _
    rw [ih]
    rfl

noncomputable def averagedState {T : ℕ} (F : Space n → ℝ) (η h : ℝ)
    (seed : PaperStochasticEntropy.Seed n T) : Fin n → ℝ :=
  ∑ t ∈ Finset.range T, (T : ℝ)⁻¹ • PaperStochasticEntropy.actualState F η h seed t

theorem rounds_average_state {T : ℕ} (hn : 0 < n) (F : Space n → ℝ) (η h : ℝ)
    (seed : PaperStochasticEntropy.Seed n T) (hT : 0 < T) :
    (rounds hn (fun z => F (WithLp.toLp 1 z)) η h
      (PaperStochasticEntropy.sampleNoise seed) T).2.1.val = averagedState F η h seed := by
  rw [rounds_average_eq hn _ η h _ T hT]
  unfold averagedState PaperStochasticEntropy.actualState
  apply Finset.sum_congr rfl
  intro t ht
  rw [rounds_state]

noncomputable def canonicalPolicy (d : ℕ) (hd : 0 < d) (η h : ℝ) (T : ℕ) :
    Policy d 1 (PaperStochasticEntropy.Seed (d+d) T) :=
  policy (by omega) η h PaperStochasticEntropy.sampleNoise
    (PaperStochasticEntropy.sampleNoise_measurable (d+d) T)
    (fun z => Task003.SimplexLift.lift d (WithLp.toLp 1 z))
    ((Task003.SimplexLift.lift_lipschitz d).continuous.measurable.comp
      (PiLp.continuous_toLp 1 _).measurable)
    (Task003.SimplexLift.lift_positiveSimplex_feasible d)

theorem canonicalPolicy_output (d : ℕ) (hd : 0 < d) (η h : ℝ) (T : ℕ) (hT : 0 < T)
    (f : Objective d 1) (seed : PaperStochasticEntropy.Seed (d+d) T) :
    run (canonicalPolicy d hd η h T) f (2*T) seed =
      Task003.SimplexLift.lift d (WithLp.toLp 1
        (averagedState (f ∘ Task003.SimplexLift.lift d) η h seed)) := by
  unfold canonicalPolicy
  rw [run_policy_even]
  change Task003.SimplexLift.lift d (WithLp.toLp 1
    (rounds (by omega) (fun z => (f ∘ Task003.SimplexLift.lift d) (WithLp.toLp 1 z))
      η h (PaperStochasticEntropy.sampleNoise seed) T).2.1.val) = _
  rw [rounds_average_state _ _ _ _ _ hT]

end Task003.PolicyStochasticBridge


end
-- END PolicyStochasticBridge.lean

-- BEGIN PolicyGap.lean
section

/- Dependencies: OracleModel, ProbabilityTransfers. Real Markov conversion
on the exact arbitrary-seed/pathwise-cap oracle model. -/
namespace Task003.PolicyGap
open MeasureTheory Set Task003.OracleModel

variable {d m : ℕ} {Ω : Type} [MeasurableSpace Ω]

theorem policy_gap_bounds (a : Policy d 1 Ω) (f : Objective d 1) (ω : Ω) :
    0 ≤ f (run a f m ω)-optimum 1 f ∧
      f (run a f m ω)-optimum 1 f ≤ 2 := by
  obtain ⟨x,hx,hval,hmin⟩ := optimum_attained f (by norm_num : (0:ℝ)≤1)
  have hy := run_feasible a f m ω
  have hlo := hmin _ hy
  change ‖x‖ ≤ 1 at hx
  change ‖run a f m ω‖ ≤ 1 at hy
  have hfd := f.lip.dist_le_mul (run a f m ω) x
  rw [Real.toNNReal_one,NNReal.coe_one,one_mul,Real.dist_eq,dist_eq_norm] at hfd
  have hn : ‖run a f m ω-x‖ ≤ 2 :=
    (norm_sub_le _ _).trans (by change ‖run a f m ω‖+‖x‖≤2; linarith)
  rw [hval]
  exact ⟨sub_nonneg.mpr hlo,(le_abs_self _).trans (hfd.trans hn)⟩

theorem policy_gap_measurable (a : Policy d 1 Ω) (f : Objective d 1) :
    Measurable (fun ω => f (run a f m ω)-optimum 1 f) :=
  (f.continuous.measurable.comp (run_measurable a f f.continuous.measurable m)).sub measurable_const

theorem policy_gap_integrable (μ : Measure Ω) [IsProbabilityMeasure μ]
    (a : Policy d 1 Ω) (f : Objective d 1) :
    Integrable (fun ω => f (run a f m ω)-optimum 1 f) μ := by
  apply (integrable_const (2:ℝ)).mono'
    (policy_gap_measurable a f).aestronglyMeasurable
  exact ae_of_all μ (fun ω => by
    rw [Real.norm_eq_abs,abs_of_nonneg (policy_gap_bounds a f ω).1]
    exact (policy_gap_bounds a f ω).2)

/-- The law and policy are fixed before the universal objective quantifier.
This is the actual per-fixed-objective 2/3 guarantee of the manuscript. -/
theorem solvesOn_of_expected_gap (μ : Measure Ω) [IsProbabilityMeasure μ]
    (a : Policy d 1 Ω) (α : ℝ) (hα : 0 < α)
    (he : ∀ f : Objective d 1,
      (∫ ω, f (run a f m ω)-optimum 1 f ∂μ) ≤ α/3) :
    SolvesOn μ a m 1 α := by
  intro f
  have hs := PaperProbabilityTransfers.markov_success μ
    (fun ω => f (run a f m ω)-optimum 1 f)
    (policy_gap_measurable a f) (policy_gap_integrable μ a f)
    (ae_of_all μ (fun ω => (policy_gap_bounds a f ω).1)) α hα (he f)
  change (2/3:ℝ)≤(μ (successEvent a f m α)).toReal at hs
  have he := (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top μ (successEvent a f m α))).mpr hs
  rw [ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ)<3),ENNReal.ofReal_ofNat,ENNReal.ofReal_ofNat] at he
  exact he

theorem admissible_of_expected_gap (μ : Measure Ω) [IsProbabilityMeasure μ]
    (a : Policy d 1 Ω) (α : ℝ) (hα : 0 < α)
    (he : ∀ f : Objective d 1,
      (∫ ω, f (run a f m ω)-optimum 1 f ∂μ) ≤ α/3) :
    AdmissibleBudget d m 1 1 α :=
  ⟨Ω,inferInstance,μ,inferInstance,a,solvesOn_of_expected_gap μ a α hα he⟩

end Task003.PolicyGap


end
-- END PolicyGap.lean

-- BEGIN UpperParameters.lean
section

/- Dependencies: BoundsArithmetic. Exact manuscript h,T,eta; no optimisation
or probability inequality is postulated here. -/
namespace Task003.UpperParameters

noncomputable def iterations (n : ℕ) (α : ℝ) : ℕ :=
  ⌈288*(n : ℝ)*Real.log n/α^2⌉₊

noncomputable def radius (n : ℕ) (α : ℝ) : ℝ := α/(12*n)

noncomputable def stepsize (n T : ℕ) : ℝ := Real.sqrt (Real.log n/(2*n*T))

theorem iterations_pos {n : ℕ} {α : ℝ} (hn : 2 ≤ n) (hα : 0 < α) :
    0 < iterations n α := by
  have hnR : (1 : ℝ)<n := by exact_mod_cast (by omega : 1<n)
  have hp : 0 < 288*(n : ℝ)*Real.log n/α^2 := by
    have hl := Real.log_pos hnR
    positivity
  exact Nat.ceil_pos.mpr hp

theorem iterations_budget (n : ℕ) (α : ℝ) :
    288*(n : ℝ)*Real.log n/α^2 ≤ iterations n α := Nat.le_ceil _

theorem stepsize_pos {n T : ℕ} (hn : 2 ≤ n) (hT : 0 < T) :
    0 < stepsize n T := by
  have hnR : (1 : ℝ)<n := by exact_mod_cast (by omega : 1<n)
  have hl := Real.log_pos hnR
  unfold stepsize
  positivity

theorem stepsize_regret_identity {n T : ℕ} (hn : 2 ≤ n) (hT : 0 < T) :
    Real.log n/(stepsize n T*T)+2*stepsize n T*n =
      2*Real.sqrt (2*n*Real.log n/T) := by
  have hnR : (0 : ℝ)<n := by exact_mod_cast (by omega : 0<n)
  have hTR : (0 : ℝ)<T := by exact_mod_cast hT
  have hl : 0 ≤ Real.log n := (Real.log_pos (by exact_mod_cast (by omega : 1<n))).le
  have he := stepsize_pos hn hT
  have heq : stepsize n T^2=Real.log n/(2*n*T) :=
    Real.sq_sqrt (by positivity)
  have hbal : Real.log n/(stepsize n T*T)=2*n*stepsize n T := by
    apply (div_eq_iff (mul_ne_zero he.ne' hTR.ne')).mpr
    calc
      _ = stepsize n T^2*(2*n*T) := by rw [heq,div_mul_cancel₀ _ (by positivity)]
      _ = _ := by ring
  have hsq : (2*n*stepsize n T)^2=2*n*Real.log n/T := by
    rw [mul_pow,mul_pow,heq]
    field_simp
    <;> ring
  have hsroot := Real.sq_sqrt (show 0 ≤ 2*(n : ℝ)*Real.log n/T by positivity)
  have hroot : 2*n*stepsize n T=Real.sqrt (2*n*Real.log n/T) := by
    exact (sq_eq_sq₀ (show 0 ≤ 2*(n : ℝ)*stepsize n T by positivity)
      (Real.sqrt_nonneg _)).mp (hsq.trans hsroot.symm)
  rw [hbal,← hroot]
  ring

theorem parameters_error_bound {n : ℕ} {α : ℝ} (hn : 2 ≤ n) (hα : 0 < α) :
    Real.log n/(stepsize n (iterations n α)*iterations n α)+
      2*stepsize n (iterations n α)*n+2*radius n α*n ≤ α/3 := by
  have hnR : (0 : ℝ)<n := by exact_mod_cast (by omega : 0<n)
  have hT := iterations_pos hn hα
  have hTR : (0 : ℝ) < iterations n α := by exact_mod_cast hT
  have hl : 0 ≤ Real.log n := (Real.log_pos (by exact_mod_cast (by omega : 1<n))).le
  rw [stepsize_regret_identity hn hT]
  have hr := Task003Audit.BoundsArithmetic.smoothing_rate_term_from_iteration_budget
    (n : ℝ) (Real.log n) (iterations n α) α hnR.le hl hTR hα (iterations_budget n α)
  have hb := Task003Audit.BoundsArithmetic.smoothing_bias_exact (n : ℝ) α (radius n α) hnR rfl
  linarith

end Task003.UpperParameters


end
-- END UpperParameters.lean

-- BEGIN ActualUpperBudget.lean
section

/- Dependencies: PolicyStochasticBridge, PolicyGap, UpperParameters,
StochasticUpper and their analytic dependencies. The returned point of the
actual two-value policy is controlled, then real Markov gives the specified
per-fixed-objective probability with the seed law outside that quantifier. -/
namespace Task003.ActualUpperBudget
open MeasureTheory Task003.OracleModel Task003.PolicyStochasticBridge
open PaperProductVariance PaperStochasticEntropy

variable {n T : ℕ}

theorem raw_convex (F : Space n → ℝ) (hF : ConvexOn ℝ Set.univ F) :
    ConvexOn ℝ Set.univ (fun z : Fin n → ℝ => F (WithLp.toLp 1 z)) := by
  refine ⟨convex_univ,?_⟩
  intro x hx y hy a b ha hb hab
  change F (a • WithLp.toLp 1 x+b • WithLp.toLp 1 y) ≤ _
  exact hF.2 (Set.mem_univ _) (Set.mem_univ _) ha hb hab

theorem averagedState_jensen (hn : 0<n) (hT : 0<T) (F : Space n → ℝ)
    (hF : ConvexOn ℝ Set.univ F) (η h : ℝ) (seed : Seed n T) :
    F (WithLp.toLp 1 (averagedState F η h seed)) ≤
      (∑ t ∈ Finset.range T, F (WithLp.toLp 1 (actualState F η h seed t)))/(T : ℝ) := by
  have hj := Task003.TwoPointPolicy.rounds_jensen hn
    (fun z => F (WithLp.toLp 1 z)) (raw_convex F hF) η h (sampleNoise seed) T hT
  rw [rounds_average_state hn F η h seed hT] at hj
  simpa only [rounds_state,actualState] using hj

theorem averagedState_gap (hn : 0<n) (hT : 0<T) (F : Space n → ℝ)
    (hF : ConvexOn ℝ Set.univ F) (η h : ℝ) (seed : Seed n T) (x : Raw n) :
    F (WithLp.toLp 1 (averagedState F η h seed))-F (WithLp.toLp 1 x) ≤
      PaperStochasticUpper.averageValueGap F η h x seed := by
  have hj := averagedState_jensen hn hT F hF η h seed
  have hTR : (T : ℝ) ≠ 0 := by exact_mod_cast hT.ne'
  have hs : PaperStochasticUpper.averageValueGap F η h x seed =
      (∑ t ∈ Finset.range T, F (WithLp.toLp 1 (actualState F η h seed t)))/(T : ℝ)-
        F (WithLp.toLp 1 x) := by
    unfold PaperStochasticUpper.averageValueGap
    rw [Finset.sum_sub_distrib,Finset.sum_const,Finset.card_range,nsmul_eq_mul]
    field_simp
  rw [hs]
  linarith

theorem canonical_expected_gap (d : ℕ) (hd : 0<d) (η h : ℝ)
    (hη : 0<η) (hh : 0<h) (T : ℕ) (hT : 0<T) (f : Objective d 1) :
    (∫ seed : Seed (d+d) T,
      f (run (canonicalPolicy d hd η h T) f (2*T) seed)-optimum 1 f
      ∂seedLaw (d+d) T) ≤ Real.log (d+d)/(η*T)+2*η*(d+d)+2*h*(d+d) := by
  obtain ⟨x,hx,hval,hmin⟩ := optimum_attained f (by norm_num : (0:ℝ)≤1)
  obtain ⟨z,hz,hsz,hlift⟩ := Task003.SimplexLift.lift_simplex_surjective d hd x hx
  let F : Space (d+d) → ℝ := f ∘ Task003.SimplexLift.lift d
  have hFl : LipschitzWith 1 F := Task003.SimplexLift.lifted_objective_lipschitz d f
  have hFc : ConvexOn ℝ Set.univ F := Task003.SimplexLift.lifted_objective_convex d f
  have hv : F z=optimum 1 f := by change f (Task003.SimplexLift.lift d z)=_; rw [hlift,hval]
  have hj : ∀ seed : Seed (d+d) T,
      f (run (canonicalPolicy d hd η h T) f (2*T) seed)-optimum 1 f ≤
        PaperStochasticUpper.averageValueGap F η h (WithLp.ofLp z) seed := by
    intro seed
    rw [canonicalPolicy_output d hd η h T hT f seed,← hv]
    exact averagedState_gap (by omega) hT F hFc η h seed (WithLp.ofLp z)
  have hi := integral_mono
    (Task003.PolicyGap.policy_gap_integrable (seedLaw (d+d) T) (canonicalPolicy d hd η h T) f)
    (PaperStochasticUpper.averageValueGap_integrable (by omega) F hFl η h (WithLp.ofLp z)) hj
  exact hi.trans (by simpa only [Nat.cast_add] using
    (PaperStochasticUpper.expected_average_value_gap (by omega) hT
      F hFl hFc η h hη hh (WithLp.ofLp z) hz hsz))

theorem canonical_solves (d : ℕ) (hd : 0<d) (α : ℝ) (hα : 0<α) :
    SolvesOn (seedLaw (d+d) (Task003.UpperParameters.iterations (d+d) α))
      (canonicalPolicy d hd
        (Task003.UpperParameters.stepsize (d+d) (Task003.UpperParameters.iterations (d+d) α))
        (Task003.UpperParameters.radius (d+d) α)
        (Task003.UpperParameters.iterations (d+d) α))
      (2*Task003.UpperParameters.iterations (d+d) α) 1 α := by
  have hn : 2≤d+d := by omega
  have hT := Task003.UpperParameters.iterations_pos hn hα
  apply Task003.PolicyGap.solvesOn_of_expected_gap _ _ α hα
  intro f
  exact (canonical_expected_gap d hd _ _
    (Task003.UpperParameters.stepsize_pos hn hT)
    (by unfold Task003.UpperParameters.radius; positivity) _ hT f).trans
      (by simpa only [Nat.cast_add] using (Task003.UpperParameters.parameters_error_bound hn hα))

theorem actual_entropy_upper {d : ℕ} (hd : 0<d) {α : ℝ} (hα : 0<α) :
    AdmissibleBudget d (2*⌈576*(d : ℝ)*Real.log (2*d)/α^2⌉₊) 1 1 α := by
  have hn : (d+d : ℝ)=2*d := by ring
  have hdim : ((d+d : ℕ) : ℝ)=2*d := by push_cast; ring
  have hcount : 2*Task003.UpperParameters.iterations (d+d) α =
      2*⌈576*(d : ℝ)*Real.log (2*d)/α^2⌉₊ := by
    unfold Task003.UpperParameters.iterations
    rw [hdim]
    congr 2
    ring
  rw [← hcount]
  exact ⟨Seed (d+d) (Task003.UpperParameters.iterations (d+d) α),inferInstance,
    seedLaw (d+d) (Task003.UpperParameters.iterations (d+d) α),inferInstance,
    canonicalPolicy d hd _ _ _,canonical_solves d hd α hα⟩

end Task003.ActualUpperBudget


end
-- END ActualUpperBudget.lean

-- BEGIN ProtasovInterface.lean
section

/- Dependencies: OracleModel. This file states the manuscript's named external
relative-range algorithmic input as a hypothesis, not an axiom, and proves its
normalised absolute-accuracy consequence. It does not purport to formalise the
1996 paper's proof of that input. -/
namespace Task003.ProtasovInterface
open MeasureTheory Set Task003.OracleModel

noncomputable def oscillation {d : ℕ} (f : Objective d 1) : ℝ :=
  sSup (f '' {x : Point d | Feasible 1 x}) - optimum 1 f

theorem oscillation_le_two {d : ℕ} (f : Objective d 1) : oscillation f ≤ 2 := by
  obtain ⟨x,hx,hval,hmin⟩ := optimum_attained f (by norm_num : (0:ℝ)≤1)
  have hi : (f '' {x : Point d | Feasible 1 x}).Nonempty := ⟨f x,x,hx,rfl⟩
  have hb : ∀ z ∈ (f '' {x : Point d | Feasible 1 x}), z ≤ optimum 1 f+2 := by
    rintro z ⟨y,hy,rfl⟩
    have hfd := f.lip.dist_le_mul y x
    rw [Real.toNNReal_one,NNReal.coe_one,one_mul,Real.dist_eq,dist_eq_norm] at hfd
    have hxy := norm_sub_le y x
    change ‖x‖≤1 at hx
    change ‖y‖≤1 at hy
    rw [hval]
    linarith [le_abs_self (f y-f x)]
  have hs := csSup_le hi hb
  unfold oscillation
  linarith

/-- Specialisation of the external deterministic relative-range oracle theorem
to B1. The same policy works for every objective. Its proof is an explicit
literature input, not a proved declaration of this audit. -/
def ProtasovPrinciple (C : ℝ) : Prop :=
  ∀ d : ℕ, 2≤d → ∀ δ : ℝ, 0<δ → δ≤1/2 →
    ∃ m : ℕ, ∃ a : Policy d 1 Unit,
      (m : ℝ) ≤ C*(d : ℝ)^2*Real.log (d+1)*Real.log (1/δ) ∧
      ∀ f : Objective d 1, ∀ ω : Unit,
        f (run a f m ω)-optimum 1 f ≤ δ*oscillation f

theorem protasov_absolute_upper (C : ℝ) (hC : 0≤C) (hP : ProtasovPrinciple C)
    {d : ℕ} (hd : 2≤d) {α : ℝ} (hα : 0<α) (hα1 : α≤1) :
    ∃ m : ℕ, AdmissibleBudget d m 1 1 α ∧
      (m : ℝ) ≤ C*(d : ℝ)^2*Real.log (d+1)*Real.log (4/α) := by
  obtain ⟨m,a,hm,ha⟩ := hP d hd (α/2) (by positivity) (by linarith)
  refine ⟨m,?_,?_⟩
  · refine ⟨Unit,inferInstance,Measure.dirac (),inferInstance,a,?_⟩
    intro f
    have he : successEvent a f m α=univ := by
      apply eq_univ_of_forall
      intro ω
      have hf := ha f ω
      have ho := mul_le_mul_of_nonneg_left (oscillation_le_two f) (show 0≤α/2 by positivity)
      change f (run a f m ω)-optimum 1 f≤α
      linarith
    rw [he,measure_univ]
    exact ENNReal.div_le_of_le_mul (by norm_num)
  · have hlog : Real.log (1/(α/2))≤Real.log (4/α) := by
      apply Real.log_le_log (by positivity)
      apply (div_le_div_iff₀ (by positivity : 0<α/2) hα).mpr
      linarith
    have hc : 0≤C*(d : ℝ)^2*Real.log (d+1) := by
      have hdR : (0:ℝ)≤d := by positivity
      have hl : 0≤Real.log (d+1) := Real.log_nonneg (by linarith)
      positivity
    exact hm.trans (mul_le_mul_of_nonneg_left hlog hc)

end Task003.ProtasovInterface


end
-- END ProtasovInterface.lean

-- BEGIN UpperEnvelopeThreshold.lean
section

/- Dependencies: UpperEnvelope. The same proved envelope starting at d>=2,
matching the stated external range-reduction interface. -/
namespace Task003.UpperEnvelopeThreshold
open Task003.OracleModel CompositionAudit Task003.UpperEnvelope

theorem admissible_upper_envelope_from_two (C2 : ℝ) (hC2 : 0 ≤ C2)
    (hU1 : ∀ (d : ℕ) (α : ℝ), 2 ≤ d → 0 < α → α ≤ 1 →
      AdmissibleBudget d (2 * ⌈576*(d:ℝ)*(A α)^2*Real.log (2*(d:ℝ))⌉₊) 1 1 α)
    (hU2 : ∀ (d : ℕ) (α : ℝ), 2 ≤ d → 0 < α → α ≤ 1 →
      ∃ m : ℕ, AdmissibleBudget d m 1 1 α ∧
        (m:ℝ) ≤ C2*(d:ℝ)^2*Real.log ((d:ℝ)+1)*Real.log (4/α)) :
    ∃ b : ℝ, 0 < b ∧ ∀ (d : ℕ) (α : ℝ), 2 ≤ d → 0 < α → α ≤ 1 →
      ∃ m : ℕ, AdmissibleBudget d m 1 1 α ∧
        (m:ℝ) ≤ b*profileQ d α*(profileLambda d α)^2 := by
  refine ⟨1154+2*C2, by linarith, ?_⟩
  intro d α hd ha ha1
  have hdR : (1:ℝ) ≤ d := by exact_mod_cast (by omega : 1≤d)
  have hdpos : (0:ℝ) < d := by linarith
  have hmQ : profileQ d α = q d α := rfl
  have hmL : profileLambda d α = Lambda d α := rfl
  rw [hmQ,hmL]
  obtain ⟨hl1,hlog2,hlogd,hlogA⟩ := upper_log_bounds hdR ha ha1
  have hqnonneg := q_nonneg (α:=α) (show (0:ℝ)≤d by positivity)
  by_cases hc : (A α)^2 ≤ (d:ℝ)
  · refine ⟨2 * ⌈576*(d:ℝ)*(A α)^2*Real.log (2*(d:ℝ))⌉₊,hU1 d α hd ha ha1,?_⟩
    have hb := coarse_ceiling_bound hdR ha ha1 hc
    have hmul := mul_nonneg hC2 (mul_nonneg hqnonneg (sq_nonneg (Lambda d α)))
    nlinarith
  · obtain ⟨m,hm,hbound⟩ := hU2 d α hd ha ha1
    refine ⟨m,hm,?_⟩
    have hq : q d α = (d:ℝ)^2 := by
      unfold q M
      rw [min_eq_left (le_of_lt (lt_of_not_ge hc))]
      ring
    have hln : 0 ≤ Real.log ((d:ℝ)+1) := Real.log_nonneg (by linarith)
    have hlnA : 0 ≤ Real.log (4/α) := by
      apply Real.log_nonneg
      exact (le_div_iff₀ ha).mpr (by linarith)
    have hprod : Real.log ((d:ℝ)+1)*Real.log (4/α) ≤ 2*(Lambda d α)^2 := by
      have hh := mul_le_mul hlogd hlogA hlnA (show 0≤Lambda d α by linarith)
      nlinarith
    have hmul := mul_le_mul_of_nonneg_left hprod (mul_nonneg hC2 (sq_nonneg (d:ℝ)))
    rw [hq]
    nlinarith [sq_nonneg (d:ℝ),sq_nonneg (Lambda d α)]


end Task003.UpperEnvelopeThreshold


end
-- END UpperEnvelopeThreshold.lean

-- BEGIN GlobalUpper.lean
section

/- Dependencies: ActualUpperBudget, ProtasovInterface, UpperEnvelopeThreshold.
The only mathematical input in this upper bound is the manuscript's explicitly
named external deterministic Protasov relative-range theorem. -/
namespace Task003.GlobalUpper
open CompositionAudit Task003.OracleModel Task003.ProtasovInterface

theorem global_upper_of_protasov (C : ℝ) (hC : 0<C) (hP : ProtasovPrinciple C) :
    ∃ b : ℝ, 0<b ∧ ∀ (d : ℕ) (α : ℝ), 2≤d → 0<α → α≤1 →
      ∃ m : ℕ, AdmissibleBudget d m 1 1 α ∧
        (m : ℝ) ≤ b*profileQ d α*(profileLambda d α)^2 := by
  apply Task003.UpperEnvelopeThreshold.admissible_upper_envelope_from_two C hC.le
  · intro d α hd hα hα1
    have he : 576*(d : ℝ)*(A α)^2*Real.log (2*(d : ℝ)) =
        576*(d : ℝ)*Real.log (2*(d : ℝ))/α^2 := by
      unfold A
      field_simp
      <;> ring
    rw [he]
    exact Task003.ActualUpperBudget.actual_entropy_upper (by omega) hα
  · intro d α hd hα hα1
    exact protasov_absolute_upper C hC.le hP hd hα hα1

end Task003.GlobalUpper


end
-- END GlobalUpper.lean

-- BEGIN RawPolicyDecoder.lean
section
/- Dependencies: GaussianChannelKL, ProjectorInnovations,
AdaptiveGaussianOracleBridgeClean. This file contains only public strategy
state; the hidden Gaussian vector and hidden index are not parameters to it. -/
namespace PaperRawPolicyDecoder

open MeasureTheory ProbabilityTheory PaperGaussianKL PaperProjectorInnovations
  PaperAdaptiveGaussianOracleBridge PaperEnrichedGaussianOracleBridge
open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

instance historyMeasurableEq (t : ℕ) : MeasurableEq (History t) := by
  induction t with
  | zero => exact inferInstanceAs (MeasurableEq Unit)
  | succ t ih =>
    letI : MeasurableEq (History t) := ih
    change MeasurableEq (History t × ℝ)
    constructor
    have hf : MeasurableSet {p : (History t × ℝ) × (History t × ℝ) | p.1.1 = p.2.1} :=
      measurableSet_eq_fun measurable_fst.fst measurable_snd.fst
    have hs : MeasurableSet {p : (History t × ℝ) × (History t × ℝ) | p.1.2 = p.2.2} :=
      measurableSet_eq_fun measurable_fst.snd measurable_snd.snd
    have heq : Set.diagonal (History t × ℝ) =
        {p : (History t × ℝ) × (History t × ℝ) | p.1.1 = p.2.1} ∩
        {p : (History t × ℝ) × (History t × ℝ) | p.1.2 = p.2.2} := by
      ext p
      change (p.1 = p.2) ↔ (p.1.1 = p.2.1 ∧ p.1.2 = p.2.2)
      exact Prod.ext_iff
    rw [heq]
    exact hf.inter hs

abbrev State (t : ℕ) := (E →L[ℝ] E) × E × History t

noncomputable def state (query : (t : ℕ) → History t → E) (σ : ℝ) :
    (t : ℕ) → History t → State (E := E) t
  | 0 => fun _ => (ContinuousLinearMap.id ℝ E,0,())
  | t+1 => fun h =>
    let s := state query σ t h.1
    let v := query t s.2.2
    let w := normalizedResidual s.1 v
    let y := ⟪v,s.2.1⟫_ℝ + σ * ‖s.1 v‖ * h.2
    (projectorUpdate s.1 w, s.2.1 + (σ*h.2) • w, (s.2.2,y))

noncomputable def rows (query : (t : ℕ) → History t → E) (σ : ℝ)
    (t : ℕ) (h : History t) : E :=
  normalizedResidual (state query σ t h).1 (query t (state query σ t h).2.2)

noncomputable def decoded (query : (t : ℕ) → History t → E) (σ : ℝ)
    (t : ℕ) (h : History t) : History t := (state query σ t h).2.2

noncomputable def center (query : (t : ℕ) → History t → E) (σ : ℝ)
    (t : ℕ) (h : History t) : E := (state query σ t h).2.1

noncomputable def projection (query : (t : ℕ) → History t → E) (σ : ℝ)
    (t : ℕ) (h : History t) : E →L[ℝ] E := (state query σ t h).1

theorem projection_invariant (query : (t : ℕ) → History t → E) (σ : ℝ)
    (t : ℕ) (h : History t) :
    IsSelfAdjoint (projection query σ t h) ∧
      projection query σ t h * projection query σ t h = projection query σ t h := by
  induction t with
  | zero =>
    change IsSelfAdjoint (1 : E →L[ℝ] E) ∧ (1 : E →L[ℝ] E) * 1 = 1
    exact ⟨IsSelfAdjoint.one (E →L[ℝ] E),one_mul _⟩
  | succ t ih =>
    obtain ⟨hQ,hQQ⟩ := ih h.1
    let Q := projection query σ t h.1
    let v := query t (decoded query σ t h.1)
    by_cases hr : Q v = 0
    · change IsSelfAdjoint (projectorUpdate Q (normalizedResidual Q v)) ∧
        projectorUpdate Q (normalizedResidual Q v) * projectorUpdate Q (normalizedResidual Q v) =
          projectorUpdate Q (normalizedResidual Q v)
      rw [normalizedResidual_zero hr,projectorUpdate_zero]
      exact ⟨hQ,hQQ⟩
    · have hh := projectorUpdate_selfAdjoint_idempotent hQ hQQ
        (normalizedResidual_norm hr) (normalizedResidual_fixed hQQ v)
      simpa only [projection,state,decoded,Q,v] using hh

theorem row_norm_zero_or_one (query : (t : ℕ) → History t → E) (σ : ℝ)
    (t : ℕ) (h : History t) :
    ‖rows query σ t h‖ = 0 ∨ ‖rows query σ t h‖ = 1 := by
  by_cases hr : projection query σ t h (query t (decoded query σ t h)) = 0
  · left
    change (state query σ t h).1 (query t (state query σ t h).2.2) = 0 at hr
    simp only [rows,normalizedResidual,hr,norm_zero,inv_zero,zero_smul]
  · right
    exact normalizedResidual_norm hr

theorem row_fixed (query : (t : ℕ) → History t → E) (σ : ℝ)
    (t : ℕ) (h : History t) :
    projection query σ t h (rows query σ t h) = rows query σ t h :=
  normalizedResidual_fixed (projection_invariant query σ t h).2 _

theorem row_inner_projection (query : (t : ℕ) → History t → E) (σ : ℝ)
    (t : ℕ) (h : History t) (b : E) :
    ⟪rows query σ t h, projection query σ t h b⟫_ℝ = ⟪rows query σ t h,b⟫_ℝ :=
  inner_projector_fixed
    (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp (projection_invariant query σ t h).1)
    (row_fixed query σ t h) b

theorem state_zero_residual_ignores_noise
    (query : (t : ℕ) → History t → E) (σ : ℝ) (t : ℕ) (h : History t)
    (hr : projection query σ t h (query t (decoded query σ t h)) = 0)
    (z₁ z₂ : ℝ) : state query σ (t+1) (h,z₁) = state query σ (t+1) (h,z₂) := by
  change (state query σ t h).1 (query t (state query σ t h).2.2) = 0 at hr
  simp [state,normalizedResidual,hr]

theorem state_measurable (query : (t : ℕ) → History t → E)
    (hq : ∀ t, Measurable (query t)) (σ : ℝ) (t : ℕ) :
    Measurable (state query σ t) := by
  induction t with
  | zero => exact measurable_const
  | succ t ih =>
    have hs : Measurable (fun h : History (t+1) => state query σ t h.1) := ih.comp measurable_fst
    have hQ := hs.fst
    have hm := hs.snd.fst
    have hD := hs.snd.snd
    have hv := (hq t).comp hD
    have hw : Measurable (fun h : History (t+1) =>
        normalizedResidual (state query σ t h.1).1 (query t (state query σ t h.1).2.2)) :=
      normalizedResidual_measurable.comp (hQ.prodMk hv)
    have hnewQ := projectorUpdate_measurable.comp (hQ.prodMk hw)
    have hcoef : Measurable (fun h : History (t+1) => σ*h.2) := measurable_const.mul measurable_snd
    have hnewM := hm.add (hcoef.smul hw)
    have heval : Measurable (fun h : History (t+1) =>
        (state query σ t h.1).1 (query t (state query σ t h.1).2.2)) :=
      (continuous_fst.clm_apply continuous_snd).measurable.comp (hQ.prodMk hv)
    have hc : Measurable (fun h : History (t+1) => σ *
        ‖(state query σ t h.1).1 (query t (state query σ t h.1).2.2)‖) := measurable_const.mul heval.norm
    have hy := (hv.inner hm).add (hc.mul measurable_snd)
    exact hnewQ.prodMk (hnewM.prodMk (hD.prodMk hy))

theorem rows_measurable (query : (t : ℕ) → History t → E)
    (hq : ∀ t, Measurable (query t)) (σ : ℝ) (t : ℕ) :
    Measurable (rows query σ t) := by
  have hs := state_measurable query hq σ t
  exact normalizedResidual_measurable.comp (hs.fst.prodMk ((hq t).comp hs.snd.snd))

theorem decoded_measurable (query : (t : ℕ) → History t → E)
    (hq : ∀ t, Measurable (query t)) (σ : ℝ) (t : ℕ) :
    Measurable (decoded query σ t) := (state_measurable query hq σ t).snd.snd

theorem projection_eq_innovation (query : (t : ℕ) → History t → E) (σ : ℝ) (t : ℕ) :
    projection query σ t = innovationProjection (rows query σ) t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    funext h
    change PaperProjectorInnovations.projectorUpdate (projection query σ t h.1)
      (rows query σ t h.1) = PaperGaussianOracleBridge.projectorUpdate
        (innovationProjection (rows query σ) t h.1) (rows query σ t h.1)
    rw [ih]
    rfl

theorem center_eq_innovation (query : (t : ℕ) → History t → E) (σ : ℝ) (t : ℕ) :
    center query σ t = innovationCenter (rows query σ) σ t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    funext h
    change center query σ t h.1 + (σ * h.2) • rows query σ t h.1 =
      innovationCenter (rows query σ) σ t h.1 + (σ * h.2) • rows query σ t h.1
    rw [ih]

/-- The actual raw oracle history, using the same g at every query. -/
noncomputable def rawHistory (query : (t : ℕ) → History t → E) : (t : ℕ) → E → History t
  | 0 => fun _ => ()
  | t + 1 => fun g =>
      let h := rawHistory query t g
      (h, ⟪query t h, g⟫_ℝ)

theorem rawHistory_measurable (query : (t : ℕ) → History t → E)
    (hq : ∀ t, Measurable (query t)) (t : ℕ) : Measurable (rawHistory query t) := by
  induction t with
  | zero => exact measurable_const
  | succ t ih => exact ih.prodMk (((hq t).comp ih).inner measurable_id)

/-- Pathwise raw-answer reconstruction, including the zero-residual case.
The scalar z may be arbitrary when the residual row vanishes. -/
theorem raw_answer_reconstruction
    (Q : E →L[ℝ] E) (hsym : Q.IsSymmetric) (g m v : E) (σ z : ℝ)
    (hu : Q (g - m) = g - m)
    (hz : normalizedResidual Q v = 0 ∨ σ * z = ⟪normalizedResidual Q v, g - m⟫_ℝ) :
    ⟪v, g⟫_ℝ = ⟪v, m⟫_ℝ + σ * ‖Q v‖ * z := by
  have hi : ⟪v, g - m⟫_ℝ = ⟪Q v, g - m⟫_ℝ := by
    have hh : ⟪Q v, g - m⟫_ℝ = ⟪v, Q (g - m)⟫_ℝ := by
      convert! hsym v (g - m) using 1
    exact (congrArg (fun x : E => ⟪v, x⟫_ℝ) hu).symm.trans hh.symm
  by_cases hr : Q v = 0
  · rw [hr, inner_zero_left] at hi
    simp only [hr, norm_zero, mul_zero, zero_mul, add_zero]
    rw [inner_sub_right] at hi
    linarith
  · have hw : ‖normalizedResidual Q v‖ = 1 := normalizedResidual_norm hr
    have hc : σ * z = ⟪normalizedResidual Q v, g - m⟫_ℝ := by
      rcases hz with hzero | hc
      · rw [hzero, norm_zero] at hw
        norm_num at hw
      · exact hc
    have hrw : ‖Q v‖ • normalizedResidual Q v = Q v := by
      rw [normalizedResidual, smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hr), one_smul]
    have hin : ⟪Q v, g - m⟫_ℝ = ‖Q v‖ * (σ * z) := by
      calc
        _ = ⟪‖Q v‖ • normalizedResidual Q v, g - m⟫_ℝ :=
          congrArg (fun r : E => ⟪r, g - m⟫_ℝ) hrw.symm
        _ = _ := by rw [real_inner_smul_left, ← hc]
    calc
      ⟪v, g⟫_ℝ = ⟪v, m⟫_ℝ + ⟪v, g - m⟫_ℝ := by rw [inner_sub_right]; ring
      _ = ⟪v, m⟫_ℝ + ⟪Q v, g - m⟫_ℝ := by rw [hi]
      _ = ⟪v, m⟫_ℝ + σ * ‖Q v‖ * z := by
        rw [hin]
        ring

/-- The residual fixed-point identity is preserved pathwise by either an
active true innovation or a zero row with arbitrary private noise. -/
theorem residual_fixed_after_innovation
    (Q : E →L[ℝ] E) (hQQ : Q * Q = Q) (g m v : E) (σ z : ℝ)
    (hu : Q (g - m) = g - m)
    (hz : normalizedResidual Q v = 0 ∨ σ * z = ⟪normalizedResidual Q v, g - m⟫_ℝ) :
    projectorUpdate Q (normalizedResidual Q v)
      (g - (m + (σ * z) • normalizedResidual Q v)) =
        g - (m + (σ * z) • normalizedResidual Q v) := by
  by_cases hwzero : normalizedResidual Q v = 0
  · rw [hwzero, projectorUpdate_zero]
    simpa using hu
  · have hr : Q v ≠ 0 := by
      intro hr
      exact hwzero (normalizedResidual_zero hr)
    have hw : ‖normalizedResidual Q v‖ = 1 := normalizedResidual_norm hr
    have hfix := normalizedResidual_fixed hQQ v
    have hc : σ * z = ⟪normalizedResidual Q v, g - m⟫_ℝ := hz.resolve_left hwzero
    have hww : ⟪normalizedResidual Q v, normalizedResidual Q v⟫_ℝ = 1 := by
      rw [real_inner_self_eq_norm_sq, hw]
      norm_num
    have hv : g - (m + (σ * z) • normalizedResidual Q v) =
        (g - m) - (σ * z) • normalizedResidual Q v := by abel
    rw [hv]
    change Q ((g - m) - (σ * z) • normalizedResidual Q v) -
      ⟪normalizedResidual Q v, (g - m) - (σ * z) • normalizedResidual Q v⟫_ℝ •
        normalizedResidual Q v = _
    rw [map_sub, map_smul, hu, hfix, inner_sub_right, inner_smul_right, hww, ← hc]
    simp

/-- A public transcript agrees with the true raw history and leaves the
unobserved source residual in the current projector's range. -/
def Coherent (query : (t : ℕ) → History t → E) (σ : ℝ)
    (t : ℕ) (p : History t × E) : Prop :=
  projection query σ t p.1 (p.2 - center query σ t p.1) = p.2 - center query σ t p.1 ∧
    decoded query σ t p.1 = rawHistory query t p.2

theorem coherent_measurable (query : (t : ℕ) → History t → E)
    (hq : ∀ t, Measurable (query t)) (σ : ℝ) (t : ℕ) :
    MeasurableSet {p | Coherent query σ t p} := by
  have hs : Measurable (fun p : History t × E => state query σ t p.1) :=
    (state_measurable query hq σ t).comp measurable_fst
  have hu := measurable_snd.sub hs.snd.fst
  have heval : Measurable (fun p : (E →L[ℝ] E) × E => p.1 p.2) :=
    (continuous_fst.clm_apply continuous_snd).measurable
  exact (measurableSet_eq_fun (heval.comp (hs.fst.prodMk hu)) hu).inter
    (measurableSet_eq_fun hs.snd.snd ((rawHistory_measurable query hq t).comp measurable_snd))

theorem coherent_step
    (query : (t : ℕ) → History t → E) (σ : ℝ) (hσ : σ ≠ 0)
    (t : ℕ) (h : History t) (g : E) (z : ℝ)
    (hc : Coherent query σ t (h, g))
    (hz : rows query σ t h = 0 ∨
      z = innovationObservation (rows query σ) σ t (h, g)) :
    Coherent query σ (t + 1) ((h, z), g) := by
  have ha : rows query σ t h = 0 ∨
      σ * z = ⟪rows query σ t h, g - center query σ t h⟫_ℝ := by
    rcases hz with hz | hz
    · exact Or.inl hz
    · right
      rw [hz, innovationObservation, ← center_eq_innovation query σ t]
      field_simp [hσ]
  have hp := projection_invariant query σ t h
  have hres := residual_fixed_after_innovation (projection query σ t h) hp.2
    g (center query σ t h) (query t (decoded query σ t h)) σ z hc.1 ha
  have hans := raw_answer_reconstruction (projection query σ t h)
    (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hp.1)
    g (center query σ t h) (query t (decoded query σ t h)) σ z hc.1 ha
  constructor
  · exact hres
  · change (decoded query σ t h,
      ⟪query t (decoded query σ t h), center query σ t h⟫_ℝ +
        σ * ‖projection query σ t h (query t (decoded query σ t h))‖ * z) =
      (rawHistory query t g, ⟪query t (rawHistory query t g), g⟫_ℝ)
    apply Prod.ext hc.2
    rw [← hc.2]
    exact hans.symm

/-- Decoder correctness for the actual enriched source process, including
private Gaussian padding at every zero/dependent/unused query. -/
theorem enrichedSourceJoint_coherent
    (query : (t : ℕ) → History t → E) (hq : ∀ t, Measurable (query t))
    (σ δ : ℝ) (hσ : σ ≠ 0) (θ : E) (t : ℕ) :
    ∀ᵐ p ∂enrichedSourceJoint (rows query σ) (rows_measurable query hq σ) σ δ θ t,
      Coherent query σ t p := by
  apply enrichedSourceJoint_ae_invariant (rows query σ) (rows_measurable query hq σ) σ δ θ
    (Coherent query σ) (coherent_measurable query hq σ)
  · exact ae_of_all _ (fun _ => ⟨rfl, rfl⟩)
  · intro s h g hc
    exact (sourceObservationKernel_support (rows query σ) (rows_measurable query hq σ) σ s h g).mono
      (fun z hz => coherent_step query σ hσ s h g z hc hz)

/-- Joint decoded transcript/source law equals the original deterministic
raw-oracle execution on the source vector sampled once. -/
theorem decoded_source_joint_law
    (query : (t : ℕ) → History t → E) (hq : ∀ t, Measurable (query t))
    (σ δ : ℝ) (hσ : σ ≠ 0) (θ : E) (t : ℕ) :
    (enrichedSourceJoint (rows query σ) (rows_measurable query hq σ) σ δ θ t).map
      (fun p => (decoded query σ t p.1, p.2)) =
        (PaperGaussianOracleBridge.sourcePrior σ (δ • θ)).map
          (fun g => (rawHistory query t g, g)) := by
  let μ := enrichedSourceJoint (rows query σ) (rows_measurable query hq σ) σ δ θ t
  have hc := enrichedSourceJoint_coherent query hq σ δ hσ θ t
  calc
    μ.map (fun p => (decoded query σ t p.1, p.2)) =
        μ.map (fun p => (rawHistory query t p.2, p.2)) := by
      apply Measure.map_congr
      exact hc.mono (fun p hp => congrArg (fun a : History t => (a, p.2)) hp.2)
    _ = μ.snd.map (fun g => (rawHistory query t g, g)) := by
      exact (Measure.map_map (μ := μ)
        ((rawHistory_measurable query hq t).prodMk measurable_id) measurable_snd).symm
    _ = _ := by rw [enrichedSourceJoint_source_marginal]

/-- The actual Gaussian channel, decoded without reading zero-row noise,
has exactly the original raw-policy transcript distribution. -/
theorem raw_policy_channel_law
    (query : (t : ℕ) → History t → E) (hq : ∀ t, Measurable (query t))
    (σ δ : ℝ) (hσ : σ ≠ 0) (θ : E) (t : ℕ) :
    (signalLaw (signalMeans (rows query σ) (rows_measurable query hq σ) σ δ θ) t).map
      (decoded query σ t) =
        (PaperGaussianOracleBridge.sourcePrior σ (δ • θ)).map (rawHistory query t) := by
  let μ := enrichedSourceJoint (rows query σ) (rows_measurable query hq σ) σ δ θ t
  have hm : μ.fst = signalLaw
      (signalMeans (rows query σ) (rows_measurable query hq σ) σ δ θ) t := by
    apply finite_enriched_source_history_law _ (rows_measurable query hq σ) σ δ hσ θ t
    · intro s hs h
      rcases row_norm_zero_or_one query σ s h with hz | hone
      · exact Or.inl (norm_eq_zero.mp hz)
      · exact Or.inr hone
    · intro s hs h
      rw [← projection_eq_innovation]
      exact row_fixed query σ s h
    · intro s hs h b
      rw [← projection_eq_innovation]
      exact row_inner_projection query σ s h b
  have hc := enrichedSourceJoint_coherent query hq σ δ hσ θ t
  calc
    (signalLaw (signalMeans (rows query σ) (rows_measurable query hq σ) σ δ θ) t).map
        (decoded query σ t) = μ.fst.map (decoded query σ t) := by rw [hm]
    _ = μ.map (decoded query σ t ∘ Prod.fst) :=
      Measure.map_map (decoded_measurable query hq σ t) measurable_fst
    _ = μ.map (rawHistory query t ∘ Prod.snd) :=
      Measure.map_congr (hc.mono fun p hp => hp.2)
    _ = μ.snd.map (rawHistory query t) :=
      (Measure.map_map (rawHistory_measurable query hq t) measurable_snd).symm
    _ = _ := by rw [enrichedSourceJoint_source_marginal]

/-- Every measurable raw-history estimator has the same output law after
channel decoding as on the original source Gaussian oracle. -/
theorem raw_policy_output_law
    {Output : Type*} [MeasurableSpace Output]
    (query : (t : ℕ) → History t → E) (hq : ∀ t, Measurable (query t))
    (σ δ : ℝ) (hσ : σ ≠ 0) (θ : E) (t : ℕ)
    (estimate : History t → Output) (he : Measurable estimate) :
    (signalLaw (signalMeans (rows query σ) (rows_measurable query hq σ) σ δ θ) t).map
      (fun h => estimate (decoded query σ t h)) =
        (PaperGaussianOracleBridge.sourcePrior σ (δ • θ)).map
          (fun g => estimate (rawHistory query t g)) := by
  rw [show (fun h => estimate (decoded query σ t h)) = estimate ∘ decoded query σ t from rfl,
    ← Measure.map_map he (decoded_measurable query hq σ t), raw_policy_channel_law query hq σ δ hσ θ t,
    Measure.map_map he (rawHistory_measurable query hq t)]
  rfl

/-- Exact event-probability transfer for a measurable raw estimator.
This derives the Gaussian-channel success event from the original oracle. -/
theorem raw_policy_event_probability
    {Output : Type*} [MeasurableSpace Output]
    (query : (t : ℕ) → History t → E) (hq : ∀ t, Measurable (query t))
    (σ δ : ℝ) (hσ : σ ≠ 0) (θ : E) (t : ℕ)
    (estimate : History t → Output) (he : Measurable estimate)
    (B : Set Output) (hB : MeasurableSet B) :
    (signalLaw (signalMeans (rows query σ) (rows_measurable query hq σ) σ δ θ) t)
      {h | estimate (decoded query σ t h) ∈ B} =
        (PaperGaussianOracleBridge.sourcePrior σ (δ • θ))
          {g | estimate (rawHistory query t g) ∈ B} := by
  have h := congrArg (fun μ : Measure Output => μ B)
    (raw_policy_output_law query hq σ δ hσ θ t estimate he)
  have hd : Measurable (fun h => estimate (decoded query σ t h)) :=
    he.comp (decoded_measurable query hq σ t)
  have hg : Measurable (fun g => estimate (rawHistory query t g)) :=
    he.comp (rawHistory_measurable query hq t)
  rw [Measure.map_apply hd hB, Measure.map_apply hg hB] at h
  exact h

end PaperRawPolicyDecoder


end
-- END RawPolicyDecoder.lean

-- BEGIN PolicyGaussianBridge.lean
section
namespace PaperPolicyGaussianBridge

open MeasureTheory ProbabilityTheory PaperGaussianKL PaperRawPolicyDecoder
open Task003.OracleModel
open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

noncomputable def historyVector : (t : ℕ) → History t → Fin t → ℝ
  | 0 => fun _ => Fin.elim0
  | t + 1 => fun h => Fin.snoc (historyVector t h.1) h.2

theorem historyVector_measurable (t : ℕ) : Measurable (historyVector t) := by
  induction t with
  | zero => exact measurable_pi_lambda _ (fun i => Fin.elim0 i)
  | succ t ih =>
    apply measurable_pi_lambda
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · convert! (measurable_snd : Measurable (fun h : History t × ℝ => h.2)) using 1
      all_goals (try simp only [historyVector, Fin.snoc_last])
      all_goals rfl
    · convert! ((measurable_pi_apply j).comp (ih.comp measurable_fst)) using 1
      all_goals (try simp only [historyVector, Fin.snoc_castSucc, Function.comp_def])
      all_goals rfl

/-- The first early-stop output is frozen. No hidden source or index is
available to this public replay state. -/
noncomputable def frozen {d R Ω} [MeasurableSpace Ω]
    (a : Policy d R Ω) (ω : Ω) : (t : ℕ) → History t → Bool × Point d
  | 0 => fun _ => (false, 0)
  | t + 1 => fun h =>
      let s := frozen a ω t h.1
      if s.1 then s else if a.stop t (ω, historyVector t h.1)
        then (true, a.output t (ω, historyVector t h.1)) else (false, 0)

noncomputable def paddedQuery {d R Ω} [MeasurableSpace Ω]
    (a : Policy d R Ω) (ω : Ω) (T : Point d → E) (t : ℕ) (h : History t) : E :=
  if (frozen a ω t h).1 then 0 else
    if a.stop t (ω, historyVector t h) then 0 else T (a.query t (ω, historyVector t h))

noncomputable def paddedOutput {d R Ω} [MeasurableSpace Ω]
    (a : Policy d R Ω) (ω : Ω) (t : ℕ) (h : History t) : Point d :=
  if (frozen a ω t h).1 then (frozen a ω t h).2 else a.output t (ω, historyVector t h)

theorem frozen_measurable {d R Ω} [MeasurableSpace Ω]
    (a : Policy d R Ω) (ω : Ω) (t : ℕ) : Measurable (frozen a ω t) := by
  induction t with
  | zero => exact measurable_const
  | succ t ih =>
    have hs : Measurable (fun h : History (t + 1) => frozen a ω t h.1) := ih.comp measurable_fst
    have hp : Measurable (fun h : History (t + 1) => (ω, historyVector t h.1)) :=
      measurable_const.prodMk ((historyVector_measurable t).comp measurable_fst)
    exact Measurable.ite (measurableSet_eq_fun hs.fst measurable_const) hs
      (Measurable.ite (measurableSet_eq_fun ((a.stop_measurable t).comp hp) measurable_const)
        (measurable_const.prodMk ((a.output_measurable t).comp hp)) measurable_const)

theorem paddedQuery_measurable {d R Ω} [MeasurableSpace Ω]
    (a : Policy d R Ω) (ω : Ω) (T : Point d → E) (hT : Measurable T) (t : ℕ) :
    Measurable (paddedQuery a ω T t) := by
  have hp : Measurable (fun h : History t => (ω, historyVector t h)) :=
    measurable_const.prodMk (historyVector_measurable t)
  exact Measurable.ite
    (measurableSet_eq_fun (frozen_measurable a ω t).fst measurable_const) measurable_const
    (Measurable.ite (measurableSet_eq_fun ((a.stop_measurable t).comp hp) measurable_const)
      measurable_const (hT.comp ((a.query_measurable t).comp hp)))

theorem paddedOutput_measurable {d R Ω} [MeasurableSpace Ω]
    (a : Policy d R Ω) (ω : Ω) (t : ℕ) : Measurable (paddedOutput a ω t) := by
  have hp : Measurable (fun h : History t => (ω, historyVector t h)) :=
    measurable_const.prodMk (historyVector_measurable t)
  exact Measurable.ite
    (measurableSet_eq_fun (frozen_measurable a ω t).fst measurable_const)
    (frozen_measurable a ω t).snd ((a.output_measurable t).comp hp)

noncomputable def follow {d R Ω} [MeasurableSpace Ω]
    (a : Policy d R Ω) (ω : Ω) (T : Point d → E) (g : E) :
    (fuel t : ℕ) → History t → Point d
  | 0, t, h => paddedOutput a ω t h
  | fuel + 1, t, h => follow a ω T g fuel (t + 1) (h, ⟪paddedQuery a ω T t h, g⟫)

/-- The padded process has exactly the original stop/output semantics. -/
theorem follow_execute {d R Ω} [MeasurableSpace Ω]
    (a : Policy d R Ω) (ω : Ω) (T : Point d → E) (g : E)
    (fuel t : ℕ) (h : History t) :
    follow a ω T g fuel t h =
      if (frozen a ω t h).1 then (frozen a ω t h).2 else
        execute a (fun x => ⟪T x, g⟫) fuel t (ω, historyVector t h) := by
  induction fuel generalizing t with
  | zero => rfl
  | succ fuel ih =>
    rw [follow, ih]
    cases hf : (frozen a ω t h).1 <;>
      cases hs : a.stop t (ω, historyVector t h) <;>
      simp [frozen, paddedQuery, execute, nextHistory, historyVector, hf, hs]

/-- The same fixed g supplies every raw scalar answer of the padded path. -/
theorem follow_rawHistory {d R Ω} [MeasurableSpace Ω]
    (a : Policy d R Ω) (ω : Ω) (T : Point d → E) (g : E)
    (fuel t : ℕ) :
    follow a ω T g fuel t (rawHistory (paddedQuery a ω T) t g) =
      paddedOutput a ω (t + fuel) (rawHistory (paddedQuery a ω T) (t + fuel) g) := by
  induction fuel generalizing t with
  | zero => rfl
  | succ fuel ih =>
    change follow a ω T g fuel (t + 1) (rawHistory (paddedQuery a ω T) (t + 1) g) = _
    rw [ih]
    have hn : t + 1 + fuel = t + (fuel + 1) := by omega
    rw [hn]

/-- Finite cap and all early stopping branches of the actual Policy are
preserved by zero padding, with no assumed simulator output equality. -/
theorem paddedOutput_rawHistory_eq_run {d R Ω} [MeasurableSpace Ω]
    (a : Policy d R Ω) (ω : Ω) (T : Point d → E) (g : E) (cap : ℕ) :
    paddedOutput a ω cap (rawHistory (paddedQuery a ω T) cap g) =
      run a (fun x => ⟪T x, g⟫) cap ω := by
  have hp := follow_rawHistory a ω T g cap 0
  have he := follow_execute a ω T g cap 0 ()
  rw [Nat.zero_add] at hp
  change follow a ω T g cap 0 () = paddedOutput a ω cap (rawHistory (paddedQuery a ω T) cap g) at hp
  simp only [frozen, Bool.false_eq_true, ↓reduceIte, historyVector] at he
  exact hp.symm.trans he

/-- Exact output-law transfer for the manuscript's actual Policy, preserving
its finite cap, early stopping, and feasible output fallback. -/
theorem policy_gaussian_output_law {d R Ω} [MeasurableSpace Ω]
    (a : Policy d R Ω) (ω : Ω) (T : Point d → E) (hT : Measurable T)
    (σ δ : ℝ) (hσ : σ ≠ 0) (θ : E) (cap : ℕ) :
    (signalLaw (PaperAdaptiveGaussianOracleBridge.signalMeans
      (rows (paddedQuery a ω T) σ)
      (rows_measurable (paddedQuery a ω T) (paddedQuery_measurable a ω T hT) σ)
      σ δ θ) cap).map
      (fun h => paddedOutput a ω cap (decoded (paddedQuery a ω T) σ cap h)) =
        (PaperGaussianOracleBridge.sourcePrior σ (δ • θ)).map
          (fun g => run a (fun x => ⟪T x, g⟫) cap ω) := by
  have h := raw_policy_output_law (paddedQuery a ω T) (paddedQuery_measurable a ω T hT)
    σ δ hσ θ cap (paddedOutput a ω cap) (paddedOutput_measurable a ω cap)
  have hf : (fun g => paddedOutput a ω cap (rawHistory (paddedQuery a ω T) cap g)) =
      (fun g => run a (fun x => ⟪T x, g⟫) cap ω) := by
    funext g
    exact paddedOutput_rawHistory_eq_run a ω T g cap
  rw [hf] at h
  exact h

/-- The success event of an actual stopped Policy has exactly its original
source-prior probability under the constructed Gaussian sensing channel. -/
theorem policy_gaussian_event_probability {d R Ω} [MeasurableSpace Ω]
    (a : Policy d R Ω) (ω : Ω) (T : Point d → E) (hT : Measurable T)
    (σ δ : ℝ) (hσ : σ ≠ 0) (θ : E) (cap : ℕ)
    (B : Set (Point d)) (hB : MeasurableSet B) :
    (signalLaw (PaperAdaptiveGaussianOracleBridge.signalMeans
      (rows (paddedQuery a ω T) σ)
      (rows_measurable (paddedQuery a ω T) (paddedQuery_measurable a ω T hT) σ)
      σ δ θ) cap)
      {h | paddedOutput a ω cap (decoded (paddedQuery a ω T) σ cap h) ∈ B} =
        (PaperGaussianOracleBridge.sourcePrior σ (δ • θ))
          {g | run a (fun x => ⟪T x, g⟫) cap ω ∈ B} := by
  have h := raw_policy_event_probability (paddedQuery a ω T) (paddedQuery_measurable a ω T hT)
    σ δ hσ θ cap (paddedOutput a ω cap) (paddedOutput_measurable a ω cap) B hB
  simpa only [paddedOutput_rawHistory_eq_run] using h

/-- Coordinate identity from the manuscript's l1 model points to the
Euclidean vectors used by the Gaussian source calculation. -/
noncomputable def pointVector {d : ℕ} (x : Point d) : EuclideanSpace ℝ (Fin d) :=
  WithLp.toLp 2 (WithLp.ofLp x)

theorem pointVector_measurable (d : ℕ) : Measurable (@pointVector d) := by
  exact (WithLp.measurable_toLp 2 (Fin d → ℝ)).comp (WithLp.measurable_ofLp 1 (Fin d → ℝ))

end PaperPolicyGaussianBridge


end
-- END PolicyGaussianBridge.lean

-- BEGIN PolicyRecovery.lean
section
namespace PaperPolicyRecovery

open MeasureTheory ProbabilityTheory InformationTheory PaperGaussianKL PaperPinsker
  PaperRawPolicyDecoder PaperPolicyGaussianBridge Task003.OracleModel
open scoped RealInnerProductSpace NNReal ENNReal

/-- Gaussian sensing recovery bound for the actual total stopped Policy,
with all source priors, adaptive queries, output decoder, and event laws
constructed explicitly. No expected-KL or probability-gap premise is used. -/
theorem policy_gaussian_recovery_bound
    {d : ℕ} (hd : 0 < d) {R : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    (a : Policy d R Ω) (ω : Ω) (σ δ : ℝ) (hσ : σ ≠ 0) (cap : ℕ)
    (estimate : Point d → Fin d) (he : Measurable estimate) :
    (∑ i, (PaperGaussianOracleBridge.sourcePrior σ
      (δ • EuclideanSpace.single i (1 : ℝ))).real
        {g | estimate (run a (fun x => ⟪pointVector x, g⟫) cap ω) = i}) / d ≤
      1 / d + Real.sqrt ((cap : ℝ) * (δ / σ) ^ 2 / (4 * d)) := by
  let q := paddedQuery a ω (@pointVector d)
  let hq : ∀ t, Measurable (q t) := paddedQuery_measurable a ω _ (pointVector_measurable d)
  let w := rows q σ
  let hw : ∀ t, Measurable (w t) := rows_measurable q hq σ
  let A : Fin d → AdaptiveMean := fun i =>
    PaperAdaptiveGaussianOracleBridge.signalMeans w hw σ δ (EuclideanSpace.single i (1 : ℝ))
  let decoder : History cap → Fin d := fun h => estimate
    (paddedOutput a ω cap (decoded q σ cap h))
  have hm : Measurable decoder :=
    he.comp ((paddedOutput_measurable a ω cap).comp (decoded_measurable q hq σ cap))
  have henergy : ∀ t (h : History t), ∑ i, (A i).mean t h ^ 2 ≤ (δ / σ) ^ 2 := by
    intro t h
    dsimp [A, PaperAdaptiveGaussianOracleBridge.signalMeans]
    simp only [EuclideanSpace.inner_single_right, conj_trivial, one_mul,
      mul_pow, ← Finset.mul_sum]
    rw [← EuclideanSpace.real_norm_sq_eq]
    rcases row_norm_zero_or_one q σ t h with hz | hone
    · change (δ / σ) ^ 2 * ‖rows q σ t h‖ ^ 2 ≤ _
      rw [hz]
      simpa only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero] using sq_nonneg (δ / σ)
    · change (δ / σ) ^ 2 * ‖rows q σ t h‖ ^ 2 ≤ _
      rw [hone]
      simp
  have hbound := finite_adaptive_gaussian_kl_sum_le A cap ((δ / σ) ^ 2)
    (sq_nonneg _) henergy
  have hsumfinite : (∑ i, klDiv (nullLaw cap) (signalLaw (A i) cap)) ≠ ∞ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hbound
  have hfinite : ∀ i, klDiv (nullLaw cap) (signalLaw (A i) cap) ≠ ∞ := by
    intro i
    exact ENNReal.sum_ne_top.mp hsumfinite i (Finset.mem_univ i)
  have hb := finite_estimator_recovery_bound hd (nullLaw cap)
    (fun i => signalLaw (A i) cap) hfinite decoder hm
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hbound
  rw [ENNReal.toReal_sum (ENNReal.sum_ne_top.mp hsumfinite),
    ENNReal.toReal_ofReal (by positivity)] at hreal
  have hscaled : (∑ i, (klDiv (nullLaw cap) (signalLaw (A i) cap)).toReal) /
      (2 * d) ≤ (cap : ℝ) * (δ / σ) ^ 2 / (4 * d) := by
    have ht := div_le_div_of_nonneg_right hreal (by positivity : (0 : ℝ) ≤ 2 * d)
    simpa only [div_div, show (2 : ℝ) * (2 * d) = 4 * d by ring] using ht
  have hp (i : Fin d) :
      (signalLaw (A i) cap).real (decoder ⁻¹' {i}) =
        (PaperGaussianOracleBridge.sourcePrior σ (δ • EuclideanSpace.single i (1 : ℝ))).real
          {g | estimate (run a (fun x => ⟪pointVector x, g⟫) cap ω) = i} := by
    have h := policy_gaussian_event_probability a ω (@pointVector d) (pointVector_measurable d)
      σ δ hσ (EuclideanSpace.single i (1 : ℝ)) cap
      {x | estimate x = i} (measurableSet_eq_fun he measurable_const)
    exact congrArg ENNReal.toReal h
  have hsum :
      (∑ i, (PaperGaussianOracleBridge.sourcePrior σ
        (δ • EuclideanSpace.single i (1 : ℝ))).real
          {g | estimate (run a (fun x => ⟪pointVector x, g⟫) cap ω) = i}) =
        ∑ i, (signalLaw (A i) cap).real (decoder ⁻¹' {i}) := by
    apply Finset.sum_congr rfl
    intro i hi
    exact (hp i).symm
  rw [hsum]
  exact hb.trans (add_le_add le_rfl (Real.sqrt_le_sqrt hscaled))

/-- The resulting observation lower bound applies directly to the original
Policy's source-Gaussian recovery events, including every stopping branch. -/
theorem policy_gaussian_observation_lower_bound
    {d : ℕ} (hd : 6 ≤ d) {R : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    (a : Policy d R Ω) (ω : Ω) (σ δ : ℝ) (hσ : σ ≠ 0) (cap : ℕ)
    (estimate : Point d → Fin d) (he : Measurable estimate)
    (hrecovery : (2 / 3 : ℝ) <
      (∑ i, (PaperGaussianOracleBridge.sourcePrior σ
        (δ • EuclideanSpace.single i (1 : ℝ))).real
          {g | estimate (run a (fun x => ⟪pointVector x, g⟫) cap ω) = i}) / d) :
    (d : ℝ) ≤ (cap : ℝ) * (δ / σ) ^ 2 := by
  have hdpos : 0 < d := by omega
  have hb := policy_gaussian_recovery_bound hdpos a ω σ δ hσ cap estimate he
  have hdreal : (6 : ℝ) ≤ d := by exact_mod_cast hd
  have hbase : 1 / (d : ℝ) ≤ 1 / 6 :=
    one_div_le_one_div_of_le (by norm_num) hdreal
  have hsqrt : (1 / 2 : ℝ) < Real.sqrt ((cap : ℝ) * (δ / σ) ^ 2 / (4 * d)) := by
    linarith
  have hsquare := Real.sq_sqrt (show 0 ≤ (cap : ℝ) * (δ / σ) ^ 2 / (4 * d) by positivity)
  have hrootnonneg := Real.sqrt_nonneg ((cap : ℝ) * (δ / σ) ^ 2 / (4 * d))
  have hratio : (1 / 4 : ℝ) < (cap : ℝ) * (δ / σ) ^ 2 / (4 * d) := by nlinarith
  have hm := (lt_div_iff₀ (show (0 : ℝ) < 4 * d by positivity)).mp hratio
  nlinarith

end PaperPolicyRecovery


end
-- END PolicyRecovery.lean

-- BEGIN OracleJointMeasurability.lean
section

/- Dependencies: OracleModel. Actual run measurability jointly in a parametric
objective and the private seed, including genuine stopping. -/
namespace Task003.OracleJointMeasurability
open MeasureTheory Task003.OracleModel

variable {d : ℕ} {R : ℝ} {Ω P : Type*} [MeasurableSpace Ω] [MeasurableSpace P]

noncomputable def jointNext (a : Policy d R Ω) (F : P × Point d → ℝ) (n : ℕ)
    (p : P × (Ω × (Fin n → ℝ))) : P × (Ω × (Fin (n+1) → ℝ)) :=
  (p.1,nextHistory a (fun x => F (p.1,x)) n p.2)

theorem jointNext_measurable (a : Policy d R Ω) (F : P × Point d → ℝ)
    (hF : Measurable F) (n : ℕ) : Measurable (jointNext a F n) := by
  apply measurable_fst.prodMk
  apply measurable_snd.fst.prodMk
  apply measurable_pi_lambda
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simpa only [jointNext,nextHistory,Fin.snoc_last,Function.comp_def] using
      hF.comp (measurable_fst.prodMk ((a.query_measurable n).comp measurable_snd))
  · simpa only [jointNext,nextHistory,Fin.snoc_castSucc,Function.comp_def] using
      (measurable_pi_apply j).comp measurable_snd.snd

theorem execute_joint_measurable (a : Policy d R Ω) (F : P × Point d → ℝ)
    (hF : Measurable F) (fuel n : ℕ) :
    Measurable (fun p : P × (Ω × (Fin n → ℝ)) => execute a (fun x => F (p.1,x)) fuel n p.2) := by
  induction fuel generalizing n with
  | zero => exact (a.output_measurable n).comp measurable_snd
  | succ k ih =>
    change Measurable (fun p : P × (Ω × (Fin n → ℝ)) =>
      if a.stop n p.2 then a.output n p.2 else
        execute a (fun x => F (p.1,x)) k (n+1) (nextHistory a (fun x => F (p.1,x)) n p.2))
    apply Measurable.ite
    · exact measurableSet_eq_fun ((a.stop_measurable n).comp measurable_snd) measurable_const
    · exact (a.output_measurable n).comp measurable_snd
    · simpa only [Function.comp_def,jointNext] using
        (ih (n+1)).comp (jointNext_measurable a F hF n)

theorem run_joint_measurable (a : Policy d R Ω) (F : P × Point d → ℝ)
    (hF : Measurable F) (cap : ℕ) :
    Measurable (fun p : P × Ω => run a (fun x => F (p.1,x)) cap p.2) := by
  exact (execute_joint_measurable a F hF cap 0).comp
    (measurable_fst.prodMk (measurable_snd.prodMk measurable_const))

end Task003.OracleJointMeasurability


end
-- END OracleJointMeasurability.lean

-- BEGIN FiniteFamilyProduct.lean
section

/- Actual finite-family Tonelli/Fubini averaging. Instance laws are fixed
independently of the algorithm seed. No averaged probability bound is assumed. -/
namespace PaperFiniteFamilyProduct
open MeasureTheory

variable {G Seed : Type*} [MeasurableSpace G] [MeasurableSpace Seed]

theorem fiber_real_integrable (μ : Measure G) (ν : Measure Seed)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (S : Set (G×Seed)) (hS : MeasurableSet S) :
    Integrable (fun ω => μ.real {g | (g,ω)∈S}) ν := by
  apply (integrable_const (1:ℝ)).mono'
    (measurable_measure_prodMk_right hS).ennreal_toReal.aestronglyMeasurable
  exact ae_of_all ν (fun ω => by
    rw [Real.norm_eq_abs,abs_of_nonneg ENNReal.toReal_nonneg]
    change μ.real {g | (g,ω)∈S}≤1
    exact measureReal_le_one)

theorem fiber_real_integral_identity (μ : Measure G) (ν : Measure Seed)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (S : Set (G×Seed)) (hS : MeasurableSet S) :
    (∫ ω, μ.real {g | (g,ω)∈S} ∂ν)=(μ.prod ν).real S := by
  rw [measureReal_def,Measure.prod_apply_symm hS]
  exact integral_toReal (measurable_measure_prodMk_right hS).aemeasurable
    (ae_of_all ν (fun ω => measure_lt_top μ _))

theorem finite_family_product_event_average_eq {d : ℕ}
    (μ : Fin d → Measure G) [∀ i,IsProbabilityMeasure (μ i)]
    (ν : Measure Seed) [IsProbabilityMeasure ν]
    (S : Fin d → Set (G×Seed)) (hS : ∀ i,MeasurableSet (S i)) :
    (∑ i,((μ i).prod ν).real (S i))/(d : ℝ) =
      ∫ ω, (∑ i,(μ i).real {g | (g,ω)∈S i})/(d : ℝ) ∂ν := by
  rw [integral_div,integral_finsetSum Finset.univ
    (fun i _ => fiber_real_integrable (μ i) ν (S i) (hS i))]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  exact (fiber_real_integral_identity (μ i) ν (S i) (hS i)).symm

theorem finite_family_product_event_average_le {d : ℕ} (hd : 0<d)
    (μ : Fin d → Measure G) [∀ i,IsProbabilityMeasure (μ i)]
    (ν : Measure Seed) [IsProbabilityMeasure ν]
    (S : Fin d → Set (G×Seed)) (hS : ∀ i,MeasurableSet (S i))
    (C : ℝ) (hC : 0≤C)
    (hfixed : ∀ ω,(∑ i,(μ i).real {g | (g,ω)∈S i})/(d : ℝ)≤C) :
    (∑ i,((μ i).prod ν).real (S i))/(d : ℝ)≤C := by
  rw [finite_family_product_event_average_eq μ ν S hS]
  have hi : Integrable (fun ω => (∑ i,(μ i).real {g | (g,ω)∈S i})/(d : ℝ)) ν :=
    (integrable_finsetSum Finset.univ (fun i _ => fiber_real_integrable (μ i) ν (S i) (hS i))).div_const _
  have hb := integral_mono hi (integrable_const C) hfixed
  simpa only [integral_const,probReal_univ,one_smul] using hb

end PaperFiniteFamilyProduct


end
-- END FiniteFamilyProduct.lean

-- BEGIN HiddenSpikeGeometry.lean
section

namespace PaperHiddenSpikeGeometry

open PaperGeometry

noncomputable def spikeCoeff {d : ℕ} (b : Fin d → ℝ) (α : ℝ) (I : Fin d) (j : Fin d) : ℝ :=
  b j + if j = I then 4 * α else 0

noncomputable def spikeValue {d : ℕ} (b : Fin d → ℝ) (α : ℝ) (I : Fin d)
    (x : L1Space (Fin d)) : ℝ := rowValue (spikeCoeff b α I) x

noncomputable def negativeVertex {d : ℕ} (I : Fin d) : L1Space (Fin d) :=
  -PiLp.single 1 I (1 : ℝ)

theorem spikeCoeff_self {d : ℕ} (b : Fin d → ℝ) (α : ℝ) (I : Fin d) :
    spikeCoeff b α I I = b I + 4 * α := by simp [spikeCoeff]

theorem spikeCoeff_other {d : ℕ} (b : Fin d → ℝ) (α : ℝ) (I j : Fin d) (hj : j ≠ I) :
    spikeCoeff b α I j = b j := by simp [spikeCoeff, hj]

theorem negativeVertex_norm {d : ℕ} (I : Fin d) : ‖negativeVertex I‖ = 1 := by
  simp [negativeVertex]

theorem spikeValue_vertex {d : ℕ} (b : Fin d → ℝ) (α : ℝ) (I j : Fin d) :
    spikeValue b α I (negativeVertex j) = -spikeCoeff b α I j := by
  simp [spikeValue, rowValue, negativeVertex, PiLp.single_apply]

theorem spikeValue_decomposition {d : ℕ} (b : Fin d → ℝ) (α : ℝ) (I : Fin d)
    (x : L1Space (Fin d)) : spikeValue b α I x = rowValue b x + 4 * α * x I := by
  classical
  unfold spikeValue rowValue spikeCoeff
  simp_rw [add_mul, ite_mul, zero_mul]
  rw [Finset.sum_add_distrib]
  simp

theorem rowValue_abs_le {d : ℕ} (b : Fin d → ℝ) (ρ : ℝ) (_hρ : 0 ≤ ρ)
    (hb : ∀ j, |b j| ≤ ρ) (x : L1Space (Fin d)) : |rowValue b x| ≤ ρ * ‖x‖ := by
  rw [l1_norm_eq_sum_abs]
  unfold rowValue
  calc
    |∑ j, b j * x j| ≤ ∑ j, |b j * x j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, ρ * |x j| := by
      apply Finset.sum_le_sum
      intro j _
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right (hb j) (abs_nonneg _)
    _ = _ := (Finset.mul_sum _ _ _).symm

theorem spikeCoeff_bounds {d : ℕ} (b : Fin d → ℝ) (α : ℝ) (hα : 0 < α)
    (hb : ∀ j, |b j| ≤ α / 4) (I : Fin d) :
    15 * α / 4 ≤ spikeCoeff b α I I ∧ spikeCoeff b α I I ≤ 17 * α / 4 ∧
      ∀ j ≠ I, |spikeCoeff b α I j| < spikeCoeff b α I I := by
  have hbi := abs_le.mp (hb I)
  rw [spikeCoeff_self]
  refine ⟨by linarith, by linarith, ?_⟩
  intro j hj
  rw [spikeCoeff_other b α I j hj]
  have hbj := hb j
  linarith

theorem spikeCoeff_abs_le_one {d : ℕ} (b : Fin d → ℝ) (α : ℝ) (hα : 0 < α)
    (hsmall : α ≤ 1 / 8) (hb : ∀ j, |b j| ≤ α / 4) (I : Fin d) :
    ∀ j, |spikeCoeff b α I j| ≤ 1 := by
  intro j
  by_cases hj : j = I
  · subst j
    have hpos : 0 ≤ spikeCoeff b α I I := by
      have h := (spikeCoeff_bounds b α hα hb I).1
      linarith
    rw [abs_of_nonneg hpos]
    have h := (spikeCoeff_bounds b α hα hb I).2.1
    linarith
  · rw [spikeCoeff_other b α I j hj]
    have h := hb j
    linarith

theorem spikeValue_lipschitz {d : ℕ} (b : Fin d → ℝ) (α : ℝ) (hα : 0 < α)
    (hsmall : α ≤ 1 / 8) (hb : ∀ j, |b j| ≤ α / 4) (I : Fin d) :
    LipschitzWith 1 (spikeValue b α I) :=
  rowValue_lipschitz (spikeCoeff b α I) 1 (spikeCoeff_abs_le_one b α hα hsmall hb I)

theorem spikeValue_convex {d : ℕ} (b : Fin d → ℝ) (α : ℝ) (I : Fin d) :
    ConvexOn ℝ Set.univ (spikeValue b α I) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a c _ _ _
  change (∑ j, spikeCoeff b α I j * (a * x j + c * y j)) ≤
    a * (∑ j, spikeCoeff b α I j * x j) + c * (∑ j, spikeCoeff b α I j * y j)
  apply le_of_eq
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem spikeValue_minimum {d : ℕ} (b : Fin d → ℝ) (α : ℝ) (hα : 0 < α)
    (hb : ∀ j, |b j| ≤ α / 4) (I : Fin d) :
    ‖negativeVertex I‖ ≤ 1 ∧
      spikeValue b α I (negativeVertex I) = -spikeCoeff b α I I ∧
      ∀ x : L1Space (Fin d), ‖x‖ ≤ 1 → -spikeCoeff b α I I ≤ spikeValue b α I x := by
  have hbound := spikeCoeff_bounds b α hα hb I
  have hIpos : 0 ≤ spikeCoeff b α I I := by linarith [hbound.1]
  refine ⟨(negativeVertex_norm I).le, spikeValue_vertex b α I I, ?_⟩
  intro x hx
  have hg : ∀ j, |spikeCoeff b α I j| ≤ spikeCoeff b α I I := by
    intro j
    by_cases hj : j = I
    · subst j; rw [abs_of_nonneg hIpos]
    · exact (hbound.2.2 j hj).le
  have hrow := rowValue_abs_le (spikeCoeff b α I) (spikeCoeff b α I I) hIpos hg x
  have hmul := mul_le_mul_of_nonneg_left hx hIpos
  change -spikeCoeff b α I I ≤ rowValue (spikeCoeff b α I) x
  linarith [neg_abs_le (rowValue (spikeCoeff b α I) x)]

theorem success_coordinate_negative {d : ℕ} (b : Fin d → ℝ) (α : ℝ) (hα : 0 < α)
    (hb : ∀ j, |b j| ≤ α / 4) (I : Fin d) (x : L1Space (Fin d)) (hx : ‖x‖ ≤ 1)
    (hsuccess : spikeValue b α I x + spikeCoeff b α I I ≤ α) : x I < -(1 / 2 : ℝ) := by
  have hbrow := rowValue_abs_le b (α / 4) (by positivity) hb x
  have hmul := mul_le_mul_of_nonneg_left hx (show 0 ≤ α / 4 by positivity)
  have hblow : -(α / 4) ≤ rowValue b x := by linarith [neg_abs_le (rowValue b x)]
  have hbi := (abs_le.mp (hb I)).1
  rw [spikeValue_decomposition, spikeCoeff_self] at hsuccess
  by_contra hnot
  have hxi : -(1 / 2 : ℝ) ≤ x I := le_of_not_gt hnot
  have hprod := mul_nonneg hα.le (show 0 ≤ x I + 1 / 2 by linarith)
  nlinarith

theorem two_coordinates_norm_le {d : ℕ} (x : L1Space (Fin d)) (I j : Fin d) (hj : j ≠ I) :
    |x I| + |x j| ≤ ‖x‖ := by
  classical
  rw [l1_norm_eq_sum_abs]
  have hp : ∑ k ∈ ({I, j} : Finset (Fin d)), |x k| ≤ ∑ k : Fin d, |x k| :=
    Finset.sum_le_sum_of_subset_of_nonneg (by simp) (fun k _ _ => abs_nonneg (x k))
  simpa [Finset.sum_pair, hj, Ne.symm hj] using hp

theorem success_unique_largest_coordinate {d : ℕ} (b : Fin d → ℝ) (α : ℝ) (hα : 0 < α)
    (hb : ∀ j, |b j| ≤ α / 4) (I : Fin d) (x : L1Space (Fin d)) (hx : ‖x‖ ≤ 1)
    (hsuccess : spikeValue b α I x + spikeCoeff b α I I ≤ α) :
    ∀ j ≠ I, |x j| < |x I| := by
  have hxI := success_coordinate_negative b α hα hb I x hx hsuccess
  have hbig : 1 / 2 < |x I| := by rw [abs_of_neg (by linarith : x I < 0)]; linarith
  intro j hj
  have hpair := two_coordinates_norm_le x I j hj
  linarith

theorem wrong_vertex_separation {d : ℕ} (b : Fin d → ℝ) (α : ℝ) (_hα : 0 < α)
    (hb : ∀ j, |b j| ≤ α / 4) (I j : Fin d) (hj : j ≠ I) :
    7 * α / 2 ≤ spikeValue b α I (negativeVertex j) - spikeValue b α I (negativeVertex I) := by
  rw [spikeValue_vertex, spikeValue_vertex, spikeCoeff_other b α I j hj, spikeCoeff_self]
  have hI := (abs_le.mp (hb I)).1
  have hjb := (abs_le.mp (hb j)).2
  linarith

def MaximumIndex (d : ℕ) (x : L1Space (Fin d)) (k : ℕ) : Prop :=
  ∃ hk : k < d, ∀ j : Fin d, |x j| ≤ |x ⟨k, hk⟩|

theorem maximumIndex_exists (d : ℕ) (hd : 0 < d) (x : L1Space (Fin d)) :
    ∃ k : ℕ, MaximumIndex d x k := by
  obtain ⟨i, _, hi⟩ := Finset.exists_max_image Finset.univ (fun j => |x j|)
    (by exact ⟨⟨0, hd⟩, Finset.mem_univ _⟩)
  exact ⟨i.val, i.isLt, fun j => hi j (Finset.mem_univ _)⟩

theorem maximumIndex_measurable (d k : ℕ) :
    MeasurableSet {x : L1Space (Fin d) | MaximumIndex d x k} := by
  by_cases hk : k < d
  · have he : {x : L1Space (Fin d) | MaximumIndex d x k} =
        ⋂ j : Fin d, {x | |x j| ≤ |x ⟨k, hk⟩|} := by
      ext x
      simp [MaximumIndex, hk]
    rw [he]
    exact MeasurableSet.iInter (fun j => measurableSet_le
      (PiLp.continuous_apply 1 _ j).abs.measurable
      (PiLp.continuous_apply 1 _ (⟨k, hk⟩ : Fin d)).abs.measurable)
  · simp [MaximumIndex, hk]

noncomputable def argmaxAbsNat (d : ℕ) (hd : 0 < d) (x : L1Space (Fin d)) : ℕ := by
  classical
  exact Nat.find (maximumIndex_exists d hd x)

theorem argmaxAbsNat_measurable (d : ℕ) (hd : 0 < d) : Measurable (argmaxAbsNat d hd) := by
  classical
  exact Measurable.find (f := fun k (_ : L1Space (Fin d)) => k)
    (fun _ => measurable_const) (maximumIndex_measurable d) (maximumIndex_exists d hd)

theorem argmaxAbsNat_lt (d : ℕ) (hd : 0 < d) (x : L1Space (Fin d)) : argmaxAbsNat d hd x < d := by
  classical
  exact (Nat.find_spec (maximumIndex_exists d hd x)).choose

noncomputable def argmaxAbs (d : ℕ) (hd : 0 < d) (x : L1Space (Fin d)) : Fin d :=
  ⟨argmaxAbsNat d hd x % d, Nat.mod_lt _ hd⟩

theorem argmaxAbs_measurable (d : ℕ) (hd : 0 < d) : Measurable (argmaxAbs d hd) := by
  let q : ℕ → Fin d := fun k => ⟨k % d, Nat.mod_lt _ hd⟩
  exact (measurable_of_countable q).comp (argmaxAbsNat_measurable d hd)

theorem argmaxAbs_is_maximum (d : ℕ) (hd : 0 < d) (x : L1Space (Fin d)) (j : Fin d) :
    |x j| ≤ |x (argmaxAbs d hd x)| := by
  classical
  obtain ⟨hk, hmax⟩ := Nat.find_spec (maximumIndex_exists d hd x)
  simpa only [argmaxAbs, argmaxAbsNat, Nat.mod_eq_of_lt hk] using hmax j

theorem success_recovers_index {d : ℕ} (hd : 0 < d) (b : Fin d → ℝ) (α : ℝ) (hα : 0 < α)
    (hb : ∀ j, |b j| ≤ α / 4) (I : Fin d) (x : L1Space (Fin d)) (hx : ‖x‖ ≤ 1)
    (hsuccess : spikeValue b α I x + spikeCoeff b α I I ≤ α) : argmaxAbs d hd x = I := by
  by_contra hne
  have hstrict := success_unique_largest_coordinate b α hα hb I x hx hsuccess (argmaxAbs d hd x) hne
  have hmax := argmaxAbs_is_maximum d hd x I
  linarith

noncomputable def chooseVertex {d : ℕ} (p : (Fin d × Fin d) × (ℝ × ℝ)) : Fin d :=
  if p.2.1 ≤ p.2.2 then p.1.1 else p.1.2

theorem chooseVertex_measurable (d : ℕ) : Measurable (@chooseVertex d) := by
  exact Measurable.ite (measurableSet_le (measurable_fst.comp measurable_snd)
    (measurable_snd.comp measurable_snd))
    (measurable_fst.comp measurable_fst) (measurable_snd.comp measurable_fst)

theorem chooseVertex_recovers {d : ℕ} (b : Fin d → ℝ) (α : ℝ) (hα : 0 < α)
    (hb : ∀ j, |b j| ≤ α / 4) (I j₁ j₂ : Fin d) (hit : j₁ = I ∨ j₂ = I) :
    chooseVertex ((j₁, j₂),
      (spikeValue b α I (negativeVertex j₁), spikeValue b α I (negativeVertex j₂))) = I := by
  rcases hit with h₁ | h₂
  · subst j₁
    by_cases hj : j₂ = I
    · subst j₂; simp [chooseVertex]
    · have hsep := wrong_vertex_separation b α hα hb I j₂ hj
      have hle : spikeValue b α I (negativeVertex I) ≤ spikeValue b α I (negativeVertex j₂) := by
        linarith
      simp [chooseVertex, hle]
  · subst j₂
    by_cases hj : j₁ = I
    · subst j₁; simp [chooseVertex]
    · have hsep := wrong_vertex_separation b α hα hb I j₁ hj
      have hnot : ¬spikeValue b α I (negativeVertex j₁) ≤ spikeValue b α I (negativeVertex I) := by
        linarith
      simp [chooseVertex, hnot]

end PaperHiddenSpikeGeometry


end
-- END HiddenSpikeGeometry.lean

-- BEGIN HiddenSpikeTails.lean
section

namespace PaperHiddenSpikeTails

open MeasureTheory ProbabilityTheory Set

theorem centeredGaussian_subgaussian (v : NNReal) :
    HasSubgaussianMGF (id : ℝ → ℝ) v (gaussianReal 0 v) where
  integrable_exp_mul t := integrable_exp_mul_gaussianReal t
  mgf_le t := by rw [mgf_id_gaussianReal]; simp

theorem centeredGaussian_abs_tail (v : NNReal) (r : ℝ) (hr : 0 ≤ r) :
    (gaussianReal 0 v).real {x : ℝ | r ≤ |x|} ≤ 2 * Real.exp (-r ^ 2 / (2 * (v : ℝ))) := by
  have hp := (centeredGaussian_subgaussian v).measure_ge_le hr
  have hn := (centeredGaussian_subgaussian v).neg.measure_ge_le hr
  have he : {x : ℝ | r ≤ |x|} = {x : ℝ | r ≤ x} ∪ {x : ℝ | r ≤ -x} := by
    ext x
    simp only [mem_setOf_eq, mem_union]
    constructor
    · intro hx
      rcases le_total 0 x with h | h
      · exact Or.inl (by rwa [abs_of_nonneg h] at hx)
      · exact Or.inr (by rwa [abs_of_nonpos h] at hx)
    · rintro (hx | hx)
      · exact hx.trans (le_abs_self _)
      · exact hx.trans (neg_le_abs _)
  rw [he]
  have hu := measureReal_union_le (μ := gaussianReal 0 v) {x : ℝ | r ≤ x} {x : ℝ | r ≤ -x}
  change (gaussianReal 0 v).real {x : ℝ | r ≤ x} ≤ _ at hp
  change (gaussianReal 0 v).real {x : ℝ | r ≤ -x} ≤ _ at hn
  linarith

noncomputable def noiseLaw (d : ℕ) (v : NNReal) : Measure (Fin d → ℝ) :=
  Measure.pi (fun _ : Fin d => gaussianReal 0 v)

instance noiseLaw_isProbability (d : ℕ) (v : NNReal) : IsProbabilityMeasure (noiseLaw d v) := by
  unfold noiseLaw
  infer_instance

theorem coordinate_abs_tail (d : ℕ) (v : NNReal) (i : Fin d) (r : ℝ) (hr : 0 ≤ r) :
    (noiseLaw d v).real {b | r ≤ |b i|} ≤ 2 * Real.exp (-r ^ 2 / (2 * (v : ℝ))) := by
  have hp : MeasurePreserving (Function.eval i) (noiseLaw d v) (gaussianReal 0 v) :=
    measurePreserving_eval (μ := fun _ : Fin d => gaussianReal 0 v) i
  have he : (noiseLaw d v) {b | r ≤ |b i|} = (gaussianReal 0 v) {x : ℝ | r ≤ |x|} := by
    rw [← hp.map_eq, Measure.map_apply (measurable_pi_apply i) (by measurability)]
    rfl
  unfold Measure.real
  rw [he]
  exact centeredGaussian_abs_tail v r hr

theorem product_bad_tail (d : ℕ) (v : NNReal) (r : ℝ) (hr : 0 ≤ r) :
    (noiseLaw d v).real {b | ∃ i : Fin d, r < |b i|} ≤
      2 * d * Real.exp (-r ^ 2 / (2 * (v : ℝ))) := by
  have hsub : {b : Fin d → ℝ | ∃ i, r < |b i|} ⊆ ⋃ i : Fin d, {b | r ≤ |b i|} := by
    rintro b ⟨i, hi⟩
    exact mem_iUnion.mpr ⟨i, hi.le⟩
  calc
    _ ≤ (noiseLaw d v).real (⋃ i : Fin d, {b | r ≤ |b i|}) := measureReal_mono hsub
    _ ≤ ∑ i : Fin d, (noiseLaw d v).real {b | r ≤ |b i|} := measureReal_iUnion_fintype_le _
    _ ≤ ∑ _ : Fin d, 2 * Real.exp (-r ^ 2 / (2 * (v : ℝ))) :=
      Finset.sum_le_sum (fun i _ => coordinate_abs_tail d v i r hr)
    _ = _ := by simp; ring

noncomputable def spikeSigma (α ell : ℝ) : ℝ := α / (16 * Real.sqrt ell)

noncomputable def spikeVariance (α ell : ℝ) : NNReal := ⟨spikeSigma α ell ^ 2, sq_nonneg _⟩

theorem hidden_bad_tail_ell (d : ℕ) (α ell : ℝ) (hα : 0 < α) (hell : 0 < ell) :
    (noiseLaw d (spikeVariance α ell)).real {b | ∃ i : Fin d, α / 4 < |b i|} ≤
      2 * d * Real.exp (-8 * ell) := by
  have hb := product_bad_tail d (spikeVariance α ell) (α / 4) (by positivity)
  have hs : Real.sqrt ell ≠ 0 := (Real.sqrt_pos.mpr hell).ne'
  have halgebra : ∀ a s : ℝ, a ≠ 0 → s ≠ 0 →
      -(a / 4) ^ 2 / (2 * (a / (16 * s)) ^ 2) = -8 * s ^ 2 := by
    intro a s ha hs
    field_simp [ha, hs]
    ring
  have he : -(α / 4) ^ 2 / (2 * ((spikeVariance α ell : NNReal) : ℝ)) = -8 * ell := by
    change -(α / 4) ^ 2 / (2 * (α / (16 * Real.sqrt ell)) ^ 2) = _
    rw [halgebra α (Real.sqrt ell) hα.ne' hs, Real.sq_sqrt hell.le]
  rwa [he] at hb

theorem exp_log_eight (d : ℕ) (hd : 0 < d) :
    2 * (d : ℝ) * Real.exp (-8 * Real.log (Real.exp 1 * d)) =
      2 / (Real.exp 8 * (d : ℝ) ^ 7) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hx : 0 < Real.exp 1 * (d : ℝ) := mul_pos (Real.exp_pos _) hdR
  have hexp : Real.exp (-8 * Real.log (Real.exp 1 * d)) =
      ((Real.exp 1 * (d : ℝ)) ^ 8)⁻¹ := by
    have hn : Real.exp (8 * Real.log (Real.exp 1 * d)) =
        Real.exp (Real.log (Real.exp 1 * d)) ^ 8 := by
      convert Real.exp_nat_mul (Real.log (Real.exp 1 * d)) 8 using 1
      norm_num
    rw [show -8 * Real.log (Real.exp 1 * d) = -(8 * Real.log (Real.exp 1 * d)) by ring,
      Real.exp_neg, hn, Real.exp_log hx]
  have he8 : (Real.exp (1 : ℝ)) ^ 8 = Real.exp 8 := by
    rw [← Real.exp_nat_mul]
    norm_num
  rw [hexp, mul_pow, he8]
  field_simp [hdR.ne', Real.exp_ne_zero]

theorem hidden_bad_tail (d : ℕ) (hd : 0 < d) (α : ℝ) (hα : 0 < α) :
    (noiseLaw d (spikeVariance α (Real.log (Real.exp 1 * d)))).real
      {b | ∃ i : Fin d, α / 4 < |b i|} ≤ 2 / (Real.exp 8 * (d : ℝ) ^ 7) := by
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hell : 0 < Real.log (Real.exp 1 * (d : ℝ)) := by
    apply Real.log_pos
    have he : 1 < Real.exp (1 : ℝ) := Real.one_lt_exp_iff.mpr (by norm_num)
    nlinarith
  have hb := hidden_bad_tail_ell d α (Real.log (Real.exp 1 * d)) hα hell
  rwa [exp_log_eight d hd] at hb

def goodEvent (d : ℕ) (α : ℝ) : Set (Fin d → ℝ) := {b | ∀ i, |b i| ≤ α / 4}

theorem goodEvent_measurable (d : ℕ) (α : ℝ) : MeasurableSet (goodEvent d α) := by
  have he : goodEvent d α = ⋂ i : Fin d, {b : Fin d → ℝ | |b i| ≤ α / 4} := by
    ext b
    simp [goodEvent]
  rw [he]
  exact MeasurableSet.iInter (fun i => measurableSet_le (measurable_pi_apply i).abs measurable_const)

theorem hidden_good_mass (d : ℕ) (hd : 0 < d) (α : ℝ) (hα : 0 < α) :
    (63 / 64 : ℝ) ≤ (noiseLaw d (spikeVariance α (Real.log (Real.exp 1 * d)))).real (goodEvent d α) := by
  have hb := hidden_bad_tail d hd α hα
  have hgood : (goodEvent d α)ᶜ = {b : Fin d → ℝ | ∃ i, α / 4 < |b i|} := by
    ext b
    simp [goodEvent, not_forall, not_le]
  have hsum := measureReal_add_measureReal_compl
    (μ := noiseLaw d (spikeVariance α (Real.log (Real.exp 1 * d)))) (goodEvent_measurable d α)
  rw [hgood] at hsum
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hd7 : (1 : ℝ) ≤ (d : ℝ) ^ 7 := by nlinarith [one_le_pow₀ hdR (n := 7)]
  have he1 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have he8 : (256 : ℝ) ≤ Real.exp 8 := by
    calc
      (256 : ℝ) = (2 : ℝ) ^ 8 := by norm_num
      _ ≤ (Real.exp 1) ^ 8 := by gcongr
      _ = Real.exp 8 := by rw [← Real.exp_nat_mul]; norm_num
  have hden : (256 : ℝ) ≤ Real.exp 8 * (d : ℝ) ^ 7 := by nlinarith
  have hfrac : 2 / (Real.exp 8 * (d : ℝ) ^ 7) ≤ (1 / 128 : ℝ) := by
    apply (div_le_iff₀ (by positivity)).2
    linarith
  have huniv : (noiseLaw d (spikeVariance α (Real.log (Real.exp 1 * d)))).real Set.univ = 1 := by simp
  rw [huniv] at hsum
  linarith

end PaperHiddenSpikeTails


end
-- END HiddenSpikeTails.lean

-- BEGIN TruncatedGaussianRows.lean
section

namespace PaperTruncatedGaussianRows

open MeasureTheory ProbabilityTheory Set PaperHiddenSpikeTails

noncomputable def normSq {d : ℕ} (b : Fin d → ℝ) : ℝ := ∑ i, (b i) ^ 2

def truncEvent (d : ℕ) : Set (Fin d → ℝ) := {b | normSq b ≤ 4 * d}

theorem normSq_nonneg {d : ℕ} (b : Fin d → ℝ) : 0 ≤ normSq b :=
  Finset.sum_nonneg (fun i _ => sq_nonneg (b i))

theorem normSq_continuous (d : ℕ) : Continuous (@normSq d) := by
  unfold normSq
  fun_prop

theorem truncEvent_measurable (d : ℕ) : MeasurableSet (truncEvent d) :=
  measurableSet_le (normSq_continuous d).measurable measurable_const

theorem gaussian_second_moment : (∫ x : ℝ, x ^ 2 ∂gaussianReal 0 1) = 1 := by
  have hv := variance_fun_id_gaussianReal (μ := 0) (v := 1)
  rw [variance_of_integral_eq_zero (by fun_prop) (by simp)] at hv
  exact hv

theorem coordinate_sq_integrable (d : ℕ) (i : Fin d) :
    Integrable (fun b : Fin d → ℝ => (b i) ^ 2) (noiseLaw d 1) := by
  have hp : MeasurePreserving (Function.eval i) (noiseLaw d 1) (gaussianReal 0 1) :=
    measurePreserving_eval (μ := fun _ : Fin d => gaussianReal 0 1) i
  exact hp.integrable_comp_of_integrable (memLp_id_gaussianReal (μ := 0) (v := 1) 2).integrable_sq

theorem coordinate_sq_integral (d : ℕ) (i : Fin d) :
    (∫ b : Fin d → ℝ, (b i) ^ 2 ∂noiseLaw d 1) = 1 := by
  have hp : MeasurePreserving (Function.eval i) (noiseLaw d 1) (gaussianReal 0 1) :=
    measurePreserving_eval (μ := fun _ : Fin d => gaussianReal 0 1) i
  calc
    _ = ∫ x : ℝ, x ^ 2 ∂(noiseLaw d 1).map (Function.eval i) :=
      (integral_map hp.measurable.aemeasurable (by fun_prop)).symm
    _ = 1 := by rw [hp.map_eq, gaussian_second_moment]

theorem normSq_integrable (d : ℕ) : Integrable (@normSq d) (noiseLaw d 1) := by
  exact integrable_finsetSum _ (fun i _ => coordinate_sq_integrable d i)

theorem normSq_integral (d : ℕ) : (∫ b, normSq b ∂noiseLaw d 1) = d := by
  unfold normSq
  rw [integral_finsetSum _ (fun i _ => coordinate_sq_integrable d i)]
  simp [coordinate_sq_integral]

theorem truncEvent_mass (d : ℕ) (hd : 0 < d) : (3 / 4 : ℝ) ≤ (noiseLaw d 1).real (truncEvent d) := by
  have hm := mul_meas_ge_le_integral_of_nonneg
    (μ := noiseLaw d 1) (Filter.Eventually.of_forall (@normSq_nonneg d))
    (normSq_integrable d) (4 * d)
  rw [normSq_integral] at hm
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hbad : (noiseLaw d 1).real {b | 4 * (d : ℝ) < normSq b} ≤ (1 / 4 : ℝ) := by
    have hmono : (noiseLaw d 1).real {b | 4 * (d : ℝ) < normSq b} ≤
        (noiseLaw d 1).real {b | 4 * (d : ℝ) ≤ normSq b} :=
      measureReal_mono (fun b hb => show 4 * (d : ℝ) ≤ normSq b from le_of_lt hb)
    have hdiv := (mul_le_mul_of_nonneg_left hmono (show 0 ≤ 4 * (d : ℝ) by positivity)).trans hm
    nlinarith
  have hcomp : (truncEvent d)ᶜ = {b : Fin d → ℝ | 4 * (d : ℝ) < normSq b} := by
    ext b
    simp [truncEvent, not_le]
  have hsum := measureReal_add_measureReal_compl (μ := noiseLaw d 1) (truncEvent_measurable d)
  rw [hcomp] at hsum
  have huniv : (noiseLaw d 1).real Set.univ = 1 := by simp
  rw [huniv] at hsum
  linarith

theorem cond_real_le_four_thirds {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (S A : Set Ω) (hS : MeasurableSet S) (hmass : (3 / 4 : ℝ) ≤ μ.real S) :
    (ProbabilityTheory.cond μ S).real A ≤ (4 / 3 : ℝ) * μ.real A := by
  have hspos : 0 < μ.real S := by linarith
  have hinv : (μ.real S)⁻¹ ≤ (4 / 3 : ℝ) := by
    apply (inv_le_iff_one_le_mul₀ hspos).2
    linarith
  unfold Measure.real
  rw [ProbabilityTheory.cond_apply hS μ A, ENNReal.toReal_mul, ENNReal.toReal_inv]
  change (μ.real S)⁻¹ * μ.real (S ∩ A) ≤ _
  calc
    _ ≤ (μ.real S)⁻¹ * μ.real A :=
      mul_le_mul_of_nonneg_left (measureReal_mono inter_subset_right) (inv_nonneg.mpr hspos.le)
    _ ≤ _ := mul_le_mul_of_nonneg_right hinv measureReal_nonneg

noncomputable def truncatedLaw (d : ℕ) : Measure (Fin d → ℝ) :=
  ProbabilityTheory.cond (noiseLaw d 1) (truncEvent d)

theorem truncatedLaw_isProbability (d : ℕ) (hd : 0 < d) : IsProbabilityMeasure (truncatedLaw d) := by
  have hm : (noiseLaw d 1) (truncEvent d) ≠ 0 := by
    intro hz
    have hl := truncEvent_mass d hd
    norm_num [Measure.real, hz] at hl
  exact ProbabilityTheory.cond_isProbabilityMeasure hm

theorem truncated_bad_tail (d : ℕ) (hd : 0 < d) (r : ℝ) (hr : 0 ≤ r) :
    (truncatedLaw d).real {b | ∃ i : Fin d, r < |b i|} ≤
      (8 / 3 : ℝ) * d * Real.exp (-r ^ 2 / 2) := by
  have hc := cond_real_le_four_thirds (noiseLaw d 1) (truncEvent d)
    {b | ∃ i : Fin d, r < |b i|} (truncEvent_measurable d) (truncEvent_mass d hd)
  have hu := product_bad_tail d 1 r hr
  change (truncatedLaw d).real _ ≤ _ at hc
  have hmul := mul_le_mul_of_nonneg_left hu (show (0 : ℝ) ≤ 4 / 3 by norm_num)
  simp only [NNReal.coe_one, mul_one] at hmul
  nlinarith

noncomputable def scaleRow (d : ℕ) (b : Fin d → ℝ) : Fin d → ℝ :=
  fun j => b j / (2 * Real.sqrt d)

theorem scaleRow_measurable (d : ℕ) : Measurable (scaleRow d) := by
  unfold scaleRow
  fun_prop

noncomputable def rowLaw (d : ℕ) : Measure (Fin d → ℝ) := (truncatedLaw d).map (scaleRow d)

theorem rowLaw_isProbability (d : ℕ) (hd : 0 < d) : IsProbabilityMeasure (rowLaw d) := by
  letI := truncatedLaw_isProbability d hd
  exact Measure.isProbabilityMeasure_map (scaleRow_measurable d).aemeasurable

noncomputable def coordinateThreshold (d : ℕ) (ell : ℝ) : ℝ := Real.sqrt ell / Real.sqrt d

def rowBadEvent (d : ℕ) (ell : ℝ) : Set (Fin d → ℝ) :=
  {a | ∃ j, coordinateThreshold d ell < |a j|}

theorem rowBadEvent_measurable (d : ℕ) (ell : ℝ) : MeasurableSet (rowBadEvent d ell) := by
  have he : rowBadEvent d ell = ⋃ j : Fin d, {a : Fin d → ℝ | coordinateThreshold d ell < |a j|} := by
    ext a
    simp [rowBadEvent]
  rw [he]
  exact MeasurableSet.iUnion (fun j => measurableSet_lt measurable_const (measurable_pi_apply j).abs)

theorem rowBadEvent_preimage (d : ℕ) (hd : 0 < d) (ell : ℝ) :
    scaleRow d ⁻¹' rowBadEvent d ell = {b : Fin d → ℝ | ∃ j, 2 * Real.sqrt ell < |b j|} := by
  have hs : 0 < Real.sqrt (d : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hd)
  have hden : 0 < 2 * Real.sqrt (d : ℝ) := by positivity
  have he : coordinateThreshold d ell * (2 * Real.sqrt d) = 2 * Real.sqrt ell := by
    unfold coordinateThreshold
    field_simp
  ext b
  change (∃ j, coordinateThreshold d ell < |b j / (2 * Real.sqrt d)|) ↔ _
  simp_rw [abs_div, abs_of_pos hden, lt_div_iff₀ hden, he]
  rfl

theorem row_bad_tail (d : ℕ) (hd : 0 < d) (ell : ℝ) (hell : 0 ≤ ell) :
    (rowLaw d).real (rowBadEvent d ell) ≤ (8 / 3 : ℝ) * d * Real.exp (-2 * ell) := by
  have hc := truncated_bad_tail d hd (2 * Real.sqrt ell) (by positivity)
  have he : -(2 * Real.sqrt ell) ^ 2 / 2 = -2 * ell := by
    rw [mul_pow, Real.sq_sqrt hell]
    ring
  rw [he] at hc
  unfold Measure.real rowLaw
  rw [Measure.map_apply (scaleRow_measurable d) (rowBadEvent_measurable d ell), rowBadEvent_preimage d hd ell]
  exact hc

noncomputable def rowsLaw (d k : ℕ) : Measure (Fin k → Fin d → ℝ) :=
  Measure.pi (fun _ : Fin k => rowLaw d)

theorem rowsLaw_isProbability (d k : ℕ) (hd : 0 < d) : IsProbabilityMeasure (rowsLaw d k) := by
  letI := rowLaw_isProbability d hd
  unfold rowsLaw
  infer_instance

def rowsBadEvent (d k : ℕ) (ell : ℝ) : Set (Fin k → Fin d → ℝ) :=
  {a | ∃ i, a i ∈ rowBadEvent d ell}

theorem rowsBadEvent_measurable (d k : ℕ) (ell : ℝ) : MeasurableSet (rowsBadEvent d k ell) := by
  have he : rowsBadEvent d k ell = ⋃ i : Fin k, {a : Fin k → Fin d → ℝ | a i ∈ rowBadEvent d ell} := by
    ext a
    simp [rowsBadEvent]
  rw [he]
  exact MeasurableSet.iUnion (fun i => (rowBadEvent_measurable d ell).preimage (measurable_pi_apply i))

theorem rows_bad_tail (d k : ℕ) (hd : 0 < d) (ell : ℝ) (hell : 0 ≤ ell) :
    (rowsLaw d k).real (rowsBadEvent d k ell) ≤ (8 / 3 : ℝ) * k * d * Real.exp (-2 * ell) := by
  letI := rowLaw_isProbability d hd
  letI := rowsLaw_isProbability d k hd
  have hcoord : ∀ i : Fin k, (rowsLaw d k).real {a | a i ∈ rowBadEvent d ell} =
      (rowLaw d).real (rowBadEvent d ell) := by
    intro i
    have hp : MeasurePreserving (Function.eval i) (rowsLaw d k) (rowLaw d) :=
      measurePreserving_eval (μ := fun _ : Fin k => rowLaw d) i
    unfold Measure.real
    rw [← hp.map_eq, Measure.map_apply (measurable_pi_apply i) (rowBadEvent_measurable d ell)]
    rfl
  have he : rowsBadEvent d k ell = ⋃ i : Fin k, {a : Fin k → Fin d → ℝ | a i ∈ rowBadEvent d ell} := by
    ext a
    simp [rowsBadEvent]
  rw [he]
  calc
    _ ≤ ∑ i : Fin k, (rowsLaw d k).real {a | a i ∈ rowBadEvent d ell} := measureReal_iUnion_fintype_le _
    _ = ∑ _ : Fin k, (rowLaw d).real (rowBadEvent d ell) := by simp_rw [hcoord]
    _ ≤ ∑ _ : Fin k, (8 / 3 : ℝ) * d * Real.exp (-2 * ell) :=
      Finset.sum_le_sum (fun _ _ => row_bad_tail d hd ell hell)
    _ = _ := by simp; ring

theorem log_ed_pos (d : ℕ) (hd : 0 < d) : 0 < Real.log (Real.exp 1 * (d : ℝ)) := by
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have he : 1 < Real.exp (1 : ℝ) := Real.one_lt_exp_iff.mpr (by norm_num)
  apply Real.log_pos
  nlinarith

theorem exp_log_two (d : ℕ) (hd : 0 < d) :
    Real.exp (-2 * Real.log (Real.exp 1 * d)) = (Real.exp 2 * (d : ℝ) ^ 2)⁻¹ := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hx : 0 < Real.exp 1 * (d : ℝ) := mul_pos (Real.exp_pos _) hdR
  have hn : Real.exp (2 * Real.log (Real.exp 1 * d)) =
      Real.exp (Real.log (Real.exp 1 * d)) ^ 2 := by
    convert Real.exp_nat_mul (Real.log (Real.exp 1 * d)) 2 using 1
    norm_num
  rw [show -2 * Real.log (Real.exp 1 * d) = -(2 * Real.log (Real.exp 1 * d)) by ring,
    Real.exp_neg, hn, Real.exp_log hx, mul_pow]
  congr 2
  rw [← Real.exp_nat_mul]
  norm_num

theorem rows_bad_mass_le (d k : ℕ) (hd : 0 < d) (hk : 16 * k ≤ d) :
    (rowsLaw d k).real (rowsBadEvent d k (Real.log (Real.exp 1 * d))) ≤ (1 / 16 : ℝ) := by
  have hb := rows_bad_tail d k hd (Real.log (Real.exp 1 * d)) (log_ed_pos d hd).le
  rw [exp_log_two d hd] at hb
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hkR : 16 * (k : ℝ) ≤ d := by exact_mod_cast hk
  have he1 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have he2 : (4 : ℝ) ≤ Real.exp 2 := by
    calc
      (4 : ℝ) = (2 : ℝ) ^ 2 := by norm_num
      _ ≤ (Real.exp 1) ^ 2 := by gcongr
      _ = Real.exp 2 := by rw [← Real.exp_nat_mul]; norm_num
  have heprod := mul_le_mul_of_nonneg_right he2 hdR.le
  have halgebra : (8 / 3 : ℝ) * k * d * (Real.exp 2 * (d : ℝ) ^ 2)⁻¹ =
      ((8 / 3 : ℝ) * k) / (Real.exp 2 * d) := by
    field_simp [hdR.ne', Real.exp_ne_zero]
  rw [halgebra] at hb
  have hfrac : ((8 / 3 : ℝ) * k) / (Real.exp 2 * d) ≤ (1 / 16 : ℝ) := by
    apply (div_le_iff₀ (by positivity)).2
    nlinarith
  exact hb.trans hfrac

def rowsGoodEvent (d k : ℕ) : Set (Fin k → Fin d → ℝ) :=
  {a | ∀ i j, |a i j| ≤ coordinateThreshold d (Real.log (Real.exp 1 * d))}

theorem rowsGoodEvent_compl (d k : ℕ) :
    (rowsGoodEvent d k)ᶜ = rowsBadEvent d k (Real.log (Real.exp 1 * d)) := by
  ext a
  simp [rowsGoodEvent, rowsBadEvent, rowBadEvent, not_forall, not_le]

theorem rowsGoodEvent_measurable (d k : ℕ) : MeasurableSet (rowsGoodEvent d k) := by
  have he : rowsGoodEvent d k = (rowsBadEvent d k (Real.log (Real.exp 1 * d)))ᶜ := by
    rw [← rowsGoodEvent_compl, compl_compl]
  rw [he]
  exact (rowsBadEvent_measurable d k _).compl

theorem rows_good_mass (d k : ℕ) (hd : 0 < d) (hk : 16 * k ≤ d) :
    (15 / 16 : ℝ) ≤ (rowsLaw d k).real (rowsGoodEvent d k) := by
  letI := rowsLaw_isProbability d k hd
  have hb := rows_bad_mass_le d k hd hk
  have hsum := measureReal_add_measureReal_compl (μ := rowsLaw d k) (rowsGoodEvent_measurable d k)
  rw [rowsGoodEvent_compl] at hsum
  have huniv : (rowsLaw d k).real Set.univ = 1 := by simp
  rw [huniv] at hsum
  linarith

theorem scaleRow_euclidean_norm_le (d : ℕ) (hd : 0 < d) (b : Fin d → ℝ) (hb : b ∈ truncEvent d) :
    ‖(WithLp.toLp 2 (scaleRow d b) : EuclideanSpace ℝ (Fin d))‖ ≤ 1 := by
  change normSq b ≤ 4 * d at hb
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have he : ‖(WithLp.toLp 2 (scaleRow d b) : EuclideanSpace ℝ (Fin d))‖ ^ 2 =
      normSq b / (4 * d) := by
    rw [EuclideanSpace.real_norm_sq_eq]
    change (∑ i, (b i / (2 * Real.sqrt d)) ^ 2) = (∑ i, (b i) ^ 2) / (4 * d)
    simp_rw [div_pow]
    rw [← Finset.sum_div]
    congr 1
    rw [mul_pow, Real.sq_sqrt hdR.le]
    ring
  have hsq : ‖(WithLp.toLp 2 (scaleRow d b) : EuclideanSpace ℝ (Fin d))‖ ^ 2 ≤ 1 := by
    rw [he]
    apply (div_le_iff₀ (by positivity)).2
    simpa only [one_mul] using hb
  nlinarith [norm_nonneg (WithLp.toLp 2 (scaleRow d b) : EuclideanSpace ℝ (Fin d))]

theorem row_norm_ae (d : ℕ) (hd : 0 < d) :
    ∀ᵐ a ∂rowLaw d, ‖(WithLp.toLp 2 a : EuclideanSpace ℝ (Fin d))‖ ≤ 1 := by
  have hz : truncatedLaw d (truncEvent d)ᶜ = 0 := by
    unfold truncatedLaw
    rw [ProbabilityTheory.cond_apply (truncEvent_measurable d)]
    simp
  apply ae_iff.2
  change (rowLaw d) {a | ¬‖(WithLp.toLp 2 a : EuclideanSpace ℝ (Fin d))‖ ≤ 1} = 0
  unfold rowLaw
  rw [Measure.map_apply (scaleRow_measurable d) (by measurability)]
  apply measure_mono_null (t := (truncEvent d)ᶜ) _ hz
  intro b hb
  exact fun hmem => hb (scaleRow_euclidean_norm_le d hd b hmem)

theorem rows_norm_ae (d k : ℕ) (hd : 0 < d) :
    ∀ᵐ a ∂rowsLaw d k, ∀ i : Fin k, ‖(WithLp.toLp 2 (a i) : EuclideanSpace ℝ (Fin d))‖ ≤ 1 := by
  letI := rowLaw_isProbability d hd
  rw [ae_all_iff]
  intro i
  have hp : MeasurePreserving (Function.eval i) (rowsLaw d k) (rowLaw d) :=
    measurePreserving_eval (μ := fun _ : Fin k => rowLaw d) i
  exact hp.quasiMeasurePreserving.ae (row_norm_ae d hd)

end PaperTruncatedGaussianRows


end
-- END TruncatedGaussianRows.lean

-- BEGIN SourceRowsBridge.lean
section

/-! Concrete truncated-Gaussian source rows satisfy the actual oracle reduction's
public coordinate promise with probability at least 15/16. Euclidean row norms
hold almost surely, so adjoining that source promise loses no mass. Dependencies:
RegionalSourceBridge, HiddenSpikeTails, TruncatedGaussianRows and their dependencies.
No probability-mass or row-normalization assertion is a hypothesis here. -/
noncomputable section
namespace Task003.SourceRowsBridge
open Set MeasureTheory
open Task003.SourcePriorBridge Task003.RegionalSourceBridge
open PaperTruncatedGaussianRows

/-- The concrete Gaussian threshold equals the exact public U_d used by the
normalized penalty simulator, including its NNReal coercion. -/
theorem coordinate_threshold_eq (d : ℕ) (hd : 0 < d) :
    coordinateThreshold d (Real.log (Real.exp 1 * d)) = (coordinateBound d 1 : ℝ) := by
  have he : 0 ≤ Real.log (Real.exp 1 * (d:ℝ)) := (log_ed_pos d hd).le
  calc
    coordinateThreshold d (Real.log (Real.exp 1 * d)) =
        Real.sqrt (Real.log (Real.exp 1 * (d:ℝ)) / (d:ℝ)) := by
      unfold coordinateThreshold
      exact (Real.sqrt_div he (d:ℝ)).symm
    _ = (coordinateBound d 1 : ℝ) := by
      simp only [coordinateBound, one_mul, Real.coe_toNNReal _ (Real.sqrt_nonneg _), CompositionAudit.ell]

theorem goodRows_eq_rowsGoodEvent (d k : ℕ) (hd : 0 < d) :
    @GoodRows (Fin k) d (coordinateBound d 1) = rowsGoodEvent d k := by
  ext rows
  simp only [GoodRows, rowsGoodEvent, mem_setOf_eq, coordinate_threshold_eq d hd]

theorem rows_prior_probability (d k : ℕ) (hd : 0 < d) :
    IsProbabilityMeasure (rowsLaw d k) := rowsLaw_isProbability d k hd

instance rows_prior_probability_of_neZero (d k : ℕ) [NeZero d] :
    IsProbabilityMeasure (rowsLaw d k) :=
  rows_prior_probability d k (Nat.pos_of_ne_zero (NeZero.ne d))

/-- The good-coordinate mass used by the actual source-prior reduction, for the
same concrete row law and the same public bound as the manuscript normalization. -/
theorem rows_good_mass (d k : ℕ) (hd : 0 < d) (hk : 16*k ≤ d) :
    (15/16 : ℝ) ≤ (rowsLaw d k).real (@GoodRows (Fin k) d (coordinateBound d 1)) := by
  rw [goodRows_eq_rowsGoodEvent d k hd]
  exact PaperTruncatedGaussianRows.rows_good_mass d k hd hk

def NormRows (d k : ℕ) : Set (Fin k → Fin d → ℝ) :=
  {rows | ∀ i : Fin k, ‖(WithLp.toLp 2 (rows i) : EuclideanSpace ℝ (Fin d))‖ ≤ 1}

def GoodSourceRows (d k : ℕ) : Set (Fin k → Fin d → ℝ) :=
  @GoodRows (Fin k) d (coordinateBound d 1) ∩ NormRows d k

theorem normRows_measurable (d k : ℕ) : MeasurableSet (NormRows d k) := by
  have he : NormRows d k = ⋂ i : Fin k,
      {rows : Fin k → Fin d → ℝ | ‖(WithLp.toLp 2 (rows i) : EuclideanSpace ℝ (Fin d))‖ ≤ 1} := by
    ext rows
    simp [NormRows]
  rw [he]
  apply MeasurableSet.iInter
  intro i
  exact measurableSet_le
    ((PiLp.continuous_toLp 2 (fun _ : Fin d => ℝ)).norm.measurable.comp (measurable_pi_apply i)) measurable_const

theorem goodSourceRows_measurable (d k : ℕ) : MeasurableSet (GoodSourceRows d k) :=
  (goodRows_measurable d (coordinateBound d 1)).inter (normRows_measurable d k)

theorem normRows_ae (d k : ℕ) (hd : 0 < d) : ∀ᵐ rows ∂rowsLaw d k, rows ∈ NormRows d k :=
  rows_norm_ae d k hd

theorem goodSourceRows_measure_eq (d k : ℕ) (hd : 0 < d) :
    (rowsLaw d k) (GoodSourceRows d k) =
      (rowsLaw d k) (@GoodRows (Fin k) d (coordinateBound d 1)) := by
  unfold GoodSourceRows
  rw [Set.inter_comm]
  exact Measure.measure_inter_eq_of_ae (normRows_ae d k hd)

/-- The full coordinate-and-Euclidean-norm promise has the same 15/16 mass;
normalization is proved for the actual conditional Gaussian row construction. -/
theorem rows_good_source_mass (d k : ℕ) (hd : 0 < d) (hk : 16*k ≤ d) :
    (15/16 : ℝ) ≤ (rowsLaw d k).real (GoodSourceRows d k) := by
  change (15/16 : ℝ) ≤ ((rowsLaw d k) (GoodSourceRows d k)).toReal
  rw [goodSourceRows_measure_eq d k hd]
  exact rows_good_mass d k hd hk

end Task003.SourceRowsBridge

end
end
-- END SourceRowsBridge.lean

-- BEGIN ZhangInterface.lean
section

/- Dependencies: SourceRowsBridge, RegionalSourceBridge.
The only unproved input here is the manuscript's named external deterministic-prior
Euclidean value-oracle hardness theorem, on its specified fixed truncated
Gaussian row prior. The target oracle simulation, conditioning, coordinate
probabilities, integer selection and accuracy reduction are proved separately. -/
namespace Task003.ZhangInterface
open MeasureTheory Task003.OracleModel Task003.OracleSimulation
open Task003.StrictSourcePrior Task003.RegionalSourceBridge Task003.SourcePriorBridge
open PaperTruncatedGaussianRows PaperGeometry

/-- A constant-shrunk, normalized statement of External Theorem Z. It refers
to its concrete Gaussian row prior and strict-success event, not the desired
target-space query lower bound. Its truth remains an explicit literature input. -/
def ZhangPrinciple (Dsource : ℕ) (κ δ cp : ℝ) : Prop :=
  ∀ (d : ℕ), Dsource≤d → ∀ (k : ℕ) (hk : 1≤k), k≤⌊κ*(d:ℝ)⌋₊ →
    letI : Nonempty (Fin k) := ⟨⟨0, by omega⟩⟩
    ∀ N : ℕ, 1≤N → (N:ℝ)<cp*(d:ℝ)*(k:ℝ)/Real.log (Real.exp 1*(k:ℝ)) →
      ∀ b : SourcePolicy d Unit,
      (∀ rows : Rows (Fin k) d,
        b.queriesUsed (sourceSupport rows) N 0 ((),Fin.elim0)≤N) →
      (rowsLaw d k).real {rows | ()∈strictSourceSuccessEvent b (sourceSupport rows) N
        (sourceAccuracy 1 δ k)} ≤ (1/4:ℝ)

theorem regional_of_zhang {Dsource : ℕ} (hD : 0<Dsource)
    (κ δ cp : ℝ) (hκ : 0<κ) (hκmax : κ≤1/16)
    (hδ : 0<δ) (hδmax : δ≤1) (hcp : 0<cp)
    (hZ : ZhangPrinciple Dsource κ δ cp) :
    ∃ (D : ℕ) (c : ℝ), Dsource≤D ∧ 0<D ∧ 0<c ∧
      ∀ (d : ℕ), D≤d → ∀ (α : ℝ), 0<α →
        α≤δ/Real.sqrt (CompositionAudit.ell (d:ℝ)) →
        ∀ m : ℕ, AdmissibleBudget d m 1 1 α →
          c*CompositionAudit.q (d:ℝ) α /
            (CompositionAudit.ell (d:ℝ)*Real.log (Real.exp 1*CompositionAudit.M (d:ℝ) α))≤(m:ℝ) := by
  apply eventual_regional_from_strict_source_priors Dsource κ δ cp 1
    hκ (by linarith) hδ hδmax hcp (by norm_num)
  intro d hd k hk hkfloor
  letI : Nonempty (Fin k) := ⟨⟨0,by omega⟩⟩
  have hdpos : 0<d := lt_of_lt_of_le hD hd
  have hκd : 0≤κ*(d:ℝ) := by positivity
  have hkr : (k:ℝ)≤κ*(d:ℝ) :=
    (Nat.cast_le.mpr hkfloor).trans (Nat.floor_le hκd)
  have hkd : 16*k≤d := by
    have hd0 : (0:ℝ)≤d := by positivity
    have hc := mul_le_mul_of_nonneg_right hκmax hd0
    have hkR : (16:ℝ)*(k:ℝ)≤(d:ℝ) := by linarith
    exact_mod_cast hkR
  refine ⟨rowsLaw d k,Task003.SourceRowsBridge.rows_prior_probability d k hdpos,
    Task003.SourceRowsBridge.rows_good_mass d k hdpos hkd,?_⟩
  exact hZ d hd k hk hkfloor

end Task003.ZhangInterface


end
-- END ZhangInterface.lean

-- BEGIN SpikeThreshold.lean
section

/- Dependencies: Composition, BoundsArithmetic. A fixed explicit dimension
threshold absorbs the additive cost without a dimension-dependent constant. -/
namespace Task003.SpikeThreshold
open CompositionAudit

/-- A deliberately loose threshold; the theorem only requires one fixed D. -/
def absorptionDimension : ℕ := 4294967296

theorem absorption_after_dimension {d : ℕ} (hd : absorptionDimension≤d) :
    0<ell (d:ℝ) ∧ 16384*ell (d:ℝ)≤(d:ℝ) := by
  have hdR : (4294967296:ℝ)≤(d:ℝ) := by exact_mod_cast hd
  have hdpos : (0:ℝ)<d := by linarith
  have hspos : 0<Real.sqrt (d:ℝ) := Real.sqrt_pos.mpr hdpos
  have hs : (65536:ℝ)≤Real.sqrt (d:ℝ) := by
    nlinarith [Real.sq_sqrt hdpos.le]
  have hlog : Real.log (d:ℝ)≤2*Real.sqrt (d:ℝ)-2 := by
    have hl := Real.log_le_sub_one_of_pos hspos
    have he : Real.log (d:ℝ)=2*Real.log (Real.sqrt (d:ℝ)) := by
      rw [← Real.sq_sqrt hdpos.le,Real.log_pow]
      norm_num
    rw [he]
    linarith
  have hell : ell (d:ℝ)=1+Real.log (d:ℝ) := by
    unfold ell
    rw [Real.log_mul (Real.exp_ne_zero _) hdpos.ne',Real.log_exp]
  have hlogpos : 0≤Real.log (d:ℝ) := Real.log_nonneg (by linarith)
  constructor
  · rw [hell]; linarith
  · have hm : (32768:ℝ)*Real.sqrt (d:ℝ)≤d := by
      nlinarith [Real.sq_sqrt hdpos.le,
        mul_nonneg hspos.le (show 0≤Real.sqrt (d:ℝ)-32768 by linarith)]
    rw [hell]
    linarith

theorem spike_lower_after_cost {d m : ℕ} (hd : absorptionDimension≤d)
    (hcost : (d:ℝ)≤(2*(m:ℝ)+2)*(4096*ell (d:ℝ))) :
    (1/16384:ℝ)*(d:ℝ)/ell (d:ℝ)≤(m:ℝ) := by
  obtain ⟨hell,hthreshold⟩ := absorption_after_dimension hd
  have hb := Task003Audit.BoundsArithmetic.observation_cost_to_query_lower_bound
    (d:ℝ) (m:ℝ) (ell (d:ℝ)) hell hcost
  have hc := Task003Audit.BoundsArithmetic.query_lower_bound_after_threshold
    (d:ℝ) (m:ℝ) (ell (d:ℝ)) hell hthreshold hb
  convert hc using 1 <;> ring

end Task003.SpikeThreshold


end
-- END SpikeThreshold.lean

-- BEGIN RandomizedPolicyRecovery.lean
section

/- Dependencies: PolicyRecovery, OracleJointMeasurability, FiniteFamilyProduct.
The private probability law is fixed independently of every hidden index and
source vector. Real Tonelli averaging extends the actual fixed-seed bound. -/
namespace PaperRandomizedPolicyRecovery
open MeasureTheory Task003.OracleModel PaperPolicyGaussianBridge
open PaperGaussianOracleBridge PaperPolicyRecovery PaperFiniteFamilyProduct
open scoped RealInnerProductSpace

 theorem randomized_policy_gaussian_recovery_bound
    {d : ℕ} (hd : 0<d) {R : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    (a : Policy d R Ω) (ν : Measure Ω) [IsProbabilityMeasure ν]
    (σ δ : ℝ) (hσ : σ ≠ 0) (cap : ℕ)
    (estimate : Point d → Fin d) (he : Measurable estimate) :
    (∑ i, ((sourcePrior σ (δ • EuclideanSpace.single i (1:ℝ))).prod ν).real
      {p | estimate (run a (fun x => ⟪pointVector x,p.1⟫) cap p.2)=i})/d ≤
      1/d+Real.sqrt ((cap:ℝ)*(δ/σ)^2/(4*d)) := by
  let μ : Fin d → Measure (EuclideanSpace ℝ (Fin d)) :=
    fun i => sourcePrior σ (δ • EuclideanSpace.single i (1:ℝ))
  letI : ∀ i,IsProbabilityMeasure (μ i) := fun i => sourcePrior_isProbability _ _
  let S : Fin d → Set (EuclideanSpace ℝ (Fin d)×Ω) :=
    fun i => {p | estimate (run a (fun x => ⟪pointVector x,p.1⟫) cap p.2)=i}
  have hf : Measurable (fun p : EuclideanSpace ℝ (Fin d)×Point d => ⟪pointVector p.2,p.1⟫) :=
    ((pointVector_measurable d).comp measurable_snd).inner measurable_fst
  have hr := Task003.OracleJointMeasurability.run_joint_measurable a _ hf cap
  have hS : ∀ i,MeasurableSet (S i) :=
    fun i => measurableSet_eq_fun (he.comp hr) measurable_const
  apply finite_family_product_event_average_le hd μ ν S hS _ (by positivity)
  intro ω
  exact policy_gaussian_recovery_bound hd a ω σ δ hσ cap estimate he

 theorem randomized_policy_gaussian_observation_lower_bound
    {d : ℕ} (hd : 6≤d) {R : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    (a : Policy d R Ω) (ν : Measure Ω) [IsProbabilityMeasure ν]
    (σ δ : ℝ) (hσ : σ ≠ 0) (cap : ℕ)
    (estimate : Point d → Fin d) (he : Measurable estimate)
    (hrecovery : (2/3:ℝ)<
      (∑ i,((sourcePrior σ (δ • EuclideanSpace.single i (1:ℝ))).prod ν).real
        {p | estimate (run a (fun x => ⟪pointVector x,p.1⟫) cap p.2)=i})/d) :
    (d:ℝ)≤(cap:ℝ)*(δ/σ)^2 := by
  have hb := randomized_policy_gaussian_recovery_bound (by omega) a ν σ δ hσ cap estimate he
  have hdR : (6:ℝ)≤d := by exact_mod_cast hd
  have hbase : 1/(d:ℝ)≤1/6 := one_div_le_one_div_of_le (by norm_num) hdR
  have hroot : (1/2:ℝ)<Real.sqrt ((cap:ℝ)*(δ/σ)^2/(4*d)) := by linarith
  have hsquare := Real.sq_sqrt (show 0≤(cap:ℝ)*(δ/σ)^2/(4*d) by positivity)
  have hratio : (1/4:ℝ)<(cap:ℝ)*(δ/σ)^2/(4*d) := by
    nlinarith [Real.sqrt_nonneg ((cap:ℝ)*(δ/σ)^2/(4*d))]
  have hm := (lt_div_iff₀ (show (0:ℝ)<4*d by positivity)).mp hratio
  nlinarith

end PaperRandomizedPolicyRecovery


end
-- END RandomizedPolicyRecovery.lean

-- BEGIN HiddenSpikeGaussianBridge.lean
section

namespace PaperHiddenSpikeGaussianBridge

open MeasureTheory ProbabilityTheory Set PaperHiddenSpikeTails PaperHiddenSpikeGeometry PaperGeometry

noncomputable def varianceOfScale (σ : ℝ) : NNReal := ⟨σ ^ 2, sq_nonneg σ⟩

theorem scaled_coordinates_map (d : ℕ) (σ : ℝ) :
    (noiseLaw d 1).map (fun b : Fin d → ℝ => fun j => σ * b j) =
      noiseLaw d (varianceOfScale σ) := by
  have hp : ∀ j : Fin d, MeasurePreserving (fun x : ℝ => σ * x)
      (gaussianReal 0 1) (gaussianReal 0 (varianceOfScale σ)) := by
    intro j
    refine ⟨by fun_prop, ?_⟩
    convert! gaussianReal_map_const_mul (μ := 0) (v := 1) σ using 1
    simp [varianceOfScale]
    congr 1
  exact (measurePreserving_pi (fun _ : Fin d => gaussianReal 0 1)
    (fun _ : Fin d => gaussianReal 0 (varianceOfScale σ)) hp).map_eq

theorem sourcePrior_eq_noiseLaw {d : ℕ} (σ : ℝ) (θ : EuclideanSpace ℝ (Fin d)) :
    PaperGaussianOracleBridge.sourcePrior σ θ =
      (noiseLaw d (varianceOfScale σ)).map (fun b : Fin d → ℝ => WithLp.toLp 2 b + θ) := by
  rw [PaperGaussianOracleBridge.sourcePrior_eq_independent_coordinate_image]
  rw [← scaled_coordinates_map d σ, Measure.map_map (by fun_prop) (by fun_prop)]
  rfl

def sourceGoodEvent {d : ℕ} (α : ℝ) (θ : EuclideanSpace ℝ (Fin d)) : Set (EuclideanSpace ℝ (Fin d)) :=
  {g | ∀ j, |g j - θ j| ≤ α / 4}

theorem sourceGoodEvent_measurable {d : ℕ} (α : ℝ) (θ : EuclideanSpace ℝ (Fin d)) :
    MeasurableSet (sourceGoodEvent α θ) := by
  have he : sourceGoodEvent α θ = ⋂ j : Fin d, {g : EuclideanSpace ℝ (Fin d) | |g j - θ j| ≤ α / 4} := by
    ext g
    simp [sourceGoodEvent]
  rw [he]
  exact MeasurableSet.iInter (fun j => measurableSet_le
    ((PiLp.continuous_apply 2 _ j).sub continuous_const).abs.measurable measurable_const)

theorem sourcePrior_good_mass {d : ℕ} (hd : 0 < d) (α : ℝ) (hα : 0 < α)
    (θ : EuclideanSpace ℝ (Fin d)) :
    (63 / 64 : ℝ) ≤ (PaperGaussianOracleBridge.sourcePrior
      (spikeSigma α (Real.log (Real.exp 1 * d))) θ).real (sourceGoodEvent α θ) := by
  rw [sourcePrior_eq_noiseLaw]
  have he : (fun b : Fin d → ℝ => (WithLp.toLp 2 b : EuclideanSpace ℝ (Fin d)) + θ) ⁻¹'
      sourceGoodEvent α θ = goodEvent d α := by
    ext b
    simp [sourceGoodEvent, goodEvent]
  unfold Measure.real
  rw [Measure.map_apply (by fun_prop) (sourceGoodEvent_measurable α θ), he]
  exact hidden_good_mass d hd α hα

theorem sourcePrior_bad_mass {d : ℕ} (hd : 0 < d) (α : ℝ) (hα : 0 < α)
    (θ : EuclideanSpace ℝ (Fin d)) :
    (PaperGaussianOracleBridge.sourcePrior (spikeSigma α (Real.log (Real.exp 1 * d))) θ).real
      (sourceGoodEvent α θ)ᶜ ≤ 2 / (Real.exp 8 * (d : ℝ) ^ 7) := by
  rw [sourcePrior_eq_noiseLaw]
  have he : (fun b : Fin d → ℝ => (WithLp.toLp 2 b : EuclideanSpace ℝ (Fin d)) + θ) ⁻¹'
      (sourceGoodEvent α θ)ᶜ = {b : Fin d → ℝ | ∃ j, α / 4 < |b j|} := by
    ext b
    simp [sourceGoodEvent, not_forall, not_le]
  unfold Measure.real
  rw [Measure.map_apply (by fun_prop) (sourceGoodEvent_measurable α θ).compl, he]
  exact hidden_bad_tail d hd α hα

noncomputable def spikeMean {d : ℕ} (α : ℝ) (I : Fin d) : EuclideanSpace ℝ (Fin d) :=
  (4 * α) • EuclideanSpace.single I (1 : ℝ)

noncomputable def centeredCoordinates {d : ℕ} (g θ : EuclideanSpace ℝ (Fin d)) : Fin d → ℝ :=
  fun j => g j - θ j

theorem actual_coefficients_spike {d : ℕ} (g : EuclideanSpace ℝ (Fin d)) (α : ℝ) (I : Fin d) :
    spikeCoeff (centeredCoordinates g (spikeMean α I)) α I = WithLp.ofLp g := by
  funext j
  by_cases hj : j = I
  · subst j
    simp [spikeCoeff, centeredCoordinates, spikeMean]
  · simp [spikeCoeff, centeredCoordinates, spikeMean, hj]

theorem actual_source_success_recovers {d : ℕ} (hd : 0 < d) (g : EuclideanSpace ℝ (Fin d))
    (α : ℝ) (hα : 0 < α) (I : Fin d) (hgood : g ∈ sourceGoodEvent α (spikeMean α I))
    (x : L1Space (Fin d)) (hx : ‖x‖ ≤ 1)
    (hsuccess : rowValue (WithLp.ofLp g) x + g I ≤ α) : argmaxAbs d hd x = I := by
  have hb : ∀ j, |centeredCoordinates g (spikeMean α I) j| ≤ α / 4 := hgood
  apply success_recovers_index hd (centeredCoordinates g (spikeMean α I)) α hα hb I x hx
  simpa only [spikeValue, actual_coefficients_spike] using hsuccess

theorem actual_source_admissible {d : ℕ} (g : EuclideanSpace ℝ (Fin d))
    (α : ℝ) (hα : 0 < α) (hsmall : α ≤ 1 / 8) (I : Fin d)
    (hgood : g ∈ sourceGoodEvent α (spikeMean α I)) :
    LipschitzWith 1 (rowValue (WithLp.ofLp g)) ∧
      ConvexOn ℝ Set.univ (rowValue (WithLp.ofLp g)) := by
  have hb : ∀ j, |centeredCoordinates g (spikeMean α I) j| ≤ α / 4 := hgood
  have he : spikeValue (centeredCoordinates g (spikeMean α I)) α I = rowValue (WithLp.ofLp g) := by
    funext x
    unfold spikeValue
    rw [actual_coefficients_spike]
  rw [← he]
  exact ⟨spikeValue_lipschitz _ α hα hsmall hb I, spikeValue_convex _ α I⟩

theorem actual_source_minimum {d : ℕ} (g : EuclideanSpace ℝ (Fin d))
    (α : ℝ) (hα : 0 < α) (I : Fin d) (hgood : g ∈ sourceGoodEvent α (spikeMean α I)) :
    ‖negativeVertex I‖ ≤ 1 ∧ rowValue (WithLp.ofLp g) (negativeVertex I) = -g I ∧
      ∀ x : L1Space (Fin d), ‖x‖ ≤ 1 → -g I ≤ rowValue (WithLp.ofLp g) x := by
  have hb : ∀ j, |centeredCoordinates g (spikeMean α I) j| ≤ α / 4 := hgood
  have hm := spikeValue_minimum (centeredCoordinates g (spikeMean α I)) α hα hb I
  simpa only [spikeValue, actual_coefficients_spike] using hm

end PaperHiddenSpikeGaussianBridge


end
-- END HiddenSpikeGaussianBridge.lean

-- BEGIN HistoryPolicyTools.lean
section
namespace PaperHistoryPolicyTools

open MeasureTheory Task003.OracleModel PaperGaussianKL PaperPolicyGaussianBridge

noncomputable def vectorHistory : (t : ℕ) → (Fin t → ℝ) → History t
  | 0 => fun _ => ()
  | t + 1 => fun v => (vectorHistory t (Fin.init v), v (Fin.last t))

theorem vectorHistory_measurable (t : ℕ) : Measurable (vectorHistory t) := by
  induction t with
  | zero => exact measurable_const
  | succ t ih =>
    exact (ih.comp (measurable_pi_lambda _ (fun j => measurable_pi_apply j.castSucc))).prodMk
      (measurable_pi_apply (Fin.last t))

theorem vectorHistory_historyVector (t : ℕ) (h : History t) :
    vectorHistory t (historyVector t h) = h := by
  induction t with
  | zero => cases h; rfl
  | succ t ih =>
    simp only [vectorHistory, historyVector, Fin.init_snoc, Fin.snoc_last, ih]
    cases h
    rfl

theorem historyVector_vectorHistory (t : ℕ) (v : Fin t → ℝ) :
    historyVector t (vectorHistory t v) = v := by
  induction t with
  | zero => exact Subsingleton.elim _ _
  | succ t ih =>
    simp only [vectorHistory, historyVector, ih, Fin.snoc_init_self]

noncomputable def castHistory {m n : ℕ} (h : m = n) : History m → History n := h ▸ id

theorem castHistory_measurable {m n : ℕ} (h : m = n) : Measurable (castHistory h) := by
  subst n
  exact measurable_id

theorem castHistory_self {n : ℕ} (h : n = n) : castHistory h = id := by
  cases h
  rfl

noncomputable def takeHistory (m : ℕ) : (k : ℕ) → History (m + k) → History m
  | 0 => id
  | k + 1 => fun h => takeHistory m k h.1

noncomputable def dropHistory (m : ℕ) : (k : ℕ) → History (m + k) → History k
  | 0 => fun _ => ()
  | k + 1 => fun h => (dropHistory m k h.1, h.2)

theorem takeHistory_measurable (m k : ℕ) : Measurable (takeHistory m k) := by
  induction k with
  | zero => exact measurable_id
  | succ k ih => exact ih.comp measurable_fst

theorem dropHistory_measurable (m k : ℕ) : Measurable (dropHistory m k) := by
  induction k with
  | zero => exact measurable_const
  | succ k ih => exact (ih.comp measurable_fst).prodMk measurable_snd

/-- A generic full scalar reply history. The oracle is fixed throughout. -/
noncomputable def replyHistory {d Ω} (q : (t : ℕ) → Ω × History t → Point d)
    (f : Point d → ℝ) (ω : Ω) : (t : ℕ) → History t
  | 0 => ()
  | t + 1 => let h := replyHistory q f ω t; (h, f (q t (ω, h)))

theorem take_replyHistory {d Ω} (q : (t : ℕ) → Ω × History t → Point d)
    (f : Point d → ℝ) (ω : Ω) (m k : ℕ) :
    takeHistory m k (replyHistory q f ω (m + k)) = replyHistory q f ω m := by
  induction k with
  | zero => rfl
  | succ k ih => exact ih

/-- A fixed-horizon public query/output strategy compiles to the original
Policy type, with exactly one query per time step and no hidden objective input. -/
noncomputable def fixedPolicy {d R Ω} [MeasurableSpace Ω]
    (q : (t : ℕ) → Ω × History t → Point d) (hq : ∀ t, Measurable (q t))
    (out : (t : ℕ) → Ω × History t → Point d) (ho : ∀ t, Measurable (out t))
    (hfeas : ∀ t p, Feasible R (out t p)) : Policy d R Ω where
  query := fun t h => q t (h.1, vectorHistory t h.2)
  query_measurable t := (hq t).comp (measurable_fst.prodMk ((vectorHistory_measurable t).comp measurable_snd))
  stop := fun _ _ => false
  stop_measurable _ := measurable_const
  output := fun t h => out t (h.1, vectorHistory t h.2)
  output_measurable t := (ho t).comp (measurable_fst.prodMk ((vectorHistory_measurable t).comp measurable_snd))
  output_feasible t h := hfeas t _

noncomputable def followOutput {d Ω}
    (q : (t : ℕ) → Ω × History t → Point d)
    (out : (t : ℕ) → Ω × History t → Point d)
    (f : Point d → ℝ) (ω : Ω) : (fuel t : ℕ) → History t → Point d
  | 0, t, h => out t (ω, h)
  | fuel + 1, t, h => followOutput q out f ω fuel (t + 1) (h, f (q t (ω, h)))

theorem execute_fixedPolicy {d R Ω} [MeasurableSpace Ω]
    (q : (t : ℕ) → Ω × History t → Point d) (hq : ∀ t, Measurable (q t))
    (out : (t : ℕ) → Ω × History t → Point d) (ho : ∀ t, Measurable (out t))
    (hfeas : ∀ t p, Feasible R (out t p)) (f : Point d → ℝ) (ω : Ω)
    (fuel t : ℕ) (h : History t) :
    execute (fixedPolicy q hq out ho hfeas) f fuel t (ω, historyVector t h) =
      followOutput q out f ω fuel t h := by
  induction fuel generalizing t with
  | zero => simp only [execute, fixedPolicy, vectorHistory_historyVector, followOutput]
  | succ fuel ih =>
    simp only [execute, fixedPolicy, Bool.false_eq_true, ↓reduceIte]
    simp only [nextHistory, fixedPolicy, vectorHistory_historyVector]
    exact ih (t + 1) (h, f (q t (ω, h)))

theorem followOutput_replyHistory {d Ω}
    (q : (t : ℕ) → Ω × History t → Point d)
    (out : (t : ℕ) → Ω × History t → Point d)
    (f : Point d → ℝ) (ω : Ω) (fuel t : ℕ) :
    followOutput q out f ω fuel t (replyHistory q f ω t) =
      out (t + fuel) (ω, replyHistory q f ω (t + fuel)) := by
  induction fuel generalizing t with
  | zero => rfl
  | succ fuel ih =>
    change followOutput q out f ω fuel (t + 1) (replyHistory q f ω (t + 1)) = _
    rw [ih]
    have hn : t + 1 + fuel = t + (fuel + 1) := by omega
    rw [hn]

theorem run_fixedPolicy {d R Ω} [MeasurableSpace Ω]
    (q : (t : ℕ) → Ω × History t → Point d) (hq : ∀ t, Measurable (q t))
    (out : (t : ℕ) → Ω × History t → Point d) (ho : ∀ t, Measurable (out t))
    (hfeas : ∀ t p, Feasible R (out t p)) (f : Point d → ℝ) (ω : Ω) (cap : ℕ) :
    run (fixedPolicy q hq out ho hfeas) f cap ω = out cap (ω, replyHistory q f ω cap) := by
  have he := execute_fixedPolicy q hq out ho hfeas f ω cap 0 ()
  have hp := followOutput_replyHistory q out f ω cap 0
  rw [Nat.zero_add] at hp
  simpa only [historyVector, run] using he.trans hp

theorem queriesUsed_fixedPolicy {d R Ω} [MeasurableSpace Ω]
    (q : (t : ℕ) → Ω × History t → Point d) (hq : ∀ t, Measurable (q t))
    (out : (t : ℕ) → Ω × History t → Point d) (ho : ∀ t, Measurable (out t))
    (hfeas : ∀ t p, Feasible R (out t p)) (f : Point d → ℝ)
    (fuel t : ℕ) (h : Ω × (Fin t → ℝ)) :
    queriesUsed (fixedPolicy q hq out ho hfeas) f fuel t h = fuel := by
  induction fuel generalizing t with
  | zero => rfl
  | succ fuel ih =>
    change 1 + queriesUsed (fixedPolicy q hq out ho hfeas) f fuel (t + 1)
      (nextHistory (fixedPolicy q hq out ho hfeas) f t h) = fuel + 1
    rw [ih]
    omega

end PaperHistoryPolicyTools


end
-- END HistoryPolicyTools.lean

-- BEGIN SequentialQueryBlocks.lean
section
/-! Exact scalar reply slices for two sequential public-query blocks. The
objective and private seed are fixed throughout; query maps outside the two
blocks are unrestricted. No measurability assumption is needed for these
pathwise identities. -/
namespace PaperSequentialQueryBlocks
open Task003.OracleModel PaperGaussianKL PaperHistoryPolicyTools

variable {d : ℕ} {Seed : Type*}

theorem firstBlockReply
    (q q1 : (n : ℕ) → Seed × History n → Point d) (m : ℕ)
    (hfirst : ∀ n < m, ∀ seed : Seed, ∀ h : History n, q n (seed,h) = q1 n (seed,h))
    (f : Point d → ℝ) (seed : Seed) (n : ℕ) (hn : n ≤ m) :
    replyHistory q f seed n = replyHistory q1 f seed n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [replyHistory]
    rw [ih (by omega), hfirst n (by omega) seed (replyHistory q1 f seed n)]

theorem secondBlockReply
    (q q2 : (n : ℕ) → Seed × History n → Point d) (m : ℕ)
    (hsecond : ∀ k < m, ∀ seed : Seed, ∀ h : History (m+k),
      q (m+k) (seed,h) = q2 k (seed,dropHistory m k h))
    (f : Point d → ℝ) (seed : Seed) (k : ℕ) (hk : k ≤ m) :
    dropHistory m k (replyHistory q f seed (m+k)) = replyHistory q2 f seed k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change (dropHistory m k (replyHistory q f seed (m+k)),
      f (q (m+k) (seed,replyHistory q f seed (m+k)))) =
      (replyHistory q2 f seed k, f (q2 k (seed,replyHistory q2 f seed k)))
    rw [hsecond k (by omega) seed (replyHistory q f seed (m+k)), ih (by omega)]

theorem firstBlockAtEnd
    (q q1 : (n : ℕ) → Seed × History n → Point d) (m : ℕ)
    (hfirst : ∀ n < m, ∀ seed : Seed, ∀ h : History n, q n (seed,h) = q1 n (seed,h))
    (f : Point d → ℝ) (seed : Seed) :
    takeHistory m m (replyHistory q f seed (m+m)) = replyHistory q1 f seed m := by
  rw [take_replyHistory]
  exact firstBlockReply q q1 m hfirst f seed m (le_refl m)

theorem secondBlockAtEnd
    (q q2 : (n : ℕ) → Seed × History n → Point d) (m : ℕ)
    (hsecond : ∀ k < m, ∀ seed : Seed, ∀ h : History (m+k),
      q (m+k) (seed,h) = q2 k (seed,dropHistory m k h))
    (f : Point d → ℝ) (seed : Seed) :
    dropHistory m m (replyHistory q f seed (m+m)) = replyHistory q2 f seed m :=
  secondBlockReply q q2 m hsecond f seed m (le_refl m)

end PaperSequentialQueryBlocks


end
-- END SequentialQueryBlocks.lean

-- BEGIN HistoryCastTools.lean
section
/-! Pure dependent transport for finite scalar histories and sequential slices.
Theorems use only equality elimination; no probability assumptions are needed. -/
namespace PaperHistoryCastTools
open PaperGaussianKL PaperHistoryPolicyTools

theorem castHistory_heq {m n : ℕ} (e : m=n) (h : History m) :
    HEq (castHistory e h) h := by
  cases e
  rfl

theorem castHistory_trans {m n r : ℕ} (e : m=n) (f : n=r) (h : History m) :
    castHistory f (castHistory e h) = castHistory (e.trans f) h := by
  cases e
  cases f
  rfl

theorem cast_dropHistory {m k l : ℕ} (e : k=l) (h : History (m+k)) :
    castHistory e (dropHistory m k h) =
      dropHistory m l (castHistory (congrArg (fun j => m+j) e) h) := by
  cases e
  rfl

/-- Exact normalization of a middle-block slice at a time written as m+k.
This is the unfolded middleHistory adapter used by sequential two-run policies. -/
theorem dropHistory_add_cast (m k : ℕ) (hmn : m ≤ m+k) (h : History (m+k)) :
    castHistory (Nat.add_sub_cancel_left m k)
      (dropHistory m ((m+k)-m) (castHistory (Nat.add_sub_of_le hmn).symm h)) =
        dropHistory m k h := by
  rw [cast_dropHistory, castHistory_trans]
  simp only [castHistory_self, id_eq]

/-- A public dependent query or output map commutes with transport of its
finite-history length. This directly discharges phase-index adapter goals. -/
theorem apply_castHistory {Seed Result : Type*}
    (q : (n : ℕ) → Seed × History n → Result)
    {m n : ℕ} (e : m=n) (seed : Seed) (h : History m) :
    q n (seed,castHistory e h) = q m (seed,h) := by
  cases e
  rfl

theorem apply_history_cast {Result : Type*} (F : (n : ℕ) → History n → Result)
    {m n : ℕ} (e : m=n) (h : History m) : F n (castHistory e h) = F m h := by
  cases e
  rfl

/-- Direct phase adapter, including both the query-length and slice transports. -/
theorem apply_middleHistory_add {Result : Type*} (F : (n : ℕ) → History n → Result)
    (m k : ℕ) (hmn : m ≤ m+k) (h : History (m+k)) :
    F ((m+k)-m) (dropHistory m ((m+k)-m) (castHistory (Nat.add_sub_of_le hmn).symm h)) =
      F k (dropHistory m k h) := by
  calc
    _ = F k (castHistory (Nat.add_sub_cancel_left m k)
        (dropHistory m ((m+k)-m) (castHistory (Nat.add_sub_of_le hmn).symm h))) :=
      (apply_history_cast F (Nat.add_sub_cancel_left m k) _).symm
    _ = _ := by rw [dropHistory_add_cast m k hmn h]

end PaperHistoryCastTools


end
-- END HistoryCastTools.lean

-- BEGIN TwoRunRecovery.lean
section
namespace PaperTwoRunRecovery

open MeasureTheory Task003.OracleModel PaperGaussianKL PaperPolicyGaussianBridge PaperHistoryPolicyTools
  PaperHiddenSpikeGeometry PaperSequentialQueryBlocks

/-- Joint public replay-state measurability in the original private seed
and all scalar replies. -/
theorem frozen_joint_measurable {d Ω} [MeasurableSpace Ω]
    (a : Policy d 1 Ω) (t : ℕ) :
    Measurable (fun p : Ω × History t => frozen a p.1 t p.2) := by
  induction t with
  | zero => exact measurable_const
  | succ t ih =>
    have hs : Measurable (fun p : Ω × History (t + 1) => frozen a p.1 t p.2.1) :=
      ih.comp (measurable_fst.prodMk measurable_snd.fst)
    have hp : Measurable (fun p : Ω × History (t + 1) => (p.1, historyVector t p.2.1)) :=
      measurable_fst.prodMk ((historyVector_measurable t).comp measurable_snd.fst)
    exact Measurable.ite (measurableSet_eq_fun hs.fst measurable_const) hs
      (Measurable.ite (measurableSet_eq_fun ((a.stop_measurable t).comp hp) measurable_const)
        (measurable_const.prodMk ((a.output_measurable t).comp hp)) measurable_const)

noncomputable def paddedPointQuery {d Ω} [MeasurableSpace Ω]
    (a : Policy d 1 Ω) (t : ℕ) (p : Ω × History t) : Point d :=
  if (frozen a p.1 t p.2).1 then 0 else
    if a.stop t (p.1, historyVector t p.2) then 0 else a.query t (p.1, historyVector t p.2)

noncomputable def paddedPointOutput {d Ω} [MeasurableSpace Ω]
    (a : Policy d 1 Ω) (t : ℕ) (p : Ω × History t) : Point d :=
  paddedOutput a p.1 t p.2

theorem paddedPointQuery_measurable {d Ω} [MeasurableSpace Ω]
    (a : Policy d 1 Ω) (t : ℕ) : Measurable (paddedPointQuery a t) := by
  have hp : Measurable (fun p : Ω × History t => (p.1, historyVector t p.2)) :=
    measurable_fst.prodMk ((historyVector_measurable t).comp measurable_snd)
  exact Measurable.ite
    (measurableSet_eq_fun (frozen_joint_measurable a t).fst measurable_const) measurable_const
    (Measurable.ite (measurableSet_eq_fun ((a.stop_measurable t).comp hp) measurable_const)
      measurable_const ((a.query_measurable t).comp hp))

theorem paddedPointOutput_measurable {d Ω} [MeasurableSpace Ω]
    (a : Policy d 1 Ω) (t : ℕ) : Measurable (paddedPointOutput a t) := by
  have hp : Measurable (fun p : Ω × History t => (p.1, historyVector t p.2)) :=
    measurable_fst.prodMk ((historyVector_measurable t).comp measurable_snd)
  exact Measurable.ite
    (measurableSet_eq_fun (frozen_joint_measurable a t).fst measurable_const)
    (frozen_joint_measurable a t).snd ((a.output_measurable t).comp hp)

theorem follow_paddedPoint_execute {d Ω} [MeasurableSpace Ω]
    (a : Policy d 1 Ω) (f : Point d → ℝ) (ω : Ω) (fuel t : ℕ) (h : History t) :
    followOutput (paddedPointQuery a) (paddedPointOutput a) f ω fuel t h =
      if (frozen a ω t h).1 then (frozen a ω t h).2 else
        execute a f fuel t (ω, historyVector t h) := by
  induction fuel generalizing t with
  | zero => rfl
  | succ fuel ih =>
    rw [followOutput, ih]
    cases hf : (frozen a ω t h).1 <;>
      cases hs : a.stop t (ω, historyVector t h) <;>
      simp [frozen, paddedPointQuery, execute, nextHistory, historyVector, hf, hs]

/-- A complete m-slot replay, with zero padding after its first stop,
returns exactly the original cap-m optimizer's output for every oracle. -/
theorem paddedPointOutput_replyHistory {d Ω} [MeasurableSpace Ω]
    (a : Policy d 1 Ω) (f : Point d → ℝ) (ω : Ω) (m : ℕ) :
    paddedPointOutput a m (ω, replyHistory (paddedPointQuery a) f ω m) = run a f m ω := by
  have hp := followOutput_replyHistory (paddedPointQuery a) (paddedPointOutput a) f ω m 0
  have he := follow_paddedPoint_execute a f ω m 0 ()
  rw [Nat.zero_add] at hp
  change followOutput (paddedPointQuery a) (paddedPointOutput a) f ω m 0 () =
    paddedPointOutput a m (ω, replyHistory (paddedPointQuery a) f ω m) at hp
  simp only [frozen, Bool.false_eq_true, ↓reduceIte, historyVector] at he
  exact hp.symm.trans he

noncomputable def middleHistory (m n : ℕ) (hmn : m ≤ n) (h : History n) : History (n - m) :=
  dropHistory m (n - m) (castHistory (Nat.add_sub_of_le hmn).symm h)

theorem middleHistory_measurable (m n : ℕ) (hmn : m ≤ n) : Measurable (middleHistory m n hmn) :=
  (dropHistory_measurable m (n - m)).comp (castHistory_measurable (Nat.add_sub_of_le hmn).symm)

/-- Candidate indices computed from the two disjoint m-reply blocks. -/
noncomputable def candidates {d Ω} [MeasurableSpace Ω]
    (a : Policy d 1 Ω) (J : Point d → Fin d) (m : ℕ)
    (p : (Ω × Ω) × History (m + m)) : Fin d × Fin d :=
  (J (paddedPointOutput a m (p.1.1, takeHistory m m p.2)),
   J (paddedPointOutput a m (p.1.2, dropHistory m m p.2)))

theorem candidates_measurable {d Ω} [MeasurableSpace Ω]
    (a : Policy d 1 Ω) (J : Point d → Fin d) (hJ : Measurable J) (m : ℕ) :
    Measurable (candidates a J m) := by
  exact (hJ.comp ((paddedPointOutput_measurable a m).comp
    (measurable_fst.fst.prodMk ((takeHistory_measurable m m).comp measurable_snd)))).prodMk
    (hJ.comp ((paddedPointOutput_measurable a m).comp
      (measurable_fst.snd.prodMk ((dropHistory_measurable m m).comp measurable_snd))))

/-- The actual query schedule: two padded cap-m optimizer executions,
followed by the two candidate vertices, with no oracle input to the policy. -/
noncomputable def recoveryQuery {d Ω} [MeasurableSpace Ω]
    (a : Policy d 1 Ω) (J : Point d → Fin d) (m n : ℕ)
    (p : (Ω × Ω) × History n) : Point d :=
  if hfirst : n < m then paddedPointQuery a n (p.1.1, p.2) else
  if _hsecond : n < m + m then
    paddedPointQuery a (n - m) (p.1.2, middleHistory m n (Nat.le_of_not_gt hfirst) p.2) else
  if hvertex₁ : n = m + m then
    negativeVertex (candidates a J m (p.1, castHistory hvertex₁ p.2)).1 else
  if hvertex₂ : n = m + m + 1 then
    negativeVertex (candidates a J m (p.1, (castHistory hvertex₂ p.2).1)).2 else 0

noncomputable def recoveryOutput {d Ω} [MeasurableSpace Ω]
    (a : Policy d 1 Ω) (J : Point d → Fin d) (hd : 0 < d) (m n : ℕ)
    (p : (Ω × Ω) × History n) : Point d :=
  if hcap : n = m + m + 2 then
    let h := castHistory hcap p.2
    negativeVertex (chooseVertex (candidates a J m (p.1, h.1.1), (h.1.2, h.2)))
  else negativeVertex ⟨0, hd⟩

theorem recoveryQuery_measurable {d Ω} [MeasurableSpace Ω]
    (a : Policy d 1 Ω) (J : Point d → Fin d) (hJ : Measurable J) (m n : ℕ) :
    Measurable (recoveryQuery a J m n) := by
  unfold recoveryQuery
  have hv : Measurable (@negativeVertex d) := measurable_of_countable _
  by_cases hfirst : n < m
  · simp only [dif_pos hfirst]
    exact
      (paddedPointQuery_measurable a n).comp (measurable_fst.fst.prodMk measurable_snd)
  by_cases hsecond : n < m + m
  · simp only [dif_neg hfirst, dif_pos hsecond]
    exact
      (paddedPointQuery_measurable a (n - m)).comp
        (measurable_fst.snd.prodMk ((middleHistory_measurable m n (Nat.le_of_not_gt hfirst)).comp measurable_snd))
  by_cases hv₁ : n = m + m
  · simp only [dif_neg hfirst, dif_neg hsecond, dif_pos hv₁]
    exact
      hv.comp (((candidates_measurable a J hJ m).comp
        (measurable_fst.prodMk ((castHistory_measurable hv₁).comp measurable_snd))).fst)
  by_cases hv₂ : n = m + m + 1
  · simp only [dif_neg hfirst, dif_neg hsecond, dif_neg hv₁, dif_pos hv₂]
    exact
      hv.comp (((candidates_measurable a J hJ m).comp
        (measurable_fst.prodMk (((castHistory_measurable hv₂).comp measurable_snd).fst))).snd)
  · simp only [dif_neg hfirst, dif_neg hsecond, dif_neg hv₁, dif_neg hv₂]
    exact measurable_const

theorem recoveryOutput_measurable {d Ω} [MeasurableSpace Ω]
    (a : Policy d 1 Ω) (J : Point d → Fin d) (hJ : Measurable J) (hd : 0 < d) (m n : ℕ) :
    Measurable (recoveryOutput a J hd m n) := by
  unfold recoveryOutput
  have hv : Measurable (@negativeVertex d) := measurable_of_countable _
  by_cases hcap : n = m + m + 2
  · have hh := (castHistory_measurable hcap).comp
      (measurable_snd : Measurable (fun p : (Ω × Ω) × History n => p.2))
    simp only [dif_pos hcap]
    convert! hv.comp ((chooseVertex_measurable d).comp
        (((candidates_measurable a J hJ m).comp (measurable_fst.prodMk hh.fst.fst)).prodMk
          (hh.fst.snd.prodMk hh.snd))) using 1
  · simp only [dif_neg hcap]
    exact measurable_const

theorem recoveryOutput_feasible {d Ω} [MeasurableSpace Ω]
    (a : Policy d 1 Ω) (J : Point d → Fin d) (hd : 0 < d) (m n : ℕ)
    (p : (Ω × Ω) × History n) : Feasible 1 (recoveryOutput a J hd m n p) := by
  unfold recoveryOutput
  split
  · exact (negativeVertex_norm _).le
  · exact (negativeVertex_norm _).le

/-- An actual Policy with product seed space and exactly 2m+2 query slots. -/
noncomputable def recoveryPolicy {d Ω} [MeasurableSpace Ω]
    (a : Policy d 1 Ω) (J : Point d → Fin d) (hJ : Measurable J) (hd : 0 < d) (m : ℕ) :
    Policy d 1 (Ω × Ω) :=
  fixedPolicy (recoveryQuery a J m) (recoveryQuery_measurable a J hJ m)
    (recoveryOutput a J hd m) (recoveryOutput_measurable a J hJ hd m)
    (recoveryOutput_feasible a J hd m)

theorem recoveryPolicy_query_count {d Ω} [MeasurableSpace Ω]
    (a : Policy d 1 Ω) (J : Point d → Fin d) (hJ : Measurable J) (hd : 0 < d) (m : ℕ)
    (f : Point d → ℝ) (ω : Ω × Ω) :
    queriesUsed (recoveryPolicy a J hJ hd m) f (2 * m + 2) 0 (ω, Fin.elim0) = 2 * m + 2 :=
  queriesUsed_fixedPolicy _ _ _ _ _ _ _ _ _

theorem recoveryQuery_first {d Ω} [MeasurableSpace Ω]
    (a : Policy d 1 Ω) (J : Point d → Fin d) (m n : ℕ) (hn : n < m)
    (ω : Ω × Ω) (h : History n) :
    recoveryQuery a J m n (ω, h) = paddedPointQuery a n (ω.1, h) := by
  unfold recoveryQuery
  rw [dif_pos hn]

theorem recoveryQuery_second {d Ω} [MeasurableSpace Ω]
    (a : Policy d 1 Ω) (J : Point d → Fin d) (m k : ℕ) (hk : k < m)
    (ω : Ω × Ω) (h : History (m + k)) :
    recoveryQuery a J m (m + k) (ω, h) = paddedPointQuery a k (ω.2, dropHistory m k h) := by
  have hn : ¬ m + k < m := by omega
  have hm : m + k < m + m := by omega
  unfold recoveryQuery
  rw [dif_neg hn, dif_pos hm]
  unfold middleHistory
  exact PaperHistoryCastTools.apply_middleHistory_add
    (fun n hist => paddedPointQuery a n (ω.2, hist)) m k (Nat.le_of_not_gt hn) h

theorem recoveryQuery_vertex_first {d Ω} [MeasurableSpace Ω]
    (a : Policy d 1 Ω) (J : Point d → Fin d) (m : ℕ)
    (ω : Ω × Ω) (h : History (m + m)) :
    recoveryQuery a J m (m + m) (ω, h) = negativeVertex (candidates a J m (ω, h)).1 := by
  have h₁ : ¬m + m < m := by omega
  unfold recoveryQuery
  rw [dif_neg h₁, dif_neg (lt_irrefl _), dif_pos rfl, castHistory_self]
  rfl

theorem recoveryQuery_vertex_second {d Ω} [MeasurableSpace Ω]
    (a : Policy d 1 Ω) (J : Point d → Fin d) (m : ℕ)
    (ω : Ω × Ω) (h : History (m + m + 1)) :
    recoveryQuery a J m (m + m + 1) (ω, h) = negativeVertex (candidates a J m (ω, h.1)).2 := by
  have h₁ : ¬m + m + 1 < m := by omega
  have h₂ : ¬m + m + 1 < m + m := by omega
  have h₃ : ¬m + m + 1 = m + m := by omega
  unfold recoveryQuery
  rw [dif_neg h₁, dif_neg h₂, dif_neg h₃, dif_pos rfl, castHistory_self]
  rfl

theorem replyHistory_seed_map {d Seed Ω}
    (q : (t : ℕ) → Ω × History t → Point d) (f : Point d → ℝ)
    (s : Seed → Ω) (ω : Seed) (t : ℕ) :
    replyHistory (fun n p => q n (s p.1, p.2)) f ω t = replyHistory q f (s ω) t := by
  induction t with
  | zero => rfl
  | succ t ih => simp only [replyHistory, ih]

theorem candidates_replyHistory {d Ω} [MeasurableSpace Ω]
    (a : Policy d 1 Ω) (J : Point d → Fin d) (m : ℕ) (f : Point d → ℝ) (ω : Ω × Ω) :
    candidates a J m (ω, replyHistory (recoveryQuery a J m) f ω (m + m)) =
      (J (run a f m ω.1), J (run a f m ω.2)) := by
  have hfirst := firstBlockAtEnd (recoveryQuery a J m)
    (fun n p => paddedPointQuery a n (p.1.1, p.2)) m
    (fun n hn seed h => recoveryQuery_first a J m n hn seed h) f ω
  have hsecond := secondBlockAtEnd (recoveryQuery a J m)
    (fun n p => paddedPointQuery a n (p.1.2, p.2)) m
    (fun k hk seed h => recoveryQuery_second a J m k hk seed h) f ω
  unfold candidates
  rw [hfirst, hsecond, replyHistory_seed_map, replyHistory_seed_map,
    paddedPointOutput_replyHistory, paddedPointOutput_replyHistory]

/-- Exact behavior of the actual 2m+2-query recovery Policy on every
oracle and both private seeds, including each optimizer's stopping branches. -/
theorem run_recoveryPolicy {d Ω} [MeasurableSpace Ω]
    (a : Policy d 1 Ω) (J : Point d → Fin d) (hJ : Measurable J) (hd : 0 < d) (m : ℕ)
    (f : Point d → ℝ) (ω : Ω × Ω) :
    run (recoveryPolicy a J hJ hd m) f (2 * m + 2) ω =
      negativeVertex (chooseVertex ((J (run a f m ω.1), J (run a f m ω.2)),
        (f (negativeVertex (J (run a f m ω.1))), f (negativeVertex (J (run a f m ω.2)))))) := by
  have hcap : 2 * m + 2 = m + m + 2 := by omega
  rw [hcap]
  change run (fixedPolicy _ _ _ _ _) f (m + m + 2) ω = _
  rw [run_fixedPolicy]
  let H := replyHistory (recoveryQuery a J m) f ω (m + m)
  let c := candidates a J m (ω, H)
  have h₁ : replyHistory (recoveryQuery a J m) f ω (m + m + 1) =
      (H, f (negativeVertex c.1)) := by
    change (H, f (recoveryQuery a J m (m + m) (ω, H))) = _
    rw [recoveryQuery_vertex_first]
  have h₂ : replyHistory (recoveryQuery a J m) f ω (m + m + 2) =
      ((H, f (negativeVertex c.1)), f (negativeVertex c.2)) := by
    change (replyHistory (recoveryQuery a J m) f ω (m + m + 1),
      f (recoveryQuery a J m (m + m + 1)
        (ω, replyHistory (recoveryQuery a J m) f ω (m + m + 1)))) = _
    rw [h₁, recoveryQuery_vertex_second]
    rfl
  rw [h₂]
  unfold recoveryOutput
  rw [dif_pos rfl, castHistory_self]
  change negativeVertex (chooseVertex (c, (f (negativeVertex c.1), f (negativeVertex c.2)))) = _
  have hc := candidates_replyHistory a J m f ω
  change c = _ at hc
  rw [hc]

theorem argmaxAbs_negativeVertex {d : ℕ} (hd : 0 < d) (I : Fin d) :
    argmaxAbs d hd (negativeVertex I) = I := by
  have hm := argmaxAbs_is_maximum d hd (negativeVertex I) I
  by_contra hne
  simp only [negativeVertex] at hne hm
  simp [hne] at hm
  norm_num at hm

/-- If either original optimizer succeeds, the constructed actual Policy
recovers the spike using its two additional scalar vertex observations. -/
theorem recoveryPolicy_success_of_either {d Ω} [MeasurableSpace Ω]
    (a : Policy d 1 Ω) (hd : 0 < d) (m : ℕ)
    (b : Fin d → ℝ) (α : ℝ) (hα : 0 < α) (hb : ∀ j, |b j| ≤ α / 4) (I : Fin d)
    (ω : Ω × Ω)
    (hsuccess :
      spikeValue b α I (run a (spikeValue b α I) m ω.1) + spikeCoeff b α I I ≤ α ∨
      spikeValue b α I (run a (spikeValue b α I) m ω.2) + spikeCoeff b α I I ≤ α) :
    run (recoveryPolicy a (argmaxAbs d hd) (argmaxAbs_measurable d hd) hd m)
      (spikeValue b α I) (2 * m + 2) ω = negativeVertex I := by
  have hhit : argmaxAbs d hd (run a (spikeValue b α I) m ω.1) = I ∨
      argmaxAbs d hd (run a (spikeValue b α I) m ω.2) = I := by
    rcases hsuccess with h₁ | h₂
    · exact Or.inl (success_recovers_index hd b α hα hb I _
        (run_feasible a (spikeValue b α I) m ω.1) h₁)
    · exact Or.inr (success_recovers_index hd b α hα hb I _
        (run_feasible a (spikeValue b α I) m ω.2) h₂)
  rw [run_recoveryPolicy, chooseVertex_recovers b α hα hb I _ _ hhit]

/-- Actual product-seed recovery probability for every fixed good source
instance. The 8/9 conclusion is obtained from two independent Policy runs. -/
theorem recoveryPolicy_seed_success {d Ω} [MeasurableSpace Ω]
    (a : Policy d 1 Ω) (ν : Measure Ω) [IsProbabilityMeasure ν]
    (hd : 0 < d) (m : ℕ) (α : ℝ) (hα : 0 < α) (hsmall : α ≤ 1 / 8)
    (hsolve : SolvesOn ν a m 1 α)
    (b : Fin d → ℝ) (hb : ∀ j, |b j| ≤ α / 4) (I : Fin d) :
    (8 / 9 : ℝ) ≤ (ν.prod ν).real
      {ω | argmaxAbs d hd
        (run (recoveryPolicy a (argmaxAbs d hd) (argmaxAbs_measurable d hd) hd m)
          (spikeValue b α I) (2 * m + 2) ω) = I} := by
  let f : Objective d 1 :=
    ⟨spikeValue b α I, spikeValue_convex b α I,
      by simpa using spikeValue_lipschitz b α hα hsmall hb I⟩
  let S := successEvent a f m α
  have hSm : MeasurableSet S := successEvent_measurable a f f.continuous.measurable m α
  have hprob : (2 / 3 : ℝ) ≤ ν.real S := by
    have h := ENNReal.toReal_mono (measure_ne_top ν S) (hsolve f)
    norm_num [measureReal_def] at h ⊢
    exact h
  have htwo := PaperProbabilityReduction.independent_two_seed_success ν ν S S hSm hSm hprob hprob
  apply htwo.trans
  refine measureReal_mono (μ := ν.prod ν) ?_ (measure_ne_top _ _)
  intro ω hω
  have hgap (seed : Ω) (hs : seed ∈ S) :
      spikeValue b α I (run a (spikeValue b α I) m seed) + spikeCoeff b α I I ≤ α := by
    have hh := (success_iff_comparison a f (by norm_num) m α seed).mp hs
    have hv := hh (negativeVertex I) (negativeVertex_norm I).le
    change spikeValue b α I (run a (spikeValue b α I) m seed) ≤
      spikeValue b α I (negativeVertex I) + α at hv
    rw [spikeValue_vertex] at hv
    linarith
  have hsucc :
      spikeValue b α I (run a (spikeValue b α I) m ω.1) + spikeCoeff b α I I ≤ α ∨
      spikeValue b α I (run a (spikeValue b α I) m ω.2) + spikeCoeff b α I I ≤ α :=
    hω.elim (fun hs => Or.inl (hgap ω.1 hs)) (fun hs => Or.inr (hgap ω.2 hs))
  change argmaxAbs d hd
    (run (recoveryPolicy a (argmaxAbs d hd) (argmaxAbs_measurable d hd) hd m)
      (spikeValue b α I) (2 * m + 2) ω) = I
  rw [recoveryPolicy_success_of_either a hd m b α hα hb I ω hsucc, argmaxAbs_negativeVertex]

end PaperTwoRunRecovery


end
-- END TwoRunRecovery.lean

-- BEGIN HiddenSpikeLower.lean
section
namespace PaperHiddenSpikeLower

open MeasureTheory ProbabilityTheory Set Task003.OracleModel
  PaperPolicyGaussianBridge PaperTwoRunRecovery PaperRandomizedPolicyRecovery
  PaperHiddenSpikeGeometry PaperHiddenSpikeTails PaperHiddenSpikeGaussianBridge PaperGeometry
open scoped RealInnerProductSpace NNReal ENNReal

/-- Actual Tonelli lower bound on a good prior event. -/
theorem product_event_lower_of_good_fibres
    {G Seed : Type*} [MeasurableSpace G] [MeasurableSpace Seed]
    (μ : Measure G) (ν : Measure Seed) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (E : Set G) (hE : MeasurableSet E) (S : Set (G × Seed)) (hS : MeasurableSet S)
    (c : ℝ) (hc : 0 ≤ c)
    (hgood : ∀ g ∈ E, c ≤ ν.real {ω | (g, ω) ∈ S}) :
    c * μ.real E ≤ (μ.prod ν).real S := by
  have hb : ENNReal.ofReal c * μ E ≤ (μ.prod ν) S := by
    rw [Measure.prod_apply hS]
    calc
      ENNReal.ofReal c * μ E = ∫⁻ _ in E, ENNReal.ofReal c ∂μ := by rw [setLIntegral_const]
      _ ≤ ∫⁻ g in E, ν (Prod.mk g ⁻¹' S) ∂μ := by
        apply setLIntegral_mono' hE
        intro g hg
        exact ENNReal.ofReal_le_of_le_toReal (hgood g hg)
      _ ≤ ∫⁻ g, ν (Prod.mk g ⁻¹' S) ∂μ := lintegral_mono' Measure.restrict_le_self le_rfl
  have ht := ENNReal.toReal_mono (measure_ne_top _ _) hb
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hc, ← measureReal_def] using ht

theorem linearOracle_eq_rowValue {d : ℕ} (g : EuclideanSpace ℝ (Fin d)) (x : Point d) :
    ⟪pointVector x, g⟫ = rowValue (WithLp.ofLp g) x := by
  simp [pointVector, PiLp.inner_apply, rowValue, RCLike.inner_apply]

/-- The two-run actual Policy has recovery probability at least 8/9 on
every fixed coefficient vector in the good event. -/
theorem recovery_seed_success_on_good_source
    {d Ω} [MeasurableSpace Ω] (a : Policy d 1 Ω) (ν : Measure Ω) [IsProbabilityMeasure ν]
    (hd : 0 < d) (m : ℕ) (α : ℝ) (hα : 0 < α) (hsmall : α ≤ 1 / 8)
    (hsolve : SolvesOn ν a m 1 α) (I : Fin d) (g : EuclideanSpace ℝ (Fin d))
    (hgood : g ∈ sourceGoodEvent α (spikeMean α I)) :
    (8 / 9 : ℝ) ≤ (ν.prod ν).real
      {ω | argmaxAbs d hd
        (run (recoveryPolicy a (argmaxAbs d hd) (argmaxAbs_measurable d hd) hd m)
          (fun x => ⟪pointVector x, g⟫) (2 * m + 2) ω) = I} := by
  let b := centeredCoordinates g (spikeMean α I)
  have hb : ∀ j, |b j| ≤ α / 4 := hgood
  have hf : spikeValue b α I = (fun x => ⟪pointVector x, g⟫) := by
    funext x
    unfold spikeValue
    rw [show spikeCoeff b α I = WithLp.ofLp g from actual_coefficients_spike g α I]
    exact (linearOracle_eq_rowValue g x).symm
  have h := recoveryPolicy_seed_success a ν hd m α hα hsmall hsolve b hb I
  rw [hf] at h
  exact h

/-- The complete hidden-spike observation-cost theorem for the manuscript's
actual randomized minimax/oracle model. It derives both recovery bounds from
actual priors and a constructed 2m+2-query Policy. -/
theorem admissible_spike_observation_cost
    {d : ℕ} (hd : 6 ≤ d) {α : ℝ} (hα : 0 < α) (hsmall : α ≤ 1 / 8)
    {m : ℕ} (hm : AdmissibleBudget d m 1 1 α) :
    (d : ℝ) ≤ (2 * (m : ℝ) + 2) * (4096 * CompositionAudit.ell (d : ℝ)) := by
  obtain ⟨Ω, s, ν, hν, a, hsolve⟩ := hm
  letI : MeasurableSpace Ω := s
  letI : IsProbabilityMeasure ν := hν
  have hdpos : 0 < d := by omega
  have hdreal : (0 : ℝ) < d := by exact_mod_cast hdpos
  let ell := Real.log (Real.exp 1 * (d : ℝ))
  have hell : 0 < ell := by
    dsimp [ell]
    rw [CompositionAudit.log_e_mul hdreal]
    have hlog : 0 ≤ Real.log (d : ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ d by omega))
    linarith
  let σ := spikeSigma α ell
  have hσ : σ ≠ 0 := by
    dsimp [σ, spikeSigma]
    exact (div_pos hα (mul_pos (by norm_num) (Real.sqrt_pos.mpr hell))).ne'
  let J := argmaxAbs d hdpos
  let hJ : Measurable J := argmaxAbs_measurable d hdpos
  let r := recoveryPolicy a J hJ hdpos m
  let μ : Fin d → Measure (EuclideanSpace ℝ (Fin d)) :=
    fun I => PaperGaussianOracleBridge.sourcePrior σ (spikeMean α I)
  letI : ∀ I, IsProbabilityMeasure (μ I) := fun I => PaperGaussianOracleBridge.sourcePrior_isProbability _ _
  let S : Fin d → Set (EuclideanSpace ℝ (Fin d) × (Ω × Ω)) :=
    fun I => {p | J (run r (fun x => ⟪pointVector x, p.1⟫) (2 * m + 2) p.2) = I}
  have hF : Measurable (fun p : EuclideanSpace ℝ (Fin d) × Point d => ⟪pointVector p.2, p.1⟫) :=
    ((pointVector_measurable d).comp measurable_snd).inner measurable_fst
  have hr := Task003.OracleJointMeasurability.run_joint_measurable r _ hF (2 * m + 2)
  have hS : ∀ I, MeasurableSet (S I) := fun I => measurableSet_eq_fun (hJ.comp hr) measurable_const
  have hprod (I : Fin d) : (7 / 8 : ℝ) ≤ ((μ I).prod (ν.prod ν)).real (S I) := by
    have hb := product_event_lower_of_good_fibres (μ I) (ν.prod ν)
      (sourceGoodEvent α (spikeMean α I)) (sourceGoodEvent_measurable α (spikeMean α I))
      (S I) (hS I) (8 / 9) (by norm_num) (by
        intro g hg
        exact recovery_seed_success_on_good_source a ν hdpos m α hα hsmall hsolve I g hg)
    have hmass : (63 / 64 : ℝ) ≤ (μ I).real (sourceGoodEvent α (spikeMean α I)) :=
      sourcePrior_good_mass hdpos α hα (spikeMean α I)
    nlinarith
  have hmean : (7 / 8 : ℝ) ≤ (∑ I, ((μ I).prod (ν.prod ν)).real (S I)) / d := by
    apply (le_div_iff₀ hdreal).mpr
    have hsum := Finset.sum_le_sum (s := Finset.univ) (fun I _ => hprod I)
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
    nlinarith
  have hrec : (2 / 3 : ℝ) < (∑ I, ((μ I).prod (ν.prod ν)).real (S I)) / d := by
    linarith
  have hcost := randomized_policy_gaussian_observation_lower_bound hd r (ν.prod ν)
    σ (4 * α) hσ (2 * m + 2) J hJ hrec
  have hsqrt : Real.sqrt ell ≠ 0 := (Real.sqrt_pos.mpr hell).ne'
  have hratio : (4 * α / σ) ^ 2 = 4096 * ell := by
    have he : 4 * α / σ = 64 * Real.sqrt ell := by
      dsimp [σ, spikeSigma]
      field_simp [hα.ne', hsqrt]
      ring
    rw [he, mul_pow, Real.sq_sqrt hell.le]
    norm_num
  rw [hratio] at hcost
  simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, CompositionAudit.ell] using hcost

end PaperHiddenSpikeLower


end
-- END HiddenSpikeLower.lean

-- BEGIN MainTheorem.lean
section

/- Dependencies: ZhangInterface, HiddenSpikeLower, GlobalUpper, SpikeThreshold,
MinimaxAssembly. This is the whole manuscript's internal derivation with exactly
its two named external literature inputs. They are ordinary theorem parameters,
not newly declared axioms. This file does not certify proofs of those two cited
papers, and the audit must retain that scope distinction. -/
namespace Task003.MainTheorem
open Task003.OracleModel Task003.MinimaxAssembly CompositionAudit

/-- The complete normalized main theorem relative only to External Z and the
Protasov relative-range algorithmic theorem stated in the manuscript. -/
theorem full_joint_profile_of_named_literature_inputs
    (Dsource : ℕ) (hDsource : 0<Dsource) (κ δ cp C2 c0 : ℝ)
    (hκ : 0<κ) (hκmax : κ≤1/16) (hδ : 0<δ) (hδmax : δ≤1)
    (hcp : 0<cp) (hC2 : 0<C2) (hc0 : 0<c0) (hc0max : c0≤1/8)
    (hZhang : Task003.ZhangInterface.ZhangPrinciple Dsource κ δ cp)
    (hProtasov : Task003.ProtasovInterface.ProtasovPrinciple C2) :
    FullJointProfile c0 := by
  obtain ⟨Dr,c,hDr,hDrpos,hc,hregional⟩ :=
    Task003.ZhangInterface.regional_of_zhang hDsource κ δ cp hκ hκmax hδ hδmax hcp hZhang
  obtain ⟨b,hb,hupper⟩ := Task003.GlobalUpper.global_upper_of_protasov C2 hC2 hProtasov
  let D := max Dr Task003.SpikeThreshold.absorptionDimension
  have hD6 : 6≤D := (show 6≤Task003.SpikeThreshold.absorptionDimension by
    norm_num [Task003.SpikeThreshold.absorptionDimension]).trans (le_max_right _ _)
  apply fullJointProfile_of_components D c0 c (1/16384) δ b
    hc0 hc0max hc (by norm_num) hδ hb
  · intro d α hd hα hα0 hscope m hm
    have hscope' : α≤δ/Real.sqrt (ell (d:ℝ)) := by simpa only [tau] using hscope
    exact hregional d ((le_max_left _ _).trans hd) α hα hscope' m hm
  · intro d α hd hα hα0 m hm
    have hcost := PaperHiddenSpikeLower.admissible_spike_observation_cost
      (hD6.trans hd) hα (hα0.trans hc0max) hm
    exact Task003.SpikeThreshold.spike_lower_after_cost ((le_max_right _ _).trans hd) hcost
  · intro d α hd hα hα0
    obtain ⟨m,hm,hbound⟩ := hupper d α (by omega) hα (by linarith)
    exact ⟨m,hm,hbound⟩

/-- The original unnormalised exact-value model, uniformly in d and epsilon,
with arbitrary positive L,R and the same least admissible pathwise budget. -/
theorem main_theorem_scaled_of_named_literature_inputs
    (Dsource : ℕ) (hDsource : 0<Dsource) (κ δ cp C2 c0 : ℝ)
    (hκ : 0<κ) (hκmax : κ≤1/16) (hδ : 0<δ) (hδmax : δ≤1)
    (hcp : 0<cp) (hC2 : 0<C2) (hc0 : 0<c0) (hc0max : c0≤1/8)
    (hZhang : Task003.ZhangInterface.ZhangPrinciple Dsource κ δ cp)
    (hProtasov : Task003.ProtasovInterface.ProtasovPrinciple C2) :
    ∃ (D : ℕ) (a b : ℝ), 0<D ∧ 0<a ∧ 0<b ∧
      ∀ (d : ℕ), D≤d → ∀ (L R ε : ℝ), 0<L → 0<R →
        0<ε/(L*R) → ε/(L*R)≤c0 →
        ∃ N : ℕ, minimaxBudget d L R ε=some N ∧
          a*profileQ d (ε/(L*R))/(profileLambda d (ε/(L*R)))^2≤(N:ℝ) ∧
          (N:ℝ)≤b*profileQ d (ε/(L*R))*(profileLambda d (ε/(L*R)))^2 :=
  Task003.MinimaxAssembly.FullJointProfile.scaled (full_joint_profile_of_named_literature_inputs Dsource hDsource
    κ δ cp C2 c0 hκ hκmax hδ hδmax hcp hC2 hc0 hc0max hZhang hProtasov)

end Task003.MainTheorem


end
-- END MainTheorem.lean

-- BEGIN ProtasovEndpoint.lean
section

/- Dependencies: OracleModel, ProtasovInterface.
The original relative-range input has an open accuracy endpoint. This file
proves the closed normalized endpoint by querying the same input at half the
requested accuracy. It supplies no proof of the external algorithm itself. -/
namespace Task003.ProtasovEndpoint
open MeasureTheory Set Task003.OracleModel Task003.ProtasovInterface

/-- The literature input with its stated open accuracy interval. -/
def ProtasovOpenPrinciple (C : ℝ) : Prop :=
  ∀ d : ℕ, 2 ≤ d → ∀ δ : ℝ, 0 < δ → δ < 1 / 2 →
    ∃ m : ℕ, ∃ a : Policy d 1 Unit,
      (m : ℝ) ≤ C * (d : ℝ)^2 * Real.log (d + 1) * Real.log (1 / δ) ∧
      ∀ f : Objective d 1, ∀ ω : Unit,
        f (run a f m ω) - optimum 1 f ≤ δ * Task003.ProtasovInterface.oscillation f

theorem oscillation_nonneg {d : ℕ} (f : Objective d 1) : 0 ≤ Task003.ProtasovInterface.oscillation f := by
  obtain ⟨x, hx, hval, _⟩ := optimum_attained f (by norm_num : (0 : ℝ) ≤ 1)
  have hset : {x : Point d | Feasible 1 x} = Metric.closedBall 0 1 := by
    ext y
    simp [Feasible, Metric.mem_closedBall, dist_zero_right]
  have hc : IsCompact {x : Point d | Feasible 1 x} := by
    rw [hset]
    exact isCompact_closedBall 0 1
  have hb : BddAbove (f '' {x : Point d | Feasible 1 x}) :=
    (hc.image f.continuous).bddAbove
  have hs := le_csSup hb (show f x ∈ f '' {x : Point d | Feasible 1 x} from
    ⟨x, hx, rfl⟩)
  unfold Task003.ProtasovInterface.oscillation
  linarith

theorem closed_protasov_of_open {C : ℝ} (hC : 0 ≤ C)
    (hOpen : ProtasovOpenPrinciple C) : ProtasovPrinciple (2 * C) := by
  intro d hd δ hδ hδ2
  obtain ⟨m, a, hm, ha⟩ := hOpen d hd (δ / 2) (by positivity) (by linarith)
  refine ⟨m, a, ?_, ?_⟩
  · have h2 : (2 : ℝ) ≤ 1 / δ := (le_div_iff₀ hδ).mpr (by linarith)
    have hl : Real.log 2 ≤ Real.log (1 / δ) :=
      Real.log_le_log (by norm_num) h2
    have he : 1 / (δ / 2) = 2 * (1 / δ) := by ring
    have hlog : Real.log (1 / (δ / 2)) ≤ 2 * Real.log (1 / δ) := by
      rw [he, Real.log_mul (by norm_num : (2 : ℝ) ≠ 0)
        (ne_of_gt (by positivity : 0 < 1 / δ))]
      linarith
    have hc : 0 ≤ C * (d : ℝ)^2 * Real.log (d + 1) := by
      have hl0 : 0 ≤ Real.log (d + 1 : ℝ) :=
        Real.log_nonneg (by have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d; linarith)
      positivity
    calc
      (m : ℝ) ≤ C * (d : ℝ)^2 * Real.log (d + 1) * Real.log (1 / (δ / 2)) := hm
      _ ≤ C * (d : ℝ)^2 * Real.log (d + 1) * (2 * Real.log (1 / δ)) :=
        mul_le_mul_of_nonneg_left hlog hc
      _ = (2 * C) * (d : ℝ)^2 * Real.log (d + 1) * Real.log (1 / δ) := by ring
  · intro f ω
    exact (ha f ω).trans (mul_le_mul_of_nonneg_right (by linarith) (oscillation_nonneg f))

end Task003.ProtasovEndpoint


end
-- END ProtasovEndpoint.lean

-- BEGIN LiteratureMain.lean
section

/- Dependencies: MainTheorem, ProtasovEndpoint. A reusable statement with just
one existential source-hardness input and one strict-range algorithmic input.
Neither external input is asserted to be a proved theorem of this project. -/
namespace Task003.LiteratureMain
open Task003.OracleModel

/-- The normalized constants and the fixed-prior hardness content of External Z.
The actual prior, its norm support and its coordinate good mass are constructed
and proved in TruncatedGaussianRows and SourceRowsBridge. -/
def ZhangLiteratureInput : Prop :=
  ∃ (D : ℕ) (κ δ cp : ℝ), 0<D ∧ 0<κ ∧ κ≤1/16 ∧
    0<δ ∧ δ≤1 ∧ 0<cp ∧ Task003.ZhangInterface.ZhangPrinciple D κ δ cp

/-- Only the strict-range relative-error theorem from the cited source is
needed; the endpoint extension is proved internally in ProtasovEndpoint. -/
def ProtasovLiteratureInput : Prop :=
  ∃ C : ℝ, 0<C ∧ Task003.ProtasovEndpoint.ProtasovOpenPrinciple C

/-- Every internal component of the manuscript main theorem, with exactly its
two named external mathematical inputs, and with a genuine least admissible
pathwise query budget. This is intentionally a conditional theorem. -/
theorem normalized_main_from_literature
    (hZ : ZhangLiteratureInput) (hP : ProtasovLiteratureInput)
    (c0 : ℝ) (hc0 : 0<c0) (hc0max : c0≤1/8) : FullJointProfile c0 := by
  obtain ⟨D,κ,δ,cp,hD,hκ,hκmax,hδ,hδmax,hcp,hZ⟩ := hZ
  obtain ⟨C,hC,hP⟩ := hP
  exact Task003.MainTheorem.full_joint_profile_of_named_literature_inputs D hD
    κ δ cp (2*C) c0 hκ hκmax hδ hδmax hcp (by positivity) hc0 hc0max hZ
      (Task003.ProtasovEndpoint.closed_protasov_of_open hC.le hP)

/-- The full original-scale conclusion, uniform over dimensions and accuracies,
relative only to the two displayed external literature propositions. -/
theorem scaled_main_from_literature
    (hZ : ZhangLiteratureInput) (hP : ProtasovLiteratureInput)
    (c0 : ℝ) (hc0 : 0<c0) (hc0max : c0≤1/8) :
    ∃ (D : ℕ) (a b : ℝ), 0<D ∧ 0<a ∧ 0<b ∧
      ∀ (d : ℕ), D≤d → ∀ (L R ε : ℝ), 0<L → 0<R →
        0<ε/(L*R) → ε/(L*R)≤c0 →
        ∃ N : ℕ, minimaxBudget d L R ε=some N ∧
          a*profileQ d (ε/(L*R))/(profileLambda d (ε/(L*R)))^2≤(N:ℝ) ∧
          (N:ℝ)≤b*profileQ d (ε/(L*R))*(profileLambda d (ε/(L*R)))^2 :=
  Task003.MinimaxAssembly.FullJointProfile.scaled
    (normalized_main_from_literature hZ hP c0 hc0 hc0max)

end Task003.LiteratureMain


end
-- END LiteratureMain.lean