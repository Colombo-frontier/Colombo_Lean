import Mathlib.Analysis.Convex.Strong
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Module

/-!
# Proximal inequalities used in Appendix A

These results prove minimizer existence, uniqueness, growth, gap bounds and
perturbation directly. `proxResidual` is the algebraic residual; identifying it
with the derivative of the minimized envelope is a separate calculus theorem.
-/

open Set Filter Metric
open scoped InnerProductSpace Topology

namespace NCConcave16991

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def WeaklyConvex (ρ : ℝ) (f : E → ℝ) : Prop :=
  ConvexOn ℝ univ (fun x ↦ f x + ρ / 2 * ‖x‖ ^ 2)

def proxObjective (f : E → ℝ) (L : ℝ) (c x : E) : ℝ :=
  f x + L * ‖x - c‖ ^ 2

def IsProxPoint (f : E → ℝ) (L : ℝ) (c p : E) : Prop :=
  ∀ x, proxObjective f L c p ≤ proxObjective f L c x

def proxResidual (L : ℝ) (c p : E) : E := (2 * L) • (c - p)

/-- Strong convexity gives the sharp quadratic growth at a global minimizer. -/
theorem strongConvex_min_growth {F : E → ℝ} {μ : ℝ} {p : E}
    (hF : StrongConvexOn univ μ F) (hp : ∀ x, F p ≤ F x) (q : E) :
    F p + μ / 2 * ‖p - q‖ ^ 2 ≤ F q := by
  by_contra! h
  let d := μ / 2 * ‖p - q‖ ^ 2
  have hgap : 0 ≤ F q - F p := sub_nonneg.mpr (hp q)
  have hd : 0 < d := by dsimp [d]; linarith
  have hratio : (F q - F p) / d < 1 := (div_lt_one hd).2 (by dsimp [d]; linarith)
  obtain ⟨a, ha, ha1⟩ := exists_between hratio
  have ha0 : 0 ≤ a := le_trans (div_nonneg hgap hd.le) ha.le
  have hdist : F q - F p < a * d := (div_lt_iff₀ hd).1 ha
  have hc := hF.2 (mem_univ p) (mem_univ q) ha0
    (show 0 ≤ 1 - a by linarith) (show a + (1 - a) = 1 by ring)
  have hm := hp (a • p + (1 - a) • q)
  simp only [smul_eq_mul] at hc
  change F (a • p + (1 - a) • q) ≤ a * F p + (1 - a) * F q -
    a * (1 - a) * d at hc
  have hbad : 0 < (1 - a) * (a * d - (F q - F p)) :=
    mul_pos (by linarith) (by linarith)
  nlinarith

theorem weaklyConvex_prox_strong {f : E → ℝ} {L : ℝ}
    (hf : WeaklyConvex L f) (c : E) :
    StrongConvexOn univ L (proxObjective f L c) := by
  rw [strongConvexOn_iff_convex]
  have ha : ConvexOn ℝ (univ : Set E)
      (fun x ↦ -2 * L * ⟪x, c⟫_ℝ + L * ‖c‖ ^ 2) := by
    refine ⟨convex_univ, ?_⟩
    intro x hx y hy a b ha hb hab
    simp only [inner_add_left, real_inner_smul_left, smul_eq_mul]
    apply le_of_eq
    rw [show b = 1 - a by linarith]
    ring
  convert hf.add ha using 1
  ext x
  simp only [Pi.add_apply, proxObjective, norm_sub_sq_real]
  ring

theorem proxPoint_unique {f : E → ℝ} {L : ℝ} {c p q : E}
    (hL : 0 < L) (hf : WeaklyConvex L f)
    (hp : IsProxPoint f L c p) (hq : IsProxPoint f L c q) : p = q := by
  have hg := strongConvex_min_growth (weaklyConvex_prox_strong hf c) hp q
  have hh := hq p
  have hz : ‖p - q‖ ^ 2 = 0 := by nlinarith [sq_nonneg ‖p - q‖]
  exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hz))

/-- Every continuous bounded-below function admits a proximal minimizer in a
proper inner-product space (in particular in every finite-dimensional space). -/
theorem exists_proxPoint [ProperSpace E] {f : E → ℝ} {L : ℝ}
    (hL : 0 < L) (hf : Continuous f) (hb : BddBelow (range f)) (c : E) :
    ∃ p, IsProxPoint f L c p := by
  obtain ⟨m, hm⟩ := hb
  have hm' : ∀ x, m ≤ f x := fun x ↦ hm (mem_range_self x)
  let r := Real.sqrt ((f c - m) / L) + 1
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hc : c ∈ closedBall c r := by simpa using hr
  have hcont : Continuous (proxObjective f L c) :=
    hf.add (continuous_const.mul ((continuous_id.sub continuous_const).norm.pow 2))
  obtain ⟨p, hp, hpmin⟩ := (isCompact_closedBall c r).exists_isMinOn ⟨c, hc⟩ hcont.continuousOn
  refine ⟨p, fun x ↦ ?_⟩
  by_cases hx : x ∈ closedBall c r
  · exact hpmin hx
  · have hn : r < ‖x - c‖ := by
      simpa only [mem_closedBall, dist_eq_norm, not_le] using hx
    have hsq : (f c - m) / L ≤ ‖x - c‖ ^ 2 := by
      have hs := Real.sq_sqrt (div_nonneg (sub_nonneg.mpr (hm' c)) hL.le)
      have hsn := Real.sqrt_nonneg ((f c - m) / L)
      dsimp [r] at hn
      nlinarith
    have hcost : f c - m ≤ L * ‖x - c‖ ^ 2 := by
      have hh := (div_le_iff₀ hL).1 hsq
      nlinarith
    have hp0 : proxObjective f L c p ≤ proxObjective f L c c := hpmin hc
    simp only [proxObjective, sub_self, norm_zero, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, zero_pow, mul_zero, add_zero] at hp0
    dsimp [proxObjective]
    linarith [hm' x]

theorem exists_unique_proxPoint [ProperSpace E] {f : E → ℝ} {L : ℝ}
    (hL : 0 < L) (hf : Continuous f) (hb : BddBelow (range f))
    (hw : WeaklyConvex L f) (c : E) : ∃! p, IsProxPoint f L c p := by
  obtain ⟨p, hp⟩ := exists_proxPoint hL hf hb c
  exact ⟨p, hp, fun q hq ↦ proxPoint_unique hL hw hq hp⟩

theorem proxPoint_gap_bound {f : E → ℝ} {L Δ : ℝ} {c p : E}
    (hp : IsProxPoint f L c p) (hgap : f c - f p ≤ Δ) :
    L * ‖p - c‖ ^ 2 ≤ Δ := by
  have h := hp c
  simp only [proxObjective, sub_self, norm_zero, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, zero_pow, mul_zero, add_zero] at h
  linarith

theorem proxResidual_sq (L : ℝ) (c p : E) :
    ‖proxResidual L c p‖ ^ 2 = 4 * L ^ 2 * ‖p - c‖ ^ 2 := by
  simp only [proxResidual, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  rw [norm_sub_rev c p]
  ring

theorem proxResidual_gap {f : E → ℝ} {L Δ : ℝ} {c p : E}
    (hL : 0 ≤ L) (hp : IsProxPoint f L c p) (hgap : f c - f p ≤ Δ) :
    ‖proxResidual L c p‖ ^ 2 ≤ 4 * L * Δ := by
  rw [proxResidual_sq]
  have hg := mul_le_mul_of_nonneg_left (proxPoint_gap_bound hp hgap)
    (show 0 ≤ 4 * L by positivity)
  nlinarith

/-- The zero-query accuracy threshold, for an actual proximal minimizer. -/
theorem zeroQuery_of_small_gap {f : E → ℝ} {L Δ ε : ℝ} {c p : E}
    (hL : 0 ≤ L) (hε : 0 ≤ ε) (hp : IsProxPoint f L c p)
    (hgap : f c - f p ≤ Δ) (hsmall : 4 * L * Δ ≤ ε ^ 2) :
    ‖proxResidual L c p‖ ≤ ε := by
  have hg := proxResidual_gap hL hp hgap
  nlinarith [norm_nonneg (proxResidual L c p)]

/-- The sharp Appendix A.2 perturbation bound, without assuming derivatives. -/
theorem proxPoint_perturbation {f g : E → ℝ} {L r : ℝ} {c p q : E}
    (hf : WeaklyConvex L f) (hg : WeaklyConvex L g)
    (hp : IsProxPoint f L c p) (hq : IsProxPoint g L c q)
    (hfg : ∀ x, 0 ≤ f x - g x ∧ f x - g x ≤ r) :
    L * ‖p - q‖ ^ 2 ≤ r := by
  have hfp := strongConvex_min_growth (weaklyConvex_prox_strong hf c) hp q
  have hgq := strongConvex_min_growth (weaklyConvex_prox_strong hg c) hq p
  rw [norm_sub_rev q p] at hgq
  dsimp [proxObjective] at hfp hgq
  have hl := (hfg p).1
  have hu := (hfg q).2
  linarith

theorem proxResidual_perturbation {f g : E → ℝ} {L r : ℝ} {c p q : E}
    (hL : 0 ≤ L) (hf : WeaklyConvex L f) (hg : WeaklyConvex L g)
    (hp : IsProxPoint f L c p) (hq : IsProxPoint g L c q)
    (hfg : ∀ x, 0 ≤ f x - g x ∧ f x - g x ≤ r) :
    ‖proxResidual L c p - proxResidual L c q‖ ^ 2 ≤ 4 * L * r := by
  have he : proxResidual L c p - proxResidual L c q = (2 * L) • (q - p) := by
    dsimp [proxResidual]
    module
  rw [he, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, norm_sub_rev q p]
  have hh := mul_le_mul_of_nonneg_left (proxPoint_perturbation hf hg hp hq hfg)
    (show 0 ≤ 4 * L by positivity)
  nlinarith

end NCConcave16991
