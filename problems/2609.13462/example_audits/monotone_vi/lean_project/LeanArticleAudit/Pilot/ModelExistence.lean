import LeanArticleAudit.Pilot.TaylorModel
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.Topology.MetricSpace.Contracting

/-!
# Existence, uniqueness, and stability of the known Taylor-model VI

This module starts with the general compact-convex projection machinery needed
to avoid assuming a Brouwer fixed-point theorem.  The projection is obtained
from the Hilbert projection theorem already in mathlib.
-/

open Set Filter Topology
open scoped RealInnerProductSpace

namespace LeanArticleAudit.Pilot

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Variational-inequality predicate with the paper's outward normal sign. -/
def SolvesModelVI (X : Set E) (M : E → E) (y : E) : Prop :=
  y ∈ X ∧ ∀ z ∈ X, 0 ≤ inner ℝ (M y) (z - y)

/-- Metric projection onto a fixed nonempty compact convex feasible set. -/
noncomputable def compactConvexProjection (X : Set E) (hne : X.Nonempty)
    (hcpt : IsCompact X) (hconv : Convex ℝ X) (u : E) : E :=
  Classical.choose (exists_norm_eq_iInf_of_complete_convex hne hcpt.isComplete hconv u)

private theorem compactConvexProjection_spec (X : Set E) (hne : X.Nonempty)
    (hcpt : IsCompact X) (hconv : Convex ℝ X) (u : E) :
    compactConvexProjection X hne hcpt hconv u ∈ X ∧
      ‖u - compactConvexProjection X hne hcpt hconv u‖ = ⨅ w : X, ‖u - w‖ :=
  Classical.choose_spec (exists_norm_eq_iInf_of_complete_convex hne hcpt.isComplete hconv u)

theorem compactConvexProjection_mem (X : Set E) (hne : X.Nonempty)
    (hcpt : IsCompact X) (hconv : Convex ℝ X) (u : E) :
    compactConvexProjection X hne hcpt hconv u ∈ X :=
  (compactConvexProjection_spec X hne hcpt hconv u).1

theorem compactConvexProjection_variational (X : Set E) (hne : X.Nonempty)
    (hcpt : IsCompact X) (hconv : Convex ℝ X) (u : E) :
    ∀ z ∈ X, inner ℝ
      (u - compactConvexProjection X hne hcpt hconv u)
      (z - compactConvexProjection X hne hcpt hconv u) ≤ 0 := by
  exact (norm_eq_iInf_iff_real_inner_le_zero hconv
    (compactConvexProjection_mem X hne hcpt hconv u)).mp
      (compactConvexProjection_spec X hne hcpt hconv u).2

/-- Projection onto a nonempty compact convex set is nonexpansive. -/
theorem compactConvexProjection_dist_le (X : Set E) (hne : X.Nonempty)
    (hcpt : IsCompact X) (hconv : Convex ℝ X) (u v : E) :
    ‖compactConvexProjection X hne hcpt hconv u -
        compactConvexProjection X hne hcpt hconv v‖ ≤ ‖u - v‖ := by
  let p := compactConvexProjection X hne hcpt hconv u
  let q := compactConvexProjection X hne hcpt hconv v
  have hu := compactConvexProjection_variational X hne hcpt hconv u q
    (compactConvexProjection_mem X hne hcpt hconv v)
  have hv := compactConvexProjection_variational X hne hcpt hconv v p
    (compactConvexProjection_mem X hne hcpt hconv u)
  change inner ℝ (u - p) (q - p) ≤ 0 at hu
  change inner ℝ (v - q) (p - q) ≤ 0 at hv
  have hu' : 0 ≤ inner ℝ (u - p) (p - q) := by
    rw [show p - q = -(q - p) by abel, inner_neg_right]
    linarith
  have hsq : ‖p - q‖ * ‖p - q‖ ≤ ‖u - v‖ * ‖p - q‖ := by
    have hid : inner ℝ (u - v) (p - q) =
        inner ℝ (u - p) (p - q) - inner ℝ (v - q) (p - q) +
          inner ℝ (p - q) (p - q) := by
      rw [show u - v = (u - p) - (v - q) + (p - q) by abel,
        inner_add_left, inner_sub_left]
    calc
      ‖p - q‖ * ‖p - q‖ = inner ℝ (p - q) (p - q) :=
        (real_inner_self_eq_norm_mul_norm (p - q)).symm
      _ ≤ inner ℝ (u - v) (p - q) := by
        rw [hid]
        linarith
      _ ≤ ‖u - v‖ * ‖p - q‖ := real_inner_le_norm _ _
  by_cases hpq : ‖p - q‖ = 0
  · simpa [p, q, hpq] using norm_nonneg (u - v)
  · have hpqpos : 0 < ‖p - q‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hpq)
    nlinarith

/-- Squared contraction estimate for one forward step of a strongly monotone,
Lipschitz operator.  Keeping this algebraic estimate separate avoids hiding
the quantitative step-size condition in a fixed-point certificate. -/
theorem forwardStep_norm_sq_le {X : Set E} {M : E → E} {mu L alpha : ℝ}
    (halpha : 0 ≤ alpha) (hL0 : 0 ≤ L)
    (hstrong : ∀ x ∈ X, ∀ y ∈ X,
      mu * ‖x - y‖ ^ 2 ≤ inner ℝ (M x - M y) (x - y))
    (hlip : ∀ x ∈ X, ∀ y ∈ X, ‖M x - M y‖ ≤ L * ‖x - y‖)
    {x y : E} (hx : x ∈ X) (hy : y ∈ X) :
    ‖(x - alpha • M x) - (y - alpha • M y)‖ ^ 2 ≤
      (1 - 2 * alpha * mu + alpha ^ 2 * L ^ 2) * ‖x - y‖ ^ 2 := by
  have hmon := hstrong x hx y hy
  have hL := hlip x hx y hy
  have hLsq : ‖M x - M y‖ ^ 2 ≤ L ^ 2 * ‖x - y‖ ^ 2 := by
    have hright : 0 ≤ L * ‖x - y‖ := mul_nonneg hL0 (norm_nonneg _)
    simpa [mul_pow] using
      (sq_le_sq₀ (norm_nonneg (M x - M y)) hright).mpr hL
  have hexpand (a b : E) :
      ‖a - alpha • b‖ ^ 2 =
        ‖a‖ ^ 2 - 2 * alpha * inner ℝ b a + alpha ^ 2 * ‖b‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq]
    simp only [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right,
      conj_trivial]
    rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, real_inner_comm a b]
    ring
  rw [show (x - alpha • M x) - (y - alpha • M y) =
      (x - y) - alpha • (M x - M y) by module]
  rw [hexpand]
  nlinarith [mul_nonneg halpha (sub_nonneg.mpr hmon),
    mul_nonneg (sq_nonneg alpha) (sub_nonneg.mpr hLsq)]

/-- A contraction of one projected forward step produces a VI solution.
This is the Banach-fixed-point replacement for an unavailable Brouwer API. -/
theorem exists_solvesModelVI_of_projected_contracting
    (X : Set E) (hne : X.Nonempty) (hcpt : IsCompact X) (hconv : Convex ℝ X)
    (M : E → E) (alpha : ℝ) (halpha : 0 < alpha) (K : NNReal)
    (hcontract : ContractingWith K
      (fun y : X ↦ ⟨compactConvexProjection X hne hcpt hconv
        (y.1 - alpha • M y.1), compactConvexProjection_mem X hne hcpt hconv _⟩)) :
    ∃ y, SolvesModelVI X M y := by
  let T : X → X := fun y ↦ ⟨compactConvexProjection X hne hcpt hconv
    (y.1 - alpha • M y.1), compactConvexProjection_mem X hne hcpt hconv _⟩
  let x0 : X := ⟨hne.some, hne.some_mem⟩
  letI : CompleteSpace X := hcpt.isComplete.completeSpace_coe
  change ContractingWith K T at hcontract
  obtain ⟨y, hyfix, _, _⟩ := hcontract.exists_fixedPoint x0 (edist_ne_top _ _)
  refine ⟨y.1, y.2, ?_⟩
  intro z hz
  have hvar := compactConvexProjection_variational X hne hcpt hconv
    (y.1 - alpha • M y.1) z hz
  have heq : compactConvexProjection X hne hcpt hconv
      (y.1 - alpha • M y.1) = y.1 := by
    exact Subtype.ext_iff.mp hyfix
  rw [heq] at hvar
  simp only [sub_sub_cancel_left, inner_neg_left, inner_smul_left,
    RCLike.conj_to_real, conj_trivial] at hvar
  nlinarith

/-- A quantitative strong-monotonicity/Lipschitz criterion for existence.
The displayed scalar inequality is exactly the admissible forward-step
condition; in applications one may take `alpha = mu / L^2`. -/
theorem exists_solvesModelVI_of_strong_monotone_lipschitz
    (X : Set E) (hne : X.Nonempty) (hcpt : IsCompact X) (hconv : Convex ℝ X)
    (M : E → E) (mu L alpha : ℝ) (K : NNReal)
    (halpha : 0 < alpha) (hL0 : 0 ≤ L) (hK : K < 1)
    (hrate : 1 - 2 * alpha * mu + alpha ^ 2 * L ^ 2 ≤ (K : ℝ) ^ 2)
    (hstrong : ∀ x ∈ X, ∀ y ∈ X,
      mu * ‖x - y‖ ^ 2 ≤ inner ℝ (M x - M y) (x - y))
    (hlip : ∀ x ∈ X, ∀ y ∈ X, ‖M x - M y‖ ≤ L * ‖x - y‖) :
    ∃ y, SolvesModelVI X M y := by
  apply exists_solvesModelVI_of_projected_contracting X hne hcpt hconv M alpha halpha K
  refine ⟨hK, LipschitzWith.of_dist_le_mul fun x y ↦ ?_⟩
  simp only [Subtype.dist_eq, dist_eq_norm]
  let ux := x.1 - alpha • M x.1
  let uy := y.1 - alpha • M y.1
  have hproj := compactConvexProjection_dist_le X hne hcpt hconv ux uy
  have hsquare := forwardStep_norm_sq_le (le_of_lt halpha) hL0 hstrong hlip x.2 y.2
  change ‖compactConvexProjection X hne hcpt hconv ux -
      compactConvexProjection X hne hcpt hconv uy‖ ≤ (K : ℝ) * ‖x.1 - y.1‖
  apply hproj.trans
  have hright : 0 ≤ (K : ℝ) * ‖x.1 - y.1‖ :=
    mul_nonneg K.coe_nonneg (norm_nonneg _)
  apply (sq_le_sq₀ (norm_nonneg (ux - uy)) hright).mp
  calc
    ‖ux - uy‖ ^ 2 ≤
        (1 - 2 * alpha * mu + alpha ^ 2 * L ^ 2) * ‖x.1 - y.1‖ ^ 2 := by
      simpa [ux, uy] using hsquare
    _ ≤ (K : ℝ) ^ 2 * ‖x.1 - y.1‖ ^ 2 :=
      mul_le_mul_of_nonneg_right hrate (sq_nonneg _)
    _ = ((K : ℝ) * ‖x.1 - y.1‖) ^ 2 := by ring

/-- Compactness passage from solutions of all positive Tikhonov
regularizations to a solution of the original continuous VI. -/
theorem exists_solvesModelVI_of_vanishing_regularization
    (X : Set E) (hcpt : IsCompact X) (M : E → E)
    (hcont : ContinuousOn M X)
    (hreg : ∀ epsilon : ℝ, 0 < epsilon →
      ∃ y, SolvesModelVI X (fun u ↦ M u + epsilon • u) y) :
    ∃ y, SolvesModelVI X M y := by
  let epsilon : ℕ → ℝ := fun n ↦ 1 / ((n : ℝ) + 1)
  have hepsilon_pos : ∀ n, 0 < epsilon n := by
    intro n
    simp [epsilon]
    positivity
  choose y hy using fun n ↦ hreg (epsilon n) (hepsilon_pos n)
  obtain ⟨y₀, hy₀, phi, hphi, hy_tendsto⟩ := hcpt.tendsto_subseq (fun n ↦ (hy n).1)
  refine ⟨y₀, hy₀, ?_⟩
  intro z hz
  have hy_within : Tendsto (fun n ↦ y (phi n)) atTop (nhdsWithin y₀ X) :=
    tendsto_nhdsWithin_iff.mpr
      ⟨hy_tendsto, Eventually.of_forall fun n ↦ (hy (phi n)).1⟩
  have hM_within : Tendsto M (nhdsWithin y₀ X) (nhds (M y₀)) := hcont y₀ hy₀
  have hM_tendsto : Tendsto (fun n ↦ M (y (phi n))) atTop (nhds (M y₀)) :=
    hM_within.comp hy_within
  have hepsilon_tendsto : Tendsto (fun n ↦ epsilon (phi n)) atTop (nhds 0) := by
    exact tendsto_one_div_add_atTop_nhds_zero_nat.comp hphi.tendsto_atTop
  have hleft_tendsto : Tendsto
      (fun n ↦ inner ℝ
        (M (y (phi n)) + epsilon (phi n) • y (phi n))
        (z - y (phi n))) atTop
      (nhds (inner ℝ (M y₀) (z - y₀))) := by
    have hregterm : Tendsto
        (fun n ↦ epsilon (phi n) • y (phi n)) atTop (nhds (0 : E)) := by
      simpa using hepsilon_tendsto.smul hy_tendsto
    exact Filter.Tendsto.inner (by simpa using hM_tendsto.add hregterm)
      (tendsto_const_nhds.sub hy_tendsto)
  exact ge_of_tendsto' hleft_tendsto fun n ↦ (hy (phi n)).2 z hz

/-- A continuous locally Lipschitz monotone operator has a variational-
inequality solution on every nonempty compact convex feasible set.  The proof
uses projected contractions of positive Tikhonov regularizations and then the
preceding compactness limit, rather than a Brouwer axiom. -/
theorem continuous_monotone_vi_exists
    (X : Set E) (hne : X.Nonempty) (hcpt : IsCompact X) (hconv : Convex ℝ X)
    (M : E → E) (hcont : ContinuousOn M X) (hloc : LocallyLipschitzOn X M)
    (hmono : ∀ x ∈ X, ∀ y ∈ X,
      0 ≤ inner ℝ (M x - M y) (x - y)) :
    ∃ y, SolvesModelVI X M y := by
  apply exists_solvesModelVI_of_vanishing_regularization X hcpt M hcont
  intro epsilon hepsilon
  obtain ⟨L₀, hL₀⟩ := hloc.exists_lipschitzOnWith_of_compact hcpt
  let L : ℝ := (L₀ : ℝ) + epsilon
  have hLpos : 0 < L := by
    dsimp [L]
    positivity
  let alpha : ℝ := epsilon / L ^ 2
  have halpha : 0 < alpha := div_pos hepsilon (sq_pos_of_pos hLpos)
  let q : ℝ := 1 - epsilon ^ 2 / L ^ 2
  have hepsilon_le_L : epsilon ≤ L := by
    dsimp [L]
    exact le_add_of_nonneg_left L₀.coe_nonneg
  have hq_nonneg : 0 ≤ q := by
    dsimp [q]
    rw [sub_nonneg, div_le_one (sq_pos_of_pos hLpos)]
    exact (sq_le_sq₀ (le_of_lt hepsilon) (le_of_lt hLpos)).mpr hepsilon_le_L
  have hq_lt_one : q < 1 := by
    dsimp [q]
    have : 0 < epsilon ^ 2 / L ^ 2 := div_pos (sq_pos_of_pos hepsilon) (sq_pos_of_pos hLpos)
    linarith
  let K : NNReal := ⟨Real.sqrt q, Real.sqrt_nonneg q⟩
  have hKsq : (K : ℝ) ^ 2 = q := by
    change (Real.sqrt q) ^ 2 = q
    exact Real.sq_sqrt hq_nonneg
  have hK : K < 1 := by
    apply NNReal.coe_lt_coe.mp
    have hKnonneg : 0 ≤ (K : ℝ) := K.coe_nonneg
    norm_num only [NNReal.coe_one]
    nlinarith
  let N : E → E := fun u ↦ M u + epsilon • u
  have hstrongN : ∀ x ∈ X, ∀ y ∈ X,
      epsilon * ‖x - y‖ ^ 2 ≤ inner ℝ (N x - N y) (x - y) := by
    intro x hx y hy
    have hm := hmono x hx y hy
    dsimp [N]
    rw [show (M x + epsilon • x) - (M y + epsilon • y) =
      (M x - M y) + epsilon • (x - y) by module, inner_add_left,
      inner_smul_left, conj_trivial, real_inner_self_eq_norm_sq]
    linarith
  have hLipN : ∀ x ∈ X, ∀ y ∈ X, ‖N x - N y‖ ≤ L * ‖x - y‖ := by
    intro x hx y hy
    have hbase := hL₀.dist_le_mul x hx y hy
    simp only [dist_eq_norm] at hbase
    dsimp [N, L]
    rw [show (M x + epsilon • x) - (M y + epsilon • y) =
      (M x - M y) + epsilon • (x - y) by module]
    calc
      ‖(M x - M y) + epsilon • (x - y)‖ ≤
          ‖M x - M y‖ + ‖epsilon • (x - y)‖ := norm_add_le _ _
      _ ≤ (L₀ : ℝ) * ‖x - y‖ + epsilon * ‖x - y‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos hepsilon]
        exact add_le_add hbase le_rfl
      _ = ((L₀ : ℝ) + epsilon) * ‖x - y‖ := by ring
  have hrate : 1 - 2 * alpha * epsilon + alpha ^ 2 * L ^ 2 ≤ (K : ℝ) ^ 2 := by
    rw [hKsq]
    dsimp [alpha, q]
    field_simp
    ring_nf
    exact le_refl (L ^ 2 - epsilon ^ 2)
  exact exists_solvesModelVI_of_strong_monotone_lipschitz X hne hcpt hconv N
    epsilon L alpha K halpha (le_of_lt hLpos) hK hrate hstrongN hLipN

/-- Uniqueness of a VI solution for a strictly monotone model operator. -/
theorem solvesModelVI_unique {X : Set E} {M : E → E}
    (hstrict : ∀ x ∈ X, ∀ y ∈ X, x ≠ y →
      0 < inner ℝ (M x - M y) (x - y))
    {x y : E} (hx : SolvesModelVI X M x) (hy : SolvesModelVI X M y) : x = y := by
  by_contra hxy
  have h1 := hx.2 y hy.1
  have h2 := hy.2 x hx.1
  have hs := hstrict x hx.1 y hy.1 hxy
  rw [inner_sub_left] at hs
  have heq1 : inner ℝ (M x) (x - y) = -inner ℝ (M x) (y - x) := by
    rw [show x - y = -(y - x) by abel, inner_neg_right]
  rw [heq1] at hs
  linarith

end LeanArticleAudit.Pilot
