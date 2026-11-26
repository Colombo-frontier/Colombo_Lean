import LeanArticleAudit.Pilot.ModelExistence

/-!
# Analysis-only constrained resolvent for a monotone VI

The resolvent is defined by unique choice from a theorem, not supplied as an
algorithmic certificate.  It is therefore suitable for the upper-bound
analysis without pretending that the exact resolvent is an oracle operation.
-/

open Set Filter Topology
open scoped RealInnerProductSpace

namespace LeanArticleAudit.Pilot

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- The regularized operator whose VI solution is the constrained resolvent. -/
def resolventOperator (F : E → E) (eta : ℝ) (center z : E) : E :=
  F z + (eta⁻¹) • (z - center)

theorem exists_resolventVI
    (X : Set E) (hne : X.Nonempty) (hcpt : IsCompact X) (hconv : Convex ℝ X)
    (F : E → E) (hcont : ContinuousOn F X) (hloc : LocallyLipschitzOn X F)
    (hmono : ∀ x ∈ X, ∀ y ∈ X,
      0 ≤ inner ℝ (F x - F y) (x - y))
    (eta : ℝ) (heta : 0 < eta) (center : E) :
    ∃ y, SolvesModelVI X (resolventOperator F eta center) y := by
  have hinv : 0 < eta⁻¹ := inv_pos.mpr heta
  apply continuous_monotone_vi_exists X hne hcpt hconv
    (resolventOperator F eta center)
  · exact hcont.add
      ((continuous_const.smul (continuous_id.sub continuous_const)).continuousOn)
  · intro x hx
    obtain ⟨K, t, ht, hKt⟩ := hloc hx
    refine ⟨Real.toNNReal ((K : ℝ) + eta⁻¹), t, ht,
      LipschitzOnWith.of_dist_le' fun u hu v hv ↦ ?_⟩
    simp only [dist_eq_norm]
    dsimp [resolventOperator]
    rw [show (F u + eta⁻¹ • (u - center)) - (F v + eta⁻¹ • (v - center)) =
      (F u - F v) + eta⁻¹ • (u - v) by module]
    calc
      ‖(F u - F v) + eta⁻¹ • (u - v)‖ ≤
          ‖F u - F v‖ + ‖eta⁻¹ • (u - v)‖ := norm_add_le _ _
      _ ≤ (K : ℝ) * ‖u - v‖ + eta⁻¹ * ‖u - v‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos hinv]
        exact add_le_add (by simpa [dist_eq_norm] using hKt.dist_le_mul u hu v hv) le_rfl
      _ = ((K : ℝ) + eta⁻¹) * ‖u - v‖ := by ring
  · intro x hx y hy
    have hm := hmono x hx y hy
    dsimp [resolventOperator]
    rw [show (F x + eta⁻¹ • (x - center)) - (F y + eta⁻¹ • (y - center)) =
      (F x - F y) + eta⁻¹ • (x - y) by module, inner_add_left,
      inner_smul_left, conj_trivial, real_inner_self_eq_norm_sq]
    positivity

theorem resolventVI_unique
    {X : Set E} {F : E → E}
    (hmono : ∀ x ∈ X, ∀ y ∈ X,
      0 ≤ inner ℝ (F x - F y) (x - y))
    {eta : ℝ} (heta : 0 < eta) (center : E)
    {x y : E}
    (hx : SolvesModelVI X (resolventOperator F eta center) x)
    (hy : SolvesModelVI X (resolventOperator F eta center) y) : x = y := by
  apply solvesModelVI_unique (X := X) (M := resolventOperator F eta center) ?_ hx hy
  intro u hu v hv huv
  have hm := hmono u hu v hv
  have hnorm : 0 < ‖u - v‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr huv))
  have hinv : 0 < eta⁻¹ := inv_pos.mpr heta
  dsimp [resolventOperator]
  rw [show (F u + eta⁻¹ • (u - center)) - (F v + eta⁻¹ • (v - center)) =
    (F u - F v) + eta⁻¹ • (u - v) by module, inner_add_left,
    inner_smul_left, conj_trivial, real_inner_self_eq_norm_sq]
  positivity

/-- The exact constrained resolvent, used only as a mathematical object. -/
noncomputable def resolventPoint
    (X : Set E) (hne : X.Nonempty) (hcpt : IsCompact X) (hconv : Convex ℝ X)
    (F : E → E) (hcont : ContinuousOn F X) (hloc : LocallyLipschitzOn X F)
    (hmono : ∀ x ∈ X, ∀ y ∈ X,
      0 ≤ inner ℝ (F x - F y) (x - y))
    (eta : ℝ) (heta : 0 < eta) (center : E) : E :=
  Classical.choose (exists_resolventVI X hne hcpt hconv F hcont hloc hmono eta heta center)

theorem resolventPoint_spec
    (X : Set E) (hne : X.Nonempty) (hcpt : IsCompact X) (hconv : Convex ℝ X)
    (F : E → E) (hcont : ContinuousOn F X) (hloc : LocallyLipschitzOn X F)
    (hmono : ∀ x ∈ X, ∀ y ∈ X,
      0 ≤ inner ℝ (F x - F y) (x - y))
    (eta : ℝ) (heta : 0 < eta) (center : E) :
    SolvesModelVI X (resolventOperator F eta center)
      (resolventPoint X hne hcpt hconv F hcont hloc hmono eta heta center) :=
  Classical.choose_spec
    (exists_resolventVI X hne hcpt hconv F hcont hloc hmono eta heta center)

/-- Firm nonexpansiveness of the constrained resolvent. -/
theorem resolventPoint_firmly_nonexpansive
    (X : Set E) (hne : X.Nonempty) (hcpt : IsCompact X) (hconv : Convex ℝ X)
    (F : E → E) (hcont : ContinuousOn F X) (hloc : LocallyLipschitzOn X F)
    (hmono : ∀ x ∈ X, ∀ y ∈ X,
      0 ≤ inner ℝ (F x - F y) (x - y))
    (eta : ℝ) (heta : 0 < eta) (a b : E) :
    ‖resolventPoint X hne hcpt hconv F hcont hloc hmono eta heta a -
        resolventPoint X hne hcpt hconv F hcont hloc hmono eta heta b‖ ^ 2 ≤
      inner ℝ (a - b)
        (resolventPoint X hne hcpt hconv F hcont hloc hmono eta heta a -
          resolventPoint X hne hcpt hconv F hcont hloc hmono eta heta b) := by
  let u := resolventPoint X hne hcpt hconv F hcont hloc hmono eta heta a
  let v := resolventPoint X hne hcpt hconv F hcont hloc hmono eta heta b
  have hu := resolventPoint_spec X hne hcpt hconv F hcont hloc hmono eta heta a
  have hv := resolventPoint_spec X hne hcpt hconv F hcont hloc hmono eta heta b
  change ‖u - v‖ ^ 2 ≤ inner ℝ (a - b) (u - v)
  change SolvesModelVI X (resolventOperator F eta a) u at hu
  change SolvesModelVI X (resolventOperator F eta b) v at hv
  have h1 := hu.2 v hv.1
  have h2 := hv.2 u hu.1
  have hm := hmono u hu.1 v hv.1
  have hF : inner ℝ (F u) (v - u) + inner ℝ (F v) (u - v) =
      -inner ℝ (F u - F v) (u - v) := by
    rw [show v - u = -(u - v) by abel, inner_neg_right, inner_sub_left]
    ring
  have hreg : inner ℝ (u - a) (v - u) + inner ℝ (v - b) (u - v) =
      -‖u - v‖ ^ 2 + inner ℝ (a - b) (u - v) := by
    rw [show v - u = -(u - v) by abel, inner_neg_right]
    calc
      -inner ℝ (u - a) (u - v) + inner ℝ (v - b) (u - v) =
          inner ℝ (v - b) (u - v) - inner ℝ (u - a) (u - v) := by ring
      _ = inner ℝ ((v - b) - (u - a)) (u - v) := by
        simp only [inner_sub_left]
      _ = inner ℝ (-(u - v) + (a - b)) (u - v) := by
        rw [show (v - b) - (u - a) = -(u - v) + (a - b) by abel]
      _ = -‖u - v‖ ^ 2 + inner ℝ (a - b) (u - v) := by
        rw [inner_add_left, inner_neg_left, real_inner_self_eq_norm_sq]
  have hsum : 0 ≤ inner ℝ (resolventOperator F eta a u) (v - u) +
      inner ℝ (resolventOperator F eta b v) (u - v) := add_nonneg h1 h2
  dsimp [resolventOperator] at hsum
  simp only [inner_add_left, inner_smul_left, conj_trivial] at hsum
  have hrearrange :
      inner ℝ (F u) (v - u) + eta⁻¹ * inner ℝ (u - a) (v - u) +
          (inner ℝ (F v) (u - v) + eta⁻¹ * inner ℝ (v - b) (u - v)) =
        (inner ℝ (F u) (v - u) + inner ℝ (F v) (u - v)) +
          eta⁻¹ * (inner ℝ (u - a) (v - u) + inner ℝ (v - b) (u - v)) := by
    ring
  rw [hrearrange, hF, hreg] at hsum
  have hinv : 0 < eta⁻¹ := inv_pos.mpr heta
  nlinarith

/-- VI solutions are exactly the fixed points of every positive constrained
resolvent. -/
theorem solvesModelVI_iff_resolventPoint_fixed
    (X : Set E) (hne : X.Nonempty) (hcpt : IsCompact X) (hconv : Convex ℝ X)
    (F : E → E) (hcont : ContinuousOn F X) (hloc : LocallyLipschitzOn X F)
    (hmono : ∀ x ∈ X, ∀ y ∈ X,
      0 ≤ inner ℝ (F x - F y) (x - y))
    (eta : ℝ) (heta : 0 < eta) (y : E) :
    SolvesModelVI X F y ↔
      resolventPoint X hne hcpt hconv F hcont hloc hmono eta heta y = y := by
  constructor
  · intro hy
    have hp := resolventPoint_spec X hne hcpt hconv F hcont hloc hmono eta heta y
    have hyreg : SolvesModelVI X (resolventOperator F eta y) y := by
      refine ⟨hy.1, ?_⟩
      intro z hz
      simpa [resolventOperator] using hy.2 z hz
    exact resolventVI_unique hmono heta y hp hyreg
  · intro hfix
    have hp := resolventPoint_spec X hne hcpt hconv F hcont hloc hmono eta heta y
    rw [hfix] at hp
    refine ⟨hp.1, ?_⟩
    intro z hz
    simpa [resolventOperator] using hp.2 z hz

end
end LeanArticleAudit.Pilot
