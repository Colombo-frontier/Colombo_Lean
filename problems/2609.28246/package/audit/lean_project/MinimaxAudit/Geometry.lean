import Mathlib

/-!
# Conditional geometric bridges for the minimax audit

The normal-cone argument here is a theorem in an arbitrary real inner product
space. Strong monotonicity at a saddle zero and membership of that zero in the
feasible set are explicit hypotheses. This file does NOT establish these
hypotheses for the manuscript's differentiated gated potential.

The perturbation theorem compares two scalar objective values. The numerical
lemmas verify the stated parameter choices. No theorem below claims a
formalized derivative construction or an oracle lower bound.
-/

namespace MinimaxAudit


section InnerProduct
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The manuscript's sign convention for the convex-analytic normal cone. -/
def IsNormalAt (Z : Set E) (z v : E) : Prop :=
  ∀ z' ∈ Z, inner ℝ v (z' - z) ≤ 0

/-- A feasible comparison point pairs nonnegatively with the outward normal. -/
theorem normal_pairing_nonneg {Z : Set E} {z zstar v : E}
    (hv : IsNormalAt Z z v) (hzstar : zstar ∈ Z) :
    0 ≤ inner ℝ v (z - zstar) := by
  have h := hv zstar hzstar
  have hsub : z - zstar = -(zstar - z) := by abel
  rw [hsub, inner_neg_right]
  linarith

/-- A contraction perturbation of the identity is strongly monotone. This
can be applied to the full saddle operator after proving the concrete rotated
gate-gradient perturbation is q-Lipschitz. -/
theorem contraction_residual_strong_monotone {T : E → E} {q lam : ℝ}
    (hlam : 0 ≤ lam)
    (hT : ∀ x y, ‖T x - T y‖ ≤ q * ‖x - y‖) (x y : E) :
    lam * (1 - q) * ‖x - y‖ ^ 2 ≤
      inner ℝ (lam • (x - T x) - lam • (y - T y)) (x - y) := by
  have hcs := real_inner_le_norm (T x - T y) (x - y)
  have hm := mul_le_mul_of_nonneg_right (hT x y) (norm_nonneg (x - y))
  have hi : inner ℝ (T x - T y) (x - y) ≤ q * ‖x - y‖ ^ 2 := by
    nlinarith
  have hscaled := mul_le_mul_of_nonneg_left hi hlam
  have heq : (x - T x) - (y - T y) = (x - y) - (T x - T y) := by abel
  rw [← smul_sub, heq, real_inner_smul_left, inner_sub_left,
    real_inner_self_eq_norm_sq]
  nlinarith

/-- A point admitting a full ambient ball has no nonzero outward normal. -/
theorem normal_zero_of_ball {Z : Set E} {z v : E} {r : ℝ}
    (hr : 0 < r) (hball : Metric.ball z r ⊆ Z)
    (hv : IsNormalAt Z z v) : v = 0 := by
  by_contra hvzero
  have hnv : 0 < ‖v‖ := norm_pos_iff.mpr hvzero
  let step : ℝ := r / (2 * ‖v‖)
  have hs : 0 < step := by dsimp [step]; positivity
  have hscale : step * ‖v‖ = r / 2 := by
    dsimp [step]
    field_simp
  have hmem : z + step • v ∈ Metric.ball z r := by
    rw [Metric.mem_ball, dist_eq_norm]
    simp only [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hs]
    rw [hscale]
    linarith
  have hnormal := hv (z + step • v) (hball hmem)
  simp only [add_sub_cancel_left, inner_smul_right, real_inner_self_eq_norm_sq] at hnormal
  have hpositive : 0 < step * ‖v‖ ^ 2 := mul_pos hs (sq_pos_of_pos hnv)
  linarith

/-- Manuscript lines 920--927. The estimate is pointwise in the normal vector,
so no attainment of a distance-to-normal-cone infimum is needed. -/
theorem strong_zero_normal_norm_bound {Z : Set E} {F : E → E}
    {z zstar v : E} {mu : ℝ}
    (hzstar : zstar ∈ Z) (hzero : F zstar = 0)
    (hstrong : mu * ‖z - zstar‖ ^ 2 ≤
      inner ℝ (F z - F zstar) (z - zstar))
    (hv : IsNormalAt Z z v) :
    mu * ‖z - zstar‖ ≤ ‖F z + v‖ := by
  have hnormal := normal_pairing_nonneg hv hzstar
  have hstrong' : mu * ‖z - zstar‖ ^ 2 ≤
      inner ℝ (F z) (z - zstar) := by
    simpa [hzero] using hstrong
  have hpair : mu * ‖z - zstar‖ ^ 2 ≤
      inner ℝ (F z + v) (z - zstar) := by
    rw [inner_add_left]
    linarith
  have hcs := real_inner_le_norm (F z + v) (z - zstar)
  by_cases hd : ‖z - zstar‖ = 0
  · simp [hd]
  · have hdpos : 0 < ‖z - zstar‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hd)
    nlinarith

/- An inner zero and a boundary block are separated by seven eighths radius. -/
omit [InnerProductSpace ℝ E] in
theorem boundary_distance_lower {z zstar : E} {R : ℝ}
    (hboundary : ‖z‖ = R) (hinner : ‖zstar‖ ≤ R / 8) :
    7 * R / 8 ≤ ‖z - zstar‖ := by
  have h := norm_sub_norm_le z zstar
  rw [hboundary] at h
  linarith

/-- The normal estimate combined with an independent distance bound. -/
theorem strong_zero_normal_uniform_bound {Z : Set E} {F : E → E}
    {z zstar v : E} {mu d : ℝ}
    (hmu : 0 ≤ mu) (hzstar : zstar ∈ Z) (hzero : F zstar = 0)
    (hstrong : mu * ‖z - zstar‖ ^ 2 ≤
      inner ℝ (F z - F zstar) (z - zstar))
    (hv : IsNormalAt Z z v) (hd : d ≤ ‖z - zstar‖) :
    mu * d ≤ ‖F z + v‖ := by
  exact (mul_le_mul_of_nonneg_left hd hmu).trans
    (strong_zero_normal_norm_bound hzstar hzero hstrong hv)

/- The outer shell begins at R-2κR; an R/8-interior saddle is at least R/2 away
provided κ≤3/16. The actual manuscript choice κ=1/1024 meets this condition. -/
omit [InnerProductSpace ℝ E] in
theorem shell_distance_lower {z zstar : E} {R kappa : ℝ}
    (hR : 0 ≤ R) (hk : kappa ≤ 3 / 16)
    (hshell : R - 2 * kappa * R ≤ ‖z‖)
    (hinner : ‖zstar‖ ≤ R / 8) :
    R / 2 ≤ ‖z - zstar‖ := by
  have h := norm_sub_norm_le z zstar
  have hkR := mul_le_mul_of_nonneg_right hk hR
  nlinarith

/- A nonnegative strong-convexity error estimate gives the shell gap scale.
The variational gap inequality is explicit, rather than built into a premise
named after the desired conclusion. -/
omit [InnerProductSpace ℝ E] in
theorem shell_gap_lower {x xstar : E} {gap mu R : ℝ}
    (hmu : 0 ≤ mu) (hR : 0 ≤ R)
    (hdistance : R / 2 ≤ ‖x - xstar‖)
    (hgap : mu / 2 * ‖x - xstar‖ ^ 2 ≤ gap) :
    mu * R ^ 2 / 8 ≤ gap := by
  have hn := norm_nonneg (x - xstar)
  have hsquare : R ^ 2 / 4 ≤ ‖x - xstar‖ ^ 2 := by nlinarith
  have hmul := mul_le_mul_of_nonneg_left hsquare (show 0 ≤ mu / 2 by positivity)
  nlinarith

/-- All vectors obtained by adding a feasible normal correction. -/
def normalCorrections (Z : Set E) (F : E → E) (z : E) : Set E :=
  {u | ∃ v, IsNormalAt Z z v ∧ u = F z + v}

/-- This set is nonempty because the zero vector is always a normal. -/
theorem normalCorrections_nonempty (Z : Set E) (F : E → E) (z : E) :
    (normalCorrections Z F z).Nonempty := by
  refine ⟨F z, 0, ?_, by simp⟩
  intro z' hz'
  simp

/-- Actual distance-to-normal-cone tangent residual, with the manuscript sign. -/
noncomputable def auditedTangentResidual (Z : Set E) (F : E → E) (z : E) : ℝ :=
  Metric.infDist 0 (normalCorrections Z F z)

/-- At an ambient interior point, the actual tangent residual is exactly the
operator norm; this closes the normal-cone part of the manuscript interior case. -/
theorem tangent_residual_eq_norm_of_ball {Z : Set E} {F : E → E}
    {z : E} {r : ℝ} (hr : 0 < r) (hball : Metric.ball z r ⊆ Z) :
    auditedTangentResidual Z F z = ‖F z‖ := by
  have hset : normalCorrections Z F z = {F z} := by
    ext u
    constructor
    · rintro ⟨v, hv, rfl⟩
      have hz := normal_zero_of_ball hr hball hv
      simp [hz]
    · intro hu
      have heq : u = F z := Set.mem_singleton_iff.mp hu
      refine ⟨0, ?_, ?_⟩
      · intro z' hz'
        simp
      · simpa using heq
  simp [auditedTangentResidual, hset]

/-- Passing the uniform correction estimate to the actual infimum, without
assuming that an optimal normal correction is attained. -/
theorem strong_zero_tangent_residual_bound {Z : Set E} {F : E → E}
    {z zstar : E} {mu d : ℝ}
    (hmu : 0 ≤ mu) (hzstar : zstar ∈ Z) (hzero : F zstar = 0)
    (hstrong : mu * ‖z - zstar‖ ^ 2 ≤
      inner ℝ (F z - F zstar) (z - zstar))
    (hd : d ≤ ‖z - zstar‖) :
    mu * d ≤ auditedTangentResidual Z F z := by
  apply (Metric.le_infDist (normalCorrections_nonempty Z F z)).2
  intro u hu
  obtain ⟨v, hv, rfl⟩ := hu
  simpa only [dist_zero_left] using
    strong_zero_normal_uniform_bound hmu hzstar hzero hstrong hv hd

end InnerProduct

section SaddleGap

variable {P Q : Type*}

/-- All differences used to compare primal and dual feasible points. -/
def saddleDifferences (X : Set P) (Y : Set Q) (phi : P → Q → ℝ)
    (x : P) (y : Q) : Set ℝ :=
  {d | ∃ x' ∈ X, ∃ y' ∈ Y, d = phi x y' - phi x' y}

/-- Supremum form of the product saddle gap. The boundedness hypothesis must be
supplied when using supremum inequalities; compactness is not silently assumed. -/
noncomputable def auditedSaddleGap (X : Set P) (Y : Set Q)
    (phi : P → Q → ℝ) (x : P) (y : Q) : ℝ :=
  sSup (saddleDifferences X Y phi x y)

/-- Every feasible primal/dual comparison is bounded by the actual supremum. -/
theorem comparison_le_saddleGap {X : Set P} {Y : Set Q} {phi : P → Q → ℝ}
    {x x' : P} {y y' : Q}
    (hbounded : BddAbove (saddleDifferences X Y phi x y))
    (hx' : x' ∈ X) (hy' : y' ∈ Y) :
    phi x y' - phi x' y ≤ auditedSaddleGap X Y phi x y := by
  exact le_csSup hbounded ⟨x', hx', y', hy', rfl⟩

/-- Inner-region robustness at two feasible comparison points. Uniform
potential estimates enter only through the two explicit absolute-value bounds. -/
theorem saddleGap_stability_at_witness {X : Set P} {Y : Set Q}
    {phi phi0 : P → Q → ℝ} {x x' : P} {y y' : Q} {lower delta : ℝ}
    (hbounded : BddAbove (saddleDifferences X Y phi x y))
    (hx' : x' ∈ X) (hy' : y' ∈ Y)
    (ha : |phi x y' - phi0 x y'| ≤ delta)
    (hb : |phi x' y - phi0 x' y| ≤ delta)
    (hideal : lower ≤ phi0 x y' - phi0 x' y) :
    lower - 2 * delta ≤ auditedSaddleGap X Y phi x y := by
  have hcomparison := comparison_le_saddleGap hbounded hx' hy'
  obtain ⟨ha1, ha2⟩ := abs_le.mp ha
  obtain ⟨hb1, hb2⟩ := abs_le.mp hb
  linarith

variable [NormedAddCommGroup P] [NormedAddCommGroup Q]

/-- Strong primal and dual saddle estimates combine into a genuine product-gap
bound. These two analytic inequalities are explicit hypotheses and still need
to be instantiated for the manuscript's smooth potential. -/
theorem strong_saddle_gap_lower {X : Set P} {Y : Set Q} {phi : P → Q → ℝ}
    {x xstar : P} {y ystar : Q} {mu : ℝ}
    (hbounded : BddAbove (saddleDifferences X Y phi x y))
    (hxstar : xstar ∈ X) (hystar : ystar ∈ Y)
    (hprimal : phi xstar ystar + mu / 2 * ‖x - xstar‖ ^ 2 ≤ phi x ystar)
    (hdual : phi xstar y + mu / 2 * ‖y - ystar‖ ^ 2 ≤ phi xstar ystar) :
    mu / 2 * (‖x - xstar‖ ^ 2 + ‖y - ystar‖ ^ 2) ≤
      auditedSaddleGap X Y phi x y := by
  have hcomparison := comparison_le_saddleGap hbounded hxstar hystar
  linarith

/-- A primal shell is enough for the μR²/8 gap obstruction. The dual shell
follows by exchanging the two explicit squared-distance terms. -/
theorem primal_shell_saddle_gap {X : Set P} {Y : Set Q} {phi : P → Q → ℝ}
    {x xstar : P} {y ystar : Q} {mu R : ℝ}
    (hmu : 0 ≤ mu) (hR : 0 ≤ R)
    (hbounded : BddAbove (saddleDifferences X Y phi x y))
    (hxstar : xstar ∈ X) (hystar : ystar ∈ Y)
    (hprimal : phi xstar ystar + mu / 2 * ‖x - xstar‖ ^ 2 ≤ phi x ystar)
    (hdual : phi xstar y + mu / 2 * ‖y - ystar‖ ^ 2 ≤ phi xstar ystar)
    (hdistance : R / 2 ≤ ‖x - xstar‖) :
    mu * R ^ 2 / 8 ≤ auditedSaddleGap X Y phi x y := by
  have h := strong_saddle_gap_lower hbounded hxstar hystar hprimal hdual
  have hdualnonneg : 0 ≤ mu / 2 * ‖y - ystar‖ ^ 2 := by positivity
  have hone : mu / 2 * ‖x - xstar‖ ^ 2 ≤ auditedSaddleGap X Y phi x y := by
    nlinarith
  have hsquare : R ^ 2 / 4 ≤ ‖x - xstar‖ ^ 2 := by
    have hn := norm_nonneg (x - xstar)
    nlinarith
  have hmul := mul_le_mul_of_nonneg_left hsquare (show 0 ≤ mu / 2 by positivity)
  nlinarith

/-- The analogous μR²/8 estimate for an outer dual block. -/
theorem dual_shell_saddle_gap {X : Set P} {Y : Set Q} {phi : P → Q → ℝ}
    {x xstar : P} {y ystar : Q} {mu R : ℝ}
    (hmu : 0 ≤ mu) (hR : 0 ≤ R)
    (hbounded : BddAbove (saddleDifferences X Y phi x y))
    (hxstar : xstar ∈ X) (hystar : ystar ∈ Y)
    (hprimal : phi xstar ystar + mu / 2 * ‖x - xstar‖ ^ 2 ≤ phi x ystar)
    (hdual : phi xstar y + mu / 2 * ‖y - ystar‖ ^ 2 ≤ phi xstar ystar)
    (hdistance : R / 2 ≤ ‖y - ystar‖) :
    mu * R ^ 2 / 8 ≤ auditedSaddleGap X Y phi x y := by
  have h := strong_saddle_gap_lower hbounded hxstar hystar hprimal hdual
  have hprimalnonneg : 0 ≤ mu / 2 * ‖x - xstar‖ ^ 2 := by positivity
  have hone : mu / 2 * ‖y - ystar‖ ^ 2 ≤ auditedSaddleGap X Y phi x y := by
    nlinarith
  have hsquare : R ^ 2 / 4 ≤ ‖y - ystar‖ ^ 2 := by
    have hn := norm_nonneg (y - ystar)
    nlinarith
  have hmul := mul_le_mul_of_nonneg_left hsquare (show 0 ≤ mu / 2 by positivity)
  nlinarith

end SaddleGap

/-- A direct two-point comparison loses at most twice a uniform perturbation. -/
theorem gap_two_point_perturbation {gap a b a0 b0 delta : ℝ}
    (hgap : a - b ≤ gap)
    (ha : |a - a0| ≤ delta) (hb : |b - b0| ≤ delta) :
    a0 - b0 - 2 * delta ≤ gap := by
  obtain ⟨ha1, ha2⟩ := abs_le.mp ha
  obtain ⟨hb1, hb2⟩ := abs_le.mp hb
  linarith

/-- Universal parameters from the manuscript. -/
noncomputable def geometryKappa : ℝ := 1 / 1024

noncomputable def geometryEta : ℝ := 1 / 16777216

/-- c₁=1/16 is valid with the looser perturbation coefficient 18. -/
theorem explicit_inner_gap_constant (t : ℝ) (ht : 0 ≤ t) :
    t / 16 ≤ t / 8 - 18 * (geometryEta / geometryKappa) * t := by
  norm_num [geometryEta, geometryKappa]
  linarith

/-- The shell coefficient is stronger than c₁=1/16. -/
theorem explicit_outer_gap_constant (t : ℝ) (ht : 0 ≤ t) :
    t / 16 ≤ t / (32 * geometryKappa ^ 2) := by
  norm_num [geometryKappa]
  linarith

/-- c₀=1/2 is valid after removing the common nonnegative factor λR/n. -/
theorem explicit_boundary_residual_constant (t : ℝ) (ht : 0 ≤ t) :
    geometryKappa * t / 2 ≤ 7 * t / 32 := by
  norm_num [geometryKappa]
  linarith

/-- The gated residual numerator is at least half the seed. -/
theorem explicit_gated_residual_margin (c : ℝ) (hc : 0 ≤ c) :
    c / 2 ≤ (3 / 4 - 2 * geometryEta) * c := by
  norm_num [geometryEta]
  linarith

/-- The explicit numerical inner estimate gives c₁=1/16. -/
theorem inner_gap_from_explicit_estimate {gap t : ℝ} (ht : 0 ≤ t)
    (hgap : t / 8 - 18 * (geometryEta / geometryKappa) * t ≤ gap) :
    t / 16 ≤ gap :=
  (explicit_inner_gap_constant t ht).trans hgap

/-- The explicit shell estimate gives the same c₁=1/16. -/
theorem outer_gap_from_explicit_estimate {gap t : ℝ} (ht : 0 ≤ t)
    (hgap : t / (32 * geometryKappa ^ 2) ≤ gap) :
    t / 16 ≤ gap :=
  (explicit_outer_gap_constant t ht).trans hgap

end MinimaxAudit
