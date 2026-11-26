import VIReference.Pilot.Resolvent
import VIReference.Pilot.UpperRestart

/-!
# Computed approximate-proximal certificates

The resolvent below is analysis-only.  The hypotheses concern the actually
computed point, normal, and regularized residual.
-/

open Set
open scoped RealInnerProductSpace

namespace VIReference.Pilot

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem approximateProximal_core
    (data : VIPublicData E) (F : E → E)
    (hcont : ContinuousOn F data.X) (hloc : LocallyLipschitzOn data.X F)
    (hmono : ∀ x ∈ data.X, ∀ y ∈ data.X,
      0 ≤ inner ℝ (F x - F y) (x - y))
    (z yHat : E) (hz : z ∈ data.X) (hy : yHat ∈ data.X)
    (n : E) (hn : n ∈ normalCone data.X yHat)
    (eta delta : ℝ) (heta : 0 < eta) (hdelta : 0 ≤ delta)
    (hcert : ‖F yHat + n + (eta⁻¹) • (yHat - z)‖ ≤ delta) :
    let yStar := resolventPoint data.X data.X_nonempty data.X_compact
      data.X_convex F hcont hloc hmono eta heta z
    ‖yHat - yStar‖ ≤ eta * delta ∧
    tangentResidual data F yHat ≤ ‖z - yStar‖ / eta + 2 * delta := by
  let yStar := resolventPoint data.X data.X_nonempty data.X_compact
    data.X_convex F hcont hloc hmono eta heta z
  let G := resolventOperator F eta z
  have hyStar : IsVISolution data G yStar := by
    exact resolventPoint_spec data.X data.X_nonempty data.X_compact
      data.X_convex F hcont hloc hmono eta heta z
  have hstrong : StronglyMonotoneOn data G eta⁻¹ := by
    intro x hx y hy'
    have hm := hmono x hx y hy'
    dsimp [G, resolventOperator]
    rw [show (F x + eta⁻¹ • (x - z)) - (F y + eta⁻¹ • (y - z)) =
      (F x - F y) + eta⁻¹ • (x - y) by module,
      inner_add_left, inner_smul_left, conj_trivial, real_inner_self_eq_norm_sq]
    linarith
  let cert : EvaluatedNormalCertificate data := {
    point := ⟨yHat, hy⟩
    normal := n
    value := G yHat }
  have hverified : cert.IsVerifiedFor data G delta := by
    refine ⟨hn, rfl, ?_⟩
    change ‖G yHat + n‖ ≤ delta
    rw [show G yHat + n = F yHat + n + eta⁻¹ • (yHat - z) by
      simp [G, resolventOperator]
      abel]
    exact hcert
  have hdistanceScaled := strong_certificate_distance data G eta⁻¹ delta
    (inv_pos.mpr heta) hstrong yStar hyStar cert hverified
  have hdistanceScaled' : eta⁻¹ * ‖yHat - yStar‖ ≤ delta :=
    hdistanceScaled.trans hverified.2.2
  have hetaInv : eta * eta⁻¹ = 1 := mul_inv_cancel₀ heta.ne'
  have hdistance : ‖yHat - yStar‖ ≤ eta * delta := by
    calc
      ‖yHat - yStar‖ = eta * (eta⁻¹ * ‖yHat - yStar‖) := by
        rw [← mul_assoc, hetaInv, one_mul]
      _ ≤ eta * delta := mul_le_mul_of_nonneg_left hdistanceScaled' heta.le
  refine ⟨hdistance, ?_⟩
  have hmem : F yHat + n ∈ (fun m ↦ F yHat + m) '' normalCone data.X yHat :=
    ⟨n, hn, rfl⟩
  have htan : tangentResidual data F yHat ≤ ‖F yHat + n‖ := by
    calc
      tangentResidual data F yHat ≤ dist 0 (F yHat + n) :=
        Metric.infDist_le_dist_of_mem hmem
      _ = ‖F yHat + n‖ := dist_zero_left _
  have hdecomp : F yHat + n =
      (F yHat + n + eta⁻¹ • (yHat - z)) - eta⁻¹ • (yHat - z) := by
    abel
  have hinv0 : 0 ≤ eta⁻¹ := (inv_pos.mpr heta).le
  have hzy : ‖yHat - z‖ ≤ ‖z - yStar‖ + ‖yHat - yStar‖ := by
    rw [show yHat - z = (yHat - yStar) + (yStar - z) by abel]
    exact (norm_add_le _ _).trans_eq (by rw [add_comm, norm_sub_rev yStar z])
  calc
    tangentResidual data F yHat ≤ ‖F yHat + n‖ := htan
    _ = ‖(F yHat + n + eta⁻¹ • (yHat - z)) -
        eta⁻¹ • (yHat - z)‖ := congrArg norm hdecomp
    _ ≤ ‖F yHat + n + eta⁻¹ • (yHat - z)‖ +
        ‖eta⁻¹ • (yHat - z)‖ := by
      exact norm_sub_le _ _
    _ = ‖F yHat + n + eta⁻¹ • (yHat - z)‖ +
        eta⁻¹ * ‖yHat - z‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hinv0]
    _ ≤ delta + eta⁻¹ * (‖z - yStar‖ + ‖yHat - yStar‖) := by
      gcongr
    _ ≤ delta + eta⁻¹ * (‖z - yStar‖ + eta * delta) := by
      gcongr
    _ = ‖z - yStar‖ / eta + 2 * delta := by
      field_simp [heta.ne']
      ring

/-- Source-facing first two clauses of `prop:approx-recovery`.  The final
model-correction specialization is added after the certified model selector. -/
def ApproximateProximalCoreClaim : Prop :=
  ∀ (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (data : VIPublicData E) (F : E → E)
    (hcont : ContinuousOn F data.X) (hloc : LocallyLipschitzOn data.X F)
    (hmono : ∀ x ∈ data.X, ∀ y ∈ data.X,
      0 ≤ inner ℝ (F x - F y) (x - y))
    (z yHat : E), z ∈ data.X → yHat ∈ data.X →
    ∀ n, n ∈ normalCone data.X yHat →
    ∀ eta delta, ∀ heta : 0 < eta, 0 ≤ delta →
    ‖F yHat + n + eta⁻¹ • (yHat - z)‖ ≤ delta →
    let yStar := resolventPoint data.X data.X_nonempty data.X_compact
      data.X_convex F hcont hloc hmono eta heta z
    ‖yHat - yStar‖ ≤ eta * delta ∧
    tangentResidual data F yHat ≤ ‖z - yStar‖ / eta + 2 * delta

theorem approximateProximalCoreClaim_proof : ApproximateProximalCoreClaim.{u} := by
  intro E _ _ _ data F hcont hloc hmono z yHat hz hy n hn eta delta heta hdelta hcert
  exact approximateProximal_core data F hcont hloc hmono z yHat hz hy n hn
    eta delta heta hdelta hcert

end

end VIReference.Pilot
