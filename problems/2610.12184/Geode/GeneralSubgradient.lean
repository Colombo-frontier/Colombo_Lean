import Geode.ProximalMinimizer
import Geode.ProximalSupport
import Geode.JointLogContinuity
import Geode.SubdifferentialGeometry
import Mathlib.Topology.MetricSpace.Sequences

/-! Existence and canonical minimum-norm selection of global subgradients for
every globally geodesically convex Lipschitz function. -/
namespace Geode.Lorentz

open Set Filter
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem global_subgradient_exists {f : Point E → ℝ} {L : ℝ}
    (hf : GConvexFunction f) (hL : 0 ≤ L)
    (hlip : ∀ x y, |f x - f y| ≤ L * dist x y) (x : Point E) :
    ∃ v : Ambient E, IsSubgradient f x v := by
  classical
  have hex : ∀ n : ℕ, ∃ p : Point E, ∀ y,
      f p + ((n : ℝ) + 1) * dist p x ^ 2 ≤ f y + ((n : ℝ) + 1) * dist y x ^ 2 := by
    intro n
    exact proximal_minimizer_exists hL (by have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n; linarith) hlip x
  choose p hp using hex
  let g : ℕ → Ambient E := fun n => (2 * ((n : ℝ) + 1)) • logMap (p n) x
  have hsub : ∀ n, IsSubgradient f (p n) (g n) :=
    fun n => proximal_isSubgradient hf x (p n) ((n : ℝ) + 1) (hp n)
  have hdist : ∀ n, dist (p n) x ≤ L / ((n : ℝ) + 1) := by
    intro n
    exact proximal_distance_bound hL (by positivity) hlip x (p n) (hp n)
  have hdistL : ∀ n, dist (p n) x ≤ L := by
    intro n
    exact (hdist n).trans (div_le_self hL (by have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n; linarith))
  have hpconv : Tendsto p atTop (𝓝 x) := by
    apply tendsto_iff_dist_tendsto_zero.mpr
    apply squeeze_zero (fun _ => dist_nonneg) hdist
    simpa only [mul_zero, mul_one_div] using
      (tendsto_const_nhds (x := L)).mul tendsto_one_div_add_atTop_nhds_zero_nat
  let C := Real.cosh (dist (origin : Point E) x + L)
  have htime : ∀ n, (p n).val.1 ≤ C := by
    intro n
    rw [← cosh_dist_origin (p n)]
    apply Real.cosh_strictMonoOn.monotoneOn dist_nonneg
      (show (0 : ℝ) ≤ dist (origin : Point E) x + L from add_nonneg dist_nonneg hL)
    exact (dist_triangle origin x (p n)).trans
      (add_le_add_left (by simpa only [dist_comm] using hdistL n) _)
  have hnorm : ∀ n, ‖g n‖ ≤ C * L := by
    intro n
    calc
      ‖g n‖ ≤ (p n).val.1 * tangentNorm (g n) := ambient_norm_le_tangent (p n) (hsub n).1
      _ ≤ (p n).val.1 * L := mul_le_mul_of_nonneg_left
        (subgradient_norm_le hL hlip (hsub n)) (p n).future.le
      _ ≤ C * L := mul_le_mul_of_nonneg_right (htime n) hL
  have hmem : ∀ n, g n ∈ Metric.closedBall (0 : Ambient E) (C * L) := by
    intro n
    simpa only [Metric.mem_closedBall, dist_zero_right] using hnorm n
  obtain ⟨v, _, φ, hφ, hv⟩ := (isCompact_closedBall (0 : Ambient E) (C * L)).tendsto_subseq hmem
  refine ⟨v, ?_⟩
  exact isSubgradient_of_tendsto (continuous_of_lipschitz_bound hL hlip)
    (hpconv.comp hφ.tendsto_atTop) hv (fun n => hsub (φ n))

/-- The complete general selection lemma from the manuscript. -/
theorem subgradient_selection {f : Point E → ℝ} {L : ℝ}
    (hf : GConvexFunction f) (hL : 0 ≤ L)
    (hlip : ∀ x y, |f x - f y| ≤ L * dist x y) (x : Point E) :
    (subdifferential f x).Nonempty ∧ IsCompact (subdifferential f x) ∧
      Convex ℝ (subdifferential f x) ∧
      (∀ v ∈ subdifferential f x, form E x.val v = 0 ∧ tangentNorm v ≤ L) ∧
      ∃! v : Ambient E, IsSubgradient f x v ∧
        ∀ w, IsSubgradient f x w → tangentNorm v ≤ tangentNorm w := by
  have hne := global_subgradient_exists hf hL hlip x
  exact ⟨hne, subdifferential_compact x hL hlip, subdifferential_convex f x,
    fun _ hv => ⟨hv.1, subgradient_norm_le hL hlip hv⟩,
    subdifferential_unique_minimum x hL hlip hne⟩

noncomputable def canonicalOracle {f : Point E → ℝ} {L : ℝ}
    (hf : GConvexFunction f) (hL : 0 ≤ L)
    (hlip : ∀ x y, |f x - f y| ≤ L * dist x y) : Point E → FirstOrderReply E :=
  minimumNormOracle f hL hlip (global_subgradient_exists hf hL hlip)

theorem canonicalOracle_legal {f : Point E → ℝ} {L : ℝ}
    (hf : GConvexFunction f) (hL : 0 ≤ L)
    (hlip : ∀ x y, |f x - f y| ≤ L * dist x y) :
    LegalOracle f (canonicalOracle hf hL hlip) :=
  minimumNormOracle_legal f hL hlip (global_subgradient_exists hf hL hlip)

theorem canonicalOracle_minimum_norm {f : Point E → ℝ} {L : ℝ}
    (hf : GConvexFunction f) (hL : 0 ≤ L)
    (hlip : ∀ x y, |f x - f y| ≤ L * dist x y) (x : Point E)
    (v : Ambient E) (hv : IsSubgradient f x v) :
    tangentNorm ((canonicalOracle hf hL hlip x).2) ≤ tangentNorm v :=
  (minimumNormSubgradient_spec x hL hlip (global_subgradient_exists hf hL hlip x)).2 v hv

theorem admissible_has_legal_oracle {o : Point E} {R L : ℝ} {f : Point E → ℝ}
    (hf : AdmissibleObjective o R L f) (hL : 0 ≤ L) :
    ∃ O : Point E → FirstOrderReply E, LegalOracle f O :=
  ⟨canonicalOracle hf.convex hL hf.lipschitz, canonicalOracle_legal hf.convex hL hf.lipschitz⟩

end Geode.Lorentz

