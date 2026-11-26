import Geode.JointDistance
import Geode.GeodesicConvex
import Geode.HyperbolicCompact
import Geode.MetricCarrier

/-! Concrete hyperbolic convexity of metric carriers and compact closed hulls. -/
namespace Geode.Lorentz

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

@[simp] theorem segment_self (x : Point E) (t : ℝ) : segment x x t = x := by
  classical
  simp [segment]

theorem gconvexFunction_distance (p : Point E) : GConvexFunction (fun x => dist x p) := by
  intro x y t ht ht1
  simpa using joint_distance_convex x y p p ht ht1

theorem gconvex_closedBall (p : Point E) (r : ℝ) : GConvex (Metric.closedBall p r) :=
  (gconvexFunction_distance p).sublevel r

theorem isCompact_closedGConv_of_bounded [FiniteDimensional ℝ E]
    {S : Set (Point E)} (hS : Bornology.IsBounded S) : IsCompact (closedGConv S) := by
  obtain ⟨r, hr⟩ := hS.subset_closedBall (origin : Point E)
  exact isCompact_closedGConv (isCompact_closedBall (origin : Point E) r)
    (gconvex_closedBall origin r) hr

theorem carrierValue_gconvex {K : Set (Point E)} {p : Point E} {μ : ℝ}
    (hK : IsCompact K) (hne : K.Nonempty) (hKg : GConvex K) (hμ : 0 ≤ μ) :
    GConvexFunction (Geode.carrierValue K p μ) := by
  intro y₀ y₁ t ht ht1
  exact Geode.carrierValue_interpolation hK hne hμ ht ht1 segment (segment_self p t)
    (fun a b c d => joint_distance_convex a b c d ht ht1)
    (fun x₀ hx₀ x₁ hx₁ => hKg x₀ hx₀ x₁ hx₁ t ht ht1)

/-- The entire bounded convex carrier lemma in the actual hyperboloid model. -/
theorem metric_carrier {K : Set (Point E)} {p : Point E} {μ : ℝ}
    (hK : IsCompact K) (hKg : GConvex K) (hp : p ∈ K)
    (hμ : 0 < μ) (hμ1 : μ < 1) :
    GConvexFunction (Geode.carrierValue K p μ) ∧
    LipschitzWith 1 (Geode.carrierValue K p μ) ∧
    (∀ y, μ * dist y p ≤ Geode.carrierValue K p μ y) ∧
    Geode.carrierValue K p μ p = 0 ∧
    (∀ y, (∀ z, Geode.carrierValue K p μ y ≤ Geode.carrierValue K p μ z) ↔ y = p) ∧
    (∀ y ∈ K, Geode.carrierValue K p μ y = μ * dist y p) := by
  refine ⟨carrierValue_gconvex hK ⟨p, hp⟩ hKg hμ.le,
    Geode.carrierValue_lipschitz hK ⟨p, hp⟩ hμ.le,
    fun y => Geode.carrierValue_floor ⟨p, hp⟩ hμ.le hμ1.le,
    Geode.carrierValue_at_center hp hμ.le hμ1.le, ?_, ?_⟩
  · intro y
    exact Geode.carrierValue_unique_minimizer hp hμ hμ1.le
  · intro y hy
    exact Geode.carrierValue_eq_source hy hμ.le hμ1.le

end Geode.Lorentz
