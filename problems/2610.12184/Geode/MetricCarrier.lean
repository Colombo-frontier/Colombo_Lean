import Mathlib.Topology.Order.Compact
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Tactic

/-!
# Metric carrier extension

The metric part of `lem:metric-carrier` in `source/geode/geode.tex`.
These theorems hold in every metric space; they do not assert that a concrete
hyperbolic model has jointly geodesically convex distance.
-/

namespace Geode

open Set

variable {X : Type*} [MetricSpace X]

/-- The actual metric infimal convolution, with values in the real numbers. -/
noncomputable def carrierValue (K : Set X) (p : X) (μ : ℝ) (y : X) : ℝ :=
  sInf ((fun x => μ * dist x p + dist y x) '' K)

theorem carrierValue_le_contact {K : Set X} {p y x : X} {μ : ℝ}
    (hμ : 0 ≤ μ) (hx : x ∈ K) :
    carrierValue K p μ y ≤ μ * dist x p + dist y x := by
  apply csInf_le _ (mem_image_of_mem _ hx)
  refine ⟨0, ?_⟩
  rintro _ ⟨z, _, rfl⟩
  positivity

theorem carrierValue_attained {K : Set X} {p y : X} {μ : ℝ}
    (hK : IsCompact K) (hne : K.Nonempty) :
    ∃ x ∈ K, carrierValue K p μ y = μ * dist x p + dist y x := by
  have hc : Continuous (fun x : X => μ * dist x p + dist y x) := by
    fun_prop
  obtain ⟨x, hx, hmin⟩ := hK.exists_isMinOn hne hc.continuousOn
  refine ⟨x, hx, ?_⟩
  apply IsLeast.csInf_eq
  refine ⟨mem_image_of_mem _ hx, ?_⟩
  rintro _ ⟨z, hz, rfl⟩
  exact hmin hz

theorem carrierValue_floor {K : Set X} {p y : X} {μ : ℝ}
    (hne : K.Nonempty) (hμ : 0 ≤ μ) (hμ1 : μ ≤ 1) :
    μ * dist y p ≤ carrierValue K p μ y := by
  apply le_csInf (hne.image _)
  rintro _ ⟨x, _, rfl⟩
  change μ * dist y p ≤ μ * dist x p + dist y x
  have htri := dist_triangle y x p
  have hdist := dist_nonneg (x := y) (y := x)
  nlinarith [mul_le_mul_of_nonneg_left htri hμ,
    mul_le_mul_of_nonneg_right hμ1 hdist]

theorem carrierValue_eq_source {K : Set X} {p y : X} {μ : ℝ}
    (hy : y ∈ K) (hμ : 0 ≤ μ) (hμ1 : μ ≤ 1) :
    carrierValue K p μ y = μ * dist y p := by
  apply le_antisymm
  · simpa using carrierValue_le_contact (p := p) (y := y) hμ hy
  · exact carrierValue_floor ⟨y, hy⟩ hμ hμ1

theorem carrierValue_at_center {K : Set X} {p : X} {μ : ℝ}
    (hp : p ∈ K) (hμ : 0 ≤ μ) (hμ1 : μ ≤ 1) :
    carrierValue K p μ p = 0 := by
  simpa using carrierValue_eq_source (p := p) hp hμ hμ1

theorem carrierValue_nonneg {K : Set X} {p y : X} {μ : ℝ}
    (hne : K.Nonempty) (hμ : 0 ≤ μ) (hμ1 : μ ≤ 1) :
    0 ≤ carrierValue K p μ y :=
  le_trans (mul_nonneg hμ dist_nonneg) (carrierValue_floor hne hμ hμ1)

theorem carrierValue_eq_zero_iff {K : Set X} {p y : X} {μ : ℝ}
    (hp : p ∈ K) (hμ : 0 < μ) (hμ1 : μ ≤ 1) :
    carrierValue K p μ y = 0 ↔ y = p := by
  constructor
  · intro hzero
    have hf := carrierValue_floor (p := p) (y := y) ⟨p, hp⟩ hμ.le hμ1
    have hd : dist y p = 0 := by nlinarith [dist_nonneg (x := y) (y := p)]
    exact dist_eq_zero.mp hd
  · rintro rfl
    exact carrierValue_at_center hp hμ.le hμ1

theorem carrierValue_unique_minimizer {K : Set X} {p y : X} {μ : ℝ}
    (hp : p ∈ K) (hμ : 0 < μ) (hμ1 : μ ≤ 1) :
    (∀ z, carrierValue K p μ y ≤ carrierValue K p μ z) ↔ y = p := by
  constructor
  · intro hmin
    apply (carrierValue_eq_zero_iff hp hμ hμ1).mp
    apply le_antisymm
    · simpa [carrierValue_at_center hp hμ.le hμ1] using hmin p
    · exact carrierValue_nonneg ⟨p, hp⟩ hμ.le hμ1
  · intro hy
    subst y
    intro z
    rw [carrierValue_at_center hp hμ.le hμ1]
    exact carrierValue_nonneg ⟨p, hp⟩ hμ.le hμ1

theorem carrierValue_le_add_dist {K : Set X} {p y z : X} {μ : ℝ}
    (hK : IsCompact K) (hne : K.Nonempty) (hμ : 0 ≤ μ) :
    carrierValue K p μ y ≤ carrierValue K p μ z + dist y z := by
  obtain ⟨x, hx, hval⟩ := carrierValue_attained (p := p) (y := z) (μ := μ) hK hne
  have hc := carrierValue_le_contact (p := p) (y := y) hμ hx
  rw [hval]
  linarith [dist_triangle y z x]

theorem carrierValue_lipschitz {K : Set X} {p : X} {μ : ℝ}
    (hK : IsCompact K) (hne : K.Nonempty) (hμ : 0 ≤ μ) :
    LipschitzWith 1 (carrierValue K p μ) := by
  apply LipschitzWith.of_dist_le_mul
  intro y z
  simp only [NNReal.coe_one, one_mul, Real.dist_eq]
  apply abs_le.mpr
  constructor
  · have h := carrierValue_le_add_dist (p := p) (y := z) (z := y) hK hne hμ
    rw [dist_comm z y] at h
    linarith
  · have h := carrierValue_le_add_dist (p := p) (y := y) (z := z) hK hne hμ
    linarith

/-- Partial minimization preserves convexity along an interpolation with jointly
convex distance. This explicitly records the geometric input still needed when
specializing to a concrete model of hyperbolic space. -/
theorem carrierValue_interpolation {K : Set X} {p y₀ y₁ : X} {μ t : ℝ}
    (hK : IsCompact K) (hne : K.Nonempty) (hμ : 0 ≤ μ)
    (_ht : 0 ≤ t) (_ht1 : t ≤ 1)
    (γ : X → X → ℝ → X)
    (hconst : γ p p t = p)
    (hjoint : ∀ a b c d, dist (γ a b t) (γ c d t) ≤
      (1 - t) * dist a c + t * dist b d)
    (hconv : ∀ x₀ ∈ K, ∀ x₁ ∈ K, γ x₀ x₁ t ∈ K) :
    carrierValue K p μ (γ y₀ y₁ t) ≤
      (1 - t) * carrierValue K p μ y₀ + t * carrierValue K p μ y₁ := by
  obtain ⟨x₀, hx₀, hv₀⟩ := carrierValue_attained (p := p) (y := y₀) (μ := μ) hK hne
  obtain ⟨x₁, hx₁, hv₁⟩ := carrierValue_attained (p := p) (y := y₁) (μ := μ) hK hne
  have hcontact := carrierValue_le_contact (p := p) (y := γ y₀ y₁ t)
    hμ (hconv x₀ hx₀ x₁ hx₁)
  have hsource := hjoint x₀ x₁ p p
  rw [hconst] at hsource
  have hdist := hjoint y₀ y₁ x₀ x₁
  rw [hv₀, hv₁]
  nlinarith [mul_le_mul_of_nonneg_left hsource hμ]

end Geode
