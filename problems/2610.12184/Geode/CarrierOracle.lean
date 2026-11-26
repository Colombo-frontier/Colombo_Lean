import Geode.GeometricCarrier
import Geode.ContactRealization
import Geode.OracleModel
import Mathlib.Analysis.Calculus.Deriv.Slope

/-! Existence of actual selected Riemannian subgradients for the constructed
carrier objective. A minimizing contact and a one-sided derivative argument
provide a globally legal selection, including contacts at the source center. -/
namespace Geode.Lorentz

open Set Filter
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem hasDerivAt_distance_segment (y z x : Point E) (hne : y ≠ z) :
    HasDerivAt (fun t => dist y (segment z x t))
      (-form E (direction z y) (logMap z x)) 0 := by
  have hd := hasDerivAt_distance_lines (segmentLine y y) (segmentLine z x)
    (t := 0) (by simpa using hne)
  simp only [segmentLine_point, segment_self, segment_zero,
    segmentLine_velocity_zero, logMap_self] at hd
  have hi := joint_direction_slope y z y x
  simp only [logMap_self, form_zero_right, neg_zero, zero_sub] at hi
  rw [hi] at hd
  exact hd

/-- A minimum over a geodesically convex carrier gives the source support
needed for a full exterior oracle reply. No differentiability of the source
is required, so this includes a minimizing contact at the radial center. -/
theorem source_support_of_contact_min {K : Set (Point E)} {source : Point E → ℝ}
    {z y : Point E} (hK : GConvex K) (hsource : GConvexFunction source)
    (hz : z ∈ K) (hyz : y ≠ z)
    (hmin : ∀ w ∈ K, source z + dist y z ≤ source w + dist y w)
    {x : Point E} (hx : x ∈ K) :
    source z + form E (direction z y) (logMap z x) ≤ source x := by
  let D : ℝ → ℝ := fun t => dist y (segment z x t)
  have hd : HasDerivAt D (-form E (direction z y) (logMap z x)) 0 :=
    hasDerivAt_distance_segment y z x hyz
  have ht : Tendsto (slope D 0) (𝓝[>] (0 : ℝ))
      (𝓝 (-form E (direction z y) (logMap z x))) :=
    (hasDerivWithinAt_iff_tendsto_slope' (not_mem_Ioi_self : (0 : ℝ) ∉ Ioi 0)).mp
      hd.hasDerivWithinAt
  have hb : source z - source x ≤ -form E (direction z y) (logMap z x) := by
    apply ge_of_tendsto ht
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds]
      with t ht0 ht1
    have hp : 0 < t := ht0
    have hc := hsource z x t hp.le ht1.le
    have hm := hmin (segment z x t) (hK z hz x hx t hp.le ht1.le)
    rw [slope_def_field]
    dsimp only [D]
    rw [segment_zero, sub_zero]
    apply (le_div_iff₀ hp).mpr
    nlinarith
  linarith

theorem carrier_minimizing_contact_support {K : Set (Point E)} {p y z : Point E}
    {μ : ℝ} (hK : GConvex K) (hz : z ∈ K) (hμ : 0 ≤ μ) (hyz : y ≠ z)
    (hmin : ∀ w ∈ K, μ * dist z p + dist y z ≤ μ * dist w p + dist y w)
    {x : Point E} (hx : x ∈ K) :
    μ * dist z p + form E (direction z y) (logMap z x) ≤ μ * dist x p := by
  apply source_support_of_contact_min hK (source := fun x => μ * dist x p) _ hz hyz hmin hx
  intro a b t ht ht1
  have h := joint_distance_convex a b p p ht ht1
  rw [segment_self] at h
  have hm := mul_le_mul_of_nonneg_left h hμ
  dsimp only
  nlinarith

theorem carrier_subgradient_at_exterior {K : Set (Point E)} {p y z : Point E}
    {μ : ℝ} (hK : GConvex K) (hz : z ∈ K) (hμ : 0 ≤ μ) (hyz : y ≠ z)
    (hval : Geode.carrierValue K p μ y = μ * dist z p + dist y z) :
    IsSubgradient (Geode.carrierValue K p μ) y (-direction y z) := by
  have hmin : ∀ w ∈ K, μ * dist z p + dist y z ≤ μ * dist w p + dist y w := by
    intro w hw
    rw [← hval]
    exact Geode.carrierValue_le_contact hμ hw
  constructor
  · simp [direction_tangent]
  · intro w
    rw [hval, form_neg_left]
    apply le_csInf (Set.Nonempty.image (f := fun x : Point E => μ * dist x p + dist w x) ⟨z, hz⟩)
    rintro _ ⟨x, hx, rfl⟩
    dsimp only
    have hs := carrier_minimizing_contact_support hK hz hμ hyz hmin hx
    have hj := joint_distance_support y z w x hyz
    linarith

theorem carrier_subgradient_on_carrier {K : Set (Point E)} {p y : Point E} {μ : ℝ}
    (hy : y ∈ K) (hμ : 0 ≤ μ) (hμ1 : μ ≤ 1) :
    ∃ g : Ambient E, IsSubgradient (Geode.carrierValue K p μ) y g := by
  have heq := Geode.carrierValue_eq_source (p := p) hy hμ hμ1
  by_cases hyp : y = p
  · subst p
    refine ⟨0, (isSubgradient_zero_iff _ _).mpr ?_⟩
    intro w
    rw [heq, dist_self, mul_zero]
    exact Geode.carrierValue_nonneg ⟨y, hy⟩ hμ hμ1
  · refine ⟨μ • (-direction y p), ?_⟩
    constructor
    · simp [direction_tangent]
    · intro w
      have hs := (distance_isSubgradient y p hyp).const_mul hμ
      have hf := Geode.carrierValue_floor (p := p) (y := w) ⟨y, hy⟩ hμ hμ1
      rw [heq]
      exact (hs.2 w).trans hf

/-- Every point has a legal ordinary Riemannian subgradient for the actual
constructed carrier objective. The legal selection is proved to exist. -/
theorem carrier_subgradient_exists {K : Set (Point E)} {p : Point E} {μ : ℝ}
    (hK : IsCompact K) (hKg : GConvex K) (hne : K.Nonempty)
    (hμ : 0 ≤ μ) (hμ1 : μ ≤ 1) (y : Point E) :
    ∃ g : Ambient E, IsSubgradient (Geode.carrierValue K p μ) y g := by
  by_cases hy : y ∈ K
  · exact carrier_subgradient_on_carrier hy hμ hμ1
  · obtain ⟨z, hz, hval⟩ := Geode.carrierValue_attained (p := p) (y := y) (μ := μ) hK hne
    have hyz : y ≠ z := fun heq => hy (heq.symm ▸ hz)
    exact ⟨-direction y z, carrier_subgradient_at_exterior hKg hz hμ hyz hval⟩

noncomputable def carrierSubgradientSelection {K : Set (Point E)} {p : Point E} {μ : ℝ}
    (hK : IsCompact K) (hKg : GConvex K) (hne : K.Nonempty)
    (hμ : 0 ≤ μ) (hμ1 : μ ≤ 1) (y : Point E) : Ambient E :=
  Classical.choose (carrier_subgradient_exists (p := p) hK hKg hne hμ hμ1 y)

theorem carrierSubgradientSelection_legal {K : Set (Point E)} {p : Point E} {μ : ℝ}
    (hK : IsCompact K) (hKg : GConvex K) (hne : K.Nonempty)
    (hμ : 0 ≤ μ) (hμ1 : μ ≤ 1) (y : Point E) :
    IsSubgradient (Geode.carrierValue K p μ) y (carrierSubgradientSelection (p := p) hK hKg hne hμ hμ1 y) :=
  Classical.choose_spec (carrier_subgradient_exists (p := p) hK hKg hne hμ hμ1 y)

noncomputable def carrierOracle {K : Set (Point E)} {p : Point E} {μ : ℝ}
    (hK : IsCompact K) (hKg : GConvex K) (hne : K.Nonempty)
    (hμ : 0 ≤ μ) (hμ1 : μ ≤ 1) : Point E → FirstOrderReply E :=
  fun y => (Geode.carrierValue K p μ y, carrierSubgradientSelection (p := p) hK hKg hne hμ hμ1 y)

theorem carrierOracle_legal {K : Set (Point E)} {p : Point E} {μ : ℝ}
    (hK : IsCompact K) (hKg : GConvex K) (hne : K.Nonempty)
    (hμ : 0 ≤ μ) (hμ1 : μ ≤ 1) :
    LegalOracle (Geode.carrierValue K p μ) (carrierOracle (p := p) hK hKg hne hμ hμ1) := by
  intro y
  exact ⟨rfl, carrierSubgradientSelection_legal hK hKg hne hμ hμ1 y⟩

end Geode.Lorentz
