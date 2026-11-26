import HeavyTail.RelativeInteriorQuery
import HeavyTail.ProjectedNoise

/-! The deterministic feasible-query reduction assembled from the actual
measurable proximal halving search and relative-interior interpolation. -/
noncomputable section
open Set MeasureTheory
open scoped InnerProductSpace
namespace HeavyTail
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def feasibleOracleQuery {S : Set E} {h : E → ℝ} (P : ProximalOracle S h)
    {G R : ℝ} {n : ℕ} (hG : 0 < G) (hR : 0 < R) (hn : 0 < n) (anchor z : E) : E :=
  interiorQuery (R / (8 * n)) anchor (selectedProximalPoint P hG hR hn z)

theorem feasibleOracleQuery_relativeInterior {S X : Set E} {h : E → ℝ}
    (P : ProximalOracle S h) (hX : Convex ℝ X) (hSX : S ⊆ X)
    {G R : ℝ} {n : ℕ} (hG : 0 < G) (hR : 0 < R) (hn : 0 < n)
    (anchor z : E) (ha : anchor ∈ intrinsicInterior ℝ X) :
    feasibleOracleQuery P hG hR hn anchor z ∈ intrinsicInterior ℝ X := by
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  exact relativeInteriorQuery_mem hX ha (hSX (selectedProximalPoint_feasible P hG hR hn z))
    (by positivity)

theorem feasibleOracleQuery_near {S : Set E} {h : E → ℝ} (P : ProximalOracle S h)
    {G R : ℝ} {n : ℕ} (hG : 0 < G) (hR : 0 < R) (hn : 0 < n) (anchor z : E) :
    ‖feasibleOracleQuery P hG hR hn anchor z - selectedProximalPoint P hG hR hn z‖ ≤ R / (8 * n) := by
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  exact interiorQuery_near (by positivity) anchor _

theorem feasibleOracleQuery_measurable [MeasurableSpace E] [BorelSpace E]
    {S : Set E} {h : E → ℝ} (P : ProximalOracle S h) (hh : ConvexOn ℝ S h)
    {G R : ℝ} {n : ℕ} (hG : 0 < G) (hR : 0 < R) (hn : 0 < n) (anchor : E) :
    Measurable (feasibleOracleQuery P hG hR hn anchor) :=
  (interiorQuery_continuous (R / (8 * n)) anchor).measurable.comp
    (selectedProximalPoint_measurable P hh hG hR hn)

/-- The bounded predictable mean and exact transfer `eq:transfer` follow from
actual feasible queries, the raw mean's subgradient property, and the original
public proximal oracle. No correction/mean norm or transfer bound is assumed. -/
theorem feasible_corrected_mean_transfer [FiniteDimensional ℝ E]
    {S X : Set E} {f h : E → ℝ} {G R : ℝ} {n : ℕ}
    (P : ProximalOracle S h) (hh : ConvexOn ℝ S h) (hX : Convex ℝ X) (hSX : S ⊆ X)
    (hG : 0 < G) (hR : 0 < R) (hn : 0 < n)
    (anchor z xstar mean : E) (ha : anchor ∈ intrinsicInterior ℝ X)
    (hx : xstar ∈ S) (hz : ‖z - xstar‖ ≤ 2 * R)
    (hmin : ∀ u ∈ S, f xstar + h xstar ≤ f u + h u)
    (hlip : ∀ u ∈ X, ∀ v ∈ X, f u - f v ≤ G * ‖u - v‖)
    (hsub : ∀ u ∈ X,
      ⟪mean, u - feasibleOracleQuery P hG hR hn anchor z⟫_ℝ ≤
        f u - f (feasibleOracleQuery P hG hR hn anchor z)) :
    let y := selectedProximalPoint P hG hR hn z
    let a := selectedProximalCorrection P hG hR hn z
    let b := ambientProjection (affineSpan ℝ X).direction mean + a
    ‖b‖ ≤ 4 * G ∧ (f y + h y) - (f xstar + h xstar) ≤
      ⟪b, z - xstar⟫_ℝ + G * R / (2 * n) := by
  let y := selectedProximalPoint P hG hR hn z
  let a := selectedProximalCorrection P hG hR hn z
  let w := feasibleOracleQuery P hG hR hn anchor z
  let K := (affineSpan ℝ X).direction
  let g := ambientProjection K mean
  have hy : y ∈ S := selectedProximalPoint_feasible P hG hR hn z
  have hwr : w ∈ intrinsicInterior ℝ X := feasibleOracleQuery_relativeInterior P hX hSX hG hR hn anchor z ha
  have hwX : w ∈ X := intrinsicInterior_subset hwr
  have hmean : ‖g‖ ≤ G := relativeInterior_projected_subgradient_norm hG.le hwr hsub
    (fun u hu => hlip u hu w hwX)
  have hlower : ∀ u ∈ S, h xstar - G * ‖u - xstar‖ ≤ h u := by
    intro u hu
    exact regularizer_linear_lower hmin hu (hlip u (hSX hu) xstar (hSX hx))
  have hab : ‖a‖ ≤ 3 * G := selectedProximalCorrection_bound P hG hR hn z xstar hx hz hlower
  refine ⟨corrected_mean_norm hmean hab, ?_⟩
  have hdir : w - xstar ∈ K := AffineSubspace.vsub_mem_direction
    (subset_affineSpan ℝ X hwX) (subset_affineSpan ℝ X (hSX hx))
  have hfg : f w - f xstar ≤ ⟪g, w - xstar⟫_ℝ := by
    have hs := hsub xstar (hSX hx)
    have hi : ⟪g, w - xstar⟫_ℝ = -⟪mean, xstar - w⟫_ℝ := by
      dsimp only [g]
      rw [← ambientProjection_inner, ambientProjection_eq_self K hdir]
      simp only [inner_sub_right]
      ring
    linarith only [hs, hi]
  have hhg : h y - h xstar ≤ ⟪a, y - xstar⟫_ℝ :=
    selectedProximalCorrection_subgradient P hh hG hR hn z xstar hx
  have hfy : f y - f w ≤ G * ‖w - y‖ := by
    simpa only [norm_sub_rev y w] using hlip y (hSX hy) w hwX
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  exact proximal_transfer hG hR.le hnR
    (proximalScale_pos hG hR (proximalHalvingIndex P hG hR hn z)).le hmean hfg hhg hfy
    (selectedProximalCorrection_identity P hG hR hn z)
    (proximalHalvingIndex_spec P hG hR hn z).2 (feasibleOracleQuery_near P hG hR hn anchor z)

end HeavyTail
