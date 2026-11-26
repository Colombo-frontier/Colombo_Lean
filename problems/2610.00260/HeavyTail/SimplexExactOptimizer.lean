import HeavyTail.SimplexApproxOptimizer
import Mathlib.Topology.Sequences
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable

/-! Exact measurable convex minimization on a finite simplex. Vanishing
quadratic regularization selects one exact optimizer even when the original
objective has many minimizers. Approximate points are used only internally;
the returned measurable map is a pointwise limit and is an exact minimizer. -/

noncomputable section
open Set MeasureTheory Filter TopologicalSpace
open scoped BigOperators Topology
namespace HeavyTail

variable {ι : Type*} [Fintype ι]

def simplexSquare (w : ι → ℝ) : ℝ := ∑ i, (w i) ^ 2

def simplexSquareDerivative (w : ι → ℝ) : (ι → ℝ) →L[ℝ] ℝ :=
  ∑ i, (2 * w i) • ContinuousLinearMap.proj i

theorem simplexSquareDerivative_apply (w h : ι → ℝ) :
    simplexSquareDerivative w h = ∑ i, 2 * w i * h i := by
  simp [simplexSquareDerivative]

theorem simplexSquare_hasFDerivAt (w : ι → ℝ) :
    HasFDerivAt simplexSquare (simplexSquareDerivative w) w := by
  classical
  apply HasFDerivAt.sum
  intro i _hi
  have h := (hasFDerivAt_apply (𝕜 := ℝ) i w).mul (hasFDerivAt_apply (𝕜 := ℝ) i w)
  convert h using 1
  · funext u
    ring
  · ext u
    simp
    ring

theorem simplexSquareDerivative_continuous : Continuous (simplexSquareDerivative (ι := ι)) := by
  classical
  apply continuous_finset_sum
  intro i _hi
  exact (continuous_const.mul (continuous_apply i)).smul continuous_const

theorem simplexSquareDerivative_unique {x y : ι → ℝ}
    (hxy : 0 ≤ simplexSquareDerivative x (y - x))
    (hyx : 0 ≤ simplexSquareDerivative y (x - y)) : x = y := by
  classical
  have hid : simplexSquareDerivative x (y - x) + simplexSquareDerivative y (x - y) =
      -2 * ∑ i, (x i - y i) ^ 2 := by
    simp only [simplexSquareDerivative_apply, Pi.sub_apply, ← Finset.sum_add_distrib,
      Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hs0 : 0 ≤ ∑ i, (x i - y i) ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hs : ∑ i, (x i - y i) ^ 2 = 0 := by nlinarith only [hid, hxy, hyx, hs0]
  ext i
  have hi : (x i - y i) ^ 2 = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun j (_ : j ∈ Finset.univ) => sq_nonneg (x j - y j))).mp hs i (Finset.mem_univ i)
  nlinarith only [hi]

/-- Every cluster limit of the regularized first-order sequence exactly
minimizes F and satisfies the square-norm first-order test against every
other exact minimizer. -/
theorem regularized_simplex_limit_minimizer
    (F : (ι → ℝ) → ℝ) (dF : (ι → ℝ) → (ι → ℝ) →L[ℝ] ℝ)
    (hconv : ConvexOn ℝ (stdSimplex ℝ ι) F)
    (hderiv : ∀ w ∈ stdSimplex ℝ ι, HasFDerivWithinAt F (dF w) (stdSimplex ℝ ι) w)
    (hcont : ContinuousOn dF (stdSimplex ℝ ι))
    {ε : ℕ → ℝ} (hε : ∀ n, 0 < ε n) (hεlim : Tendsto ε atTop (𝓝 0))
    {x : ℕ → (ι → ℝ)} (hx : ∀ n, x n ∈ stdSimplex ℝ ι)
    (hfirst : ∀ n q, q ∈ stdSimplex ℝ ι →
      -(ε n) ^ 2 ≤ (dF (x n) + ε n • simplexSquareDerivative (x n)) (q - x n))
    {z : ι → ℝ} (hz : z ∈ stdSimplex ℝ ι) (hlim : Tendsto x atTop (𝓝 z)) :
    IsMinOn F (stdSimplex ℝ ι) z ∧
      ∀ q ∈ stdSimplex ℝ ι, IsMinOn F (stdSimplex ℝ ι) q →
        0 ≤ simplexSquareDerivative z (q - z) := by
  have hxwithin : Tendsto x atTop (𝓝[stdSimplex ℝ ι] z) :=
    tendsto_nhdsWithin_iff.mpr ⟨hlim, Eventually.of_forall hx⟩
  have hdlim (q : ι → ℝ) :
      Tendsto (fun n => dF (x n) (q - x n)) atTop (𝓝 (dF z (q - z))) :=
    ((hcont.clm_apply (continuous_const.sub continuous_id).continuousOn) z hz).tendsto.comp hxwithin
  have hRlim (q : ι → ℝ) :
      Tendsto (fun n => simplexSquareDerivative (x n) (q - x n)) atTop
        (𝓝 (simplexSquareDerivative z (q - z))) :=
    (simplexSquareDerivative_continuous.clm_apply (continuous_const.sub continuous_id)).continuousAt.tendsto.comp hlim
  have hscalar (n : ℕ) (q : ι → ℝ) (hq : q ∈ stdSimplex ℝ ι) :
      -(ε n) ^ 2 ≤ dF (x n) (q - x n) + ε n * simplexSquareDerivative (x n) (q - x n) := by
    simpa only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul] using hfirst n q hq
  have hmin : IsMinOn F (stdSimplex ℝ ι) z := by
    intro q hq
    change F z ≤ F q
    have hnonneg : 0 ≤ dF z (q - z) := by
      have hh := le_of_tendsto_of_tendsto (hεlim.pow 2).neg ((hdlim q).add (hεlim.mul (hRlim q)))
        (Eventually.of_forall (fun n => hscalar n q hq))
      simpa using hh
    have hs := convex_supporting_within_derivative hconv hz hq (hderiv z hz)
    linarith only [hnonneg, hs]
  refine ⟨hmin, ?_⟩
  intro q hq hqmin
  have hR (n : ℕ) : -ε n ≤ simplexSquareDerivative (x n) (q - x n) := by
    have hs := convex_supporting_within_derivative hconv (hx n) hq (hderiv (x n) (hx n))
    have hval := hqmin (hx n)
    change F q ≤ F (x n) at hval
    have hdf : dF (x n) (q - x n) ≤ 0 := by linarith only [hs, hval]
    have hh := hscalar n q hq
    apply (mul_le_mul_left (hε n)).mp
    nlinarith only [hh, hdf]
  simpa only [neg_zero] using
    le_of_tendsto_of_tendsto hεlim.neg (hRlim q) (Eventually.of_forall hR)

theorem regularized_simplex_sequence_converges
    (F : (ι → ℝ) → ℝ) (dF : (ι → ℝ) → (ι → ℝ) →L[ℝ] ℝ)
    (hconv : ConvexOn ℝ (stdSimplex ℝ ι) F)
    (hderiv : ∀ w ∈ stdSimplex ℝ ι, HasFDerivWithinAt F (dF w) (stdSimplex ℝ ι) w)
    (hcont : ContinuousOn dF (stdSimplex ℝ ι))
    {ε : ℕ → ℝ} (hε : ∀ n, 0 < ε n) (hεlim : Tendsto ε atTop (𝓝 0))
    {x : ℕ → (ι → ℝ)} (hx : ∀ n, x n ∈ stdSimplex ℝ ι)
    (hfirst : ∀ n q, q ∈ stdSimplex ℝ ι →
      -(ε n) ^ 2 ≤ (dF (x n) + ε n • simplexSquareDerivative (x n)) (q - x n)) :
    ∃ y ∈ stdSimplex ℝ ι, IsMinOn F (stdSimplex ℝ ι) y ∧ Tendsto x atTop (𝓝 y) := by
  obtain ⟨y, hy, φ, hφ, hlim⟩ := (isCompact_stdSimplex ι).tendsto_subseq hx
  have hyprop := regularized_simplex_limit_minimizer F dF hconv hderiv hcont
    (fun n => hε (φ n)) (hεlim.comp hφ.tendsto_atTop) (fun n => hx (φ n))
    (fun n => hfirst (φ n)) hy hlim
  refine ⟨y, hy, hyprop.1, ?_⟩
  apply (isCompact_stdSimplex ι).tendsto_nhds_of_unique_mapClusterPt (Eventually.of_forall hx)
  intro z hz hcluster
  obtain ⟨ψ, hψ, hzlim⟩ := FirstCountableTopology.tendsto_subseq hcluster
  have hzprop := regularized_simplex_limit_minimizer F dF hconv hderiv hcont
    (fun n => hε (ψ n)) (hεlim.comp hψ.tendsto_atTop) (fun n => hx (ψ n))
    (fun n => hfirst (ψ n)) hz hzlim
  exact simplexSquareDerivative_unique (hzprop.2 y hy hyprop.1) (hyprop.2 z hz hzprop.1)

variable [Nonempty ι]

/-- Exact, globally measurable optimizer selection. No uniqueness assumption
on F and no residual conclusion remains. -/
theorem exists_measurable_simplex_exact_optimizer
    {P : Type*} [MeasurableSpace P]
    (F : P → (ι → ℝ) → ℝ) (dF : P → (ι → ℝ) → (ι → ℝ) →L[ℝ] ℝ)
    (hconv : ∀ p, ConvexOn ℝ (stdSimplex ℝ ι) (F p))
    (hderiv : ∀ p w, w ∈ stdSimplex ℝ ι →
      HasFDerivWithinAt (F p) (dF p w) (stdSimplex ℝ ι) w)
    (hcont : ∀ p, ContinuousOn (dF p) (stdSimplex ℝ ι))
    (hmeas : ∀ w ∈ stdSimplex ℝ ι, Measurable (fun p => dF p w)) :
    ∃ update : P → (ι → ℝ), Measurable update ∧
      (∀ p, update p ∈ stdSimplex ℝ ι) ∧
      ∀ p, IsMinOn (F p) (stdSimplex ℝ ι) (update p) := by
  classical
  let ε : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hε : ∀ n, 0 < ε n := by intro n; dsimp [ε]; positivity
  have hεlim : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hex (n : ℕ) : ∃ u : P → (ι → ℝ), Measurable u ∧
      (∀ p, u p ∈ stdSimplex ℝ ι) ∧ ∀ p q, q ∈ stdSimplex ℝ ι →
        -(ε n) ^ 2 ≤ (dF p (u p) + ε n • simplexSquareDerivative (u p)) (q - u p) := by
    apply exists_measurable_simplex_first_order_optimizer
      (fun p w => F p w + ε n * simplexSquare w)
      (fun p w => dF p w + ε n • simplexSquareDerivative w)
    · intro p w hw
      exact (hderiv p w hw).add ((simplexSquare_hasFDerivAt w).hasFDerivWithinAt.const_mul (ε n))
    · intro p
      exact (hcont p).add (simplexSquareDerivative_continuous.const_smul (ε n)).continuousOn
    · intro w hw
      exact (hmeas w hw).add_const _
    · exact measurable_const
    · intro p
      exact sq_pos_of_pos (hε n)
  choose u humeas humem hufirst using hex
  have hlimit (p : P) : ∃ y ∈ stdSimplex ℝ ι, IsMinOn (F p) (stdSimplex ℝ ι) y ∧
      Tendsto (fun n => u n p) atTop (𝓝 y) :=
    regularized_simplex_sequence_converges (F p) (dF p) (hconv p) (hderiv p) (hcont p)
      hε hεlim (fun n => humem n p) (fun n => hufirst n p)
  choose update hmem hmin hlim using hlimit
  refine ⟨update, ?_, hmem, hmin⟩
  exact measurable_of_tendsto_metrizable humeas (tendsto_pi_nhds.mpr hlim)

end HeavyTail
