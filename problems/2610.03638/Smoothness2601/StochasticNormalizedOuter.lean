import Smoothness2601.NormalizedOuter
import Bilevel.StochasticOuter

/-! Expected norm for an actual independently uniform normalized iterate.
Gradient integrability is derived from deterministic travel and smoothness.
Estimator error integrability and expectation are inputs to be supplied by
the inner/adjoint sampling construction, rather than an assumed descent bound. -/
noncomputable section
open MeasureTheory
open scoped BigOperators RealInnerProductSpace
namespace Smoothness2601.NormalizedOuter
variable {X Ω : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
  [CompleteSpace X] [MeasurableSpace X] [BorelSpace X]
  [MeasurableSpace Ω] {ν : Measure Ω} [IsProbabilityMeasure ν]

omit [CompleteSpace X] [MeasurableSpace X] [BorelSpace X] in
theorem gradient_norm_bound (g : X → X) {L η : ℝ} (hL : 0 ≤ L) (hη : 0 ≤ η)
    (hg : ∀ x y, ‖g x-g y‖ ≤ L*‖x-y‖) (x q : ℕ → X)
    (hs : ∀ k, x (k+1) = step (x k) (q k) η) (k : ℕ) :
    ‖g (x k)‖ ≤ L*((k:ℝ)*η)+‖g (x 0)‖ := by
  have htravel := travel_bound x q hη hs k
  calc
    _ ≤ ‖g (x k)-g (x 0)‖+‖g (x 0)‖ := by
      simpa only [sub_add_cancel] using norm_add_le (g (x k)-g (x 0)) (g (x 0))
    _ ≤ L*‖x k-x 0‖+‖g (x 0)‖ := add_le_add_right (hg _ _) _
    _ ≤ _ := add_le_add_right (mul_le_mul_of_nonneg_left htravel hL) _

omit [CompleteSpace X] in
theorem gradient_norm_integrable (g : X → X) {L η : ℝ} (hL : 0 ≤ L) (hη : 0 ≤ η)
    (hg : ∀ x y, ‖g x-g y‖ ≤ L*‖x-y‖) (x q : ℕ → Ω → X) (x₀ : X)
    (hx : ∀ k, Measurable (x k)) (hinit : ∀ ω, x 0 ω = x₀)
    (hs : ∀ k ω, x (k+1) ω = step (x k ω) (q k ω) η) (k : ℕ) :
    Integrable (fun ω => ‖g (x k ω)‖) ν := by
  have hgc : Continuous g := (LipschitzWith.of_dist_le_mul (K := ⟨L,hL⟩)
    (fun u v => by simpa only [dist_eq_norm, NNReal.coe_mk] using hg u v)).continuous
  apply (integrable_const (L*((k:ℝ)*η)+‖g x₀‖)).mono'
    (hgc.measurable.comp (hx k)).norm.aestronglyMeasurable
  filter_upwards [] with ω
  rw [Real.norm_of_nonneg (norm_nonneg _)]
  simpa only [hinit] using gradient_norm_bound g hL hη hg
    (fun k => x k ω) (fun k => q k ω) (fun k => hs k ω) k

theorem expected_average_norm (f : X → ℝ) (g : X → X) {L η Δ floor δ : ℝ}
    (hL : 0 ≤ L) (hη : 0 < η) (hf : ∀ x, HasGradientAt f (g x) x)
    (hg : ∀ x y, ‖g x-g y‖ ≤ L*‖x-y‖)
    (x q : ℕ → Ω → X) (x₀ : X) (hx : ∀ k, Measurable (x k))
    (hinit : ∀ ω, x 0 ω = x₀)
    (hs : ∀ k ω, x (k+1) ω = step (x k ω) (q k ω) η)
    (hlower : ∀ z, floor ≤ f z) (hgap : f x₀-floor ≤ Δ)
    (n : ℕ) (hn : 0 < n)
    (he : ∀ k < n, Integrable (fun ω => ‖q k ω-g (x k ω)‖) ν)
    (herr : ∀ k < n, (∫ ω, ‖q k ω-g (x k ω)‖ ∂ν) ≤ δ) :
    (∑ k ∈ Finset.range n, ∫ ω, ‖g (x k ω)‖ ∂ν) / n ≤
      Δ/((n:ℝ)*η)+2*δ+L*η/2 := by
  have hgi := gradient_norm_integrable (ν := ν) g hL hη.le hg x q x₀ hx hinit hs
  have hgs : Integrable (fun ω => ∑ k ∈ Finset.range n, ‖g (x k ω)‖) ν :=
    integrable_finset_sum _ (fun k _ => hgi k)
  have hes : Integrable (fun ω => ∑ k ∈ Finset.range n, ‖q k ω-g (x k ω)‖) ν :=
    integrable_finset_sum _ (fun k hk => he k (Finset.mem_range.mp hk))
  have hpoint (ω : Ω) : η*(∑ k ∈ Finset.range n, ‖g (x k ω)‖) ≤
      Δ+2*η*(∑ k ∈ Finset.range n, ‖q k ω-g (x k ω)‖)+(n:ℝ)*L*η^2/2 := by
    have ht := telescope f g hL hη.le hf hg (fun k => x k ω) (fun k => q k ω)
      (fun k => hs k ω) n
    rw [hinit] at ht
    linarith [hlower (x n ω)]
  have hi := integral_mono (hgs.const_mul η)
    (((integrable_const Δ).add (hes.const_mul (2*η))).add (integrable_const ((n:ℝ)*L*η^2/2))) hpoint
  simp only [Pi.add_apply] at hi
  have hR : Integrable (fun ω => Δ+2*η*(∑ k ∈ Finset.range n, ‖q k ω-g (x k ω)‖)) ν :=
    (integrable_const Δ).add (hes.const_mul (2*η))
  rw [integral_const_mul, integral_add hR
    (integrable_const _), integral_add (integrable_const Δ) (hes.const_mul (2*η)),
    integral_const_mul] at hi
  simp only [integral_const, measureReal_univ_eq_one, smul_eq_mul, one_mul] at hi
  rw [integral_finset_sum _ (fun k _ => hgi k),
    integral_finset_sum _ (fun k hk => he k (Finset.mem_range.mp hk))] at hi
  have heSum : (∑ k ∈ Finset.range n, ∫ ω, ‖q k ω-g (x k ω)‖ ∂ν) ≤ (n:ℝ)*δ := by
    simpa only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] using
      Finset.sum_le_sum (fun k hk => herr k (Finset.mem_range.mp hk))
  have heMul := mul_le_mul_of_nonneg_left heSum (show 0 ≤ 2*η by positivity)
  have hn' : 0 < (n:ℝ) := by exact_mod_cast hn
  apply (div_le_iff₀ hn').mpr
  apply (mul_le_mul_left hη).mp
  have hid : η*((Δ/((n:ℝ)*η)+2*δ+L*η/2)*(n:ℝ)) =
      Δ+2*η*((n:ℝ)*δ)+(n:ℝ)*L*η^2/2 := by field_simp; ring
  rw [hid]
  linarith

/-- The selected point uses an actual uniform probability law independent of
all oracle/algorithm randomness, not a symbolic average. -/
theorem expected_uniform_norm (f : X → ℝ) (g : X → X) {L η Δ floor δ : ℝ}
    (hL : 0 ≤ L) (hη : 0 < η) (hf : ∀ x, HasGradientAt f (g x) x)
    (hg : ∀ x y, ‖g x-g y‖ ≤ L*‖x-y‖)
    (x q : ℕ → Ω → X) (x₀ : X) (hx : ∀ k, Measurable (x k))
    (hinit : ∀ ω, x 0 ω = x₀)
    (hs : ∀ k ω, x (k+1) ω = step (x k ω) (q k ω) η)
    (hlower : ∀ z, floor ≤ f z) (hgap : f x₀-floor ≤ Δ)
    (n : ℕ) [NeZero n]
    (he : ∀ k < n, Integrable (fun ω => ‖q k ω-g (x k ω)‖) ν)
    (herr : ∀ k < n, (∫ ω, ‖q k ω-g (x k ω)‖ ∂ν) ≤ δ) :
    (∫ z : Fin n × Ω, ‖g (Bilevel.StochasticOuter.selected x z)‖
      ∂Bilevel.StochasticOuter.outputLaw n ν) ≤ Δ/((n:ℝ)*η)+2*δ+L*η/2 := by
  have hgi := gradient_norm_integrable (ν := ν) g hL hη.le hg x q x₀ hx hinit hs
  have hp := Bilevel.StochasticOuter.integrable_uniform_output n
    (fun k ω => ‖g (x k ω)‖) (fun k _ => hgi k)
  rw [show (fun z : Fin n × Ω => ‖g (Bilevel.StochasticOuter.selected x z)‖) =
    (fun z : Fin n × Ω => ‖g (x z.1 z.2)‖) from rfl,
    Bilevel.StochasticOuter.uniform_output_integral n (fun k ω => ‖g (x k ω)‖) hp]
  exact expected_average_norm f g hL hη hf hg x q x₀ hx hinit hs hlower hgap n
    (Nat.pos_of_neZero n) he herr

end Smoothness2601.NormalizedOuter
