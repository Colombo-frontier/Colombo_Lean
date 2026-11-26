import HeavyTail.IndependentBernoulliMoments
import HeavyTail.IndependentBernoulliCalibration
import HeavyTail.MaskedKernelMoments

/-! The original independent-coordinate importance-weighted hard oracle, as
an actual Markov kernel.  Every call samples the full product Bernoulli law.
The source amplitude `1/16` is calibrated to both prescribed moment budgets. -/

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal InnerProductSpace
namespace HeavyTail.IndependentBernoulli
noncomputable section

theorem reply_measurable {k : ℕ} (α : ℝ) :
    Measurable (fun z : HardSpace k × (Fin k → Bool) => reply α z.1 z.2) := by
  apply measurable_from_prod_countable
  intro b
  apply (PiLp.continuous_equiv_symm (p := 2) (β := fun _ : Fin k => ℝ)).measurable.comp
  apply measurable_pi_iff.mpr
  intro j
  by_cases hb : b j = true
  · simpa only [erasureReply, hb, if_true] using
      (measurable_const : Measurable (fun _ : HardSpace k => (0 : ℝ)))
  · simpa only [erasureReply, hb, if_false] using
      (EuclideanSpace.proj j).continuous.measurable.div_const (1 - (1 - α))

def sampler {k : ℕ} (a ρ α : ℝ) (v : Fin k → ℝ)
    (z : HardSpace k × (Fin k → Bool)) : HardSpace k :=
  reply α (hardGradient a ρ v z.1) z.2

theorem sampler_measurable {k : ℕ} (a ρ α : ℝ) (v : Fin k → ℝ) :
    Measurable (sampler a ρ α v) :=
  (reply_measurable α).comp
    (((hardGradient_measurable a ρ v).comp measurable_fst).prodMk measurable_snd)

/-- `false` has probability `α` independently in each coordinate. -/
theorem sampler_coordinate {k : ℕ} (a ρ α : ℝ) (v : Fin k → ℝ)
    (x : HardSpace k) (b : Fin k → Bool) (j : Fin k) :
    sampler a ρ α v (x, b) j =
      (a / Real.sqrt k) * Real.sign (x j - ρ * v j) *
        (if b j then 0 else 1) / α := by
  simp only [sampler, reply_apply, erasureReply, sub_sub_cancel]
  split_ifs <;> simp [hardGradient]

def oracle {k : ℕ} (a ρ α : ℝ) (hα : 0 ≤ α) (v : Fin k → ℝ) :
    Kernel (HardSpace k) (HardSpace k) :=
  kernelOfSampler (maskLaw k α hα) (sampler a ρ α v) (sampler_measurable a ρ α v)

instance oracle_markov {k : ℕ} (a ρ α : ℝ) (hα : 0 ≤ α) (v : Fin k → ℝ) :
    IsMarkovKernel (oracle a ρ α hα v) := by
  unfold oracle
  infer_instance

theorem oracle_integrable {k : ℕ} (a ρ α : ℝ) (hα : 0 ≤ α)
    (v : Fin k → ℝ) (x : HardSpace k) :
    Integrable (fun y => y) (oracle a ρ α hα v x) := by
  change Integrable (fun y : HardSpace k => y) ((maskLaw k α hα).map _)
  apply (integrable_map_measure measurable_id.aestronglyMeasurable
    (Measurable.of_discrete : Measurable (fun b => sampler a ρ α v (x, b))).aemeasurable).mpr
  exact Integrable.of_finite

theorem oracle_unbiased {k : ℕ} (a ρ : ℝ) {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (v : Fin k → ℝ) (x : HardSpace k) :
    (∫ y, y ∂oracle a ρ α hα.le v x) = hardGradient a ρ v x := by
  change (∫ y : HardSpace k, y ∂(maskLaw k α hα.le).map _) = _
  calc
    _ = ∫ b, sampler a ρ α v (x, b) ∂maskLaw k α hα.le :=
      integral_map (Measurable.of_discrete : Measurable
        (fun b => sampler a ρ α v (x, b))).aemeasurable
        (measurable_id : Measurable (fun y : HardSpace k => y)).aestronglyMeasurable
    _ = _ := by
      simpa only [sampler] using reply_unbiased (k := k) hα hα1 (hardGradient a ρ v x)

theorem oracle_noise_memLp {k : ℕ} (a ρ α : ℝ) (hα : 0 ≤ α)
    (v : Fin k → ℝ) (x : HardSpace k) (p : ℝ≥0∞) :
    MemLp (fun y => y - ∫ z, z ∂oracle a ρ α hα v x) p (oracle a ρ α hα v x) := by
  change MemLp _ p ((maskLaw k α hα).map _)
  apply (memLp_map_measure_iff
    (measurable_id.sub measurable_const).aestronglyMeasurable
    (Measurable.of_discrete : Measurable (fun b => sampler a ρ α v (x, b))).aemeasurable).mpr
  exact MemLp.of_discrete

/-- The manuscript's displayed strong and weak moment estimates for the
actual kernel, centered at its Bochner mean. -/
theorem oracle_source_moments {k : ℕ} (hk : 0 < k) {a α p : ℝ} (ha : 0 ≤ a)
    (hα : 0 < α) (hα1 : α < 1) (hp : 1 ≤ p) (hp2 : p ≤ 2)
    (ρ : ℝ) (v : Fin k → ℝ) (x : HardSpace k) :
    (∫ y, ‖y - ∫ z, z ∂oracle a ρ α hα.le v x‖ ^ p ∂oracle a ρ α hα.le v x) ≤
      2 * a ^ p * (k : ℝ) ^ (1 - p / 2) * α ^ (1 - p) ∧
    ∀ w : HardSpace k, ‖w‖ = 1 →
    (∫ y, |⟪w, y - ∫ z, z ∂oracle a ρ α hα.le v x⟫_ℝ| ^ p
      ∂oracle a ρ α hα.le v x) ≤
      (2 : ℝ) ^ (p + 1) * a ^ p * (k : ℝ) ^ (1 - p) * α ^ (1 - p) := by
  rw [oracle_unbiased a ρ hα hα1.le v x]
  let g := hardGradient a ρ v x
  have hm := reply_source_moments hk hα hα1 hp hp2 ha g
    (MaskedLower.hardGradient_coordinate_le ha ρ v x)
  have hmap : Measurable (fun b => sampler a ρ α v (x, b)) := Measurable.of_discrete
  constructor
  · change (∫ y, ‖y - g‖ ^ p ∂(maskLaw k α hα.le).map _) ≤ _
    exact (integral_map hmap.aemeasurable
      ((measurable_id.sub_const g).norm.pow_const p).aestronglyMeasurable).trans_le hm.1
  · intro w hw
    change (∫ y, |⟪w, y - g⟫_ℝ| ^ p ∂(maskLaw k α hα.le).map _) ≤ _
    have hc : Continuous (fun y : HardSpace k => |⟪w, y - g⟫_ℝ|) :=
      (continuous_const.inner (continuous_id.sub continuous_const)).abs
    exact (integral_map hmap.aemeasurable (hc.measurable.pow_const p).aestronglyMeasurable).trans_le
      (hm.2 w hw)

/-- The original independent Bernoulli-coordinate oracle obeys both actual
centered moment budgets at the exact source amplitude. -/
theorem source_oracle_two_moment {k : ℕ} (hk : 0 < k) {G L s p α : ℝ}
    (hG : 0 ≤ G) (hL : 0 ≤ L) (hs : 0 ≤ s) (hp : 1 ≤ p) (hp2 : p ≤ 2)
    (hα : 0 < α) (hα1 : α < 1) (hdim : L ^ 2 ≤ (k : ℝ) * s ^ 2)
    (ρ : ℝ) (v : Fin k → ℝ) (x : HardSpace k) :
    let K := oracle (sourceAmplitude G L p k α) ρ α hα.le v
    (∫ y, ‖y - ∫ z, z ∂K x‖ ^ p ∂K x) ≤ L ^ p ∧
    ∀ w : HardSpace k, ‖w‖ = 1 →
      (∫ y, |⟪w, y - ∫ z, z ∂K x⟫_ℝ| ^ p ∂K x) ≤ s ^ p := by
  dsimp only
  have ha := sourceAmplitude_nonneg (p := p) hG hL hα.le k
  have hm := oracle_source_moments hk ha hα hα1 hp hp2 ρ v x
  have hc := sourceAmplitude_two_moment_budgets hk hG hL hs hp hp2 hα hdim
  exact ⟨hm.1.trans hc.1, fun w hw => (hm.2 w hw).trans hc.2⟩

/-- The oracle mean is a genuine subgradient of the source hard loss. -/
theorem source_oracle_mean_subgradient {k : ℕ} {G L p α : ℝ}
    (hG : 0 ≤ G) (hL : 0 ≤ L) (hα : 0 < α) (hα1 : α ≤ 1)
    (ρ : ℝ) (v : Fin k → ℝ) (x y : HardSpace k) :
    hardLoss (sourceAmplitude G L p k α) ρ v x -
        hardLoss (sourceAmplitude G L p k α) ρ v y ≤
      ⟪∫ z, z ∂oracle (sourceAmplitude G L p k α) ρ α hα.le v x, x - y⟫_ℝ := by
  rw [oracle_unbiased _ ρ hα hα1 v x]
  exact hardLoss_subgradient (sourceAmplitude_nonneg hG hL hα.le k) ρ v x y

/-- Source specialization `α = 1/(8T)` and `k ≥ ceil(L²/s²)`. -/
theorem source_oracle_two_moment_raw_budget {k T : ℕ} (hk : 0 < k) (hT : 0 < T)
    {G L s p : ℝ} (hG : 0 ≤ G) (hL : 0 ≤ L) (hs : 0 < s)
    (hp : 1 ≤ p) (hp2 : p ≤ 2) (hdim : Nat.ceil (L ^ 2 / s ^ 2) ≤ k)
    (ρ : ℝ) (v : Fin k → ℝ) (x : HardSpace k) :
    let α : ℝ := 1 / (8 * T)
    let K := oracle (sourceAmplitude G L p k α) ρ α (by positivity) v
    (∫ y, ‖y - ∫ z, z ∂K x‖ ^ p ∂K x) ≤ L ^ p ∧
    ∀ w : HardSpace k, ‖w‖ = 1 →
      (∫ y, |⟪w, y - ∫ z, z ∂K x⟫_ℝ| ^ p ∂K x) ≤ s ^ p := by
  have hTR : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have hα : (0 : ℝ) < 1 / (8 * T) := by positivity
  have hα1 : (1 : ℝ) / (8 * T) < 1 := by
    apply (div_lt_one (by positivity : (0 : ℝ) < 8 * T)).mpr
    linarith
  have hdimR : L ^ 2 / s ^ 2 ≤ (k : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast hdim)
  have hdim' : L ^ 2 ≤ (k : ℝ) * s ^ 2 := (div_le_iff₀ (sq_pos_of_pos hs)).mp hdimR
  exact source_oracle_two_moment hk hG hL hs.le hp hp2 hα hα1 hdim' ρ v x

end
end HeavyTail.IndependentBernoulli
