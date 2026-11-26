import NCBall.UpperBatch
import NCBall.UpperOutputGeometry
import NCBall.FiniteChoice

/-! # A uniformly selected block gives an actual Goldstein output -/

noncomputable section
open MeasureTheory Set Metric
open scoped InnerProductSpace BigOperators unitInterval
namespace NCBall

variable {E Ξ : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [MeasurableSpace Ξ]
  {μ : Measure Ξ} [IsProbabilityMeasure μ]

def upperOutputLaw (μ : Measure Ξ) [IsProbabilityMeasure μ] (K : ℕ) (hK : 0 < K) :
    Measure (UpperRandomness Ξ × Fin K) := (upperPoolLaw μ).prod (uniformIndex K hK)

instance upperOutputLaw_probability (μ : Measure Ξ) [IsProbabilityMeasure μ] (K : ℕ) (hK : 0 < K) :
    IsProbabilityMeasure (upperOutputLaw μ K hK) := by
  unfold upperOutputLaw
  infer_instance

def upperRandomOutput (D : ℝ) (hD : 0 ≤ D) (α : ℝ) (G : E → Ξ → E) (x₀ : E) (m : ℕ) {K : ℕ}
    (w : UpperRandomness Ξ × Fin K) : E := upperOutput D hD α G x₀ w.1.1 w.1.2 (w.2.val * m) m

def upperRandomCertificate (D : ℝ) (hD : 0 ≤ D) (α : ℝ) (G : E → Ξ → E) (x₀ : E) (m : ℕ)
    (a : E → E) {K : ℕ} (w : UpperRandomness Ξ × Fin K) : E :=
  (m : ℝ)⁻¹ • ∑ t ∈ Finset.range m, a (upperLocation D hD α G x₀ w.1.1 w.1.2 (w.2.val * m + t))

theorem upperOutput_measurable (D : ℝ) (hD : 0 ≤ D) (α : ℝ) (G : E → Ξ → E)
    (hG : Measurable (fun xz : E × Ξ => G xz.1 xz.2)) (x₀ : E) (s m : ℕ) :
    Measurable (fun w : UpperRandomness Ξ => upperOutput D hD α G x₀ w.1 w.2 s m) := by
  apply Measurable.const_smul
  exact Finset.measurable_sum _ (fun t _ => upperLocation_measurable D hD α G hG x₀ (s + t))

theorem upperRandomOutput_measurable (D : ℝ) (hD : 0 ≤ D) (α : ℝ) (G : E → Ξ → E)
    (hG : Measurable (fun xz : E × Ξ => G xz.1 xz.2)) (x₀ : E) (m K : ℕ) :
    Measurable (upperRandomOutput D hD α G x₀ m (K := K)) :=
  measurable_from_prod_countable (fun k => upperOutput_measurable D hD α G hG x₀ (k.val * m) m)

theorem upperRandomCertificate_measurable (D : ℝ) (hD : 0 ≤ D) (α : ℝ) (G : E → Ξ → E)
    (hG : Measurable (fun xz : E × Ξ => G xz.1 xz.2)) (x₀ : E) (m K : ℕ)
    (a : E → E) (ha : Measurable a) :
    Measurable (upperRandomCertificate D hD α G x₀ m a (K := K)) := by
  apply measurable_from_prod_countable
  intro k
  apply Measurable.const_smul
  exact Finset.measurable_sum _ (fun t _ => ha.comp
    (upperLocation_measurable D hD α G hG x₀ (k.val * m + t)))

omit [BorelSpace E] [SecondCountableTopology E] in
theorem upperRandomCertificate_norm_le {G : E → Ξ → E} {a : E → E} {V : ℝ}
    (ho : OracleMoments μ G a V) (D : ℝ) (hD : 0 ≤ D) (α : ℝ) (x₀ : E)
    {m : ℕ} (hm : 0 < m) {K : ℕ} (w : UpperRandomness Ξ × Fin K) :
    ‖upperRandomCertificate D hD α G x₀ m a w‖ ≤ |V| := by
  have hg : ∀ x, ‖a x‖ ≤ |V| := fun x =>
    kernel_mean_norm_le _ (ho.square_integrable x) _ (ho.mean x) (ho.moment x)
  rw [upperRandomCertificate, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg m))]
  calc
    _ ≤ (m : ℝ)⁻¹ * ∑ _t ∈ Finset.range m, |V| :=
      mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans (Finset.sum_le_sum (fun t _ => hg _)))
        (inv_nonneg.mpr (Nat.cast_nonneg m))
    _ = _ := by simp [ne_of_gt (Nat.cast_pos.mpr hm : (0 : ℝ) < m)]

theorem upperRandomCertificate_integrable {G : E → Ξ → E} {a : E → E} {V : ℝ}
    (ho : OracleMoments μ G a V) (D : ℝ) (hD : 0 ≤ D) (α : ℝ) (x₀ : E)
    {m : ℕ} (hm : 0 < m) (K : ℕ) (hK : 0 < K) :
    Integrable (fun w => ‖upperRandomCertificate D hD α G x₀ m a w‖) (upperOutputLaw μ K hK) := by
  have hm' := (upperRandomCertificate_measurable D hD α G ho.measurable x₀ m K a ho.mean_measurable).norm
  have hp : MemLp (fun w => ‖upperRandomCertificate D hD α G x₀ m a w‖) 2 (upperOutputLaw μ K hK) := by
    apply MemLp.of_bound hm'.aestronglyMeasurable |V|
    filter_upwards [] with w
    simpa only [norm_norm] using upperRandomCertificate_norm_le ho D hD α x₀ hm w
  exact hp.integrable (by norm_num)

theorem upperRandomCertificate_mean {G : E → Ξ → E} {f : E → ℝ} {V : ℝ}
    (hf : ContDiff ℝ 1 f) (ho : OracleMoments μ G (gradient f) V)
    {D α Δ R : ℝ} (hD : 0 < D) (hα : 0 < α) (x₀ : E) {m K : ℕ} (hm : 0 < m) (hK : 0 < K)
    (hpath : (K * m : ℕ) * D ≤ R) (hgap : ∀ x ∈ closedBall x₀ R, f x₀ - f x ≤ Δ) :
    (∫ w, ‖upperRandomCertificate D hD.le α G x₀ m (gradient f) w‖ ∂upperOutputLaw μ K hK) ≤
      Δ / (D * (m : ℝ) * (K : ℝ)) + 2 * D / (α * (m : ℝ)) + α * V ^ 2 / (2 * D) +
        Real.sqrt (m : ℝ) * |V| / (m : ℝ) := by
  rw [show (∫ w, ‖upperRandomCertificate D hD.le α G x₀ m (gradient f) w‖ ∂upperOutputLaw μ K hK) =
      (K : ℝ)⁻¹ * (∫ w : UpperRandomness Ξ, ∑ k ∈ Finset.range K,
        ‖(m : ℝ)⁻¹ • ∑ t ∈ Finset.range m,
          gradient f (upperLocation D hD.le α G x₀ w.1 w.2 (k * m + t))‖ ∂upperPoolLaw μ) from
    uniform_choice_integral (upperPoolLaw μ) K hK
      (fun w k => ‖(m : ℝ)⁻¹ • ∑ t ∈ Finset.range m,
        gradient f (upperLocation D hD.le α G x₀ w.1 w.2 (k * m + t))‖)
      (upperRandomCertificate_integrable ho D hD.le α x₀ hm K hK)]
  exact upper_expected_average_local hf ho hD hα x₀ hm hK hpath hgap

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [MeasurableSpace Ξ] in
theorem upperRandomOutput_in_ball (D : ℝ) (hD : 0 ≤ D) (α : ℝ) (G : E → Ξ → E) (x₀ : E)
    {m : ℕ} (hm : 0 < m) {K : ℕ} (w : UpperRandomness Ξ × Fin K) :
    upperRandomOutput D hD α G x₀ m w ∈ closedBall x₀ ((K * m : ℕ) * D) := by
  have hb := upperOutput_in_ball D hD α G x₀ w.1.1 w.1.2 (w.2.val * m) m hm
  apply (closedBall_subset_closedBall ?_) hb
  apply mul_le_mul_of_nonneg_right _ hD
  exact_mod_cast (show w.2.val * m + m ≤ K * m by nlinarith [w.2.isLt])

theorem upperRandomOutput_success {G : E → Ξ → E} {f : E → ℝ} {V : ℝ}
    (hf : ContDiff ℝ 1 f) (ho : OracleMoments μ G (gradient f) V)
    {D α Δ R ε : ℝ} (hD : 0 < D) (hα : 0 < α) (hε : 0 < ε)
    (x₀ : E) {m K : ℕ} (hm : 0 < m) (hK : 0 < K)
    (hpath : (K * m : ℕ) * D ≤ R) (hgap : ∀ x ∈ closedBall x₀ R, f x₀ - f x ≤ Δ)
    (hbound : Δ / (D * (m : ℝ) * (K : ℝ)) + 2 * D / (α * (m : ℝ)) + α * V ^ 2 / (2 * D) +
      Real.sqrt (m : ℝ) * |V| / (m : ℝ) ≤ ε / 2) :
    ∃ S : Set (UpperRandomness Ξ × Fin K), MeasurableSet S ∧ (1 / 2 : ℝ) ≤ (upperOutputLaw μ K hK).real S ∧
      ∀ w ∈ S, upperRandomOutput D hD.le α G x₀ m w ∈ closedBall x₀ R ∧
        clarkeGoldsteinResidual f ((m : ℝ) * D) (upperRandomOutput D hD.le α G x₀ m w) ≤ ε := by
  let Z := fun w : UpperRandomness Ξ × Fin K => ‖upperRandomCertificate D hD.le α G x₀ m (gradient f) w‖
  have hZ : Measurable Z :=
    (upperRandomCertificate_measurable D hD.le α G ho.measurable x₀ m K (gradient f) ho.mean_measurable).norm
  refine ⟨{w | Z w ≤ ε}, measurableSet_le hZ measurable_const, ?_, ?_⟩
  · exact nonnegative_half_success _ Z hZ (upperRandomCertificate_integrable ho D hD.le α x₀ hm K hK)
      (fun w => norm_nonneg _) hε ((upperRandomCertificate_mean hf ho hD hα x₀ hm hK hpath hgap).trans hbound)
  · intro w hw
    refine ⟨(closedBall_subset_closedBall hpath) (upperRandomOutput_in_ball D hD.le α G x₀ hm w), ?_⟩
    rw [clarkeGoldsteinResidual_eq_of_C1 hf]
    exact (upperOutput_residual_bound D hD.le α G x₀ w.1.1 w.1.2 (w.2.val * m) m hm (gradient f)).trans hw

end NCBall
