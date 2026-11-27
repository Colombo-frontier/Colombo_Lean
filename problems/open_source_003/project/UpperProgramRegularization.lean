import UpperProgram
import UpperSmoothing

/-!
Joint measurability is derived from the original local sample assumptions.
The regularization is used only to prove a.e. measurability of actual runs; it
agrees with the original oracle simultaneously at all legal points off one
sample-null set.
-/

open MeasureTheory Set Metric Filter

namespace Task006.Full

theorem ballProj_eq_self {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] {r : ℝ} (hr : 0 ≤ r) {x : E} (hx : ‖x‖ ≤ r) :
    ballProj r hr x = x := by
  have hb := ballProj_distance_sq_le hr x x hx
  simp only [sub_self, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] at hb
  have hn : ‖ballProj r hr x - x‖ = 0 := by nlinarith [norm_nonneg (ballProj r hr x - x)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hn)

namespace SampleInstance

variable {d : ℕ} {L R : ℝ} {Ω : Type*} [MeasurableSpace Ω]
  {μ : Measure Ω} (I : SampleInstance d L R Ω μ)

/-- Carathéodory measurability on the actual query-domain subtype, with one
common null set valid for every adaptively chosen legal query point. -/
theorem exists_joint_regularization_on_domain :
    ∃ F : queryDomain d R → Ω → ℝ,
      Measurable (Function.uncurry F) ∧
      ∀ᵐ ω ∂μ, ∀ x : queryDomain d R, F x ω = I.sample x.val ω := by
  classical
  obtain ⟨G, hGae, hGm, hG⟩ :=
    (I.nonneg_modulus.and I.lipschitz_sample).exists_measurable_mem
  let F : queryDomain d R → Ω → ℝ := fun x ω => if ω ∈ G then I.sample x.val ω else 0
  have hcont : ∀ ω, Continuous (fun x : queryDomain d R => F x ω) := by
    intro ω
    by_cases hω : ω ∈ G
    · have hmod := (hG ω hω).1
      have hlip := (hG ω hω).2
      have hL : LipschitzWith ⟨I.modulus ω, hmod⟩
          (fun x : queryDomain d R => I.sample x.val ω) := by
        apply LipschitzWith.of_dist_le_mul
        intro x y
        change ‖I.sample x.val ω - I.sample y.val ω‖ ≤ I.modulus ω * ‖x.val - y.val‖
        rw [Real.norm_eq_abs]
        exact hlip x.val x.property y.val y.property
      simpa only [F, if_pos hω] using hL.continuous
    · simpa only [F, if_neg hω] using (continuous_const : Continuous (fun _ : queryDomain d R => (0 : ℝ)))
  have hmeas : ∀ x : queryDomain d R, Measurable (F x) := by
    intro x
    exact Measurable.ite hGm (I.measurable_sample x.val x.property) measurable_const
  refine ⟨F, measurable_uncurry_of_continuous_of_measurable hcont hmeas, ?_⟩
  filter_upwards [hGae] with ω hω
  intro x
  exact if_pos hω

/-- A globally jointly measurable surrogate, equal to the original oracle at
all legal points simultaneously for almost every sample. The projection only
extends its off-domain definition and is not performed by the algorithm. -/
theorem exists_joint_regularization (hR : 0 ≤ R) :
    ∃ F : Space d → Ω → ℝ,
      Measurable (Function.uncurry F) ∧
      ∀ᵐ ω ∂μ, ∀ x ∈ queryDomain d R, F x ω = I.sample x ω := by
  obtain ⟨F, hFm, hFae⟩ := I.exists_joint_regularization_on_domain
  have hr : 0 ≤ 2 * R := by positivity
  let π : Space d → queryDomain d R := fun x =>
    ⟨ballProj (2 * R) hr x, ballProj_mem (2 * R) hr x⟩
  have hπ : Measurable π := (ballProj_lipschitz hr).continuous.measurable.subtype_mk
  refine ⟨fun x ω => F (π x) ω,
    hFm.comp ((hπ.comp measurable_fst).prodMk measurable_snd), ?_⟩
  filter_upwards [hFae] with ω hω
  intro x hx
  have hxn : ‖x‖ ≤ 2 * R := by simpa only [queryDomain, mem_closedBall, dist_zero_right] using hx
  have hp := ballProj_eq_self hr hxn
  simpa only [π, hp] using hω (π x)

end SampleInstance

#print axioms SampleInstance.exists_joint_regularization

end Task006.Full
