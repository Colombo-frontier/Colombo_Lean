import HeavyTail.GaussianAdaptiveLp
import HeavyTail.OracleQuadratic

/-! The Gaussian absolute-value family is an actual private instance of the
public quadratic problem, including the Lp and both moment requirements. -/

open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace
namespace HeavyTail.GaussianLower
noncomputable section
set_option maxHeartbeats 300000

theorem traceKernel_reply_integrable {k : ℕ} (a ρ σ : ℝ) (v : Fin k → Bool) (x : HardSpace k) :
    Integrable (fun y => y) (traceKernel a ρ σ v x) :=
  gaussianResponseKernel_integrable (hardGradient a ρ (gaussianSigns v))
    (hardGradient_measurable a ρ (gaussianSigns v)) σ x

theorem traceKernel_unbiased {k : ℕ} (a ρ σ : ℝ) (v : Fin k → Bool) (x : HardSpace k) :
    (∫ y, y ∂traceKernel a ρ σ v x) = hardGradient a ρ (gaussianSigns v) x :=
  gaussianResponseKernel_unbiased (hardGradient a ρ (gaussianSigns v))
    (hardGradient_measurable a ρ (gaussianSigns v)) σ x

theorem traceKernel_noise_memLp {k : ℕ} (a ρ σ : ℝ) (v : Fin k → Bool) (x : HardSpace k)
    {p : ℝ} (hp2 : p ≤ 2) :
    MemLp (fun y => y - ∫ z, z ∂traceKernel a ρ σ v x)
      (ENNReal.ofReal p) (traceKernel a ρ σ v x) :=
  gaussianResponseKernel_noise_memLp (hardGradient a ρ (gaussianSigns v))
    (hardGradient_measurable a ρ (gaussianSigns v)) σ hp2 x

def gaussianPrivateInstance {k : ℕ} (θ : OracleParameters) (hk : 0 < k)
    (hdim : θ.L ^ 2 ≤ (k : ℝ) * θ.s ^ 2) (a : ℝ) (ha : 0 ≤ a) (haG : a ≤ θ.G)
    (v : Fin k → Bool) : PrivateInstance (quadraticPublicProblem (HardSpace k) θ) where
  f := hardLoss a (envelopeRadius θ.μ θ.D a / Real.sqrt k) (gaussianSigns v)
  f_convex := hardLoss_convex ha _ _
  f_lipschitz := ((hardLoss_lipschitz hk ha _ _).weaken haG).lipschitzOnWith
  oracle := (traceKernel a (envelopeRadius θ.μ θ.D a / Real.sqrt k)
    (θ.L / Real.sqrt k) v).comap Subtype.val measurable_subtype_coe
  oracle_probability := by infer_instance
  reply_integrable x := by
    change Integrable (fun y => y) (traceKernel a (envelopeRadius θ.μ θ.D a / Real.sqrt k)
      (θ.L / Real.sqrt k) v (x : HardSpace k))
    exact traceKernel_reply_integrable _ _ _ _ _
  mean_subgradient x y _ := by
    change hardLoss a (envelopeRadius θ.μ θ.D a / Real.sqrt k) (gaussianSigns v) (x : HardSpace k) +
      ⟪∫ g, g ∂traceKernel a (envelopeRadius θ.μ θ.D a / Real.sqrt k)
        (θ.L / Real.sqrt k) v (x : HardSpace k), y - (x : HardSpace k)⟫_ℝ ≤ _
    rw [traceKernel_unbiased]
    have h := hardLoss_subgradient ha (envelopeRadius θ.μ θ.D a / Real.sqrt k)
      (gaussianSigns v) (x : HardSpace k) y
    rw [← neg_sub (x : HardSpace k) y, inner_neg_right] at *
    linarith
  noise_memLp x := by
    change MemLp (fun y => y - ∫ z, z ∂traceKernel a
      (envelopeRadius θ.μ θ.D a / Real.sqrt k) (θ.L / Real.sqrt k) v (x : HardSpace k))
      (ENNReal.ofReal θ.p) (traceKernel a (envelopeRadius θ.μ θ.D a / Real.sqrt k)
        (θ.L / Real.sqrt k) v (x : HardSpace k))
    exact traceKernel_noise_memLp _ _ _ _ _ θ.p_le_two
  strong_moment x := by
    change (∫ g, ‖g - ∫ z, z ∂traceKernel a _ _ v x‖ ^ θ.p
      ∂traceKernel a _ _ v x) ≤ _
    rw [traceKernel_unbiased]
    exact (traceKernel_two_moment hk (θ.s_pos.le.trans θ.s_le_L) θ.s_pos.le
      (le_trans (by norm_num) θ.p_gt_one.le) θ.p_le_two hdim a _ v x).1
  weak_moment x w hw := by
    change (∫ g, |⟪w, g - ∫ z, z ∂traceKernel a _ _ v x⟫_ℝ| ^ θ.p
      ∂traceKernel a _ _ v x) ≤ _
    rw [traceKernel_unbiased]
    exact (traceKernel_two_moment hk (θ.s_pos.le.trans θ.s_le_L) θ.s_pos.le
      (le_trans (by norm_num) θ.p_gt_one.le) θ.p_le_two hdim a _ v x).2 w hw
  minimizer := hardCenter θ.μ θ.D a (gaussianSigns v)
  minimizer_domain := Set.mem_univ _
  minimizing y _ := hardComposite_minimizer hk θ.μ_nonneg θ.D_pos.le ha
    (gaussianSigns v) (gaussianSigns_mem v) y
  initial_distance := by
    simpa only [quadraticPublicProblem_initial, zero_sub, norm_neg] using
      hardCenter_initialization hk θ.μ_nonneg θ.D_pos.le ha
        (gaussianSigns v) (gaussianSigns_mem v)

theorem gaussianPrivateInstance_loss {k : ℕ} (θ : OracleParameters) (hk : 0 < k)
    (hdim : θ.L ^ 2 ≤ (k : ℝ) * θ.s ^ 2) (a : ℝ) (ha : 0 ≤ a) (haG : a ≤ θ.G)
    (v : Fin k → Bool) (x : (quadraticPublicProblem (HardSpace k) θ).X) :
    (gaussianPrivateInstance θ hk hdim a ha haG v).loss x =
      ENNReal.ofReal (traceLoss θ.μ θ.D a v x) := by
  simp only [PrivateInstance.loss, quadraticPublicProblem_S, Set.mem_univ, ↓reduceIte]
  rfl

end
end HeavyTail.GaussianLower


