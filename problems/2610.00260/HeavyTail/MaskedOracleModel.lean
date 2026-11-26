import HeavyTail.MaskedAdmissibility
import HeavyTail.MaskedAdaptiveLower
import HeavyTail.OracleQuadratic

/-! The tuned masked-coordinate family is a private instance of the original
two-moment oracle class on the shared public quadratic problem. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal InnerProductSpace
namespace HeavyTail.MaskedLower
noncomputable section

def maskedPrivateInstance {k : ℕ} (θ : OracleParameters) (hk : 0 < k)
    (hdim : θ.L ^ 2 ≤ (k : ℝ) * θ.s ^ 2) (π : ℝ) (hπ : 0 < π)
    (hkπ : (k : ℝ) * π ≤ 1) (v : Fin k → Bool) :
    PrivateInstance (quadraticPublicProblem (HardSpace k) θ) := by
  let a := maskedAmplitude θ.G θ.L θ.p k π
  have ha : 0 ≤ a := maskedAmplitude_nonneg θ.G_pos.le (θ.s_pos.le.trans θ.s_le_L) hπ.le k
  have haG : a ≤ θ.G := maskedAmplitude_le_G θ.G θ.L θ.p k π
  let ρ := envelopeRadius θ.μ θ.D a / Real.sqrt k
  refine {
    f := hardLoss a ρ (gaussianSigns v)
    f_convex := hardLoss_convex ha ρ (gaussianSigns v)
    f_lipschitz := ((hardLoss_lipschitz hk ha ρ (gaussianSigns v)).weaken haG).lipschitzOnWith
    oracle := (maskedKernel a ρ π hπ.le hkπ v).comap Subtype.val measurable_subtype_coe
    oracle_probability := by infer_instance
    reply_integrable := ?_
    mean_subgradient := ?_
    noise_memLp := ?_
    strong_moment := ?_
    weak_moment := ?_
    minimizer := hardCenter θ.μ θ.D a (gaussianSigns v)
    minimizer_domain := Set.mem_univ _
    minimizing := ?_
    initial_distance := ?_ }
  · intro x
    change Integrable (fun y => y) (maskedKernel a ρ π hπ.le hkπ v (x : HardSpace k))
    exact maskedKernel_integrable a ρ π hπ.le hkπ v x
  · intro x y hy
    change hardLoss a ρ (gaussianSigns v) (x : HardSpace k) +
      ⟪∫ g, g ∂maskedKernel a ρ π hπ.le hkπ v (x : HardSpace k), y - (x : HardSpace k)⟫_ℝ ≤ _
    rw [maskedKernel_unbiased a ρ hπ hkπ v (x : HardSpace k)]
    have h := hardLoss_subgradient ha ρ (gaussianSigns v) (x : HardSpace k) y
    rw [← neg_sub (x : HardSpace k) y, inner_neg_right] at *
    linarith
  · intro x
    change MemLp (fun y => y - ∫ z, z ∂maskedKernel a ρ π hπ.le hkπ v (x : HardSpace k))
      (ENNReal.ofReal θ.p) (maskedKernel a ρ π hπ.le hkπ v (x : HardSpace k))
    exact maskedKernel_noise_memLp a ρ π hπ.le hkπ v x (ENNReal.ofReal θ.p)
  · intro x
    change (∫ y, ‖y - ∫ z, z ∂maskedKernel a ρ π hπ.le hkπ v (x : HardSpace k)‖ ^ θ.p
      ∂maskedKernel a ρ π hπ.le hkπ v (x : HardSpace k)) ≤ θ.L ^ θ.p
    exact (tuned_maskedKernel_two_moment hk θ.G_pos.le (θ.s_pos.le.trans θ.s_le_L)
      θ.s_pos.le θ.p_gt_one.le θ.p_le_two hπ hkπ hdim ρ v x).1
  · intro x w hw
    change (∫ y, |⟪w, y - ∫ z, z ∂maskedKernel a ρ π hπ.le hkπ v (x : HardSpace k)⟫_ℝ| ^ θ.p
      ∂maskedKernel a ρ π hπ.le hkπ v (x : HardSpace k)) ≤ θ.s ^ θ.p
    exact (tuned_maskedKernel_two_moment hk θ.G_pos.le (θ.s_pos.le.trans θ.s_le_L)
      θ.s_pos.le θ.p_gt_one.le θ.p_le_two hπ hkπ hdim ρ v x).2 w hw
  · intro y hy
    exact hardComposite_minimizer hk θ.μ_nonneg θ.D_pos.le ha
      (gaussianSigns v) (gaussianSigns_mem v) y
  · simpa only [quadraticPublicProblem_initial, zero_sub, norm_neg] using
      hardCenter_initialization hk θ.μ_nonneg θ.D_pos.le ha
        (gaussianSigns v) (gaussianSigns_mem v)

@[simp] theorem maskedPrivateInstance_oracle {k : ℕ} (θ : OracleParameters) (hk : 0 < k)
    (hdim : θ.L ^ 2 ≤ (k : ℝ) * θ.s ^ 2) (π : ℝ) (hπ : 0 < π)
    (hkπ : (k : ℝ) * π ≤ 1) (v : Fin k → Bool) :
    (maskedPrivateInstance θ hk hdim π hπ hkπ v).oracle =
      (maskedKernel (maskedAmplitude θ.G θ.L θ.p k π)
        (envelopeRadius θ.μ θ.D (maskedAmplitude θ.G θ.L θ.p k π) / Real.sqrt k)
        π hπ.le hkπ v).comap Subtype.val measurable_subtype_coe := rfl

theorem maskedPrivateInstance_loss {k : ℕ} (θ : OracleParameters) (hk : 0 < k)
    (hdim : θ.L ^ 2 ≤ (k : ℝ) * θ.s ^ 2) (π : ℝ) (hπ : 0 < π)
    (hkπ : (k : ℝ) * π ≤ 1) (v : Fin k → Bool)
    (x : (quadraticPublicProblem (HardSpace k) θ).X) :
    (maskedPrivateInstance θ hk hdim π hπ hkπ v).loss x =
      ENNReal.ofReal (GaussianLower.traceLoss θ.μ θ.D (maskedAmplitude θ.G θ.L θ.p k π) v x) := by
  simp only [PrivateInstance.loss, quadraticPublicProblem_S, Set.mem_univ, ↓reduceIte]
  rfl

end
end HeavyTail.MaskedLower
