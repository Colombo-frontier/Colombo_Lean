import HeavyTail.FeasibleOracleModel
import HeavyTail.Rejection
import HeavyTail.RejectionSamplerKernel

/-! Accepted-law guarantees for the actual public feasible-query reduction.
The pre-truncation bounds are discharged from the full private oracle model. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal InnerProductSpace
namespace HeavyTail
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
  {θ : OracleParameters} {B : PublicProblem E θ}

namespace PublicProblem
def stageAcceptance (B : PublicProblem E θ) {R : ℝ} {n : ℕ}
    (hR : 0 < R) (hn : 0 < n) (τ : ℝ) : Set (E × E) :=
  {h | ‖B.correctedReply hR hn h.1 h.2‖ ≤ τ}

theorem stageAcceptance_measurable (B : PublicProblem E θ) {R : ℝ} {n : ℕ}
    (hR : 0 < R) (hn : 0 < n) (τ : ℝ) : MeasurableSet (B.stageAcceptance hR hn τ) :=
  measurableSet_le (B.correctedReply_measurable hR hn).norm measurable_const
end PublicProblem

namespace PrivateInstance
def acceptedRawLaw (I : PrivateInstance B) {R : ℝ} {n : ℕ}
    (hR : 0 < R) (hn : 0 < n) (τ : ℝ) (z : E) : Measure E :=
  ProbabilityTheory.cond (I.stageRawKernel hR hn z) (Prod.mk z ⁻¹' B.stageAcceptance hR hn τ)

def acceptedMean (I : PrivateInstance B) {R : ℝ} {n : ℕ}
    (hR : 0 < R) (hn : 0 < n) (τ : ℝ) (z : E) : E :=
  ∫ g, B.correctedReply hR hn z g ∂I.acceptedRawLaw hR hn τ z

theorem acceptedRawLaw_bounds (I : PrivateInstance B) {R τ : ℝ} {n : ℕ}
    (hR : 0 < R) (hn : 0 < n) (hτ : 64 * (4 * θ.G + θ.L) ≤ τ)
    (z : E) (hz : ‖z - I.minimizer‖ ≤ 2 * R) :
    (I.stageRawKernel hR hn z).real (Prod.mk z ⁻¹' B.stageAcceptance hR hn τ)ᶜ ≤
      (2 * θ.L / τ) ^ θ.p ∧
    (I.stageRawKernel hR hn z).real (Prod.mk z ⁻¹' B.stageAcceptance hR hn τ)ᶜ ≤ 1 / 16 ∧
    ‖I.acceptedMean hR hn τ z - I.correctedMean hR hn z‖ ≤
      rejectionConstant θ.p * θ.s * (θ.L / τ) ^ (θ.p - 1) ∧
    (∫ g, ‖B.correctedReply hR hn z g - I.acceptedMean hR hn τ z‖ ^ 2
      ∂I.acceptedRawLaw hR hn τ z) ≤ rejectionConstant θ.p * θ.L ^ θ.p * τ ^ (2 - θ.p) ∧
    ∀ v : E, ‖v‖ = 1 →
      (∫ g, |⟪v, B.correctedReply hR hn z g - I.acceptedMean hR hn τ z⟫_ℝ| ^ θ.p
        ∂I.acceptedRawLaw hR hn τ z) ≤ rejectionConstant θ.p * θ.s ^ θ.p := by
  let b := I.correctedMean hR hn z
  let ξ : E → E := fun g => B.correctedReply hR hn z g - b
  have hzero : (∫ g, ξ g ∂I.stageRawKernel hR hn z) = 0 := by
    rw [show ξ = fun g => B.correctedReply hR hn z g - b from rfl,
      integral_sub (I.correctedReply_integrable hR hn z) (integrable_const b),
      I.correctedMean_eq_integral, integral_const]
    simp [b]
  have hb : ‖b‖ ≤ 4 * θ.G := (I.correctedMean_bound_transfer hR hn z hz).1
  have hξm : Measurable ξ := (B.correctedReply_measurable_right hR hn z).sub_const b
  have hr := rejection_lemma (E := E) (P := I.stageRawKernel hR hn z) (ξ := ξ) (b := b)
    θ.p_gt_one θ.p_le_two θ.G_pos.le (θ.s_pos.trans_le θ.s_le_L) θ.s_pos.le hτ hb hξm
    (I.correctedReply_noise_memLp hR hn z) hzero (I.correctedReply_strong_moment hR hn z)
    (I.correctedReply_weak_moment hR hn z)
  have hobs : ∀ g, b + ξ g = B.correctedReply hR hn z g := by
    intro g
    dsimp only [ξ]
    abel
  dsimp only at hr
  simp_rw [hobs] at hr
  exact hr

theorem stageAcceptance_pos (I : PrivateInstance B) {R τ : ℝ} {n : ℕ}
    (hR : 0 < R) (hn : 0 < n) (hτ : 64 * (4 * θ.G + θ.L) ≤ τ)
    (z : E) (hz : ‖z - I.minimizer‖ ≤ 2 * R) :
    I.stageRawKernel hR hn z (Prod.mk z ⁻¹' B.stageAcceptance hR hn τ) ≠ 0 := by
  have hb := (I.acceptedRawLaw_bounds hR hn hτ z hz).2.1
  have hm := measureReal_add_measureReal_compl (μ := I.stageRawKernel hR hn z)
    (s := Prod.mk z ⁻¹' B.stageAcceptance hR hn τ)
    ((B.stageAcceptance_measurable hR hn τ).preimage measurable_prodMk_left)
  simp only [measureReal_univ_eq_one] at hm
  intro he
  have hz0 : (I.stageRawKernel hR hn z).real (Prod.mk z ⁻¹' B.stageAcceptance hR hn τ) = 0 := by
    simp [Measure.real, he]
  linarith only [hb, hm, hz0]

theorem acceptedMean_bound (I : PrivateInstance B) {R τ : ℝ} {n : ℕ}
    (hR : 0 < R) (hn : 0 < n) (hτ : 64 * (4 * θ.G + θ.L) ≤ τ)
    (z : E) (hz : ‖z - I.minimizer‖ ≤ 2 * R) :
    ‖I.acceptedMean hR hn τ z‖ ≤
      4 * θ.G + rejectionConstant θ.p * θ.s * (θ.L / τ) ^ (θ.p - 1) := by
  have ha := (I.acceptedRawLaw_bounds hR hn hτ z hz).2.2.1
  have hb := (I.correctedMean_bound_transfer hR hn z hz).1
  have ht := norm_add_le (I.acceptedMean hR hn τ z - I.correctedMean hR hn z) (I.correctedMean hR hn z)
  rw [sub_add_cancel] at ht
  linarith only [ha, hb, ht]

end PrivateInstance
end HeavyTail
