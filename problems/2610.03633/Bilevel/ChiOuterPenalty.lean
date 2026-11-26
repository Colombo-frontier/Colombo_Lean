import Bilevel.ChiBoundedChainReceivers
import Bilevel.ChiBoundedChainRegularity

/-! The actual linear-growth negative-side penalty in the one-sided outer
macro. Its derivative is the concrete smooth cutoff `-theta (-t)`. -/
noncomputable section
open Set
namespace Bilevel.ChiOuter
open ChiBoundedChain

def penalty (t : ℝ) : ℝ := primitive (fun s => -theta (-s)) t

theorem penalty_hasDerivAt (t : ℝ) : HasDerivAt penalty (-theta (-t)) t :=
  primitive_hasDerivAt ((theta_contDiff (k := 0)).continuous.comp continuous_neg).neg t

theorem penalty_deriv (t : ℝ) : deriv penalty t = -theta (-t) :=
  (penalty_hasDerivAt t).deriv

theorem penalty_contDiff (k : ℕ) : ContDiff ℝ k penalty :=
  primitive_contDiff (fun _ => (theta_contDiff.comp contDiff_id.neg).neg) k

theorem penalty_zero_at_zero : penalty 0 = 0 := primitive_zero _

theorem penalty_deriv_range (t : ℝ) : -1 ≤ deriv penalty t ∧ deriv penalty t ≤ 0 := by
  rw [penalty_deriv]
  have ht := theta_range (-t)
  constructor <;> linarith

theorem penalty_deriv_one {t : ℝ} (ht : t ≤ -1) : deriv penalty t = -1 := by
  rw [penalty_deriv, theta_one (by linarith)]

theorem penalty_deriv_zero {t : ℝ} (ht : -(1/2:ℝ) ≤ t) : deriv penalty t = 0 := by
  rw [penalty_deriv, theta_zero (by linarith), neg_zero]

theorem penalty_antitone : Antitone penalty :=
  antitone_of_deriv_nonpos (fun t => (penalty_hasDerivAt t).differentiableAt)
    (fun t => (penalty_deriv_range t).2)

theorem penalty_flat {t : ℝ} (ht : -(1/2:ℝ) ≤ t) : penalty t = 0 := by
  have hb : ∀ x ∈ Ici (-(1/2:ℝ)), ‖deriv penalty x‖ ≤ (0:ℝ) := by
    intro x hx
    rw [penalty_deriv_zero hx, norm_zero]
  have h := Convex.norm_image_sub_le_of_norm_deriv_le
    (fun x (_ : x ∈ Ici (-(1/2:ℝ))) => (penalty_hasDerivAt x).differentiableAt)
    hb (convex_Ici _) (show (0:ℝ) ∈ Ici (-(1/2:ℝ)) by norm_num) ht
  simpa only [penalty_zero_at_zero, sub_zero, zero_mul, norm_le_zero_iff] using h

theorem penalty_nonneg (t : ℝ) : 0 ≤ penalty t := by
  by_cases ht : t ≤ 0
  · simpa only [penalty_zero_at_zero] using penalty_antitone ht
  · rw [penalty_flat (by linarith)]

theorem penalty_lipschitz (s t : ℝ) : |penalty s - penalty t| ≤ |s-t| := by
  simpa only [one_mul] using Regularity.scalar_lip_of_deriv_bound penalty 1
    (fun x => (penalty_hasDerivAt x).differentiableAt)
    (fun x => abs_le.mpr ⟨(penalty_deriv_range x).1,
      (penalty_deriv_range x).2.trans zero_le_one⟩) s t

theorem penalty_linear_bound (t : ℝ) : penalty t ≤ max (-t) 0 := by
  by_cases ht : t ≤ 0
  · have h := penalty_lipschitz t 0
    simpa only [penalty_zero_at_zero, sub_zero, abs_of_nonneg (penalty_nonneg t),
      abs_of_nonpos ht, max_eq_left (neg_nonneg.mpr ht)] using h
  · rw [penalty_flat (by linarith), max_eq_right (by linarith)]

end Bilevel.ChiOuter
