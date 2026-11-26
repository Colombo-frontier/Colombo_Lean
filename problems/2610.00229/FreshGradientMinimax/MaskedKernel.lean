import FreshGradientMinimax.BernoulliKernel
import FreshGradientMinimax.MaskedOracle

/-! Equations (31)--(32) as a genuine fresh-gradient Markov kernel on the full
joint space. Only the analytic full/truncated residual bound is an input; the
kernel, measurability, integrability, mean and variance are constructed here. -/

set_option autoImplicit false
noncomputable section
namespace FreshGradientMinimax
open MeasureTheory ProbabilityTheory

variable {dx dy : ℕ}

def jointMaskedReply (p : ℝ) (base full : Joint dx dy) (coin : Bool) : Joint dx dy :=
  (maskedReply p base.1 full.1 coin, maskedReply p base.2 full.2 coin)

theorem jointMaskedReply_mean {p : ℝ} (hp : p ≠ 0) (base full : Joint dx dy) :
    p • jointMaskedReply p base full true + (1 - p) • jointMaskedReply p base full false = full := by
  apply Prod.ext
  · exact masked_unbiased hp base.1 full.1
  · exact masked_unbiased hp base.2 full.2

theorem jointMaskedReply_variance {p : ℝ} (hp : p ≠ 0) (base full : Joint dx dy) :
    p * jointNormSq (jointMaskedReply p base full true - full) +
      (1 - p) * jointNormSq (jointMaskedReply p base full false - full) =
      (p⁻¹ - 1) * jointNormSq (full - base) := by
  calc
    _ = bernoulliMSE p (maskedReply p base.1 full.1) full.1 +
        bernoulliMSE p (maskedReply p base.2 full.2) full.2 := by
      simp only [bernoulliMSE, jointNormSq, jointMaskedReply, Prod.fst_sub, Prod.snd_sub]
      ring
    _ = _ := by
      rw [masked_variance hp, masked_variance hp]
      simp only [jointNormSq, Prod.fst_sub, Prod.snd_sub]
      ring

theorem revealProbability_variance_factor {r s v : ℝ} (hr : 0 < r) (hs : 0 ≤ s)
    (hv : v ≤ r) : (revealProbability r s)⁻¹ * v - v ≤ s := by
  by_cases hs0 : s = 0
  · simp [revealProbability, hs0]
  · have hspos : 0 < s := lt_of_le_of_ne hs (Ne.symm hs0)
    by_cases hrs : 1 ≤ r / s
    · simp [revealProbability, hs0, min_eq_left hrs, hs]
    · have hrs' : r / s ≤ 1 := le_of_not_ge hrs
      rw [revealProbability, if_neg hs0, min_eq_right hrs', inv_div]
      have hrs2 : r ≤ s := (div_le_one hspos).mp hrs'
      have hc : 0 ≤ s / r - 1 := by
        have : 1 ≤ s / r := (le_div_iff₀ hr).mpr (by simpa using hrs2)
        linarith
      have h := mul_le_mul_of_nonneg_left hv hc
      have he : (s / r - 1) * r = s - r := by field_simp
      rw [he] at h
      nlinarith

theorem jointMaskedReply_true_measurable {Q : Type*} [MeasurableSpace Q]
    (p : ℝ) (base full : Q → Joint dx dy) (hb : Measurable base) (hf : Measurable full) :
    Measurable (fun q => jointMaskedReply p (base q) (full q) true) := by
  unfold jointMaskedReply maskedReply
  simp only [↓reduceIte]
  exact (hb.fst.add ((hf.fst.sub hb.fst).const_smul p⁻¹)).prodMk
    (hb.snd.add ((hf.snd.sub hb.snd).const_smul p⁻¹))

def maskedGradientKernel (p : ℝ) (base full : Joint dx dy → Joint dx dy)
    (hb : Measurable base) (hf : Measurable full) : Kernel (Joint dx dy) (Joint dx dy) :=
  bernoulliKernel p (fun z => jointMaskedReply p (base z) (full z) true) base
    (jointMaskedReply_true_measurable p base full hb hf) hb

theorem maskedGradientKernel_markov {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (base full : Joint dx dy → Joint dx dy) (hb : Measurable base) (hf : Measurable full) :
    IsMarkovKernel (maskedGradientKernel p base full hb hf) :=
  bernoulliKernel_markov hp hp1 _ _ _ _

theorem maskedGradientKernel_integrable (p : ℝ) (base full : Joint dx dy → Joint dx dy)
    (hb : Measurable base) (hf : Measurable full) (z : Joint dx dy) :
    Integrable id (maskedGradientKernel p base full hb hf z) :=
  bernoulliKernel_integrable _ _ _ _ _ _ _

theorem maskedGradientKernel_mean {p : ℝ} (hp : 0 < p) (hp1 : p ≤ 1)
    (base full : Joint dx dy → Joint dx dy) (hb : Measurable base) (hf : Measurable full)
    (z : Joint dx dy) : (∫ v, v ∂maskedGradientKernel p base full hb hf z) = full z := by
  rw [maskedGradientKernel, bernoulliKernel_integral hp.le hp1]
  simpa only [jointMaskedReply, maskedReply, Bool.false_eq_true, ↓reduceIte,
    Prod.mk.eta, id_eq] using jointMaskedReply_mean hp.ne' (base z) (full z)

theorem maskedGradientKernel_square_integrable (p : ℝ)
    (base full : Joint dx dy → Joint dx dy) (hb : Measurable base) (hf : Measurable full)
    (z : Joint dx dy) :
    Integrable (fun v => jointNormSq (v - full z)) (maskedGradientKernel p base full hb hf z) :=
  bernoulliKernel_integrable _ _ _ _ _ _ _

theorem maskedGradientKernel_variance {p : ℝ} (hp : 0 < p) (hp1 : p ≤ 1)
    (base full : Joint dx dy → Joint dx dy) (hb : Measurable base) (hf : Measurable full)
    (z : Joint dx dy) :
    (∫ v, jointNormSq (v - full z) ∂maskedGradientKernel p base full hb hf z) =
      (p⁻¹ - 1) * jointNormSq (full z - base z) := by
  rw [maskedGradientKernel, bernoulliKernel_integral hp.le hp1]
  simpa only [jointMaskedReply, maskedReply, Bool.false_eq_true, ↓reduceIte,
    Prod.mk.eta, smul_eq_mul] using jointMaskedReply_variance hp.ne' (base z) (full z)

def FreshOracle.masked {L μ : ℝ} (O : NCObjective dx dy L μ) (σ r : ℝ) (hr : 0 < r)
    (base : Joint dx dy → Joint dx dy) (hb : Measurable base)
    (hR : ∀ z, jointNormSq (O.jointGradient z - base z) ≤ r) : FreshOracle O σ where
  kernel := maskedGradientKernel (revealProbability r (σ ^ 2)) base O.jointGradient hb
    O.jointGradient_continuous.measurable
  markov := maskedGradientKernel_markov (revealProbability_pos hr (sq_nonneg σ)).le
    (revealProbability_le_one _ _) _ _ _ _
  integrable := maskedGradientKernel_integrable _ _ _ _ _
  mean := maskedGradientKernel_mean (revealProbability_pos hr (sq_nonneg σ))
    (revealProbability_le_one _ _) _ _ _ _
  square_integrable := maskedGradientKernel_square_integrable _ _ _ _ _
  variance_le z := by
    rw [maskedGradientKernel_variance (revealProbability_pos hr (sq_nonneg σ))
      (revealProbability_le_one _ _)]
    have h := revealProbability_variance_factor hr (sq_nonneg σ) (hR z)
    nlinarith only [h]

theorem maskedGradientKernel_one (base full : Joint dx dy → Joint dx dy)
    (hb : Measurable base) (hf : Measurable full) :
    maskedGradientKernel 1 base full hb hf = Kernel.deterministic full hf := by
  rw [maskedGradientKernel, bernoulliKernel_one]
  congr 1
  funext z
  exact Prod.ext (masked_exact _ _) (masked_exact _ _)

theorem FreshOracle.masked_zero_kernel {L μ : ℝ} (O : NCObjective dx dy L μ)
    (r : ℝ) (hr : 0 < r) (base : Joint dx dy → Joint dx dy) (hb : Measurable base)
    (hR : ∀ z, jointNormSq (O.jointGradient z - base z) ≤ r) :
    (FreshOracle.masked O 0 r hr base hb hR).kernel = (FreshOracle.exact O 0).kernel := by
  change maskedGradientKernel (revealProbability r (0 ^ 2)) base O.jointGradient hb
    O.jointGradient_continuous.measurable = _
  simp only [zero_pow (by norm_num : 2 ≠ 0), revealProbability, ↓reduceIte]
  exact maskedGradientKernel_one _ _ _ _

end FreshGradientMinimax
