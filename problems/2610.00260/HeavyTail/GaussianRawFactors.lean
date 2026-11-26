import HeavyTail.GaussianStageMoments
import HeavyTail.RawAcceptanceFactor

/-! The Gaussian learner's actual raw-step factors. Rejected and inactive
rounds contribute one. Measurability, uniform bounds, and raw-kernel moment
bounds are derived from the original oracle contract. -/

noncomputable section
set_option maxHeartbeats 800000
open MeasureTheory Set
open scoped BigOperators InnerProductSpace Classical

namespace HeavyTail

def acceptedGaussianFactorCap (θ : OracleParameters) (τ R a η : ℝ) : ℝ :=
  Real.exp (1 + 2 * η * acceptedMeanScale θ τ * R +
    η ^ 2 * a ^ 2 * (acceptedMeanScale θ τ) ^ 2 / 2)

theorem acceptedGaussianFactorCap_ge_one (θ : OracleParameters) {τ R a η : ℝ}
    (hτ : 64 * (4 * θ.G + θ.L) ≤ τ) (hR : 0 ≤ R) (hη : 0 ≤ η) :
    1 ≤ acceptedGaussianFactorCap θ τ R a η := by
  have hM := (acceptedMeanScale_pos θ hτ).le
  have hlin : 0 ≤ 2 * η * acceptedMeanScale θ τ * R := by positivity
  have hquad : 0 ≤ η ^ 2 * a ^ 2 * (acceptedMeanScale θ τ) ^ 2 / 2 := by positivity
  have he : (0 : ℝ) ≤ 1 + 2 * η * acceptedMeanScale θ τ * R +
      η ^ 2 * a ^ 2 * (acceptedMeanScale θ τ) ^ 2 / 2 := by linarith
  simpa only [Real.exp_zero, acceptedGaussianFactorCap] using Real.exp_le_exp.mpr he

namespace PrivateInstance
open GaussianEntropy GaussianEstimates

variable {ι E : Type*} [Fintype ι]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
  {θ : OracleParameters} {B : PublicProblem E θ}

theorem acceptedGaussianW_measurable (I : PrivateInstance B) {R : ℝ} {n : ℕ}
    (hR : 0 < R) (hn : 0 < n) (τ : ℝ) (c : E) (a η : ℝ) (centers : ι → E) :
    Measurable (fun p : SimplexPoint ι × E => I.acceptedGaussianW hR hn τ c a η centers p.1 p.2) := by
  have hz : Measurable (fun p : SimplexPoint ι × E => finiteMixtureMean centers p.1.val) :=
    (finiteMixtureMean centers).continuous.measurable.comp (measurable_subtype_coe.comp measurable_fst)
  have hY := (B.correctedReply_measurable hR hn).comp (hz.prodMk measurable_snd)
  have hb := (I.acceptedMean_measurable hR hn τ).comp hz
  let input : SimplexPoint ι × E → SimplexPoint ι × (E × (E × E)) := fun p =>
    (p.1, B.correctedReply hR hn (finiteMixtureMean centers p.1.val) p.2,
      I.acceptedMean hR hn τ (finiteMixtureMean centers p.1.val), finiteMixtureMean centers p.1.val)
  have hin : Measurable input := measurable_fst.prodMk (hY.prodMk (hb.prodMk hz))
  have hm := (onlineMixtureW_measurable E c a η centers).comp hin
  simpa only [Function.comp_def, input, acceptedGaussianW] using hm

theorem acceptedGaussianComparatorFactor_measurable (I : PrivateInstance B) {R a : ℝ} {n : ℕ}
    (hR : 0 < R) (hn : 0 < n) (τ : ℝ) (c : E) (ha : a ≠ 0) (η : ℝ)
    (centers : ι → E) (q : SimplexPoint ι) :
    Measurable (fun p : SimplexPoint ι × E =>
      I.acceptedGaussianComparatorFactor hR hn τ c a η centers q p.1 p.2) := by
  have hz : Measurable (fun p : SimplexPoint ι × E => finiteMixtureMean centers p.1.val) :=
    (finiteMixtureMean centers).continuous.measurable.comp (measurable_subtype_coe.comp measurable_fst)
  have hY := (B.correctedReply_measurable hR hn).comp (hz.prodMk measurable_snd)
  have hb := (I.acceptedMean_measurable hR hn τ).comp hz
  exact ((onlineMixtureError_integral_measurable E c ha η centers q.property).comp
    (hY.prodMk (hb.prodMk measurable_fst))).exp

theorem acceptedGaussianW_pos (I : PrivateInstance B) {R : ℝ} {n : ℕ}
    (hR : 0 < R) (hn : 0 < n) (τ : ℝ) (c : E) (a η : ℝ) (centers : ι → E)
    (w : SimplexPoint ι) (g : E) : 0 < I.acceptedGaussianW hR hn τ c a η centers w g :=
  onlineMixtureW_pos E c a η centers w.property _ _ _

theorem acceptedGaussianComparatorFactor_pos (I : PrivateInstance B) {R : ℝ} {n : ℕ}
    (hR : 0 < R) (hn : 0 < n) (τ : ℝ) (c : E) (a η : ℝ) (centers : ι → E)
    (q w : SimplexPoint ι) (g : E) :
    0 < I.acceptedGaussianComparatorFactor hR hn τ c a η centers q w g := Real.exp_pos _

theorem acceptedGaussianW_bound (I : PrivateInstance B) {R τ a η : ℝ} {n : ℕ}
    (hR : 0 < R) (hn : 0 < n) (hτ : 64 * (4 * θ.G + θ.L) ≤ τ)
    (c : E) (centers : ι → E) (hc : ∀ i, ‖centers i - c‖ ≤ R)
    (hcenter : ‖c - I.minimizer‖ ≤ R) (ha : a ≠ 0) (hη : 0 ≤ η)
    (w : SimplexPoint ι) (g : E) :
    I.acceptedGaussianW hR hn τ c a η centers w g ≤ acceptedGaussianFactorCap θ τ R a η :=
  onlineMixtureW_ball_bound E c _ ha hη (acceptedMeanScale_pos θ hτ).le
    (I.acceptedMean_bound hR hn hτ _ (I.acceptedMixtureMean_distance centers hc hcenter w))
    centers hc w.property _

theorem acceptedGaussianComparatorFactor_bound (I : PrivateInstance B) {R τ a η : ℝ} {n : ℕ}
    (hR : 0 < R) (hn : 0 < n) (hτ : 64 * (4 * θ.G + θ.L) ≤ τ)
    (c : E) (centers : ι → E) (hc : ∀ i, ‖centers i - c‖ ≤ R)
    (hcenter : ‖c - I.minimizer‖ ≤ R) (ha : a ≠ 0) (hη : 0 ≤ η)
    (q w : SimplexPoint ι) (g : E) :
    I.acceptedGaussianComparatorFactor hR hn τ c a η centers q w g ≤
      acceptedGaussianFactorCap θ τ R a η := by
  have h := onlineMixture_comparator_factor_bound E c _ ha hη (acceptedMeanScale_pos θ hτ).le
    (I.acceptedMean_bound hR hn hτ _ (I.acceptedMixtureMean_distance centers hc hcenter w))
    centers hc q.property w.property (B.correctedReply hR hn (finiteMixtureMean centers w.val) g)
  apply h.trans
  apply Real.exp_le_exp.mpr
  change _ ≤ 1 + 2 * η * acceptedMeanScale θ τ * R +
    η ^ 2 * a ^ 2 * (acceptedMeanScale θ τ) ^ 2 / 2
  exact le_add_of_nonneg_right (by positivity)

def gaussianRawAcceptance (B : PublicProblem E θ) {R : ℝ} {n : ℕ}
    (hR : 0 < R) (hn : 0 < n) (τ : ℝ) (centers : ι → E) : Set ((ℕ × SimplexPoint ι) × E) :=
  {p | p.1.1 < n ∧ (finiteMixtureMean centers p.1.2.val, p.2) ∈ B.stageAcceptance hR hn τ}

theorem gaussianRawAcceptance_measurable (B : PublicProblem E θ) {R : ℝ} {n : ℕ}
    (hR : 0 < R) (hn : 0 < n) (τ : ℝ) (centers : ι → E) :
    MeasurableSet (gaussianRawAcceptance B hR hn τ centers) := by
  have hz : Measurable (fun p : (ℕ × SimplexPoint ι) × E => finiteMixtureMean centers p.1.2.val) :=
    (finiteMixtureMean centers).continuous.measurable.comp
      (measurable_subtype_coe.comp (measurable_snd.comp measurable_fst))
  exact (measurableSet_lt (measurable_fst.comp measurable_fst) measurable_const).inter
    ((B.stageAcceptance_measurable hR hn τ).preimage (hz.prodMk measurable_snd))

def gaussianRawW (I : PrivateInstance B) {R : ℝ} {n : ℕ}
    (hR : 0 < R) (hn : 0 < n) (τ : ℝ) (c : E) (a η : ℝ) (centers : ι → E)
    (p : (ℕ × SimplexPoint ι) × E) : ℝ :=
  if p ∈ gaussianRawAcceptance B hR hn τ centers then
    I.acceptedGaussianW hR hn τ c a η centers p.1.2 p.2 else 1

def gaussianRawComparatorFactor (I : PrivateInstance B) {R : ℝ} {n : ℕ}
    (hR : 0 < R) (hn : 0 < n) (τ : ℝ) (c : E) (a η : ℝ) (centers : ι → E)
    (q : SimplexPoint ι) (p : (ℕ × SimplexPoint ι) × E) : ℝ :=
  if p ∈ gaussianRawAcceptance B hR hn τ centers then
    I.acceptedGaussianComparatorFactor hR hn τ c a η centers q p.1.2 p.2 else 1

theorem gaussianRawW_measurable (I : PrivateInstance B) {R : ℝ} {n : ℕ}
    (hR : 0 < R) (hn : 0 < n) (τ : ℝ) (c : E) (a η : ℝ) (centers : ι → E) :
    Measurable (I.gaussianRawW hR hn τ c a η centers) := by
  let input : (ℕ × SimplexPoint ι) × E → SimplexPoint ι × E := fun p => (p.1.2, p.2)
  have hin : Measurable input := (measurable_snd.comp measurable_fst).prodMk measurable_snd
  have hm := (I.acceptedGaussianW_measurable hR hn τ c a η centers).comp hin
  have hF : Measurable (fun p : (ℕ × SimplexPoint ι) × E =>
      I.acceptedGaussianW hR hn τ c a η centers p.1.2 p.2) := by
    simpa only [Function.comp_def, input] using hm
  exact Measurable.ite (gaussianRawAcceptance_measurable B hR hn τ centers) hF measurable_const

theorem gaussianRawComparatorFactor_measurable (I : PrivateInstance B) {R a : ℝ} {n : ℕ}
    (hR : 0 < R) (hn : 0 < n) (τ : ℝ) (c : E) (ha : a ≠ 0) (η : ℝ)
    (centers : ι → E) (q : SimplexPoint ι) :
    Measurable (I.gaussianRawComparatorFactor hR hn τ c a η centers q) := by
  let input : (ℕ × SimplexPoint ι) × E → SimplexPoint ι × E := fun p => (p.1.2, p.2)
  have hin : Measurable input := (measurable_snd.comp measurable_fst).prodMk measurable_snd
  have hm := (I.acceptedGaussianComparatorFactor_measurable hR hn τ c ha η centers q).comp hin
  have hF : Measurable (fun p : (ℕ × SimplexPoint ι) × E =>
      I.acceptedGaussianComparatorFactor hR hn τ c a η centers q p.1.2 p.2) := by
    simpa only [Function.comp_def, input] using hm
  exact Measurable.ite (gaussianRawAcceptance_measurable B hR hn τ centers) hF measurable_const

theorem gaussianRawW_pos (I : PrivateInstance B) {R : ℝ} {n : ℕ}
    (hR : 0 < R) (hn : 0 < n) (τ : ℝ) (c : E) (a η : ℝ) (centers : ι → E)
    (p : (ℕ × SimplexPoint ι) × E) : 0 < I.gaussianRawW hR hn τ c a η centers p := by
  unfold gaussianRawW
  split_ifs
  · exact I.acceptedGaussianW_pos hR hn τ c a η centers _ _
  · exact zero_lt_one

theorem gaussianRawComparatorFactor_pos (I : PrivateInstance B) {R : ℝ} {n : ℕ}
    (hR : 0 < R) (hn : 0 < n) (τ : ℝ) (c : E) (a η : ℝ) (centers : ι → E)
    (q : SimplexPoint ι) (p : (ℕ × SimplexPoint ι) × E) :
    0 < I.gaussianRawComparatorFactor hR hn τ c a η centers q p := by
  unfold gaussianRawComparatorFactor
  split_ifs
  · exact I.acceptedGaussianComparatorFactor_pos hR hn τ c a η centers q _ _
  · exact zero_lt_one

theorem gaussianRawW_bound (I : PrivateInstance B) {R τ a η : ℝ} {n : ℕ}
    (hR : 0 < R) (hn : 0 < n) (hτ : 64 * (4 * θ.G + θ.L) ≤ τ)
    (c : E) (centers : ι → E) (hc : ∀ i, ‖centers i - c‖ ≤ R)
    (hcenter : ‖c - I.minimizer‖ ≤ R) (ha : a ≠ 0) (hη : 0 ≤ η)
    (p : (ℕ × SimplexPoint ι) × E) :
    I.gaussianRawW hR hn τ c a η centers p ≤ acceptedGaussianFactorCap θ τ R a η := by
  unfold gaussianRawW
  split_ifs
  · exact I.acceptedGaussianW_bound hR hn hτ c centers hc hcenter ha hη _ _
  · exact acceptedGaussianFactorCap_ge_one θ hτ hR.le hη

theorem gaussianRawComparatorFactor_bound (I : PrivateInstance B) {R τ a η : ℝ} {n : ℕ}
    (hR : 0 < R) (hn : 0 < n) (hτ : 64 * (4 * θ.G + θ.L) ≤ τ)
    (c : E) (centers : ι → E) (hc : ∀ i, ‖centers i - c‖ ≤ R)
    (hcenter : ‖c - I.minimizer‖ ≤ R) (ha : a ≠ 0) (hη : 0 ≤ η)
    (q : SimplexPoint ι) (p : (ℕ × SimplexPoint ι) × E) :
    I.gaussianRawComparatorFactor hR hn τ c a η centers q p ≤
      acceptedGaussianFactorCap θ τ R a η := by
  unfold gaussianRawComparatorFactor
  split_ifs
  · exact I.acceptedGaussianComparatorFactor_bound hR hn hτ c centers hc hcenter ha hη q _ _
  · exact acceptedGaussianFactorCap_ge_one θ hτ hR.le hη

theorem gaussianRawW_moment (I : PrivateInstance B) {R τ a η : ℝ} {n : ℕ}
    (hR : 0 < R) (hn : 0 < n) (hτ : 64 * (4 * θ.G + θ.L) ≤ τ)
    (c : E) (centers : ι → E) (hc : ∀ i, ‖centers i - c‖ ≤ R)
    (hcenter : ‖c - I.minimizer‖ ≤ R) (ha : 0 < a) (haR : a ≤ R)
    (hη : 0 ≤ η) (htune : η * acceptedMeanScale θ τ * R ≤ 1 / 16)
    (k : ℕ) (w : SimplexPoint ι) :
    (∫ g, I.gaussianRawW hR hn τ c a η centers ((k, w), g)
      ∂I.stageRawKernel hR hn (finiteMixtureMean centers w.val)) ≤
      Real.exp (acceptedOnlineExponent θ τ R a η) := by
  let z := finiteMixtureMean centers w.val
  let S := Prod.mk z ⁻¹' B.stageAcceptance hR hn τ
  have hi : Integrable (I.acceptedGaussianW hR hn τ c a η centers w)
      (I.stageRawKernel hR hn z) := by
    apply (integrable_const (acceptedGaussianFactorCap θ τ R a η)).mono'
    · exact ((I.acceptedGaussianW_measurable hR hn τ c a η centers).comp
        measurable_prodMk_left).aestronglyMeasurable
    · apply ae_of_all
      intro g
      rw [Real.norm_of_nonneg (I.acceptedGaussianW_pos hR hn τ c a η centers w g).le]
      exact I.acceptedGaussianW_bound hR hn hτ c centers hc hcenter ha.ne' hη w g
  have hm := I.acceptedGaussianW_moment hR hn hτ c centers hc hcenter ha haR hη htune w
  have he : (fun g => I.gaussianRawW hR hn τ c a η centers ((k, w), g)) =
      (fun g => if k < n then rawAcceptanceFactor S (I.acceptedGaussianW hR hn τ c a η centers w) g else 1) := by
    funext g
    by_cases hk : k < n <;> simp [gaussianRawW, gaussianRawAcceptance, rawAcceptanceFactor, hk, S, z]
  rw [he]
  have hC : 1 ≤ Real.exp (acceptedOnlineExponent θ τ R a η) := by
    simpa only [Real.exp_zero] using
      (Real.exp_le_exp.mpr (acceptedOnlineExponent_nonneg θ hτ hR.le hη))
  exact stopped_rawAcceptanceFactor_bound
    ((B.stageAcceptance_measurable hR hn τ).preimage measurable_prodMk_left)
    (I.stageAcceptance_pos hR hn hτ z (I.acceptedMixtureMean_distance centers hc hcenter w))
    hi.integrableOn hC hm.2 (k < n)

theorem gaussianRawComparatorFactor_moment (I : PrivateInstance B) {R τ a η : ℝ} {n : ℕ}
    (hR : 0 < R) (hn : 0 < n) (hτ : 64 * (4 * θ.G + θ.L) ≤ τ)
    (c : E) (centers : ι → E) (hc : ∀ i, ‖centers i - c‖ ≤ R)
    (hcenter : ‖c - I.minimizer‖ ≤ R) (ha : 0 < a) (haR : a ≤ R)
    (hη : 0 ≤ η) (htune : η * acceptedMeanScale θ τ * R ≤ 1 / 16)
    (q : SimplexPoint ι) (k : ℕ) (w : SimplexPoint ι) :
    (∫ g, I.gaussianRawComparatorFactor hR hn τ c a η centers q ((k, w), g)
      ∂I.stageRawKernel hR hn (finiteMixtureMean centers w.val)) ≤
      Real.exp (acceptedOnlineExponent θ τ R a η) := by
  let z := finiteMixtureMean centers w.val
  let S := Prod.mk z ⁻¹' B.stageAcceptance hR hn τ
  have hi : Integrable (I.acceptedGaussianComparatorFactor hR hn τ c a η centers q w)
      (I.stageRawKernel hR hn z) := by
    apply (integrable_const (acceptedGaussianFactorCap θ τ R a η)).mono'
    · exact ((I.acceptedGaussianComparatorFactor_measurable hR hn τ c ha.ne' η centers q).comp
        measurable_prodMk_left).aestronglyMeasurable
    · apply ae_of_all
      intro g
      rw [Real.norm_of_nonneg (I.acceptedGaussianComparatorFactor_pos hR hn τ c a η centers q w g).le]
      exact I.acceptedGaussianComparatorFactor_bound hR hn hτ c centers hc hcenter ha.ne' hη q w g
  have hm := I.acceptedGaussianComparatorFactor_moment hR hn hτ c centers hc hcenter ha haR hη htune q w
  have he : (fun g => I.gaussianRawComparatorFactor hR hn τ c a η centers q ((k, w), g)) =
      (fun g => if k < n then rawAcceptanceFactor S
        (I.acceptedGaussianComparatorFactor hR hn τ c a η centers q w) g else 1) := by
    funext g
    by_cases hk : k < n <;> simp [gaussianRawComparatorFactor, gaussianRawAcceptance,
      rawAcceptanceFactor, hk, S, z]
  rw [he]
  have hC : 1 ≤ Real.exp (acceptedOnlineExponent θ τ R a η) := by
    simpa only [Real.exp_zero] using
      (Real.exp_le_exp.mpr (acceptedOnlineExponent_nonneg θ hτ hR.le hη))
  exact stopped_rawAcceptanceFactor_bound
    ((B.stageAcceptance_measurable hR hn τ).preimage measurable_prodMk_left)
    (I.stageAcceptance_pos hR hn hτ z (I.acceptedMixtureMean_distance centers hc hcenter w))
    hi.integrableOn hC hm.2 (k < n)

end PrivateInstance
end HeavyTail
