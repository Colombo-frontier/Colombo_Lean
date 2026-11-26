import FreshGradientMinimax.BatchKernel

/-! Three independent draws for the importance-weighted correction in F.1. -/

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
namespace FreshGradientMinimax
open MeasureTheory ProbabilityTheory

variable {Q : Type*} [MeasurableSpace Q] {d : ℕ}

def correctionValue (p : ℝ) (z : Euclid d × (Euclid d × Euclid d)) : Euclid d :=
  z.1 + p⁻¹ • (z.2.1 - z.2.2)

theorem correctionValue_continuous (p : ℝ) : Continuous (correctionValue (d := d) p) := by
  exact continuous_fst.add (continuous_const.smul
    ((continuous_fst.comp continuous_snd).sub (continuous_snd.comp continuous_snd)))

theorem correctionValue_square_bound (p : ℝ) (g : Euclid d)
    (z : Euclid d × (Euclid d × Euclid d)) :
    ‖correctionValue p z - g‖ ^ 2 ≤
      2 * ‖z.1 - g‖ ^ 2 + 4 * (p⁻¹) ^ 2 * (‖z.2.1 - g‖ ^ 2 + ‖z.2.2 - g‖ ^ 2) := by
  have h0 := norm_add_sq_le_two (z.1 - g) (p⁻¹ • (z.2.1 - z.2.2))
  have h1 := norm_add_sq_le_two (z.2.1 - g) (-(z.2.2 - g))
  rw [norm_neg, show z.2.1 - g + -(z.2.2 - g) = z.2.1 - z.2.2 by abel] at h1
  rw [norm_smul_sq] at h0
  have h2 := mul_le_mul_of_nonneg_left h1 (by positivity : 0 ≤ 2 * (p⁻¹) ^ 2)
  rw [show z.1 - g + p⁻¹ • (z.2.1 - z.2.2) = correctionValue p z - g by
    dsimp [correctionValue]; abel] at h0
  nlinarith only [h0, h2]

def independentCorrectionKernel (K0 K1 K2 : Kernel Q (Euclid d)) (p : ℝ) :
    Kernel Q (Euclid d) := (K0 ×ₖ (K1 ×ₖ K2)).map (correctionValue p)

instance independentCorrectionKernel_markov (K0 K1 K2 : Kernel Q (Euclid d)) (p : ℝ)
    [IsMarkovKernel K0] [IsMarkovKernel K1] [IsMarkovKernel K2] :
    IsMarkovKernel (independentCorrectionKernel K0 K1 K2 p) :=
  Kernel.IsMarkovKernel.map _ (correctionValue_continuous p).measurable

theorem independentCorrectionKernel_apply (K0 K1 K2 : Kernel Q (Euclid d)) (p : ℝ)
    [IsMarkovKernel K0] [IsMarkovKernel K1] [IsMarkovKernel K2] (q : Q) :
    independentCorrectionKernel K0 K1 K2 p q =
      Measure.map (correctionValue p) ((K0 q).prod ((K1 q).prod (K2 q))) := by
  rw [independentCorrectionKernel, Kernel.map_apply _ (correctionValue_continuous p).measurable,
    Kernel.prod_apply, Kernel.prod_apply]

variable (K0 K1 K2 : Kernel Q (Euclid d)) (p : ℝ)
  [IsMarkovKernel K0] [IsMarkovKernel K1] [IsMarkovKernel K2] (q : Q)

theorem independentCorrectionKernel_integrable
    (h0 : Integrable id (K0 q)) (h1 : Integrable id (K1 q)) (h2 : Integrable id (K2 q)) :
    Integrable id (independentCorrectionKernel K0 K1 K2 p q) := by
  rw [independentCorrectionKernel_apply]
  apply (integrable_map_measure measurable_id.aestronglyMeasurable
    (correctionValue_continuous p).measurable.aemeasurable).mpr
  have hc : Integrable (fun z : Euclid d × Euclid d => p⁻¹ • (z.1 - z.2))
      ((K1 q).prod (K2 q)) :=
    ((integrable_on_product_fst h1).sub (integrable_on_product_snd h2)).smul p⁻¹
  exact (integrable_on_product_fst h0).add (integrable_on_product_snd hc)

theorem independentCorrectionKernel_mean
    (h0 : Integrable id (K0 q)) (h1 : Integrable id (K1 q)) (h2 : Integrable id (K2 q)) :
    (∫ r, r ∂independentCorrectionKernel K0 K1 K2 p q) =
      (∫ r, r ∂K0 q) + p⁻¹ • ((∫ r, r ∂K1 q) - ∫ r, r ∂K2 q) := by
  rw [independentCorrectionKernel_apply, integral_map (f := fun r : Euclid d => r)
    (correctionValue_continuous p).measurable.aemeasurable measurable_id.aestronglyMeasurable]
  change Integrable (fun r : Euclid d => r) (K0 q) at h0
  change Integrable (fun r : Euclid d => r) (K1 q) at h1
  change Integrable (fun r : Euclid d => r) (K2 q) at h2
  have hdiff := (integrable_on_product_fst h1).sub (integrable_on_product_snd h2)
  have hc : Integrable (fun z : Euclid d × Euclid d => p⁻¹ • (z.1 - z.2))
      ((K1 q).prod (K2 q)) := hdiff.smul p⁻¹
  change (∫ z, z.1 + p⁻¹ • (z.2.1 - z.2.2) ∂(K0 q).prod ((K1 q).prod (K2 q))) = _
  rw [independent_sum_mean h0 hc, integral_smul,
    integral_sub (integrable_on_product_fst h1) (integrable_on_product_snd h2)]
  rw [integral_fun_fst (fun r : Euclid d => r), integral_fun_snd (fun r : Euclid d => r)]
  simp

theorem independentCorrectionKernel_square_integrable (g : Euclid d)
    (h0 : Integrable (fun r => ‖r - g‖ ^ 2) (K0 q))
    (h1 : Integrable (fun r => ‖r - g‖ ^ 2) (K1 q))
    (h2 : Integrable (fun r => ‖r - g‖ ^ 2) (K2 q)) :
    Integrable (fun r => ‖r - g‖ ^ 2) (independentCorrectionKernel K0 K1 K2 p q) := by
  rw [independentCorrectionKernel_apply]
  apply (integrable_map_measure (g := fun r : Euclid d => ‖r - g‖ ^ 2)
    ((continuous_id.sub continuous_const).norm.pow 2).aestronglyMeasurable
    (correctionValue_continuous p).measurable.aemeasurable).mpr
  have hi : Integrable (fun z : Euclid d × (Euclid d × Euclid d) =>
      2 * ‖z.1 - g‖ ^ 2 + 4 * (p⁻¹) ^ 2 * (‖z.2.1 - g‖ ^ 2 + ‖z.2.2 - g‖ ^ 2))
      ((K0 q).prod ((K1 q).prod (K2 q))) :=
    ((integrable_on_product_fst h0).const_mul _).add
      ((integrable_on_product_snd ((integrable_on_product_fst h1).add
        (integrable_on_product_snd h2))).const_mul _)
  apply hi.mono' (((correctionValue_continuous p).sub continuous_const).norm.pow 2).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun z => by
    rw [Real.norm_eq_abs, abs_sq]
    exact correctionValue_square_bound p g z)

theorem independentCorrectionKernel_error (g : Euclid d)
    (h0 : Integrable (fun r => ‖r - g‖ ^ 2) (K0 q))
    (h1 : Integrable (fun r => ‖r - g‖ ^ 2) (K1 q))
    (h2 : Integrable (fun r => ‖r - g‖ ^ 2) (K2 q)) :
    (∫ r, ‖r - g‖ ^ 2 ∂independentCorrectionKernel K0 K1 K2 p q) ≤
      2 * (∫ r, ‖r - g‖ ^ 2 ∂K0 q) +
        4 * (p⁻¹) ^ 2 * ((∫ r, ‖r - g‖ ^ 2 ∂K1 q) + ∫ r, ‖r - g‖ ^ 2 ∂K2 q) := by
  have hf0 : Integrable (fun z : Euclid d × (Euclid d × Euclid d) => ‖z.1 - g‖ ^ 2)
      ((K0 q).prod ((K1 q).prod (K2 q))) := integrable_on_product_fst h0
  have hf12 : Integrable (fun z : Euclid d × (Euclid d × Euclid d) =>
      ‖z.2.1 - g‖ ^ 2 + ‖z.2.2 - g‖ ^ 2) ((K0 q).prod ((K1 q).prod (K2 q))) :=
    integrable_on_product_snd ((integrable_on_product_fst h1).add (integrable_on_product_snd h2))
  have hi := independentCorrectionKernel_square_integrable K0 K1 K2 p q g h0 h1 h2
  rw [independentCorrectionKernel_apply] at hi ⊢
  have ha : AEMeasurable (correctionValue (d := d) p)
      ((K0 q).prod ((K1 q).prod (K2 q))) := (correctionValue_continuous p).measurable.aemeasurable
  have hb : AEStronglyMeasurable (fun r : Euclid d => ‖r - g‖ ^ 2)
      (Measure.map (correctionValue p) ((K0 q).prod ((K1 q).prod (K2 q)))) :=
    ((continuous_id.sub continuous_const).norm.pow 2).aestronglyMeasurable
  have hi' := (integrable_map_measure hb ha).mp hi
  rw [integral_map (f := fun r : Euclid d => ‖r - g‖ ^ 2) ha hb]
  calc
    _ ≤ ∫ z, 2 * ‖z.1 - g‖ ^ 2 + 4 * (p⁻¹) ^ 2 *
        (‖z.2.1 - g‖ ^ 2 + ‖z.2.2 - g‖ ^ 2) ∂(K0 q).prod ((K1 q).prod (K2 q)) :=
      integral_mono hi' ((hf0.const_mul _).add (hf12.const_mul _)) (correctionValue_square_bound p g)
    _ = _ := by
      rw [integral_add (hf0.const_mul _) (hf12.const_mul _), integral_const_mul, integral_const_mul,
        integral_fun_fst (fun r => ‖r - g‖ ^ 2),
        integral_fun_snd (fun z : Euclid d × Euclid d => ‖z.1 - g‖ ^ 2 + ‖z.2 - g‖ ^ 2),
        integral_add (integrable_on_product_fst h1) (integrable_on_product_snd h2),
        integral_fun_fst (fun r => ‖r - g‖ ^ 2), integral_fun_snd (fun r => ‖r - g‖ ^ 2)]
      simp

end FreshGradientMinimax
