import MatchingBounds1005.GaussianComparison
import Mathlib.Probability.Kernel.CompProdEqIff
import Mathlib.Probability.Kernel.Composition.IntegralCompProd

/-!
# Relative entropy for actual sequential probability kernels

The composition-product density is derived from Radon-Nikodym derivatives
of the history measures and transition kernels. No chain-rule identity is
assumed as a hypothesis.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal

namespace MatchingBounds1005.KernelKL

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
variable {P Q : Measure α} [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
variable (κ η : Kernel α β) [IsMarkovKernel κ] [IsMarkovKernel η]

theorem compProd_density_left (hPQ : P ≪ Q) :
    (Q ⊗ₘ η).withDensity (fun p : α × β => P.rnDeriv Q p.1) = P ⊗ₘ η := by
  have hf : Measurable (fun p : α × β => P.rnDeriv Q p.1) :=
    (P.measurable_rnDeriv Q).comp measurable_fst
  ext s hs
  rw [withDensity_apply _ hs, ← lintegral_indicator hs,
    Measure.lintegral_compProd (hf.indicator hs), Measure.compProd_apply hs]
  have hi (a : α) :
      (∫⁻ b, s.indicator (fun p : α × β => P.rnDeriv Q p.1) (a, b) ∂η a) =
        P.rnDeriv Q a * η a (Prod.mk a ⁻¹' s) := by
    change (∫⁻ b, (Prod.mk a ⁻¹' s).indicator (fun _ => P.rnDeriv Q a) b ∂η a) = _
    rw [lintegral_indicator (measurable_prodMk_left hs), lintegral_const]
    simp
  simp_rw [hi]
  exact lintegral_rnDeriv_mul hPQ (Kernel.measurable_kernel_prodMk_left hs).aemeasurable

variable [MeasurableSpace.CountableOrCountablyGenerated α β]

theorem compProd_density (hPQ : P ≪ Q) (hκη : ∀ a, κ a ≪ η a) :
    (Q ⊗ₘ η).withDensity
      (fun p : α × β => P.rnDeriv Q p.1 * κ.rnDeriv η p.1 p.2) = P ⊗ₘ κ := by
  have hk : η.withDensity (κ.rnDeriv η) = κ := by
    ext a s hs
    rw [Kernel.withDensity_rnDeriv_eq (hκη a)]
  haveI : IsMarkovKernel (η.withDensity (κ.rnDeriv η)) := by rw [hk]; infer_instance
  calc
    (Q ⊗ₘ η).withDensity (fun p : α × β => P.rnDeriv Q p.1 * κ.rnDeriv η p.1 p.2) =
        ((Q ⊗ₘ η).withDensity (fun p : α × β => P.rnDeriv Q p.1)).withDensity
          (fun p => κ.rnDeriv η p.1 p.2) :=
      withDensity_mul (Q ⊗ₘ η) ((P.measurable_rnDeriv Q).comp measurable_fst)
        (κ.measurable_rnDeriv η)
    _ = (P ⊗ₘ η).withDensity (fun p => κ.rnDeriv η p.1 p.2) := by
      rw [compProd_density_left η hPQ]
    _ = P ⊗ₘ η.withDensity (κ.rnDeriv η) :=
      (Measure.compProd_withDensity (κ.measurable_rnDeriv η)).symm
    _ = P ⊗ₘ κ := by rw [hk]

theorem compProd_rnDeriv (hPQ : P ≪ Q) (hκη : ∀ a, κ a ≪ η a) :
    (P ⊗ₘ κ).rnDeriv (Q ⊗ₘ η) =ᵐ[Q ⊗ₘ η]
      (fun p : α × β => P.rnDeriv Q p.1 * κ.rnDeriv η p.1 p.2) := by
  have h := (Q ⊗ₘ η).rnDeriv_withDensity
    (((P.measurable_rnDeriv Q).comp measurable_fst).mul (κ.measurable_rnDeriv η))
  dsimp only [Function.comp_def] at h
  rwa [compProd_density κ η hPQ hκη] at h

def kernelLLR (p : α × β) : ℝ := Real.log ((κ.rnDeriv η p.1 p.2).toReal)

omit [IsMarkovKernel κ] [IsMarkovKernel η] in
theorem kernelLLR_measurable : Measurable (kernelLLR κ η) :=
  (κ.measurable_rnDeriv η).ennreal_toReal.log

theorem compProd_llr (hPQ : P ≪ Q) (hκη : ∀ a, κ a ≪ η a) :
    llr (P ⊗ₘ κ) (Q ⊗ₘ η) =ᵐ[P ⊗ₘ κ]
      (fun p => llr P Q p.1 + kernelLLR κ η p) := by
  have hAC : P ⊗ₘ κ ≪ Q ⊗ₘ η := hPQ.compProd (ae_of_all P hκη)
  have hp : ∀ᵐ a ∂P, 0 < (P.rnDeriv Q a).toReal := by
    filter_upwards [Measure.rnDeriv_pos hPQ, hPQ.ae_le (P.rnDeriv_ne_top Q)] with a ha ht
    exact ENNReal.toReal_pos ha.ne' ht
  have hboth : ∀ᵐ p ∂(P ⊗ₘ κ),
      0 < (P.rnDeriv Q p.1).toReal ∧ 0 < (κ.rnDeriv η p.1 p.2).toReal := by
    apply Measure.ae_compProd_of_ae_ae
    · exact (measurableSet_lt measurable_const
        (((P.measurable_rnDeriv Q).comp measurable_fst).ennreal_toReal)).inter
        (measurableSet_lt measurable_const (κ.measurable_rnDeriv η).ennreal_toReal)
    · filter_upwards [hp] with a ha
      filter_upwards [Kernel.rnDeriv_toReal_pos (hκη a)] with b hb
      exact ⟨ha, hb⟩
  filter_upwards [hAC.ae_eq (compProd_rnDeriv κ η hPQ hκη), hboth] with p hp hb
  simp only [llr, kernelLLR, hp, ENNReal.toReal_mul]
  exact Real.log_mul hb.1.ne' hb.2.ne'

theorem kernelLLR_eq_llr (hκη : ∀ a, κ a ≪ η a) (a : α) :
    (fun b => kernelLLR κ η (a, b)) =ᵐ[κ a] llr (κ a) (η a) := by
  filter_upwards [(hκη a).ae_eq (κ.rnDeriv_eq_rnDeriv_measure (η := η) (a := a))]
    with b hb
  simp only [kernelLLR, llr, hb]

theorem integral_kernelLLR (hκη : ∀ a, κ a ≪ η a) (a : α) :
    (∫ b, kernelLLR κ η (a, b) ∂κ a) = (klDiv (κ a) (η a)).toReal := by
  rw [integral_congr_ae (kernelLLR_eq_llr κ η hκη a)]
  symm
  exact toReal_klDiv_of_measure_eq (hκη a) (by simp)

/-- The KL chain rule for actual history laws and Markov transition
kernels, under genuine absolute-continuity and log-likelihood integrability
hypotheses. The expected conditional term uses the actual kernel KL. -/
theorem klDiv_compProd (hPQ : P ≪ Q) (hκη : ∀ a, κ a ≪ η a)
    (hiPQ : Integrable (llr P Q) P)
    (hiK : Integrable (kernelLLR κ η) (P ⊗ₘ κ)) :
    klDiv (P ⊗ₘ κ) (Q ⊗ₘ η) = klDiv P Q +
      ENNReal.ofReal (∫ a, (klDiv (κ a) (η a)).toReal ∂P) := by
  have hAC : P ⊗ₘ κ ≪ Q ⊗ₘ η := hPQ.compProd (ae_of_all P hκη)
  have hfst : MeasurePreserving (Prod.fst : α × β → α) (P ⊗ₘ κ) P :=
    ⟨measurable_fst, Measure.fst_compProd P κ⟩
  have hi1 : Integrable (fun p : α × β => llr P Q p.1) (P ⊗ₘ κ) :=
    (hfst.integrable_comp hiPQ.aestronglyMeasurable).mpr hiPQ
  have hi : Integrable (llr (P ⊗ₘ κ) (Q ⊗ₘ η)) (P ⊗ₘ κ) :=
    (hi1.add hiK).congr (compProd_llr κ η hPQ hκη).symm
  have hn : 0 ≤ ∫ a, llr P Q a ∂P := by
    simpa using integral_llr_add_sub_measure_univ_nonneg hPQ hiPQ
  have hnK : 0 ≤ ∫ a, (klDiv (κ a) (η a)).toReal ∂P :=
    integral_nonneg (fun _ => ENNReal.toReal_nonneg)
  rw [klDiv_of_ac_of_integrable hAC hi,
    integral_congr_ae (compProd_llr κ η hPQ hκη), integral_add hi1 hiK,
    Measure.integral_compProd hi1, Measure.integral_compProd hiK,
    klDiv_of_ac_of_integrable hPQ hiPQ]
  simp only [integral_const, measureReal_univ_eq_one, one_smul, add_sub_cancel_right,
    integral_kernelLLR κ η hκη]
  exact ENNReal.ofReal_add hn hnK

end MatchingBounds1005.KernelKL
