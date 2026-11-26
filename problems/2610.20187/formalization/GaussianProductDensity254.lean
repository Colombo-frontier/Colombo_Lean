import GaussianKL254
import Mathlib.MeasureTheory.Integral.Pi

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators
namespace Paper254

def gaussianProductPDF {d : ℕ} (m : Fin d → ℝ) (c : Fin d → ℝ≥0) (x : Fin d → ℝ) : ℝ :=
  ∏ i,gaussianPDFReal (m i) (c i) (x i)

theorem gaussian_product_density {d : ℕ} (m : Fin d → ℝ) (c : Fin d → ℝ≥0)
    (hc : ∀ i,c i ≠ 0) :
    Measure.pi (fun i => gaussianReal (m i) (c i)) =
      (Measure.pi (fun _ : Fin d => (volume : Measure ℝ))).withDensity
        (fun x => ENNReal.ofReal (gaussianProductPDF m c x)) := by
  apply Measure.pi_eq
  intro s hs
  have hi : ∀ i,Integrable (gaussianPDFReal (m i) (c i)) (volume.restrict (s i)) :=
    fun i => (integrable_gaussianPDFReal (m i) (c i)).mono_measure Measure.restrict_le_self
  have hip := Integrable.fin_nat_prod hi
  have hn : ∀ x : Fin d → ℝ,0 ≤ gaussianProductPDF m c x := by
    intro x
    exact Finset.prod_nonneg (fun i _ => (gaussianPDFReal_pos (m i) (c i) (x i) (hc i)).le)
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs)]
  rw [Measure.restrict_pi_pi]
  unfold gaussianProductPDF
  rw [← ofReal_integral_eq_lintegral_ofReal hip (ae_of_all _ hn)]
  rw [integral_fin_nat_prod_eq_prod]
  have hprod : ENNReal.ofReal (∏ i,∫ x,gaussianPDFReal (m i) (c i) x ∂volume.restrict (s i))=
      ∏ i,ENNReal.ofReal (∫ x,gaussianPDFReal (m i) (c i) x ∂volume.restrict (s i)) := by
    exact ENNReal.ofReal_prod_of_nonneg (fun i _ => integral_nonneg (fun x => (gaussianPDFReal_pos (m i) (c i) x (hc i)).le))
  rw [hprod]
  apply Finset.prod_congr rfl
  intro i _
  rw [ofReal_integral_eq_lintegral_ofReal (hi i)
    (ae_of_all _ (fun x => (gaussianPDFReal_pos (m i) (c i) x (hc i)).le)),
    gaussianReal_of_var_ne_zero (m i) (hc i),withDensity_apply _ (hs i)]
  rfl

end Paper254
#print axioms Paper254.gaussian_product_density
