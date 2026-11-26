import GaussianProductDensity254

noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal BigOperators
namespace Paper254

theorem gaussianProductPDF_pos {d : ℕ} (m : Fin d → ℝ) (c : Fin d → ℝ≥0)
    (hc : ∀ i,c i ≠ 0) (x : Fin d → ℝ) : 0 < gaussianProductPDF m c x :=
  Finset.prod_pos (fun i _ => gaussianPDFReal_pos (m i) (c i) (x i) (hc i))

theorem gaussianProductPDF_measurable {d : ℕ} (m : Fin d → ℝ) (c : Fin d → ℝ≥0) :
    Measurable (fun x => ENNReal.ofReal (gaussianProductPDF m c x)) := by
  unfold gaussianProductPDF
  fun_prop

theorem gaussian_product_ac {d : ℕ} (m : Fin d → ℝ) (c : Fin d → ℝ≥0)
    (hc : ∀ i,c i ≠ 0) :
    Measure.pi (fun i => gaussianReal (m i) (c i)) ≪ Measure.pi (fun _ : Fin d => (volume : Measure ℝ)) := by
  rw [gaussian_product_density m c hc]
  exact withDensity_absolutelyContinuous _ _

theorem gaussian_product_ac_reverse {d : ℕ} (m : Fin d → ℝ) (c : Fin d → ℝ≥0)
    (hc : ∀ i,c i ≠ 0) :
    Measure.pi (fun _ : Fin d => (volume : Measure ℝ)) ≪ Measure.pi (fun i => gaussianReal (m i) (c i)) := by
  rw [gaussian_product_density m c hc]
  apply withDensity_absolutelyContinuous' (gaussianProductPDF_measurable m c).aemeasurable
  exact ae_of_all _ (fun x => (ENNReal.ofReal_pos.mpr (gaussianProductPDF_pos m c hc x)).ne')

theorem gaussian_product_llr {d : ℕ} (u m : Fin d → ℝ) (q c : Fin d → ℝ≥0)
    (hq : ∀ i,q i ≠ 0) (hc : ∀ i,c i ≠ 0) :
    llr (Measure.pi (fun i => gaussianReal (u i) (q i)))
      (Measure.pi (fun i => gaussianReal (m i) (c i))) =ᵐ[Measure.pi (fun i => gaussianReal (u i) (q i))]
        fun x => ∑ i,Real.log (gaussianPDFReal (u i) (q i) (x i)/gaussianPDFReal (m i) (c i) (x i)) := by
  let V := Measure.pi (fun _ : Fin d => (volume : Measure ℝ))
  let Q := Measure.pi (fun i => gaussianReal (u i) (q i))
  have hr := Measure.rnDeriv_withDensity_right Q V (gaussianProductPDF_measurable m c).aemeasurable
    (ae_of_all _ (fun x => (ENNReal.ofReal_pos.mpr (gaussianProductPDF_pos m c hc x)).ne'))
    (ae_of_all _ (fun _ => ENNReal.ofReal_ne_top))
  change Q.rnDeriv (V.withDensity (fun x => ENNReal.ofReal (gaussianProductPDF m c x))) =ᵐ[V] _ at hr
  rw [← gaussian_product_density m c hc] at hr
  have hleft : Q.rnDeriv V =ᵐ[V] fun x => ENNReal.ofReal (gaussianProductPDF u q x) := by
    dsimp [Q,V]
    rw [gaussian_product_density u q hq]
    exact Measure.rnDeriv_withDensity _ (gaussianProductPDF_measurable u q)
  have hac : Q ≪ V := gaussian_product_ac u q hq
  filter_upwards [hac.ae_le hr,hac.ae_le hleft] with x hx hy
  rw [llr,hx,hy,ENNReal.toReal_mul,ENNReal.toReal_inv,
    ENNReal.toReal_ofReal (gaussianProductPDF_pos m c hc x).le,
    ENNReal.toReal_ofReal (gaussianProductPDF_pos u q hq x).le]
  have he : (gaussianProductPDF m c x)⁻¹*gaussianProductPDF u q x=
      ∏ i,gaussianPDFReal (u i) (q i) (x i)/gaussianPDFReal (m i) (c i) (x i) := by
    rw [Finset.prod_div_distrib]
    unfold gaussianProductPDF
    ring
  rw [he,Real.log_prod Finset.univ _ (fun i _ => (div_pos
    (gaussianPDFReal_pos (u i) (q i) (x i) (hq i))
    (gaussianPDFReal_pos (m i) (c i) (x i) (hc i))).ne')]

theorem gaussian_product_kl_formula {d : ℕ} (u m : Fin d → ℝ) (q c : Fin d → ℝ≥0)
    (hq : ∀ i,q i ≠ 0) (hc : ∀ i,c i ≠ 0) :
    klDiv (Measure.pi (fun i => gaussianReal (u i) (q i)))
      (Measure.pi (fun i => gaussianReal (m i) (c i))) =
        ENNReal.ofReal (∑ i,coordinateKL (q i) (c i) (u i-m i)) := by
  let Q := Measure.pi (fun i => gaussianReal (u i) (q i))
  let P := Measure.pi (fun i => gaussianReal (m i) (c i))
  let g := fun i x => Real.log (gaussianPDFReal (u i) (q i) x/gaussianPDFReal (m i) (c i) x)
  have hi : ∀ i,Integrable (g i) (gaussianReal (u i) (q i)) := by
    intro i
    exact (gaussian_llr_integrable (u i) (m i) (q i) (c i) (hq i) (hc i)).congr
      (gaussian_llr_density (u i) (m i) (q i) (c i) (hq i) (hc i))
  have hcomp : ∀ i,Integrable (fun x : Fin d → ℝ => g i (x i)) Q := by
    intro i
    exact (measurePreserving_eval (fun i => gaussianReal (u i) (q i)) i).integrable_comp_of_integrable (hi i)
  have hsum : Integrable (fun x : Fin d → ℝ => ∑ i,g i (x i)) Q :=
    integrable_finset_sum _ (fun i _ => hcomp i)
  have hllr := gaussian_product_llr u m q c hq hc
  have hint : Integrable (llr Q P) Q := hsum.congr hllr.symm
  have hac : Q ≪ P := (gaussian_product_ac u q hq).trans (gaussian_product_ac_reverse m c hc)
  rw [klDiv_of_ac_of_integrable hac hint,integral_congr_ae hllr,
    integral_finset_sum _ (fun i _ => hcomp i)]
  have he : ∀ i, (∫ x : Fin d → ℝ,g i (x i) ∂Q)=coordinateKL (q i) (c i) (u i-m i) := by
    intro i
    have hmap := (measurePreserving_eval (fun i => gaussianReal (u i) (q i)) i).map_eq
    have hg : AEStronglyMeasurable (g i) (Q.map (Function.eval i)) := by
      rw [hmap]
      exact (hi i).aestronglyMeasurable
    rw [← integral_map (measurable_pi_apply i).aemeasurable hg,hmap]
    exact gaussian_density_entropy (u i) (m i) (q i) (c i) (hq i) (hc i)
  change ENNReal.ofReal ((∑ i,∫ x : Fin d → ℝ,g i (x i) ∂Q)+P.real Set.univ-Q.real Set.univ)=_
  simp_rw [he]
  simp [P,Q]

end Paper254
#print axioms Paper254.gaussian_product_llr
#print axioms Paper254.gaussian_product_kl_formula
