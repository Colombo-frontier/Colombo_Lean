import SecondOrder.ScaledCurvatureInformation

open MeasureTheory InformationTheory
open scoped Classical ENNReal

namespace SecondOrder
noncomputable section

/-- The scaled information budget has the expected quadratic tolerance rate. -/
theorem curvatureScales_information {D σ γ : ℝ} (hD : 0≤D) (hσ : 0<σ) :
    D*(D-1)/(2*(curvatureCoefficientScale σ γ)^2) ≤
      512*curvatureNoiseConstant^2*D^2*γ^2/σ^2 := by
  have hC : 0<curvatureNoiseConstant := lt_of_lt_of_le (by norm_num) curvatureNoiseConstant_bounds.1
  have he : D^2/(2*(curvatureCoefficientScale σ γ)^2) =
      512*curvatureNoiseConstant^2*D^2*γ^2/σ^2 := by
    unfold curvatureCoefficientScale
    field_simp
    <;> ring
  rw [←he]
  exact div_le_div_of_nonneg_right (by nlinarith only [hD]) (by positivity)

variable {m T : ℕ}

theorem scaledCurvatureProgress_joint_measurable (m T : ℕ) (β : ℝ) :
    Measurable (fun w : (Fin (T+1) → BalancedVector m) × Point (CurvatureDimension m T) =>
      curvatureProgress (m := m) (T := T) w.1 (curvatureDilation m T β w.2)) := by
  apply positiveGateFrontier_measurable
  intro i
  have hL : Measurable (curvatureDilation m T β) := (curvatureDilation m T β).continuous.measurable
  have hy : Measurable (fun x : Point (CurvatureDimension m T) =>
      fun j : Fin (2*m) => (curvatureDilation m T β x i) j) :=
    measurable_pi_iff.mpr (fun j => (EuclideanSpace.proj j).continuous.measurable.comp
      ((blockProj (E := Point (2*m)) i).continuous.measurable.comp hL))
  have hc : Measurable
      (fun w : (Fin (T+1) → BalancedVector m) × Point (CurvatureDimension m T) =>
        (w.2,w.1 i)) := measurable_snd.prodMk ((measurable_pi_apply i).comp measurable_fst)
  have hm := (periodicMean_joint_measurable hy).comp hc
  change Measurable (fun w : (Fin (T+1) → BalancedVector m) × Point (CurvatureDimension m T) =>
    curvatureCompletion (periodicEnergy (w.1 i) (curvatureDilation m T β w.2 i)))
  simp only [periodicEnergy_eq]
  exact curvatureCompletion_contDiff.continuous.measurable.comp ((hm.norm.pow_const 2).div_const 2)

theorem scaledCurvatureProgress_zero (Θ : Fin (T+1) → BalancedVector m) (β : ℝ) :
    curvatureProgress Θ (curvatureDilation m T β 0)=0 := by
  rw [map_zero, curvatureProgress_zero]

theorem scaledCurvature_activation_past_tail {H : Type*} [MeasurableSpace H]
    {η : Measure H} (β : ℝ) {y : H → Point (CurvatureDimension m T)} (hy : Measurable y)
    (i : Fin (T+1)) {past : Set H} (hp : MeasurableSet past) :
    (η.prod (balancedVectorLaw m)) {w | w.1 ∈ past ∧
      0<periodicCompletion w.2 ((curvatureDilation m T β (y w.1)) i)} ≤
      ENNReal.ofReal (4*Real.exp (-((2*m:ℕ):ℝ)/512))*η past := by
  have hL : Measurable (curvatureDilation m T β) := (curvatureDilation m T β).continuous.measurable
  have hi : Measurable (fun a : H => (curvatureDilation m T β (y a)) i) :=
    (blockProj (E := Point (2*m)) i).continuous.measurable.comp (hL.comp hy)
  exact periodicCompletion_activation_past_tail hi hp

theorem curvatureHardFamily_progress_kl (Θ : Fin (T+1) → BalancedVector m)
    (θ₀ : BalancedVector m) (P : Parameters) {γ : ℝ} (hγ : 0<γ)
    (hsmall : 64*curvatureNoiseConstant*γ≤curvatureNoiseBudget P)
    (x : Point (CurvatureDimension m T))
    (hp : curvatureProgress Θ (curvatureDilation m T (curvatureInputScale P.hessianHolder γ) x)≤T) :
    klDiv ((curvatureCoefficientLaw Θ (curvatureCoefficientScale (curvatureNoiseBudget P) γ)
      (curvatureCoefficientScale_ge_two hγ hsmall)).toMeasure.map
      (fun z => richReply (scaledCurvatureSample Θ
        (curvatureOutputScale ((2*m:ℕ):ℝ) P.hessianHolder γ) (curvatureInputScale P.hessianHolder γ)) z x))
      (scaledCurvatureReferenceKernel θ₀
        (fun i : Fin (curvatureProgress Θ (curvatureDilation m T (curvatureInputScale P.hessianHolder γ) x)) =>
          Θ ⟨i.val,by omega⟩)
        (curvatureOutputScale ((2*m:ℕ):ℝ) P.hessianHolder γ) (curvatureInputScale P.hessianHolder γ)
        (curvatureCoefficientScale (curvatureNoiseBudget P) γ) (curvatureCoefficientScale_ge_two hγ hsmall) x) ≤
      ENNReal.ofReal (512*curvatureNoiseConstant^2*((2*m:ℕ):ℝ)^2*γ^2/(curvatureNoiseBudget P)^2) := by
  exact (scaledCurvatureReply_progress_kl Θ θ₀ _ _ _ _ x hp).trans
    (ENNReal.ofReal_le_ofReal (curvatureScales_information (Nat.cast_nonneg _) (curvatureNoiseBudget_pos P)))

/-- Choosing the floor chain length automatically satisfies the initial-gap
condition, while preserving all the rich common-loss model clauses. -/
theorem curvatureBudgetFamily_admissible {m : ℕ} (hm : 0<m) (P : Parameters)
    {σ₀ γ : ℝ} (hσ₀ : 0<σ₀) (hγ : 0<γ)
    (hsmall : 64*curvatureNoiseConstant*γ≤curvatureNoiseBudget P)
    (hLip : 8*curvatureGeometryConstant*γ≤P.gradientLip)
    (hgrad : 16*curvatureGeometryConstant*curvatureNoiseBudget P*γ*Real.sqrt ((2*m:ℕ):ℝ)≤
      P.hessianHolder*P.gradientNoise)
    (hvalue : 256*curvatureGeometryConstant^2*((2*m:ℕ):ℝ)*curvatureNoiseBudget P*γ^2≤
      σ₀*P.hessianHolder^2)
    (hsize : 2*curvatureOutputScale ((2*m:ℕ):ℝ) P.hessianHolder γ≤P.gap)
    (Θ : Fin (curvatureBudgetLinks P.gap (curvatureOutputScale ((2*m:ℕ):ℝ) P.hessianHolder γ)+1) →
      BalancedVector m) :
    RichCommonLoss (curvatureCoefficientLaw Θ (curvatureCoefficientScale (curvatureNoiseBudget P) γ)
      (curvatureCoefficientScale_ge_two hγ hsmall)).toMeasure P σ₀
      (scaledCurvaturePopulation Θ (curvatureOutputScale ((2*m:ℕ):ℝ) P.hessianHolder γ)
        (curvatureInputScale P.hessianHolder γ))
      (scaledCurvatureSample Θ (curvatureOutputScale ((2*m:ℕ):ℝ) P.hessianHolder γ)
        (curvatureInputScale P.hessianHolder γ)) := by
  apply curvatureHardFamily_admissible Θ hm P hσ₀ hγ hsmall hLip hgrad hvalue
  have hD : (0:ℝ)<(2*m:ℕ) := by exact_mod_cast Nat.mul_pos (by omega) hm
  have hh := curvatureBudgetLinks_gap (curvatureOutputScale_pos hD P.hessianHolder_pos hγ) hsize
  exact hh.trans (by linarith [P.gap_pos])

end
end SecondOrder
