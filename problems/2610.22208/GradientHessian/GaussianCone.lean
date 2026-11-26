import GradientHessian.GaussianHilbert

/-! A Gaussian cone estimate for the literal normalized-Gaussian sphere law.
The proof uses a diagonal quadratic exponential moment, including one positive
coefficient and arbitrarily large negative transverse coefficients. -/

namespace GradientHessian.GaussianCone
open MeasureTheory ProbabilityTheory GaussianSquare
noncomputable section

def weightedEnergy {m : ℕ} (t : Fin m → ℝ) (z : Fin m → ℝ) : ℝ := ∑ i,t i*(z i)^2

theorem weighted_exponential_integral {m : ℕ} (t : Fin m → ℝ) (ht : ∀ i,t i<1/2) :
    (∫ z,Real.exp (weightedEnergy t z) ∂gaussianVector m) =
      ∏ i,(Real.sqrt (1-2*t i))⁻¹ := by
  simp only [weightedEnergy,Real.exp_sum]
  letI : MeasureSpace ℝ := ⟨gaussianReal 0 1⟩
  letI : SigmaFinite (volume : Measure ℝ) := by
    change SigmaFinite (gaussianReal 0 1)
    infer_instance
  have h := integral_fintype_prod_eq_prod (Fin m) (fun i (z : ℝ) => Real.exp (t i*z^2))
  change (∫ z,∏ i,Real.exp (t i*(z i)^2) ∂gaussianVector m) =
    ∏ i,∫ z : ℝ,Real.exp (t i*z^2) ∂gaussianReal 0 1 at h
  rw [h]
  exact Finset.prod_congr rfl (fun i _ => square_exponential_integral (ht i))

theorem weighted_exponential_integrable {m : ℕ} (t : Fin m → ℝ) (ht : ∀ i,t i<1/2) :
    Integrable (fun z => Real.exp (weightedEnergy t z)) (gaussianVector m) := by
  apply Integrable.of_integral_ne_zero
  rw [weighted_exponential_integral t ht]
  exact ne_of_gt (Finset.prod_pos (fun i _ => inv_pos.mpr (Real.sqrt_pos.mpr (by linarith [ht i]))))

theorem weighted_chernoff {m : ℕ} (t : Fin m → ℝ) (ht : ∀ i,t i<1/2) :
    (gaussianVector m).real {z | 0≤weightedEnergy t z} ≤ ∏ i,(Real.sqrt (1-2*t i))⁻¹ := by
  have h := mul_meas_ge_le_integral_of_nonneg
    (μ := gaussianVector m) (f := fun z => Real.exp (weightedEnergy t z))
    (ae_of_all _ (fun _ => (Real.exp_pos _).le)) (weighted_exponential_integrable t ht) 1
  have he : {z | (1:ℝ)≤Real.exp (weightedEnergy t z)}={z | 0≤weightedEnergy t z} := by
    ext z
    simp only [Set.mem_setOf_eq,Real.one_le_exp_iff]
  rw [he,weighted_exponential_integral t ht,one_mul] at h
  exact h

def coneCoefficients {m : ℕ} (i₀ : Fin m) (ρ : ℝ) (i : Fin m) : ℝ :=
  if i=i₀ then 1/4 else -(1-ρ^2)/(4*ρ^2)

theorem coneCoefficients_lt {m : ℕ} (i₀ : Fin m) {ρ : ℝ} (hρ : 0<ρ) (hρ1 : ρ<1) (i : Fin m) :
    coneCoefficients i₀ ρ i<1/2 := by
  unfold coneCoefficients
  split_ifs
  · norm_num
  · have hs : 0<1-ρ^2 := by nlinarith
    have h := div_neg_of_neg_of_pos (neg_neg_of_pos hs) (by positivity : 0<4*ρ^2)
    linarith

theorem cone_energy {m : ℕ} (i₀ : Fin m) {ρ : ℝ} (hρ : ρ≠0) (z : Fin m → ℝ) :
    weightedEnergy (coneCoefficients i₀ ρ) z =
      ((z i₀)^2-(1-ρ^2)*energy z)/(4*ρ^2) := by
  have hterm (i : Fin m) : coneCoefficients i₀ ρ i*(z i)^2 =
      (if i=i₀ then (z i₀)^2/(4*ρ^2) else 0) - ((1-ρ^2)/(4*ρ^2))*(z i)^2 := by
    by_cases hi : i=i₀
    · subst i
      simp only [coneCoefficients,if_true]
      field_simp
      ring
    · simp only [coneCoefficients,if_neg hi,zero_sub]
      ring
  simp only [weightedEnergy,hterm,Finset.sum_sub_distrib,Finset.sum_ite_eq',Finset.mem_univ,if_true,
    ← Finset.mul_sum,energy]
  ring

theorem cone_moment_bound {m : ℕ} (i₀ : Fin m) {ρ : ℝ} (hρ : 0<ρ) (_hρ1 : ρ<1) :
    (∏ i,(Real.sqrt (1-2*coneCoefficients i₀ ρ i))⁻¹) ≤ 2*(2*ρ)^(m-1) := by
  classical
  let f := fun i : Fin m => (Real.sqrt (1-2*coneCoefficients i₀ ρ i))⁻¹
  have hzero : f i₀≤2 := by
    dsimp [f,coneCoefficients]
    norm_num
    exact Real.sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
  have hrest (i : Fin m) (hi : i≠i₀) : f i≤2*ρ := by
    have he : 1-2*coneCoefficients i₀ ρ i=(1+ρ^2)/(2*ρ^2) := by
      simp only [coneCoefficients,if_neg hi]
      field_simp
      ring
    have hp : 0<Real.sqrt ((1+ρ^2)/(2*ρ^2)) := Real.sqrt_pos.mpr (by positivity)
    have hs := Real.sq_sqrt (by positivity : 0≤(1+ρ^2)/(2*ρ^2))
    change (Real.sqrt (1-2*coneCoefficients i₀ ρ i))⁻¹≤2*ρ
    rw [he]
    rw [inv_eq_one_div]
    apply (div_le_iff₀ hp).mpr
    have he2 : ((1+ρ^2)/(2*ρ^2))*(2*ρ)^2=2*(1+ρ^2) := by field_simp; ring
    have hs2 : (2*ρ*Real.sqrt ((1+ρ^2)/(2*ρ^2)))^2=2*(1+ρ^2) := by
      rw [mul_pow,hs]
      linarith
    have hp2 : 0≤2*ρ*Real.sqrt ((1+ρ^2)/(2*ρ^2)) := by positivity
    nlinarith
  change (∏ i,f i)≤_
  rw [← Finset.mul_prod_erase Finset.univ f (Finset.mem_univ i₀)]
  have hprod : (∏ i ∈ Finset.univ.erase i₀,f i)≤(2*ρ)^(m-1) := by
    calc
      _ ≤ ∏ _i ∈ Finset.univ.erase i₀,2*ρ :=
        Finset.prod_le_prod (fun i _ => inv_nonneg.mpr (Real.sqrt_nonneg _))
          (fun i hi => hrest i (Finset.ne_of_mem_erase hi))
      _ = _ := by simp
  exact mul_le_mul hzero hprod
    (Finset.prod_nonneg (fun i _ => inv_nonneg.mpr (Real.sqrt_nonneg _))) (by norm_num)

theorem coordinate_cone_bound {m : ℕ} (i₀ : Fin m) {ρ : ℝ} (hρ : 0<ρ) (hρ1 : ρ<1) :
    (gaussianVector m).real {z | (1-ρ^2)*energy z≤(z i₀)^2} ≤ 2*(2*ρ)^(m-1) := by
  have he : {z : Fin m → ℝ | (1-ρ^2)*energy z≤(z i₀)^2}=
      {z | 0≤weightedEnergy (coneCoefficients i₀ ρ) z} := by
    ext z
    simp only [Set.mem_setOf_eq,cone_energy i₀ hρ.ne']
    constructor
    · intro hz
      exact div_nonneg (sub_nonneg.mpr hz) (by positivity)
    · intro hz
      have h := (le_div_iff₀ (by positivity : 0<4*ρ^2)).mp hz
      linarith
  rw [he]
  exact (weighted_chernoff _ (coneCoefficients_lt i₀ hρ hρ1)).trans (cone_moment_bound i₀ hρ hρ1)

end
end GradientHessian.GaussianCone
