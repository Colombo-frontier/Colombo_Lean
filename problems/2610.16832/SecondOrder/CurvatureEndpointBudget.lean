import SecondOrder.CurvatureIntegerBudgets

namespace SecondOrder
noncomputable section

def curvatureEndpointConstant : ℝ :=
  2199023255552*curvatureGeometryConstant^2*curvatureNoiseConstant^2

def curvatureEndpointThreshold (Δ L σ D γ : ℝ) : ℝ :=
  Δ*σ^2*L^2/(curvatureEndpointConstant*D^2*γ^5)

theorem curvatureGeometryConstant_ge_one : 1≤curvatureGeometryConstant := by
  norm_num [curvatureGeometryConstant, curvatureJetConstant, completionDerivativeBound]

theorem curvatureEndpointConstant_ge_one : 1≤curvatureEndpointConstant := by
  have hg := curvatureGeometryConstant_ge_one
  have hn := curvatureNoiseConstant_bounds.1
  unfold curvatureEndpointConstant
  nlinarith [sq_nonneg (curvatureGeometryConstant-1), sq_nonneg (curvatureNoiseConstant-1),
    mul_le_mul (show (1:ℝ)≤curvatureGeometryConstant^2 by nlinarith)
      (show (1:ℝ)≤curvatureNoiseConstant^2 by nlinarith) (by norm_num) (sq_nonneg _)]

theorem curvatureEndpointThreshold_pos {Δ L σ D γ : ℝ}
    (hΔ : 0<Δ) (hL : 0<L) (hσ : 0<σ) (hD : 0<D) (hγ : 0<γ) :
    0<curvatureEndpointThreshold Δ L σ D γ := by
  unfold curvatureEndpointThreshold
  have hC : 0<curvatureEndpointConstant := lt_of_lt_of_le (by norm_num) curvatureEndpointConstant_ge_one
  positivity

theorem curvatureEndpointThreshold_identity {Δ L σ D γ : ℝ}
    (hL : 0<L) (hD : 0<D) (hγ : 0<γ) :
    curvatureEndpointThreshold Δ L σ D γ=
      Δ*(curvatureCoefficientScale σ γ)^2/(1048576*curvatureOutputScale D L γ*D) := by
  rw [(curvatureScales_identities hD hL hγ).2.2]
  unfold curvatureEndpointThreshold curvatureEndpointConstant curvatureCoefficientScale
  have hnoise : curvatureNoiseConstant≠0 := ne_of_gt (lt_of_lt_of_le (by norm_num) curvatureNoiseConstant_bounds.1)
  field_simp [hD.ne',hL.ne',hγ.ne',curvatureGeometryConstant_pos.ne',hnoise]
  <;> ring

theorem curvatureEndpointThreshold_budget {Δ L σ D γ : ℝ}
    (hL : 0<L) (hD : 0<D) (hγ : 0<γ)
    (hsize : 8*curvatureOutputScale D L γ≤Δ)
    (hcap : 131072*D≤(curvatureCoefficientScale σ γ)^2)
    (N : ℕ) (hN : (N:ℝ)≤curvatureEndpointThreshold Δ L σ D γ) :
    2*N≤curvatureBudgetLinks Δ (curvatureOutputScale D L γ)*curvatureResponseCap D (curvatureCoefficientScale σ γ) := by
  have hh := curvatureIntegerBudget_lower (curvatureOutputScale_pos hD hL hγ) hD hsize hcap
  rw [←curvatureEndpointThreshold_identity hL hD hγ] at hh
  have hb : (2:ℝ)*(N:ℝ)≤
      (curvatureBudgetLinks Δ (curvatureOutputScale D L γ):ℝ)*(curvatureResponseCap D (curvatureCoefficientScale σ γ):ℝ) := by
    linarith only [hN,hh]
  exact_mod_cast hb

theorem curvatureEndpointThreshold_le_envelope {Δ L σ D γ : ℝ}
    (hΔ : 0≤Δ) (hD : 1≤D) (hγ : 0<γ) :
    curvatureEndpointThreshold Δ L σ D γ≤Δ*σ^2*L^2/γ^5 := by
  have hc := curvatureEndpointConstant_ge_one
  have hd2 : 1≤D^2 := by nlinarith
  have hden : γ^5≤curvatureEndpointConstant*D^2*γ^5 := by
    have hh := mul_le_mul hc hd2 (by norm_num) (le_trans (by norm_num) hc)
    nlinarith [pow_pos hγ 5]
  exact div_le_div_of_nonneg_left (by positivity) (pow_pos hγ 5) hden

theorem curvatureBudgetLinks_le_envelope {Δ L D γ : ℝ}
    (hL : 0<L) (hD : 1≤D) (hγ : 0<γ) (hsize : 8*curvatureOutputScale D L γ≤Δ) :
    (curvatureBudgetLinks Δ (curvatureOutputScale D L γ):ℝ)≤Δ*L^2/γ^3 := by
  have hD0 : 0<D := lt_of_lt_of_le (by norm_num) hD
  have hA := curvatureOutputScale_pos hD0 hL hγ
  have hΔ : 0≤Δ := by linarith
  have ht := (curvatureBudgetLinks_lower hA hsize).2.2
  have hden : γ^3≤4096*curvatureGeometryConstant^2*D*γ^3 := by
    have hg := curvatureGeometryConstant_ge_one
    have hg2 : 1≤curvatureGeometryConstant^2 := by nlinarith
    have hh := mul_le_mul hg2 hD (by norm_num) (le_trans (by norm_num) hg2)
    nlinarith [pow_pos hγ 3]
  apply ht.trans
  have he : Δ/(2*curvatureOutputScale D L γ)=Δ*L^2/(4096*curvatureGeometryConstant^2*D*γ^3) := by
    rw [(curvatureScales_identities hD0 hL hγ).2.2]
    field_simp [hL.ne',hγ.ne',hD0.ne',curvatureGeometryConstant_pos.ne']
    <;> ring
    all_goals field_simp [hγ.ne',hD0.ne',curvatureGeometryConstant_pos.ne']
    <;> ring
  rw [he]
  exact div_le_div_of_nonneg_left (by positivity) (pow_pos hγ 3) hden

end
end SecondOrder
