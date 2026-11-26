import SecondOrder.CurvatureHolderModel

namespace SecondOrder
noncomputable section

def curvatureHolderEndpointConstant (ν : ℝ) : ℝ :=
  8589934592*curvatureNoiseConstant^2*(32*curvatureGeometryConstant)^(2/ν)

def curvatureHolderThreshold (Δ L σ D γ ν : ℝ) : ℝ :=
  Δ*σ^2*L^(2/ν)/(curvatureHolderEndpointConstant ν*D^2*γ^(3+2/ν))

theorem curvatureHolderEndpointConstant_pos (ν : ℝ) : 0<curvatureHolderEndpointConstant ν := by
  have hG := curvatureGeometryConstant_pos
  have hC : 0<curvatureNoiseConstant := lt_of_lt_of_le (by norm_num) curvatureNoiseConstant_bounds.1
  unfold curvatureHolderEndpointConstant
  positivity

theorem curvatureHolderInputScale_sq {L γ ν : ℝ} (hL : 0<L) (hγ : 0<γ) :
    (curvatureHolderInputScale L γ ν)^2=
      L^(2/ν)/((32*curvatureGeometryConstant)^(2/ν)*γ^(2/ν)) := by
  have hG := curvatureGeometryConstant_pos
  unfold curvatureHolderInputScale
  rw [←Real.rpow_natCast _ 2,←Real.rpow_mul (by positivity)]
  norm_num only [Nat.cast_ofNat]
  rw [show (1/ν)*(2:ℝ)=2/ν by ring,
    Real.div_rpow hL.le (by positivity),Real.mul_rpow (by positivity) hγ.le]

theorem curvatureHolderInputScale_sq_div {L γ ν : ℝ} (hL : 0<L) (hγ : 0<γ) (n : ℕ) :
    (curvatureHolderInputScale L γ ν)^2/γ^n=
      L^(2/ν)/((32*curvatureGeometryConstant)^(2/ν)*γ^((n:ℝ)+2/ν)) := by
  rw [curvatureHolderInputScale_sq hL hγ,Real.rpow_add hγ,Real.rpow_natCast]
  ring

theorem curvatureHolderThreshold_identity {Δ L σ D γ ν : ℝ}
    (hL : 0<L) (hγ : 0<γ) :
    curvatureEndpointThreshold Δ (curvatureHolderEffectiveL L γ ν) σ D γ=
      curvatureHolderThreshold Δ L σ D γ ν := by
  by_cases hD : D=0
  · simp [hD,curvatureEndpointThreshold,curvatureHolderThreshold]
  have hG := curvatureGeometryConstant_pos
  have hC : 0<curvatureNoiseConstant := lt_of_lt_of_le (by norm_num) curvatureNoiseConstant_bounds.1
  have he : curvatureEndpointThreshold Δ (curvatureHolderEffectiveL L γ ν) σ D γ=
      Δ*σ^2/(8589934592*curvatureNoiseConstant^2*D^2)*
        ((curvatureHolderInputScale L γ ν)^2/γ^3) := by
    unfold curvatureEndpointThreshold curvatureEndpointConstant curvatureHolderEffectiveL
    field_simp [hγ.ne',hG.ne',hC.ne',hD]
    <;> ring
  rw [he,curvatureHolderInputScale_sq_div hL hγ 3]
  norm_num only [Nat.cast_ofNat]
  unfold curvatureHolderThreshold curvatureHolderEndpointConstant
  ring

theorem curvatureHolder_dimension_identity {Δ L γ ν : ℝ} (hL : 0<L) (hγ : 0<γ) :
    Δ*(curvatureHolderEffectiveL L γ ν)^2/(4096*curvatureGeometryConstant^2*γ^3)=
      Δ*L^(2/ν)/(16*(32*curvatureGeometryConstant)^(2/ν)*γ^(1+2/ν)) := by
  have hG := curvatureGeometryConstant_pos
  have he : Δ*(curvatureHolderEffectiveL L γ ν)^2/(4096*curvatureGeometryConstant^2*γ^3)=
      Δ/16*((curvatureHolderInputScale L γ ν)^2/γ^1) := by
    unfold curvatureHolderEffectiveL
    field_simp [hγ.ne',hG.ne']
    <;> ring
  rw [he,curvatureHolderInputScale_sq_div hL hγ 1]
  norm_num only [Nat.cast_one]
  ring

theorem curvatureHolderThreshold_pos {Δ L σ D γ ν : ℝ}
    (hΔ : 0<Δ) (hL : 0<L) (hσ : 0<σ) (hD : 0<D) (hγ : 0<γ) :
    0<curvatureHolderThreshold Δ L σ D γ ν := by
  have hC := curvatureHolderEndpointConstant_pos ν
  unfold curvatureHolderThreshold
  positivity

/-- The explicit coefficient lost when replacing the auxiliary Lipschitz
scale by the manuscript's Hölder powers is at most one. -/
theorem curvatureHolder_power_constant {ν : ℝ} (hν : 0<ν) (hν1 : ν≤1) :
    256*curvatureGeometryConstant^2≤(32*curvatureGeometryConstant)^(2/ν) := by
  have hG := curvatureGeometryConstant_ge_one
  have hp : (2:ℝ)≤2/ν := (le_div_iff₀ hν).2 (by linarith only [hν1])
  have hh := Real.rpow_le_rpow_of_exponent_le (show 1≤32*curvatureGeometryConstant by linarith) hp
  rw [show (2:ℝ)=(2:ℕ) by norm_num,Real.rpow_natCast] at hh
  nlinarith only [hh,sq_nonneg curvatureGeometryConstant]

theorem curvatureHolderEffectiveL_rate_le {L γ ν : ℝ}
    (hL : 0<L) (hγ : 0<γ) (hν : 0<ν) (hν1 : ν≤1) (n : ℕ) :
    (curvatureHolderEffectiveL L γ ν)^2/γ^(n+2)≤L^(2/ν)/γ^((n:ℝ)+2/ν) := by
  have hG := curvatureGeometryConstant_pos
  have hc := curvatureHolder_power_constant hν hν1
  have he : (curvatureHolderEffectiveL L γ ν)^2/γ^(n+2)=
      256*curvatureGeometryConstant^2*((curvatureHolderInputScale L γ ν)^2/γ^n) := by
    unfold curvatureHolderEffectiveL
    rw [pow_add]
    field_simp [hγ.ne']
    <;> ring
  rw [he,curvatureHolderInputScale_sq_div hL hγ n]
  calc
    _ = (256*curvatureGeometryConstant^2/(32*curvatureGeometryConstant)^(2/ν))*
      (L^(2/ν)/γ^((n:ℝ)+2/ν)) := by ring
    _ ≤ 1*(L^(2/ν)/γ^((n:ℝ)+2/ν)) := mul_le_mul_of_nonneg_right
      ((div_le_one (by positivity)).2 hc) (by positivity)
    _ = _ := one_mul _

end
end SecondOrder
