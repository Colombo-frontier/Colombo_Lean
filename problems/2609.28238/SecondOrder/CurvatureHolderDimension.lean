import SecondOrder.CurvatureHolderRates

namespace SecondOrder
noncomputable section

def curvatureHolderEnvelope (Δ L σ γ ν : ℝ) : ℝ :=
  2+Δ*L^(2/ν)/γ^(1+2/ν)+Δ*σ^2*L^(2/ν)/γ^(3+2/ν)

def curvatureHolderHalfSize (Δ L σ γ ν : ℝ) : ℕ :=
  curvatureEndpointHalfSize Δ (curvatureHolderEffectiveL L γ ν) σ γ

def curvatureHolderBlockSize (Δ L σ γ ν : ℝ) : ℕ :=
  2*curvatureHolderHalfSize Δ L σ γ ν

def curvatureHolderLinks (Δ L σ γ ν : ℝ) : ℕ :=
  curvatureBudgetLinks Δ (curvatureOutputScale (curvatureHolderBlockSize Δ L σ γ ν)
    (curvatureHolderEffectiveL L γ ν) γ)

theorem curvatureHolderEnvelope_ge_two {Δ L σ γ ν : ℝ}
    (hΔ : 0≤Δ) (hL : 0<L) (hγ : 0<γ) : 2≤curvatureHolderEnvelope Δ L σ γ ν := by
  unfold curvatureHolderEnvelope
  have h1 : 0≤Δ*L^(2/ν)/γ^(1+2/ν) := by positivity
  have h2 : 0≤Δ*σ^2*L^(2/ν)/γ^(3+2/ν) := by positivity
  linarith only [h1,h2]

theorem curvatureHolder_auxiliary_envelope_le {Δ L σ γ ν : ℝ}
    (hΔ : 0≤Δ) (hL : 0<L) (hγ : 0<γ) (hν : 0<ν) (hν1 : ν≤1) :
    curvatureEndpointEnvelope Δ (curvatureHolderEffectiveL L γ ν) σ γ≤
      curvatureHolderEnvelope Δ L σ γ ν := by
  have h1 := mul_le_mul_of_nonneg_left (curvatureHolderEffectiveL_rate_le hL hγ hν hν1 1) hΔ
  have h3 := mul_le_mul_of_nonneg_left (curvatureHolderEffectiveL_rate_le hL hγ hν hν1 3)
    (show 0≤Δ*σ^2 by positivity)
  norm_num only [Nat.cast_one,Nat.cast_ofNat] at h1 h3
  unfold curvatureEndpointEnvelope curvatureHolderEnvelope
  convert add_le_add (add_le_add_left h1 2) h3 using 1 <;> ring

/-- The actual even block size is at least eight and at most a universal
multiple of the logarithmic Hölder envelope in the manuscript. -/
theorem curvatureHolderBlockSize_bounds {Δ L σ γ ν : ℝ}
    (hΔ : 0≤Δ) (hL : 0<L) (hγ : 0<γ) (hν : 0<ν) (hν1 : ν≤1) :
    8≤curvatureHolderBlockSize Δ L σ γ ν ∧
      (curvatureHolderBlockSize Δ L σ γ ν:ℝ)≤
        131072*Real.log (curvatureHolderEnvelope Δ L σ γ ν)+2 := by
  have hd := curvatureEndpointHalfSize_bounds (L := curvatureHolderEffectiveL L γ ν) (σ := σ) hΔ hγ
  constructor
  · dsimp [curvatureHolderBlockSize,curvatureHolderHalfSize]
    omega
  · apply hd.2.2.trans
    have hx := curvatureEndpointEnvelope_ge_two (L := curvatureHolderEffectiveL L γ ν) (σ := σ) hΔ hγ
    have hl := Real.log_le_log (show 0<curvatureEndpointEnvelope Δ (curvatureHolderEffectiveL L γ ν) σ γ by linarith)
      (curvatureHolder_auxiliary_envelope_le hΔ hL hγ hν hν1)
    linarith only [hl]

theorem curvatureHolder_horizon {Δ L σ γ ν : ℝ} (hL : 0<L) (hγ : 0<γ)
    (hsize : 8*curvatureOutputScale (curvatureHolderBlockSize Δ L σ γ ν)
      (curvatureHolderEffectiveL L γ ν) γ≤Δ)
    (N : ℕ) (hN : (N:ℝ)≤curvatureHolderThreshold Δ L σ (curvatureHolderBlockSize Δ L σ γ ν) γ ν) :
    let D : ℝ := curvatureHolderBlockSize Δ L σ γ ν
    let T := curvatureHolderLinks Δ L σ γ ν
    1024*Real.log (4*(N+1:ℕ))≤D ∧ 65536*Real.log 2≤D ∧
      512*Real.log (64*(N+1:ℕ)*(T+1:ℕ))≤D := by
  rw [←curvatureHolderThreshold_identity hL hγ] at hN
  exact curvatureEndpoint_horizon (curvatureHolderEffectiveL_pos hL hγ) hγ hsize N hN

theorem curvatureHolderBudgetLinks_dimension {m : ℕ} (hm : 0<m) {Δ L γ ν : ℝ}
    (hL : 0<L) (hγ : 0<γ)
    (hsize : 2*curvatureOutputScale ((2*m:ℕ):ℝ) (curvatureHolderEffectiveL L γ ν) γ≤Δ) :
    ((CurvatureDimension m (curvatureBudgetLinks Δ
      (curvatureOutputScale ((2*m:ℕ):ℝ) (curvatureHolderEffectiveL L γ ν) γ)):ℕ):ℝ)≤
      Δ*L^(2/ν)/(16*(32*curvatureGeometryConstant)^(2/ν)*γ^(1+2/ν)) := by
  have hh := curvatureBudgetLinks_dimension hm (curvatureHolderEffectiveL_pos hL hγ) hγ hsize
  rwa [curvatureHolder_dimension_identity hL hγ] at hh

end
end SecondOrder
