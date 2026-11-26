import SecondOrder.CurvatureEndpointBudget

namespace SecondOrder
noncomputable section

def curvatureEndpointEnvelope (Δ L σ γ : ℝ) : ℝ := 2+Δ*L^2/γ^3+Δ*σ^2*L^2/γ^5

def curvatureEndpointHalfSize (Δ L σ γ : ℝ) : ℕ :=
  ⌈65536*Real.log (curvatureEndpointEnvelope Δ L σ γ)⌉₊

theorem curvatureEndpointEnvelope_ge_two {Δ L σ γ : ℝ} (hΔ : 0≤Δ) (hγ : 0<γ) :
    2≤curvatureEndpointEnvelope Δ L σ γ := by
  unfold curvatureEndpointEnvelope
  have hq : 0≤Δ*L^2/γ^3 := by positivity
  have hw : 0≤Δ*σ^2*L^2/γ^5 := by positivity
  linarith only [hq,hw]

theorem curvatureEndpointHalfSize_bounds {Δ L σ γ : ℝ} (hΔ : 0≤Δ) (hγ : 0<γ) :
    4≤curvatureEndpointHalfSize Δ L σ γ ∧
      65536*Real.log (curvatureEndpointEnvelope Δ L σ γ)≤
        ((2*curvatureEndpointHalfSize Δ L σ γ:ℕ):ℝ) ∧
      ((2*curvatureEndpointHalfSize Δ L σ γ:ℕ):ℝ)≤
        131072*Real.log (curvatureEndpointEnvelope Δ L σ γ)+2 := by
  have hx := curvatureEndpointEnvelope_ge_two (L := L) (σ := σ) hΔ hγ
  have hlog := Real.log_le_log (by norm_num : (0:ℝ)<2) hx
  have hhalf : (1:ℝ)/2≤Real.log 2 := by
    have hh := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ)<2)
    norm_num at hh ⊢
    exact hh
  have hceil := Nat.le_ceil (65536*Real.log (curvatureEndpointEnvelope Δ L σ γ))
  have hupper := Nat.ceil_lt_add_one (show 0≤65536*Real.log (curvatureEndpointEnvelope Δ L σ γ) by linarith)
  have hfour : (4:ℝ)≤(curvatureEndpointHalfSize Δ L σ γ:ℝ) := by
    change (4:ℝ)≤(⌈65536*Real.log (curvatureEndpointEnvelope Δ L σ γ)⌉₊:ℝ)
    linarith only [hlog,hhalf,hceil]
  refine ⟨by exact_mod_cast hfour,?_,?_⟩ <;>
    simp only [Nat.cast_mul, Nat.cast_ofNat, curvatureEndpointHalfSize] <;>
    linarith only [hlog,hhalf,hceil,hupper]

/-- A single logarithmic envelope implies every horizon requirement used in
the concrete sequential proof. -/
theorem curvatureHorizon_of_envelope {x D : ℝ} (hx : 2≤x)
    (hD : 65536*Real.log x≤D) (N T : ℕ)
    (hN : (N+1:ℕ)≤x) (hT : (T+1:ℕ)≤x) :
    1024*Real.log (4*(N+1:ℕ))≤D ∧ 65536*Real.log 2≤D ∧
      512*Real.log (64*(N+1:ℕ)*(T+1:ℕ))≤D := by
  have hlog2 := Real.log_le_log (by norm_num : (0:ℝ)<2) hx
  have hlogN := Real.log_le_log (by positivity : (0:ℝ)<(N+1:ℕ)) hN
  have hlogT := Real.log_le_log (by positivity : (0:ℝ)<(T+1:ℕ)) hT
  have hlogx : 0≤Real.log x := Real.log_nonneg (by linarith only [hx])
  have h4 : Real.log (4:ℝ)=2*Real.log 2 := by
    rw [show (4:ℝ)=2^2 by norm_num,Real.log_pow]
    norm_num
  have h64 : Real.log (64:ℝ)=6*Real.log 2 := by
    rw [show (64:ℝ)=2^6 by norm_num,Real.log_pow]
    norm_num
  have hn : Real.log (4*(N+1:ℕ))=2*Real.log 2+Real.log (N+1:ℕ) := by
    rw [Real.log_mul (by norm_num) (by positivity),h4]
  have ht : Real.log (64*(N+1:ℕ)*(T+1:ℕ))=
      6*Real.log 2+Real.log (N+1:ℕ)+Real.log (T+1:ℕ) := by
    rw [Real.log_mul (by positivity) (by positivity),Real.log_mul (by norm_num) (by positivity),h64]
  rw [hn,ht]
  constructor
  · linarith only [hlog2,hlogN,hlogx,hD]
  constructor <;> linarith only [hlog2,hlogN,hlogT,hlogx,hD]

theorem curvatureEndpoint_horizon {Δ L σ γ : ℝ} (hL : 0<L) (hγ : 0<γ)
    (hsize : 8*curvatureOutputScale ((2*curvatureEndpointHalfSize Δ L σ γ:ℕ):ℝ) L γ≤Δ)
    (N : ℕ) (hN : (N:ℝ)≤curvatureEndpointThreshold Δ L σ
      ((2*curvatureEndpointHalfSize Δ L σ γ:ℕ):ℝ) γ) :
    let D : ℝ := (2*curvatureEndpointHalfSize Δ L σ γ:ℕ)
    let T := curvatureBudgetLinks Δ (curvatureOutputScale D L γ)
    1024*Real.log (4*(N+1:ℕ))≤D ∧ 65536*Real.log 2≤D ∧
      512*Real.log (64*(N+1:ℕ)*(T+1:ℕ))≤D := by
  have hDnonneg : (0:ℝ)≤((2*curvatureEndpointHalfSize Δ L σ γ:ℕ):ℝ) := Nat.cast_nonneg _
  have hA : 0≤curvatureOutputScale ((2*curvatureEndpointHalfSize Δ L σ γ:ℕ):ℝ) L γ := by
    unfold curvatureOutputScale
    positivity
  have hΔ : 0≤Δ := by linarith only [hsize,hA]
  have hd := curvatureEndpointHalfSize_bounds (L := L) (σ := σ) hΔ hγ
  have hD : (1:ℝ)≤((2*curvatureEndpointHalfSize Δ L σ γ:ℕ):ℝ) := by exact_mod_cast (show 1≤2*curvatureEndpointHalfSize Δ L σ γ by omega)
  have hn := hN.trans (curvatureEndpointThreshold_le_envelope hΔ hD hγ)
  have ht := curvatureBudgetLinks_le_envelope hL hD hγ hsize
  apply curvatureHorizon_of_envelope (curvatureEndpointEnvelope_ge_two hΔ hγ) hd.2.1 N
    (curvatureBudgetLinks Δ (curvatureOutputScale ((2*curvatureEndpointHalfSize Δ L σ γ:ℕ):ℝ) L γ))
  · unfold curvatureEndpointEnvelope
    rw [Nat.cast_add,Nat.cast_one]
    have hq : 0≤Δ*L^2/γ^3 := by positivity
    linarith only [hn,hq]
  · unfold curvatureEndpointEnvelope
    rw [Nat.cast_add,Nat.cast_one]
    have hw : 0≤Δ*σ^2*L^2/γ^5 := by positivity
    linarith only [ht,hw]

end
end SecondOrder
