import SecondOrder.FirstOrderEndpointBudget

namespace SecondOrder
noncomputable section

def firstOrderEndpointEnvelope (Δ s ε : ℝ) : ℝ := 2+Δ/ε+Δ*s^2/ε^3

def firstOrderEndpointBlockSize (Δ s ε : ℝ) : ℕ :=
  ⌈16384*Real.log (firstOrderEndpointEnvelope Δ s ε)⌉₊

def firstOrderEndpointLinks (Δ ε : ℝ) : ℕ := firstOrderBudgetLinks Δ (firstOrderOutputScale ε)

theorem firstOrderEndpointEnvelope_ge_two {Δ s ε : ℝ} (hΔ : 0≤Δ) (hε : 0<ε) :
    2≤firstOrderEndpointEnvelope Δ s ε := by
  unfold firstOrderEndpointEnvelope
  have hq : 0≤Δ/ε := by positivity
  have hw : 0≤Δ*s^2/ε^3 := by positivity
  linarith only [hq,hw]

theorem firstOrderEndpointBlockSize_bounds {Δ s ε : ℝ} (hΔ : 0≤Δ) (hε : 0<ε) :
    0<firstOrderEndpointBlockSize Δ s ε ∧
      16384*Real.log (firstOrderEndpointEnvelope Δ s ε)≤(firstOrderEndpointBlockSize Δ s ε:ℝ) ∧
      (firstOrderEndpointBlockSize Δ s ε:ℝ)≤16384*Real.log (firstOrderEndpointEnvelope Δ s ε)+1 := by
  have hx := firstOrderEndpointEnvelope_ge_two (s := s) hΔ hε
  have hlog := Real.log_pos (show 1<firstOrderEndpointEnvelope Δ s ε by linarith only [hx])
  have hceil := Nat.le_ceil (16384*Real.log (firstOrderEndpointEnvelope Δ s ε))
  have hupper := Nat.ceil_lt_add_one (show 0≤16384*Real.log (firstOrderEndpointEnvelope Δ s ε) by positivity)
  refine ⟨?_,hceil,hupper.le⟩
  exact Nat.ceil_pos.2 (by positivity)

theorem firstOrderHorizon_of_envelope {x D : ℝ} (hx : 2≤x)
    (hD : 16384*Real.log x≤D) (N T : ℕ)
    (hN : (N+1:ℕ)≤x) (hT : (T+1:ℕ)≤x) :
    256*Real.log (2*(N+1:ℕ))≤D ∧ 16384*Real.log 2≤D ∧
      128*Real.log (32*(N+1:ℕ)*(T+1:ℕ))≤D := by
  have hlog2 := Real.log_le_log (by norm_num : (0:ℝ)<2) hx
  have hlogN := Real.log_le_log (by positivity : (0:ℝ)<(N+1:ℕ)) hN
  have hlogT := Real.log_le_log (by positivity : (0:ℝ)<(T+1:ℕ)) hT
  have hlogx : 0≤Real.log x := Real.log_nonneg (by linarith only [hx])
  have h32 : Real.log (32:ℝ)=5*Real.log 2 := by
    rw [show (32:ℝ)=2^5 by norm_num,Real.log_pow]
    norm_num
  have hn : Real.log (2*(N+1:ℕ))=Real.log 2+Real.log (N+1:ℕ) := by
    rw [Real.log_mul (by norm_num) (by positivity)]
  have ht : Real.log (32*(N+1:ℕ)*(T+1:ℕ))=
      5*Real.log 2+Real.log (N+1:ℕ)+Real.log (T+1:ℕ) := by
    rw [Real.log_mul (by positivity) (by positivity),Real.log_mul (by norm_num) (by positivity),h32]
  rw [hn,ht]
  constructor
  · linarith only [hlog2,hlogN,hlogx,hD]
  constructor <;> linarith only [hlog2,hlogN,hlogT,hlogx,hD]

theorem firstOrderEndpoint_horizon {Δ s ε : ℝ} (hε : 0<ε)
    (hsize : 160*firstOrderOutputScale ε≤Δ)
    (N : ℕ) (hN : (N:ℝ)≤firstOrderEndpointThreshold Δ s ε) :
    let D : ℝ := firstOrderEndpointBlockSize Δ s ε
    let T := firstOrderEndpointLinks Δ ε
    256*Real.log (2*(N+1:ℕ))≤D ∧ 16384*Real.log 2≤D ∧
      128*Real.log (32*(N+1:ℕ)*(T+1:ℕ))≤D := by
  have hA := firstOrderOutputScale_pos hε
  have hΔ : 0≤Δ := by linarith only [hsize,hA]
  have hd := firstOrderEndpointBlockSize_bounds (s := s) hΔ hε
  have hn := hN.trans (firstOrderEndpointThreshold_le_envelope hΔ hε)
  have ht := firstOrderBudgetLinks_le_envelope hε hsize
  apply firstOrderHorizon_of_envelope (firstOrderEndpointEnvelope_ge_two hΔ hε) hd.2.1 N
    (firstOrderEndpointLinks Δ ε)
  · unfold firstOrderEndpointEnvelope
    rw [Nat.cast_add,Nat.cast_one]
    have hq : 0≤Δ/ε := by positivity
    linarith only [hn,hq]
  · unfold firstOrderEndpointEnvelope
    rw [Nat.cast_add,Nat.cast_one]
    have hw : 0≤Δ*s^2/ε^3 := by positivity
    change (firstOrderBudgetLinks Δ (firstOrderOutputScale ε):ℝ)+1≤_
    linarith only [ht,hw]

end
end SecondOrder
