import SecondOrder.FirstOrderRandomizedLowerBound

namespace SecondOrder
noncomputable section

def firstOrderResponseCap (R : ℝ) : ℕ := ⌊R^2/16384⌋₊

theorem firstOrderResponseCap_bounds {R : ℝ} (hsize : 32768≤R^2) :
    0<firstOrderResponseCap R ∧ R^2/32768≤(firstOrderResponseCap R:ℝ) ∧
      (firstOrderResponseCap R:ℝ)≤R^2/16384 := by
  have hx : 2≤R^2/16384 := by linarith only [hsize]
  have hf := Nat.lt_floor_add_one (R^2/16384)
  refine ⟨Nat.floor_pos.2 (by linarith only [hx]),?_,Nat.floor_le (by positivity)⟩
  change R^2/32768≤(⌊R^2/16384⌋₊:ℝ)
  linarith only [hx,hf]

theorem firstOrderResponseCap_information (d : ℕ) {R : ℝ} (hR : 2≤R) :
    firstOrderArrayInformation d R*firstOrderResponseCap R≤(d:ℝ)/16384 := by
  have hR0 : R≠0 := by linarith
  have hc : (firstOrderResponseCap R:ℝ)≤R^2/16384 := Nat.floor_le (by positivity)
  have hh := mul_le_mul_of_nonneg_left hc (firstOrderArrayInformation_nonneg d R)
  have he : firstOrderArrayInformation d R*(R^2/16384)=(d:ℝ)/16384 := by
    rw [firstOrderArrayInformation_eq]
    field_simp
  exact hh.trans_eq he

/-- T counts links, and T+1 counts blocks. The floor leaves half the gap
budget unused, including the public regularizer's factor 20. -/
def firstOrderBudgetLinks (Δ A : ℝ) : ℕ := ⌊Δ/(40*A)⌋₊-1

theorem firstOrderBudgetLinks_count {Δ A : ℝ} (hA : 0<A) (hsize : 40*A≤Δ) :
    firstOrderBudgetLinks Δ A+1=⌊Δ/(40*A)⌋₊ := by
  have hn : 0<⌊Δ/(40*A)⌋₊ := Nat.floor_pos.2
    ((le_div_iff₀ (by positivity)).2 (by nlinarith only [hsize]))
  unfold firstOrderBudgetLinks
  omega

theorem firstOrderBudgetLinks_gap {Δ A : ℝ} (hA : 0<A) (hsize : 40*A≤Δ) :
    20*A*(firstOrderBudgetLinks Δ A+1:ℕ)≤Δ/2 := by
  rw [firstOrderBudgetLinks_count hA hsize]
  have hΔ : 0≤Δ := by linarith
  have hh := mul_le_mul_of_nonneg_left
    (Nat.floor_le (div_nonneg hΔ (by positivity : 0≤40*A))) (by positivity : 0≤20*A)
  apply hh.trans_eq
  field_simp
  <;> ring

theorem firstOrderBudgetLinks_lower {Δ A : ℝ} (hA : 0<A) (hsize : 160*A≤Δ) :
    0<firstOrderBudgetLinks Δ A ∧ Δ/(80*A)≤(firstOrderBudgetLinks Δ A:ℝ) ∧
      (firstOrderBudgetLinks Δ A:ℝ)≤Δ/(40*A) := by
  have hΔ : 0<Δ := by linarith
  have hx : 4≤Δ/(40*A) := (le_div_iff₀ (by positivity)).2 (by linarith only [hsize])
  have hn := firstOrderBudgetLinks_count (Δ := Δ) hA (by linarith only [hsize,hA])
  have hnr : (firstOrderBudgetLinks Δ A:ℝ)+1=(⌊Δ/(40*A)⌋₊:ℝ) := by exact_mod_cast hn
  have hf := Nat.lt_floor_add_one (Δ/(40*A))
  have hf' := Nat.floor_le (div_nonneg hΔ.le (by positivity : 0≤40*A))
  have he : Δ/(80*A)=(Δ/(40*A))/2 := by ring
  have hl : Δ/(80*A)≤(firstOrderBudgetLinks Δ A:ℝ) := by rw [he]; linarith only [hx,hnr,hf]
  refine ⟨?_,hl,?_⟩
  · have hpos : (0:ℝ)<(firstOrderBudgetLinks Δ A:ℝ) := lt_of_lt_of_le (by positivity) hl
    exact_mod_cast hpos
  · linarith only [hnr,hf']

theorem firstOrderIntegerBudget_lower {Δ A R : ℝ} (hA : 0<A)
    (hsize : 160*A≤Δ) (hcap : 32768≤R^2) :
    Δ*R^2/(5242880*A)≤((firstOrderBudgetLinks Δ A:ℝ)*(firstOrderResponseCap R:ℝ))/2 := by
  have ht := firstOrderBudgetLinks_lower hA hsize
  have hc := firstOrderResponseCap_bounds hcap
  have hh := mul_le_mul ht.2.1 hc.2.1 (by positivity : 0≤R^2/32768) (Nat.cast_nonneg _)
  apply le_trans _ (div_le_div_of_nonneg_right hh (by norm_num))
  exact le_of_eq (by ring)

/-- The integer stage budget has the manuscript's epsilon^{-3} rate. -/
def firstOrderEndpointThreshold (Δ s ε : ℝ) : ℝ :=
  firstOrderGradientConstant^3*Δ*s^2/(1342177280*firstOrderNoiseConstant^2*ε^3)

theorem firstOrderEndpointThreshold_eq {ε : ℝ} (hε : 0<ε) (Δ s : ℝ) :
    firstOrderEndpointThreshold Δ s ε=
      Δ*(firstOrderCoefficientScale s (firstOrderOutputScale ε))^2/(5242880*firstOrderOutputScale ε) := by
  unfold firstOrderEndpointThreshold firstOrderCoefficientScale firstOrderOutputScale
  field_simp [firstOrderGradientConstant_pos.ne',firstOrderNoiseConstant_pos.ne',hε.ne']
  <;> ring

theorem firstOrderEndpointThreshold_budget {Δ s ε : ℝ} (hε : 0<ε)
    (hsize : 160*firstOrderOutputScale ε≤Δ)
    (hcap : 32768≤(firstOrderCoefficientScale s (firstOrderOutputScale ε))^2) :
    firstOrderEndpointThreshold Δ s ε≤
      ((firstOrderBudgetLinks Δ (firstOrderOutputScale ε):ℝ)*
        (firstOrderResponseCap (firstOrderCoefficientScale s (firstOrderOutputScale ε)):ℝ))/2 := by
  rw [firstOrderEndpointThreshold_eq hε]
  exact firstOrderIntegerBudget_lower (firstOrderOutputScale_pos hε) hsize hcap

end
end SecondOrder
