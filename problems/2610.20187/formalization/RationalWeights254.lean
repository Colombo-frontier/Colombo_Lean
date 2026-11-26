import RationalExp254
import WeightNormalization254

open scoped BigOperators
namespace Paper254

def rationalSoftmaxApprox {n : ℕ} (p : ℕ) (w z : Fin n → ℚ) (j : Fin n) : ℚ :=
  w j*rationalExp (z j) (p+4)/(∑ k,w k*rationalExp (z k) (p+4))

def rationalUpperMass {n : ℕ} (p : ℕ) (w z : Fin n → ℚ) (j : Fin n) : ℚ :=
  dyadicCeil (p+1) (rationalSoftmaxApprox p w z j)+3/(2*(2:ℚ)^p)

def rationalSoftmax {n : ℕ} (p : ℕ) (w z : Fin n → ℚ) (j : Fin n) : ℚ :=
  rationalUpperMass p w z j/(∑ k,rationalUpperMass p w z k)

noncomputable def rationalPrior {n : ℕ} (w : Fin n → ℚ)
    (hw : ∀ j,0 ≤ w j) (hsum : ∑ j,w j=1) : ProbabilityWeights (Fin n) :=
  ⟨fun j => (w j:ℝ),fun j => Rat.cast_nonneg.mpr (hw j),
    by have h := congrArg (fun q : ℚ => (q:ℝ)) hsum; push_cast at h; exact h⟩

theorem rationalUpperMass_bounds {n : ℕ} (p : ℕ) (w z : Fin n → ℚ)
    (hw : ∀ j,0 ≤ w j) (hsum : ∑ j,w j=1) (hz : ∀ j,|(z j:ℝ)| ≤ 1/2) :
    let v := (⟨fun j => (w j:ℝ),fun j => Rat.cast_nonneg.mpr (hw j),
      by have h := congrArg (fun q : ℚ => (q:ℝ)) hsum; push_cast at h; exact h⟩ : ProbabilityWeights (Fin n)).exponential (-1) (fun j => (z j:ℝ))
    ∀ j,v.weight j+((2:ℝ)^p)⁻¹ ≤ (rationalUpperMass p w z j:ℝ) ∧
      (rationalUpperMass p w z j:ℝ) ≤ v.weight j+3*((2:ℝ)^p)⁻¹ := by
  let W : ProbabilityWeights (Fin n) := ⟨fun j => (w j:ℝ),
    fun j => Rat.cast_nonneg.mpr (hw j),by have h := congrArg (fun q : ℚ => (q:ℝ)) hsum; push_cast at h; exact h⟩
  let v := W.exponential (-1) (fun j => (z j:ℝ))
  let ε : ℝ := ((2:ℝ)^(p+4))⁻¹/4
  have hε : 0 ≤ ε := by dsimp [ε]; positivity
  have hpow : (1:ℝ) ≤ 2^(p+4) := one_le_pow₀ (by norm_num)
  have hεhi : ε ≤ 1/4 := by
    have hh : ((2:ℝ)^(p+4))⁻¹ ≤ 1 := (inv_le_one₀ (by positivity)).mpr hpow
    dsimp [ε]; linarith
  have he : ∀ j,1/2 ≤ Real.exp (z j:ℝ) := by
    intro j
    have hj := (abs_le.mp (hz j)).1
    linarith [Real.add_one_le_exp (z j:ℝ)]
  have herr : ∀ j,|(rationalExp (z j) (p+4):ℝ)-Real.exp (z j:ℝ)| ≤ ε := by
    intro j
    rw [abs_sub_comm]
    exact rationalExp_error (z j) (p+4) (hz j)
  change ∀ j,v.weight j+((2:ℝ)^p)⁻¹ ≤ (rationalUpperMass p w z j:ℝ) ∧
    (rationalUpperMass p w z j:ℝ) ≤ v.weight j+3*((2:ℝ)^p)⁻¹
  intro j
  have hn := normalized_weight_error W (fun k => Real.exp (z k:ℝ))
    (fun k => (rationalExp (z k) (p+4):ℝ)) ε hε hεhi he herr j
  have hn' : |(rationalSoftmaxApprox p w z j:ℝ)-v.weight j| ≤ 4*ε := by
    simpa [rationalSoftmaxApprox,v,W,ProbabilityWeights.exponential,
      exponentialUpdate,exponentialNormalizer] using hn.2.2.2
  have hr := dyadicCeil_real_bounds (p+1) (rationalSoftmaxApprox p w z j)
  have hc : (rationalUpperMass p w z j:ℝ)=
      (dyadicCeil (p+1) (rationalSoftmaxApprox p w z j):ℝ)+3/(2*(2:ℝ)^p) := by
    simp [rationalUpperMass]
  have herror : 4*ε ≤ ((2:ℝ)^p)⁻¹/2 := by
    dsimp [ε]
    rw [pow_add]
    norm_num
    have hp : 0 ≤ ((2:ℝ)^p)⁻¹ := by positivity
    linarith
  have hhalf : ((2:ℝ)^(p+1))⁻¹=((2:ℝ)^p)⁻¹/2 := by rw [pow_succ]; field_simp
  have hshift : 3/(2*(2:ℝ)^p)=3*((2:ℝ)^p)⁻¹/2 := by field_simp
  rw [hhalf] at hr
  rw [hc,hshift]
  have hh := abs_le.mp hn'
  change v.weight j+_ ≤ _ ∧ _ ≤ v.weight j+_
  constructor <;> linarith [hh.1,hh.2,hr.1,hr.2]

theorem rationalSoftmax_spec {n : ℕ} (p : ℕ) (w z : Fin n → ℚ)
    (hw : ∀ j,0 ≤ w j) (hsum : ∑ j,w j=1) (hz : ∀ j,|(z j:ℝ)| ≤ 1/2) :
    let v := (rationalPrior w hw hsum).exponential (-1) (fun j => (z j:ℝ))
    (∑ j,rationalSoftmax p w z j)=1 ∧ ∀ j,
      v.weight j/(1+3*n*((2:ℝ)^p)⁻¹) ≤ (rationalSoftmax p w z j:ℝ) ∧
      ((2:ℝ)^p)⁻¹/(1+3*n*((2:ℝ)^p)⁻¹) ≤ (rationalSoftmax p w z j:ℝ) := by
  classical
  let v := (rationalPrior w hw hsum).exponential (-1) (fun j => (z j:ℝ))
  letI : Nonempty (Fin n) := ⟨v.exists_positive.choose⟩
  have hb := rationalUpperMass_bounds p w z hw hsum hz
  have hh := upward_probability_rounding v (fun j => (rationalUpperMass p w z j:ℝ))
    (((2:ℝ)^p)⁻¹) (by positivity) (fun j => (hb j).1) (fun j => (hb j).2)
  have hZ : 0 < (∑ j,rationalUpperMass p w z j : ℚ) := by
    have hs : (∑ j,(rationalUpperMass p w z j:ℝ))=↑(∑ j,rationalUpperMass p w z j) := by simp
    rw [hs] at hh
    exact Rat.cast_pos.mp hh.1
  constructor
  · simp only [rationalSoftmax,← Finset.sum_div,div_self hZ.ne']
  · intro j
    simpa [rationalSoftmax] using hh.2.2 j

/-- The actual rounded update has a fixed-denominator integer encoding
before normalization, independent of the previous rational denominators. -/
theorem rationalUpperMass_encoding {n : ℕ} (p : ℕ) (w z : Fin n → ℚ) (j : Fin n) :
    ∃ k : ℤ,rationalUpperMass p w z j=(k:ℚ)/(2:ℚ)^(p+1) := by
  refine ⟨⌈rationalSoftmaxApprox p w z j*(2:ℚ)^(p+1)⌉+3,?_⟩
  simp only [rationalUpperMass,dyadicCeil,Int.cast_add,Int.cast_ofNat,pow_succ]
  field_simp

theorem rationalUpperMass_encoding_bound {n : ℕ} (p : ℕ) (w z : Fin n → ℚ)
    (hw : ∀ j,0 ≤ w j) (hsum : ∑ j,w j=1) (hz : ∀ j,|(z j:ℝ)| ≤ 1/2)
    (j : Fin n) : ∃ k : ℤ,0 < k ∧ k ≤ (2:ℤ)^(p+3) ∧
      rationalUpperMass p w z j=(k:ℚ)/(2:ℚ)^(p+1) := by
  obtain ⟨k,hk⟩ := rationalUpperMass_encoding p w z j
  let v := (rationalPrior w hw hsum).exponential (-1) (fun j => (z j:ℝ))
  have hb := rationalUpperMass_bounds p w z hw hsum hz j
  change v.weight j+_ ≤ _ ∧ _ ≤ v.weight j+_ at hb
  have hh : ((2:ℝ)^p)⁻¹ ≤ 1 := (inv_le_one₀ (by positivity)).mpr (one_le_pow₀ (by norm_num))
  have hpos : 0 < (rationalUpperMass p w z j:ℝ) :=
    lt_of_lt_of_le (add_pos_of_nonneg_of_pos (v.nonneg j) (by positivity)) hb.1
  have hup : (rationalUpperMass p w z j:ℝ) ≤ 4 := by linarith [v.weight_le_one j,hb.2]
  have hcast : (rationalUpperMass p w z j:ℝ)=(k:ℝ)/(2:ℝ)^(p+1) := by exact_mod_cast hk
  rw [hcast] at hpos hup
  have hkpos : (0:ℝ) < k := (div_pos_iff_of_pos_right (by positivity)).mp hpos
  have hkup : (k:ℝ) ≤ (2:ℝ)^(p+3) := by
    have hb' := (div_le_iff₀ (by positivity : (0:ℝ) < 2^(p+1))).mp hup
    calc
      _ ≤ 4*(2:ℝ)^(p+1) := hb'
      _ = _ := by rw [show p+3=(p+1)+2 by omega,pow_add]; ring
  exact ⟨k,by exact_mod_cast hkpos,by exact_mod_cast hkup,hk⟩

end Paper254
#print axioms Paper254.rationalUpperMass_bounds
#print axioms Paper254.rationalSoftmax_spec
#print axioms Paper254.rationalUpperMass_encoding_bound
