import RationalPruneShare254

open scoped BigOperators
namespace Paper254

def rationalMasterUpdate {n : ℕ} (p : ℕ) (live next : Finset (Fin n))
    (w z prior : Fin n→ℚ) (alpha : ℚ) : Fin n→ℚ :=
  rationalRoundedPruneShare p (rationalLiveSoftmax p live w z) prior alpha next

theorem rationalMasterUpdate_spec {n : ℕ} (p : ℕ) (live next : Finset (Fin n))
    (w z prior : Fin n→ℚ) (alpha : ℚ) (hw : ∀ j,0≤w j) (hw1 : ∑ j,w j=1)
    (hsupport : ∀ j,j∉live → w j=0) (hz : ∀ j,|(z j:ℝ)|≤1/2)
    (hp : ∀ j,0≤prior j) (hp1 : ∑ j,prior j=1) (ha : 0<alpha) (ha1 : alpha≤1)
    (hprior : ∀ j,0<prior j → j∈next) :
    let v := (rationalPrior w hw hw1).exponential (-1) (fun j=>(z j:ℝ))
    let B := 1+3*live.card*((2:ℝ)^p)⁻¹
    let C := 1+3*next.card*((2:ℝ)^p)⁻¹
    (∑ j,rationalMasterUpdate p live next w z prior alpha j)=1 ∧
    (∀ j,0≤rationalMasterUpdate p live next w z prior alpha j) ∧
    (∀ j,j∉next → rationalMasterUpdate p live next w z prior alpha j=0) ∧
    (∀ j,j∈next → (1-(alpha:ℝ))*v.weight j/(B*C)≤
      (rationalMasterUpdate p live next w z prior alpha j:ℝ) ∧
      (alpha:ℝ)*(prior j:ℝ)/C≤(rationalMasterUpdate p live next w z prior alpha j:ℝ)) := by
  let v := (rationalPrior w hw hw1).exponential (-1) (fun j=>(z j:ℝ))
  let B : ℝ := 1+3*live.card*((2:ℝ)^p)⁻¹
  let C : ℝ := 1+3*next.card*((2:ℝ)^p)⁻¹
  have hs := rationalLiveSoftmax_spec p live w z hw hw1 hsupport hz
  have hr := rationalRoundedPruneShare_spec p (rationalLiveSoftmax p live w z) prior alpha next
    hs.2.1 hs.1 hp hp1 ha ha1 hprior
  refine ⟨hr.1,hr.2.1,hr.2.2.1,?_⟩
  intro j hj
  refine ⟨?_,(hr.2.2.2 j hj).2⟩
  have halpha : 0≤1-(alpha:ℝ) := by exact_mod_cast (sub_nonneg.mpr ha1)
  have he := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left (hs.2.2.2.1 j) halpha) (show 0≤C by dsimp [C]; positivity)
  have hi : (1-(alpha:ℝ))*v.weight j/(B*C)=((1-(alpha:ℝ))*(v.weight j/B))/C := by ring
  rw [hi]
  exact he.trans (hr.2.2.2 j hj).1

theorem rationalMasterUpdate_log_overhead (p N M : ℕ) :
    Real.log ((1+3*N*((2:ℝ)^p)⁻¹)*(1+3*M*((2:ℝ)^p)⁻¹))≤
      3*(N+M:ℕ)*((2:ℝ)^p)⁻¹ := by
  rw [Real.log_mul (by positivity) (by positivity)]
  have hN := upward_rounding_log_overhead (N:ℝ) (((2:ℝ)^p)⁻¹) (by positivity) (by positivity)
  have hM := upward_rounding_log_overhead (M:ℝ) (((2:ℝ)^p)⁻¹) (by positivity) (by positivity)
  push_cast
  linarith

/-- Explicit logarithmic working precision for a prescribed per-round
master budget; the exponents encode upper and lower magnitude bounds. -/
theorem master_rounding_precision (a b r s : ℕ) (N T : ℕ) (lam delta : ℝ)
    (hN : (N:ℝ)≤(2:ℝ)^a) (hT : (T:ℝ)≤(2:ℝ)^b) (hTpos : 0<T)
    (hlam : ((2:ℝ)^r)⁻¹≤lam) (hdelta : ((2:ℝ)^s)⁻¹≤delta) :
    6*N*((2:ℝ)^(a+b+r+s+4))⁻¹≤lam*delta/(2*T) := by
  have hA : (0:ℝ)<2^a := by positivity
  have hB : (0:ℝ)<2^b := by positivity
  have hR : (0:ℝ)<2^r := by positivity
  have hS : (0:ℝ)<2^s := by positivity
  have hTr : (0:ℝ)<T := by exact_mod_cast hTpos
  have hprod := mul_le_mul hlam hdelta (by positivity : 0≤((2:ℝ)^s)⁻¹)
    (lt_of_lt_of_le (by positivity) hlam).le
  have hNT := mul_le_mul hN hT (Nat.cast_nonneg T) hA.le
  have hp : (2:ℝ)^(a+b+r+s+4)=16*2^a*2^b*2^r*2^s := by
    simp only [pow_add]; ring
  rw [hp]
  apply (le_div_iff₀ (by positivity)).mpr
  calc
    _ ≤ ((2:ℝ)^r)⁻¹*((2:ℝ)^s)⁻¹ := by
      have he : 6*(N:ℝ)*(16*2^a*2^b*2^r*2^s)⁻¹*(2*T)=
          (12*(N:ℝ)*T)/(16*2^a*2^b*2^r*2^s) := by ring
      rw [he,←mul_inv,inv_eq_one_div]
      apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
      have hh := mul_le_mul_of_nonneg_right hNT (show 0≤12*(2:ℝ)^r*2^s by positivity)
      nlinarith [mul_pos hA hB,mul_pos hR hS]
    _ ≤ _ := hprod

end Paper254
#print axioms Paper254.rationalMasterUpdate_spec
#print axioms Paper254.master_rounding_precision
