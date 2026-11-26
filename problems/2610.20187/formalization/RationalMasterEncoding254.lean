import RationalWeightEncoding254
import RationalMasterUpdate254
import RationalMatrixHeight254

noncomputable section
open scoped BigOperators
namespace Paper254

theorem rationalMasterUpdate_encoding {n : ℕ} (p : ℕ) (live next : Finset (Fin n))
    (w z prior : Fin n→ℚ) (alpha : ℚ) (hw : ∀ j,0≤w j) (hw1 : ∑ j,w j=1)
    (hsupport : ∀ j,j∉live → w j=0) (hz : ∀ j,|(z j:ℝ)|≤1/2)
    (hp : ∀ j,0≤prior j) (hp1 : ∑ j,prior j=1) (ha : 0<alpha) (ha1 : alpha≤1)
    (hprior : ∀ j,0<prior j → j∈next) :
    ∃ k : Fin n→ℤ,∃ den : ℤ,0<den ∧ den≤next.card*(2:ℤ)^(p+3) ∧
      (∀ j,0≤k j ∧ k j≤(2:ℤ)^(p+3)) ∧
      (∀ j,j∉next → k j=0) ∧
      ∀ j,rationalMasterUpdate p live next w z prior alpha j=(k j:ℚ)/(den:ℚ) := by
  have hs := rationalLiveSoftmax_spec p live w z hw hw1 hsupport hz
  have hr := rationalPruneShare_spec (rationalLiveSoftmax p live w z) prior alpha next
    hs.2.1 hs.1 hp hp1 ha ha1 hprior
  exact rationalLiveSoftmax_encoding p next _ (fun _=>0) hr.1 hr.2.1 hr.2.2.1
    (by intro j; norm_num)

theorem rationalMasterUpdate_height {n : ℕ} (p a : ℕ) (live next : Finset (Fin n))
    (hcard : (next.card:ℤ)≤(2:ℤ)^a)
    (w z prior : Fin n→ℚ) (alpha : ℚ) (hw : ∀ j,0≤w j) (hw1 : ∑ j,w j=1)
    (hsupport : ∀ j,j∉live → w j=0) (hz : ∀ j,|(z j:ℝ)|≤1/2)
    (hp : ∀ j,0≤prior j) (hp1 : ∑ j,prior j=1) (ha : 0<alpha) (ha1 : alpha≤1)
    (hprior : ∀ j,0<prior j → j∈next) :
    MatrixHeight (fun j (_ : Fin 1)=>rationalMasterUpdate p live next w z prior alpha j) (a+p+3) := by
  obtain ⟨k,den,hd,hdsize,hk,_,heq⟩ := rationalMasterUpdate_encoding p live next w z prior alpha
    hw hw1 hsupport hz hp hp1 ha ha1 hprior
  refine ⟨fun j _=>k j,den,hd.ne',?_,?_,fun j _=>heq j⟩
  · rw [abs_of_pos hd]
    calc
      den≤(next.card:ℤ)*2^(p+3) := hdsize
      _ ≤ (2:ℤ)^a*2^(p+3) := mul_le_mul_of_nonneg_right hcard (by positivity)
      _ = _ := by simp only [pow_add]; ring
  · intro j _
    rw [abs_of_nonneg (hk j).1]
    exact (hk j).2.trans (pow_le_pow_right₀ (by norm_num) (by omega))

theorem rationalMasterUpdate_reduced_bits {n : ℕ} (p a : ℕ) (live next : Finset (Fin n))
    (hcard : (next.card:ℤ)≤(2:ℤ)^a)
    (w z prior : Fin n→ℚ) (alpha : ℚ) (hw : ∀ j,0≤w j) (hw1 : ∑ j,w j=1)
    (hsupport : ∀ j,j∉live → w j=0) (hz : ∀ j,|(z j:ℝ)|≤1/2)
    (hp : ∀ j,0≤prior j) (hp1 : ∑ j,prior j=1) (ha : 0<alpha) (ha1 : alpha≤1)
    (hprior : ∀ j,0<prior j → j∈next) (j : Fin n) :
    (rationalMasterUpdate p live next w z prior alpha j).num.natAbs.size≤a+p+4 ∧
    (rationalMasterUpdate p live next w z prior alpha j).den.size≤a+p+4 :=
  MatrixHeight.reduced_bits (rationalMasterUpdate_height p a live next hcard w z prior alpha
    hw hw1 hsupport hz hp hp1 ha ha1 hprior) j 0

end Paper254
#print axioms Paper254.rationalMasterUpdate_reduced_bits
