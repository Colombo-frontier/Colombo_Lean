import RationalLiveWeights254

open scoped BigOperators
namespace Paper254

/-- Stored normalized probabilities have uniformly bounded numerator and
denominator encodings, independently of previous denominators. -/
theorem rationalLiveSoftmax_encoding {n : ℕ} (p : ℕ) (live : Finset (Fin n))
    (w z : Fin n→ℚ) (hw : ∀ j,0≤w j) (hsum : ∑ j,w j=1)
    (hsupport : ∀ j,j∉live → w j=0) (hz : ∀ j,|(z j:ℝ)|≤1/2) :
    ∃ k : Fin n→ℤ,∃ den : ℤ,0<den ∧ den≤live.card*(2:ℤ)^(p+3) ∧
      (∀ j,0≤k j ∧ k j≤(2:ℤ)^(p+3)) ∧
      (∀ j,j∉live → k j=0) ∧
      ∀ j,rationalLiveSoftmax p live w z j=(k j:ℚ)/(den:ℚ) := by
  classical
  choose a ha0 ha1 hae using fun j=>rationalUpperMass_encoding_bound p w z hw hsum hz j
  let k := fun j=>if j∈live then a j else 0
  let den : ℤ := ∑ j,k j
  have hk0 : ∀ j,0≤k j := by intro j; dsimp [k]; split_ifs; exact (ha0 j).le; exact le_rfl
  have hk1 : ∀ j,k j≤(2:ℤ)^(p+3) := by intro j; dsimp [k]; split_ifs; exact ha1 j; positivity
  have hm : ∀ j,rationalLiveMass p live w z j=(k j:ℚ)/(2:ℚ)^(p+1) := by
    intro j
    by_cases hj : j∈live
    · simpa only [rationalLiveMass,k,if_pos hj] using hae j
    · simp [rationalLiveMass,k,hj]
  have htotal : (∑ j,rationalLiveMass p live w z j)=(den:ℚ)/(2:ℚ)^(p+1) := by
    simp only [hm,←Finset.sum_div,den,Int.cast_sum]
  let v := (rationalPrior w hw hsum).exponential (-1) (fun j=>(z j:ℝ))
  have hb := rationalLiveMass_bounds p live w z hw hsum hsupport hz
  have hreal : 1≤∑ j,(rationalLiveMass p live w z j:ℝ) := by
    rw [←v.total]
    exact Finset.sum_le_sum (fun j _=>hb.1 j)
  have hqpos : (0:ℚ)<∑ j,rationalLiveMass p live w z j := by
    have hr : (0:ℝ)<∑ j,(rationalLiveMass p live w z j:ℝ) := by linarith
    exact_mod_cast hr
  rw [htotal] at hqpos
  have hdenq : (0:ℚ)<den := (div_pos_iff_of_pos_right (by positivity)).mp hqpos
  have hden : 0<den := by exact_mod_cast hdenq
  have hsize : den≤live.card*(2:ℤ)^(p+3) := by
    calc
      _ ≤ ∑ j : Fin n,if j∈live then (2:ℤ)^(p+3) else 0 := by
        apply Finset.sum_le_sum
        intro j _
        dsimp [k]
        split_ifs
        · exact ha1 j
        · exact le_rfl
      _ = _ := by simp
  refine ⟨k,den,hden,hsize,fun j=>⟨hk0 j,hk1 j⟩,?_,?_⟩
  · intro j hj
    simp [k,hj]
  · intro j
    rw [rationalLiveSoftmax,hm,htotal]
    field_simp

end Paper254
#print axioms Paper254.rationalLiveSoftmax_encoding
