import RationalEncodingReset254

noncomputable section
open scoped BigOperators
namespace Paper254

/-- Conversion from actual reduced rational encodings to the common
denominator representation used in the intermediate-value analysis. -/
theorem canonical_matrix_height {m n b : ℕ} (A : Matrix (Fin m) (Fin n) ℚ)
    (hbits : RationalMatrixBits A b) : MatrixHeight A ((m*n+1)*b) := by
  classical
  let den : Fin m×Fin n→ℤ := fun x=>(A x.1 x.2).den
  let q : ℤ := ∏ x,den x
  let tail : Fin m×Fin n→ℤ := fun x=>∏ y∈Finset.univ.erase x,den y
  have hdpos : ∀ x,0<den x := by intro x; dsimp [den]; exact_mod_cast (A x.1 x.2).den_pos
  have hdBound : ∀ x,den x≤(2:ℤ)^b := by
    intro x
    have hh := (Nat.size_le.mp (hbits x.1 x.2).2).le
    dsimp [den]
    exact_mod_cast hh
  have hnBound : ∀ i j,|(A i j).num|≤(2:ℤ)^b := by
    intro i j
    have hh := (Nat.size_le.mp (hbits i j).1).le
    have hh' : ((A i j).num.natAbs:ℤ)≤(2:ℤ)^b := by exact_mod_cast hh
    simpa only [Int.natCast_natAbs] using hh'
  have hp (S : Finset (Fin m×Fin n)) : ∏ x∈S,den x≤(2:ℤ)^((m*n)*b) := by
    calc
      _ ≤ ∏ _x∈S,(2:ℤ)^b := Finset.prod_le_prod (fun x _=>(hdpos x).le) (fun x _=>hdBound x)
      _ = ((2:ℤ)^b)^S.card := by simp
      _ ≤ (2:ℤ)^((m*n)*b) := by
        rw [←pow_mul]
        apply pow_le_pow_right₀ (by norm_num)
        have hc : S.card≤m*n := by simpa using Finset.card_le_univ S
        nlinarith
  have hq : 0<q := Finset.prod_pos (fun x _=>hdpos x)
  have ht : ∀ x,0<tail x := fun x=>Finset.prod_pos (fun y _=>hdpos y)
  have hprod : ∀ x,den x*tail x=q := fun x=>Finset.mul_prod_erase Finset.univ den (Finset.mem_univ x)
  refine ⟨fun i j=>(A i j).num*tail (i,j),q,hq.ne',?_,?_,?_⟩
  · rw [abs_of_pos hq]
    exact (hp Finset.univ).trans (pow_le_pow_right₀ (by norm_num) (by nlinarith))
  · intro i j
    rw [abs_mul,abs_of_pos (ht (i,j))]
    calc
      _ ≤ (2:ℤ)^b*(2:ℤ)^((m*n)*b) :=
        mul_le_mul (hnBound i j) (hp (Finset.univ.erase (i,j))) (ht (i,j)).le (by positivity)
      _ = _ := by rw [←pow_add]; congr 1; ring
  · intro i j
    have hqrat : (q:ℚ)=(den (i,j):ℚ)*(tail (i,j):ℚ) := by
      exact_mod_cast (hprod (i,j)).symm
    have htail : (tail (i,j):ℚ)≠0 := by exact_mod_cast (ht (i,j)).ne'
    change A i j=(((A i j).num*tail (i,j):ℤ):ℚ)/(q:ℚ)
    rw [hqrat,Int.cast_mul,mul_div_mul_right _ _ htail]
    exact (A i j).num_div_den.symm

end Paper254
#print axioms Paper254.canonical_matrix_height
