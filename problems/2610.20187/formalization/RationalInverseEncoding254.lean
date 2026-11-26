import EfficientInverse254

noncomputable section
open Matrix
open scoped BigOperators
namespace Paper254

theorem integer_det_bound {d : ℕ} (Z : Matrix (Fin d) (Fin d) ℤ) (B : ℕ)
    (hZ : ∀ i j,|Z i j|≤(2:ℤ)^B) : |Z.det|≤(2:ℤ)^(d*d+B*d) := by
  have hp : (Fintype.card (Equiv.Perm (Fin d)):ℤ)≤(2:ℤ)^(d*d) := by
    have hnat : Fintype.card (Equiv.Perm (Fin d))≤2^(d*d) := by
      rw [Fintype.card_perm,Fintype.card_fin]
      calc
        d.factorial≤d^d := Nat.factorial_le_pow d
        _≤(2^d)^d := Nat.pow_le_pow_left (Nat.le_of_lt Nat.lt_two_pow_self) d
        _=_ := by rw [←pow_mul]
    exact_mod_cast hnat
  rw [Matrix.det_apply]
  calc
    _ ≤ ∑ σ : Equiv.Perm (Fin d),|Equiv.Perm.sign σ • ∏ i,Z (σ i) i| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _σ : Equiv.Perm (Fin d),((2:ℤ)^B)^d := by
      apply Finset.sum_le_sum
      intro σ _
      have hh : |∏ i,Z (σ i) i|≤((2:ℤ)^B)^d := by
        rw [Finset.abs_prod]
        calc
          _ ≤ ∏ _i : Fin d,(2:ℤ)^B :=
            Finset.prod_le_prod (fun _ _=>abs_nonneg _) (fun i _=>hZ _ _)
          _ = _ := by simp
      rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs
      · simpa [hs] using hh
      · simpa only [hs,Units.smul_def,Units.val_neg,Units.val_one,neg_smul,one_smul,abs_neg] using hh
    _ = (Fintype.card (Equiv.Perm (Fin d)):ℤ)*((2:ℤ)^B)^d := by simp
    _ ≤ (2:ℤ)^(d*d)*((2:ℤ)^B)^d :=
      mul_le_mul_of_nonneg_right hp (by positivity)
    _ = _ := by simp only [pow_add,pow_mul]

theorem integer_adjugate_bound {d : ℕ} (Z : Matrix (Fin d) (Fin d) ℤ) (B : ℕ)
    (hZ : ∀ i j,|Z i j|≤(2:ℤ)^B) (i j : Fin d) :
    |Z.adjugate i j|≤(2:ℤ)^(d*d+B*d) := by
  rw [Matrix.adjugate_apply]
  apply integer_det_bound
  intro k l
  by_cases hk : k=j
  · subst k
    simp only [Matrix.updateRow_self,Pi.single_apply]
    split_ifs <;> simp only [abs_one,abs_zero]
    · exact one_le_pow₀ (by norm_num)
    · positivity
  · simpa [Matrix.updateRow_ne hk] using hZ k l

theorem rational_inverse_encoding {d : ℕ}
    (A : Matrix (Fin d) (Fin d) ℚ) (Z : Matrix (Fin d) (Fin d) ℤ)
    (q : ℤ) (B : ℕ) (hq : q≠0) (hqb : |q|≤(2:ℤ)^B)
    (hZ : ∀ i j,|Z i j|≤(2:ℤ)^B)
    (hrep : ∀ i j,A i j=(Z i j:ℚ)/(q:ℚ)) (hA : IsUnit A.det) :
    ∃ N : Matrix (Fin d) (Fin d) ℤ,∃ Q : ℤ,
      Q≠0 ∧ |Q|≤(2:ℤ)^((d+1)*(B+d+1)) ∧
      (∀ i j,|N i j|≤(2:ℤ)^((d+1)*(B+d+1))) ∧
      ∀ i j,A⁻¹ i j=(N i j:ℚ)/(Q:ℚ) := by
  let ZQ : Matrix (Fin d) (Fin d) ℚ := Z.map (Int.castRingHom ℚ)
  have hqQ : (q:ℚ)≠0 := by exact_mod_cast hq
  have heq : A=(q:ℚ)⁻¹ • ZQ := by
    ext i j
    simpa [ZQ,Matrix.smul_apply,Matrix.map_apply,smul_eq_mul,div_eq_mul_inv,mul_comm] using hrep i j
  have hdet : ZQ.det≠0 := by
    have hne := hA.ne_zero
    rw [heq,Matrix.det_smul] at hne
    exact (mul_ne_zero_iff.mp hne).2
  have hdetcast : ZQ.det=(Z.det:ℚ) := by
    exact ((Int.castRingHom ℚ).map_det Z).symm
  have hdetZ : Z.det≠0 := by exact_mod_cast (hdetcast ▸ hdet)
  have hadj : ZQ.adjugate=(Z.adjugate.map (Int.castRingHom ℚ)) := by
    exact ((Int.castRingHom ℚ).map_adjugate Z).symm
  letI : Invertible ((q:ℚ)⁻¹) := invertibleOfNonzero (inv_ne_zero hqQ)
  have hinv : A⁻¹=(q:ℚ) • ZQ⁻¹ := by
    rw [heq,Matrix.inv_smul ZQ ((q:ℚ)⁻¹) (isUnit_iff_ne_zero.mpr hdet)]
    simp
  refine ⟨fun i j=>q*Z.adjugate i j,Z.det,hdetZ,?_,?_,?_⟩
  · exact (integer_det_bound Z B hZ).trans
      (pow_le_pow_right₀ (by norm_num) (by nlinarith : d*d+B*d≤(d+1)*(B+d+1)))
  · intro i j
    rw [abs_mul]
    calc
      _ ≤ (2:ℤ)^B*(2:ℤ)^(d*d+B*d) :=
        mul_le_mul hqb (integer_adjugate_bound Z B hZ i j) (abs_nonneg _) (by positivity)
      _ = (2:ℤ)^(B+(d*d+B*d)) := by simp only [pow_add]
      _ ≤ _ := pow_le_pow_right₀ (by norm_num) (by nlinarith)
  · intro i j
    rw [hinv,Matrix.inv_def,hdetcast,hadj]
    simp only [Matrix.smul_apply,smul_eq_mul,Matrix.map_apply,Int.cast_mul]
    rw [Ring.inverse_eq_inv]
    change (q:ℚ)*((Z.det:ℚ)⁻¹*(Z.adjugate i j:ℚ))=
      ((q:ℚ)*(Z.adjugate i j:ℚ))/(Z.det:ℚ)
    ring

end Paper254
#print axioms Paper254.rational_inverse_encoding
