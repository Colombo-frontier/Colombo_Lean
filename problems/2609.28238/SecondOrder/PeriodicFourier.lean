import SecondOrder.TriangularPairs
import SecondOrder.PeriodicGeometry

open scoped BigOperators Classical

namespace SecondOrder
noncomputable section

variable {d : ℕ}

def pairSign (θ : Fin d → Bool) (e : UpperPair d) : ℝ := signValue (θ e.1.1)*signValue (θ e.1.2)

@[simp] theorem pairSign_sq (θ : Fin d → Bool) (e : UpperPair d) : pairSign θ e^2 = 1 := by
  simp [pairSign, mul_pow]

def pairCosPotential (a : UpperPair d → ℝ) (x : Point d) : ℝ :=
  ∑ e, a e*Real.cos (x e.1.1-x e.1.2)

def fourierPotential (a : UpperPair d → ℝ) (x : Point d) : ℝ :=
  -1/(2*(d:ℝ))-((d:ℝ)⁻¹)^2*pairCosPotential a x

theorem signedPhase_sum_sq_fourier (θ : Fin d → Bool) (x : Point d) :
    (∑ i, signedCos θ x i)^2+(∑ i, signedSin θ x i)^2 =
      (d:ℝ)+2*pairCosPotential (pairSign θ) x := by
  have he : (∑ i, signedCos θ x i)^2+(∑ i, signedSin θ x i)^2 =
      ∑ i, ∑ j, signValue (θ i)*signValue (θ j)*Real.cos (x i-x j) := by
    simp only [pow_two, Finset.sum_mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    simp only [signedCos_apply, signedSin_apply, Real.cos_sub]
    ring
  rw [he, symmetric_sum_pairs _ (by intro i j; rw [Real.cos_sub, Real.cos_sub]; ring)]
  have hd : (∑ i, signValue (θ i)*signValue (θ i)*Real.cos (x i-x i)) = (d:ℝ) := by
    simp only [sub_self, Real.cos_zero, mul_one, ← sq, signValue_sq,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
    norm_num
  rw [hd]
  rfl

/-- The exact upper-triangular Fourier expression of the original periodic potential. -/
theorem phasePotential_eq_fourier (θ : Fin d → Bool) (x : Point d) (hd : 0 < d) :
    phasePotential θ x = fourierPotential (pairSign θ) x := by
  have he := signedPhase_sum_sq_fourier θ x
  have hD : (d:ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hd
  unfold phasePotential phaseCosMean phaseSinMean fourierPotential
  rw [mul_pow, mul_pow, ← mul_add, he]
  field_simp
  ring

theorem periodicBlockPotential_fourier {m : ℕ} (θ : BalancedVector m) (hm : 0 < m) :
    periodicBlockPotential θ = fourierPotential (pairSign θ.1) := by
  funext x
  rw [periodicBlockPotential_eq, phasePotential_eq_fourier _ _ (by omega)]

theorem pairCosPotential_contDiff (a : UpperPair d → ℝ) (k : WithTop ℕ∞) :
    ContDiff ℝ k (pairCosPotential a) := by
  apply ContDiff.sum
  intro e _
  exact contDiff_const.mul (((EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin d) e.1.1).contDiff.sub
    (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin d) e.1.2).contDiff).cos)

theorem fourierPotential_contDiff (a : UpperPair d → ℝ) (k : WithTop ℕ∞) :
    ContDiff ℝ k (fourierPotential a) :=
  contDiff_const.sub (contDiff_const.mul (pairCosPotential_contDiff a k))

theorem pairCosPotential_sub (a b : UpperPair d → ℝ) (x : Point d) :
    pairCosPotential a x-pairCosPotential b x = pairCosPotential (fun e => a e-b e) x := by
  simp [pairCosPotential, sub_mul, Finset.sum_sub_distrib]

theorem fourierPotential_sub (a b : UpperPair d → ℝ) (x : Point d) :
    fourierPotential a x-fourierPotential b x = -((d:ℝ)⁻¹)^2*pairCosPotential (fun e => a e-b e) x := by
  unfold fourierPotential
  rw [← pairCosPotential_sub]
  ring

end
end SecondOrder
