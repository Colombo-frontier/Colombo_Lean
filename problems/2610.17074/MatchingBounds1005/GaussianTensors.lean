import MatchingBounds1005.TensorPolynomial
import MatchingBounds1005.TensorNets
import MatchingBounds1005.GaussianMatrix

/-! Actual isotropic Gaussian tensor coefficients and operator-norm tails.
The full tensor coordinates are used; polynomial observations automatically
ignore the antisymmetric component. -/
noncomputable section
open MeasureTheory
open scoped BigOperators InnerProductSpace

namespace MatchingBounds1005.TensorGeometry

def tensorCoordinates (d k : ℕ) :
    Tensor d k ≃ₗᵢ[ℝ] Vec (Fintype.card (Fin k → Fin d)) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Fintype.equivFin (Fin k → Fin d))

def gaussianTensor (d k : ℕ) (z : Vec (Fintype.card (Fin k → Fin d))) : Tensor d k :=
  (tensorCoordinates d k).symm z

theorem gaussianTensorForm_continuous (d k : ℕ) :
    Continuous (fun z => tensorForm (gaussianTensor d k z)) := by
  unfold tensorForm
  apply continuous_finset_sum
  intro idx _
  apply Continuous.smul _ continuous_const
  exact (EuclideanSpace.proj idx).continuous.comp (tensorCoordinates d k).symm.continuous

theorem gaussianTensor_evaluation_tail {d k : ℕ} (v : Fin k → Vec d)
    (hv : ∀ i, ‖v i‖ = 1) {r : ℝ} (hr : 0 ≤ r) :
    (GaussianVector.standardGaussian (Fintype.card (Fin k → Fin d))).real
      {z | r ≤ |tensorForm (gaussianTensor d k z) v|} ≤ 2 * Real.exp (-r ^ 2 / 2) := by
  let a := tensorCoordinates d k (productTensor v)
  have ha : ‖a‖ ≤ 1 := by
    simpa only [a, LinearIsometryEquiv.norm_map, productTensor_norm, hv,
      Finset.prod_const_one] using (le_rfl : (1 : ℝ) ≤ 1)
  have he (z : Vec (Fintype.card (Fin k → Fin d))) :
      tensorForm (gaussianTensor d k z) v = ⟪a, z⟫_ℝ := by
    rw [tensorForm_apply, ← (tensorCoordinates d k).inner_map_map]
    simp only [gaussianTensor, LinearIsometryEquiv.apply_symm_apply]
    exact real_inner_comm _ _
  simp_rw [he]
  exact GaussianMatrix.inner_absolute_tail a ha hr

/-- The tensor degree enters the finite-net cardinality, while its Frobenius
coordinate dimension does not enter the norm threshold. -/
theorem gaussianTensor_operator_tail {d k : ℕ} (hk : k ≤ 4)
    {r : ℝ} (hr : 0 ≤ r) :
    (GaussianVector.standardGaussian (Fintype.card (Fin k → Fin d))).real
      {z | 2 * r < ‖tensorForm (gaussianTensor d k z)‖} ≤
        (17 : ℝ) ^ (d * k) * (2 * Real.exp (-r ^ 2 / 2)) := by
  classical
  obtain ⟨s, hscard, hsunit, hsnet⟩ := GaussianNets.spectral_sphere_net (E := Vec d)
  let S := Fintype.piFinset (fun _ : Fin k => s)
  let bad (v : Fin k → Vec d) : Set (Vec (Fintype.card (Fin k → Fin d))) :=
    {z | r ≤ |tensorForm (gaussianTensor d k z) v|}
  have hsub : {z : Vec (Fintype.card (Fin k → Fin d)) |
      2 * r < ‖tensorForm (gaussianTensor d k z)‖} ⊆ ⋃ v ∈ S, bad v := by
    intro z hz
    by_contra hn
    have hb : ∀ v : Fin k → Vec d, (∀ i, v i ∈ s) →
        |tensorForm (gaussianTensor d k z) v| ≤ r := by
      intro v hv
      have hvS : v ∈ S := by simpa only [S, Fintype.mem_piFinset] using hv
      have hnv : z ∉ bad v := fun h => hn
        (Set.mem_iUnion.mpr ⟨v, Set.mem_iUnion.mpr ⟨hvS, h⟩⟩)
      exact (lt_of_not_ge hnv).le
    exact (not_lt_of_ge (TensorNets.multilinear_norm_bound_of_net hk
      (tensorForm (gaussianTensor d k z)) s hsunit hsnet hr hb)) hz
  have hcard : (S.card : ℝ) ≤ (17 : ℝ) ^ (d * k) := by
    have hc : s.card ≤ 17 ^ d := by simpa using hscard
    have hh := Nat.pow_le_pow_left hc k
    rw [← pow_mul] at hh
    have he : S.card = s.card ^ k := by
      simp only [S, Fintype.card_piFinset, Finset.prod_const, Finset.card_univ,
        Fintype.card_fin]
    rw [he]
    exact_mod_cast hh
  calc
    _ ≤ (GaussianVector.standardGaussian _).real (⋃ v ∈ S, bad v) := measureReal_mono hsub
    _ ≤ ∑ v ∈ S, (GaussianVector.standardGaussian _).real (bad v) :=
      measureReal_biUnion_finset_le _ _
    _ ≤ ∑ _v ∈ S, 2 * Real.exp (-r ^ 2 / 2) := by
      apply Finset.sum_le_sum
      intro v hv
      have hvs : ∀ i, v i ∈ s := by simpa only [S, Fintype.mem_piFinset] using hv
      exact gaussianTensor_evaluation_tail v (fun i => hsunit (v i) (hvs i)) hr
    _ = (S.card : ℝ) * (2 * Real.exp (-r ^ 2 / 2)) := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right hcard (by positivity)

theorem gaussianTensor_operator_exponential {d k : ℕ} (hk : k ≤ 4)
    {r s : ℝ} (hr : 0 ≤ r) (hsize : 6 * ((d * k : ℕ) : ℝ) + 2 * s ≤ r ^ 2) :
    (GaussianVector.standardGaussian (Fintype.card (Fin k → Fin d))).real
      {z | 2 * r < ‖tensorForm (gaussianTensor d k z)‖} ≤ 2 * Real.exp (-s) := by
  apply (gaussianTensor_operator_tail hk hr).trans
  have he : (17 : ℝ) = Real.exp (Real.log 17) := (Real.exp_log (by norm_num)).symm
  conv_lhs => rw [he, ← Real.exp_nat_mul]
  have hlog := mul_le_mul_of_nonneg_left GaussianMatrix.log_seventeen_le_three
    (Nat.cast_nonneg (d * k) : (0 : ℝ) ≤ (d * k : ℕ))
  have hx : ((d * k : ℕ) : ℝ) * Real.log 17 + -r ^ 2 / 2 ≤ -s := by linarith
  have hh := Real.exp_le_exp.mpr hx
  rw [Real.exp_add] at hh
  nlinarith

/-- A fixed numerical constant works for both cubic and quartic masks. -/
theorem gaussianTensor_norm_failure {d k : ℕ} (hk : k ≤ 4) :
    (GaussianVector.standardGaussian (Fintype.card (Fin k → Fin d))).real
      {z | 32 * Real.sqrt d < ‖tensorForm (gaussianTensor d k z)‖} ≤
        2 * Real.exp (-100 * d) := by
  have h := gaussianTensor_operator_exponential (d := d) hk
    (r := 16 * Real.sqrt d) (s := 100 * d) (by positivity) ?_
  · convert h using 1 <;> ring
  · rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg d)]
    have hkR : (k : ℝ) ≤ 4 := by exact_mod_cast hk
    have hm := mul_le_mul_of_nonneg_left hkR (Nat.cast_nonneg d : (0 : ℝ) ≤ d)
    push_cast
    nlinarith

theorem gaussianTensor_norm_failure_small {d k : ℕ} (hd : 1 ≤ d) (hk : k ≤ 4) :
    (GaussianVector.standardGaussian (Fintype.card (Fin k → Fin d))).real
      {z | 32 * Real.sqrt d < ‖tensorForm (gaussianTensor d k z)‖} ≤ 1 / 200 := by
  apply (gaussianTensor_norm_failure hk).trans
  have h1 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have h10 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) h1 10
  rw [← Real.exp_nat_mul] at h10
  norm_num at h10
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have he : Real.exp 10 ≤ Real.exp (100 * d) := Real.exp_le_exp.mpr (by linarith)
  have hbig : (400 : ℝ) ≤ Real.exp (100 * d) := by linarith
  rw [show -100 * (d : ℝ) = -(100 * d) by ring, Real.exp_neg, ← div_eq_mul_inv]
  apply (div_le_iff₀ (Real.exp_pos _)).mpr
  linarith

def TensorNormGood (d k : ℕ) : Set (Vec (Fintype.card (Fin k → Fin d))) :=
  {z | ‖tensorForm (gaussianTensor d k z)‖ ≤ 32 * Real.sqrt d}

theorem tensorNormGood_measurable (d k : ℕ) : MeasurableSet (TensorNormGood d k) :=
  measurableSet_le (gaussianTensorForm_continuous d k).norm.measurable measurable_const

theorem tensorNormGood_probability {d k : ℕ} (hd : 1 ≤ d) (hk : k ≤ 4) :
    (199 / 200 : ℝ) ≤ (GaussianVector.standardGaussian
      (Fintype.card (Fin k → Fin d))).real (TensorNormGood d k) := by
  have he : (TensorNormGood d k)ᶜ =
      {z | 32 * Real.sqrt d < ‖tensorForm (gaussianTensor d k z)‖} := by
    ext z
    simp only [TensorNormGood, Set.mem_compl_iff, Set.mem_setOf_eq, not_le]
  have hsum := measureReal_add_measureReal_compl
    (μ := GaussianVector.standardGaussian (Fintype.card (Fin k → Fin d)))
    (tensorNormGood_measurable d k)
  rw [measureReal_univ_eq_one, he] at hsum
  have hf := gaussianTensor_norm_failure_small (k := k) hd hk
  linarith

/-- The manuscript's exact Gaussian normalization constant. -/
def sourceGaussianConstant (k : ℕ) : ℝ :=
  4 * Real.sqrt ((k : ℝ) * Real.log (1 + 4 * k) + 2)

theorem sourceGaussianConstant_pos {k : ℕ} (hk : 1 ≤ k) :
    0 < sourceGaussianConstant k := by
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hl : 0 ≤ Real.log (1 + 4 * (k : ℝ)) := Real.log_nonneg (by linarith)
  unfold sourceGaussianConstant
  positivity

/-- Exact source threshold and source exponential tail. The existing 1/8-net
also suffices at degree three because the source threshold has slack. -/
theorem source_gaussian_norm_failure {d k : ℕ} (hk1 : 1 ≤ k) (hk4 : k ≤ 4) :
    (GaussianVector.standardGaussian (Fintype.card (Fin k → Fin d))).real
      {z | sourceGaussianConstant k * Real.sqrt d <
        ‖tensorForm (gaussianTensor d k z)‖} ≤ 2 * Real.exp (-4 * d) := by
  let I : ℝ := k * Real.log (1 + 4 * (k : ℝ)) + 2
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk1
  have hl : 0 ≤ Real.log (1 + 4 * (k : ℝ)) := Real.log_nonneg (by linarith)
  have hI : 0 ≤ I := by dsimp only [I]; positivity
  have hlog : Real.log 17 ≤ 2 * Real.log (1 + 4 * (k : ℝ)) := by
    have h := Real.log_le_log (by norm_num : (0 : ℝ) < 17)
      (show (17 : ℝ) ≤ (1 + 4 * (k : ℝ)) ^ 2 by nlinarith)
    simpa only [Real.log_pow, Nat.cast_ofNat] using h
  have hbase := gaussianTensor_operator_tail (d := d) hk4
    (r := 2 * Real.sqrt I * Real.sqrt d) (by positivity)
  have hevent : {z : Vec (Fintype.card (Fin k → Fin d)) |
      sourceGaussianConstant k * Real.sqrt d < ‖tensorForm (gaussianTensor d k z)‖} =
      {z | 2 * (2 * Real.sqrt I * Real.sqrt d) < ‖tensorForm (gaussianTensor d k z)‖} := by
    ext z
    simp only [Set.mem_setOf_eq]
    unfold sourceGaussianConstant
    change 4 * Real.sqrt I * Real.sqrt d < _ ↔ _
    ring_nf
  rw [hevent]
  apply hbase.trans
  have hr2 : (2 * Real.sqrt I * Real.sqrt d) ^ 2 = 4 * I * d := by
    rw [mul_pow, mul_pow, Real.sq_sqrt hI, Real.sq_sqrt (Nat.cast_nonneg d)]
    ring
  rw [hr2]
  have h17 : (17 : ℝ) = Real.exp (Real.log 17) := (Real.exp_log (by norm_num)).symm
  conv_lhs => rw [h17, ← Real.exp_nat_mul]
  have hm := mul_le_mul_of_nonneg_left hlog
    (mul_nonneg (Nat.cast_nonneg d) (Nat.cast_nonneg k) : (0 : ℝ) ≤ (d : ℝ) * k)
  have hx : ((d * k : ℕ) : ℝ) * Real.log 17 + -(4 * I * d) / 2 ≤ -4 * d := by
    push_cast
    dsimp only [I]
    nlinarith only [hm]
  have hexp := Real.exp_le_exp.mpr hx
  rw [Real.exp_add] at hexp
  nlinarith only [hexp]

end MatchingBounds1005.TensorGeometry
