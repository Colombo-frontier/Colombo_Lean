import LowRank.InverseGramTailArithmetic
import LowRank.InverseGramWishartBound
import LowRank.GaussianMatrixCompression

/-!
# The exact lower spectral threshold in the manuscript's source event

This module uses the proved inverse-Gram moment estimates for the actual iid
Gaussian matrix law.  It does not assume the manuscript's Gaussian comparison
or extreme-singular-value lemma.  The bound retains the ambient normalization
`1 / D` when rows are deleted.  The full source event also requires an upper
spectral bound and concentration of the compressed random kernel; those are
separate obligations.
-/

namespace GradientHessian.MatrixGoodEvent

open Matrix MeasureTheory LowRank
open scoped Matrix ENNReal
noncomputable section

/-- Inverse-Gram moments after row deletion, with the original ambient variance.
The matrix has `n` columns, `h` excess rows, and at most `D` rows. -/
theorem inverseGramMomentBound_ambient {D n h : ℕ} (hn : 0 < n)
    (hsize : n + h ≤ D) (hh : 4 ≤ h) :
    inverseGramMomentBound n (h + 1) (D : NNReal)⁻¹ (h / 4 : ℕ) ≤
      (48 * (D : ℝ) ^ 2 / (h : ℝ) ^ 2) ^ (h / 4) := by
  let q := h / 4
  have hq : 0 < q := by dsimp [q]; omega
  have h8 : h ≤ 8 * q := by dsimp [q]; omega
  have h4 : 4 * q ≤ h := by dsimp [q]; omega
  have hqm : 2 * q < h + 1 := by omega
  have hD : (0 : ℝ) < D := by exact_mod_cast (show 0 < D by omega)
  have hhR : (0 : ℝ) < h := by exact_mod_cast (show 0 < h by omega)
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hsizeR : (n : ℝ) + h ≤ D := by exact_mod_cast hsize
  have h4R : 4 * (q : ℝ) ≤ h := by exact_mod_cast h4
  have h8R : (h : ℝ) ≤ 8 * q := by exact_mod_cast h8
  have hgapR : 0 < (h : ℝ) + 1 - 2 * q := by linarith
  have hnq : (n : ℝ) + 2 * q ≤ D := by linarith
  have hexp : Real.exp 1 ≤ 3 := Real.exp_one_lt_d9.le.trans (by norm_num)
  have hnum : ((n : ℝ) + 2 * q) * D * Real.exp 1 ≤ 3 * (D : ℝ) ^ 2 := by
    calc
      _ ≤ (D : ℝ) * D * 3 := mul_le_mul
        (mul_le_mul_of_nonneg_right hnq hD.le) hexp (Real.exp_pos 1).le (by positivity)
      _ = _ := by ring
  have hden : (h : ℝ) ^ 2 / 16 ≤ (q : ℝ) * ((h : ℝ) + 1 - 2 * q) := by
    have hp := mul_le_mul (show (h : ℝ) / 8 ≤ q by linarith)
      (show (h : ℝ) / 2 ≤ (h : ℝ) + 1 - 2 * q by linarith) (by positivity) hqR.le
    nlinarith
  have hbase : (((n : ℝ) + 2 * q) * D * Real.exp 1 /
      ((q : ℝ) * ((h : ℝ) + 1 - 2 * q))) ≤ 48 * (D : ℝ) ^ 2 / (h : ℝ) ^ 2 := by
    calc
      _ ≤ (3 * (D : ℝ) ^ 2) / ((h : ℝ) ^ 2 / 16) :=
        div_le_div₀ (by positivity) hnum (by positivity) hden
      _ = _ := by field_simp; ring
  have hp := inverseGramMomentBound_nat_le hn hq hqm (D : NNReal)⁻¹
  simp only [NNReal.coe_inv, NNReal.coe_natCast, inv_inv, Nat.cast_add, Nat.cast_one] at hp
  exact hp.trans (pow_le_pow_left₀ (by positivity) hbase q)

/-- The inverse threshold corresponding exactly to the manuscript lower edge. -/
def sourceInverseThreshold (D k : ℕ) : ℝ := 64 * (D : ℝ) ^ 2 / (k : ℝ) ^ 2

theorem sourceInverseThreshold_pos {D k : ℕ} (hD : 0 < D) (hk : 0 < k) :
    0 < sourceInverseThreshold D k := by unfold sourceInverseThreshold; positivity

theorem sourceInverseThreshold_inv (D k : ℕ) :
    (sourceInverseThreshold D k)⁻¹ = (k : ℝ) ^ 2 / (64 * (D : ℝ) ^ 2) := by
  simp only [sourceInverseThreshold, inv_div]

/-- At least fifteen sixteenths of the original codimension survives deleting
the marked rows.  The geometric decay factor is strictly below one. -/
theorem source_inverse_moment_ratio {D n h k : ℕ} (hn : 0 < n)
    (hsize : n + h ≤ D) (hh : 4 ≤ h) (hk : 0 < k) (hgap : 15 * k ≤ 16 * h) :
    inverseGramMomentBound n (h + 1) (D : NNReal)⁻¹ (h / 4 : ℕ) /
        sourceInverseThreshold D k ^ (h / 4) ≤ (64 / 75 : ℝ) ^ (h / 4) := by
  have hD : 0 < D := by omega
  have hDR : (D : ℝ) ≠ 0 := by exact_mod_cast hD.ne'
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hhR : (0 : ℝ) < h := by exact_mod_cast (show 0 < h by omega)
  have hgapR : 15 * (k : ℝ) ≤ 16 * h := by exact_mod_cast hgap
  have hratio : (48 * (D : ℝ) ^ 2 / (h : ℝ) ^ 2) /
      sourceInverseThreshold D k ≤ 64 / 75 := by
    have he : (48 * (D : ℝ) ^ 2 / (h : ℝ) ^ 2) /
        sourceInverseThreshold D k = 3 * (k : ℝ) ^ 2 / (4 * (h : ℝ) ^ 2) := by
      unfold sourceInverseThreshold
      field_simp
      ring
    rw [he]
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 4 * (h : ℝ) ^ 2)).mpr
    nlinarith [sq_nonneg (16 * (h : ℝ) - 15 * k),
      mul_nonneg (show 0 ≤ 16 * (h : ℝ) - 15 * k by linarith)
        (show 0 ≤ 16 * (h : ℝ) + 15 * k by positivity)]
  calc
    _ ≤ (48 * (D : ℝ) ^ 2 / (h : ℝ) ^ 2) ^ (h / 4) /
        sourceInverseThreshold D k ^ (h / 4) := div_le_div_of_nonneg_right
      (inverseGramMomentBound_ambient hn hsize hh)
      (pow_nonneg (sourceInverseThreshold_pos hD hk).le _)
    _ = ((48 * (D : ℝ) ^ 2 / (h : ℝ) ^ 2) / sourceInverseThreshold D k) ^ (h / 4) :=
      (div_pow _ _ _).symm
    _ ≤ _ := pow_le_pow_left₀ (div_nonneg (by positivity)
      (sourceInverseThreshold_pos hD hk).le) hratio _

/-- A genuine Gaussian probability bound at the manuscript's exact inverse
threshold; neither a spectral event nor a concentration estimate is a premise. -/
theorem source_inverseGram_tail {D m s h k : ℕ} (hrows : s + 1 + h = m)
    (hmD : m ≤ D) (hh : 4 ≤ h) (hk : 0 < k) (hgap : 15 * k ≤ 16 * h)
    (i : Fin (s + 1)) :
    (iidMatrixLaw m (s + 1) (D : NNReal)⁻¹)
      {X | sourceInverseThreshold D k < inverseGramEigenvalue X i} ≤
        ENNReal.ofReal ((64 / 75 : ℝ) ^ (h / 4)) := by
  have hD : 0 < D := by omega
  have hs : s + 1 ≤ m := by omega
  have hv : (D : NNReal)⁻¹ ≠ 0 := inv_ne_zero (by exact_mod_cast hD.ne')
  have hres : m - s = h + 1 := by omega
  have hqm : 2 * (h / 4) < h + 1 := by omega
  have hqmR : 2 * ((h / 4 : ℕ) : ℝ) < (h + 1 : ℕ) := by exact_mod_cast hqm
  have ha : 0 < ((m - s : ℕ) : ℝ) / 2 - ((h / 4 : ℕ) : ℝ) := by rw [hres]; linarith
  have hp := inverseGram_tail_le_ofReal hs hv i (by positivity) ha
    (sourceInverseThreshold_pos hD hk)
  rw [hres, Real.rpow_natCast] at hp
  exact hp.trans (ENNReal.ofReal_le_ofReal
    (source_inverse_moment_ratio (by omega) (by omega) hh hk hgap))

/-- Inverting a positive Gram matrix reverses a scalar Loewner bound. -/
theorem gram_lower_of_inverseGram_le {d s : ℕ} (X : Matrix (Fin d) (Fin s) ℝ)
    (hX : Function.Injective X.mulVec) {R : ℝ} (hR : 0 < R)
    (hInv : LoewnerLE (inverseGram X) (R • 1)) :
    LoewnerLE (R⁻¹ • 1) (Xᵀ * X) := by
  let G := Xᵀ * X
  have hG : G.PosSemidef := rightGram_posSemidef X
  let S := hG.sqrt
  have hSS : S * S = G := hG.sqrt_mul_self
  have hSt : Sᵀ = S := by
    simpa only [conjTranspose_eq_transpose_of_trivial] using hG.posSemidef_sqrt.isHermitian.eq
  have hSdet : IsUnit S.det := by
    apply isUnit_iff_ne_zero.mpr
    intro hs
    have hd := congrArg Matrix.det hSS
    rw [Matrix.det_mul, hs, zero_mul] at hd
    exact (gram_det_isUnit_of_injective X hX).ne_zero hd.symm
  have hSinv : S⁻¹ * S = 1 := Matrix.nonsing_inv_mul S hSdet
  have hSinv' : S * S⁻¹ = 1 := Matrix.mul_nonsing_inv S hSdet
  have hconj : Sᵀ * inverseGram X * S = 1 := by
    change Sᵀ * G⁻¹ * S = 1
    rw [hSt, ← hSS, Matrix.mul_inv_rev]
    calc
      S * (S⁻¹ * S⁻¹) * S = (S * S⁻¹) * (S⁻¹ * S) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hSinv, hSinv']; simp
  have hb := loewner_congruence hInv S
  rw [hconj] at hb
  simp only [hSt, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hSS] at hb
  have hc := psd_smul hb (inv_nonneg.mpr hR.le)
  change (R⁻¹ • (R • G - 1)).PosSemidef at hc
  rw [smul_sub, smul_smul, inv_mul_cancel₀ hR.ne', one_smul] at hc
  exact hc

/-- The actual lower Gram spectral event, with an explicit geometric tail. -/
theorem source_gram_lower_tail {D m s h k : ℕ} (hrows : s + 1 + h = m)
    (hmD : m ≤ D) (hh : 4 ≤ h) (hk : 0 < k) (hgap : 15 * k ≤ 16 * h) :
    (iidMatrixLaw m (s + 1) (D : NNReal)⁻¹)
      {X | ¬LoewnerLE (((k : ℝ) ^ 2 / (64 * (D : ℝ) ^ 2)) • 1) (Xᵀ * X)} ≤
        ENNReal.ofReal ((64 / 75 : ℝ) ^ (h / 4)) := by
  have hD : 0 < D := by omega
  have hs : s + 1 ≤ m := by omega
  have hv : (D : NNReal)⁻¹ ≠ 0 := inv_ne_zero (by exact_mod_cast hD.ne')
  apply le_trans _ (source_inverseGram_tail hrows hmD hh hk hgap (Fin.last s))
  apply measure_mono_ae
  filter_upwards [iidMatrixLaw_mulVec_injective_ae m (s + 1) hs hv] with X hX
  intro hbad
  apply lt_of_not_ge
  intro htop
  apply hbad
  rw [← sourceInverseThreshold_inv]
  apply gram_lower_of_inverseGram_le X hX (sourceInverseThreshold_pos hD hk)
  let sp := orderedMatrixSpectrum (inverseGram_posSemidef X).isHermitian
  exact (sp.loewner_interval (a := 0) (b := sourceInverseThreshold D k)
    (fun i => ⟨sp.value_nonneg (inverseGram_posSemidef X) i,
      (sp.increasing (Fin.le_last i)).trans htop⟩)).2

theorem isClosed_positiveSemidefinite (n : ℕ) :
    IsClosed {A : Matrix (Fin n) (Fin n) ℝ | A.PosSemidef} := by
  simp only [Matrix.PosSemidef, Set.setOf_and, Set.setOf_forall]
  apply IsClosed.inter
  · change IsClosed {A : Matrix (Fin n) (Fin n) ℝ | Aᴴ = A}
    exact isClosed_eq (by fun_prop) continuous_id
  · apply isClosed_iInter
    intro x
    apply isClosed_le continuous_const
    simp only [dotProduct, Matrix.mulVec]
    fun_prop

theorem measurableSet_gram_lower_failure (m n : ℕ) (c : ℝ) :
    MeasurableSet {X : Matrix (Fin m) (Fin n) ℝ | ¬LoewnerLE (c • 1) (Xᵀ * X)} := by
  have hm : Measurable (fun X : Matrix (Fin m) (Fin n) ℝ => Xᵀ * X - c • 1) := by
    apply measurable_pi_lambda
    intro i
    apply measurable_pi_lambda
    intro j
    simp only [Matrix.sub_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.smul_apply,
      smul_eq_mul]
    fun_prop
  exact ((isClosed_positiveSemidefinite n).measurableSet.preimage hm).compl

/-- Transport the exact lower edge to any deterministic orthogonal deletion
of rows of the original matrix.  The variance is still `1 / D`. -/
theorem compressed_gram_lower_tail {D m n h k : ℕ} (hn : 0 < n)
    (hrows : n + h = m) (hmD : m ≤ D) (hh : 4 ≤ h) (hk : 0 < k)
    (hgap : 15 * k ≤ 16 * h)
    (V : Matrix (Fin D) (Fin m) ℝ) (hV : Vᵀ * V = 1) :
    (iidMatrixLaw D n (D : NNReal)⁻¹)
      {X | ¬LoewnerLE (((k : ℝ) ^ 2 / (64 * (D : ℝ) ^ 2)) • 1)
        (Xᵀ * (V * Vᵀ) * X)} ≤ ENNReal.ofReal ((64 / 75 : ℝ) ^ (h / 4)) := by
  cases n with
  | zero => omega
  | succ s =>
    have hp := source_gram_lower_tail hrows hmD hh hk hgap
    have hm : Measurable (fun X : Matrix (Fin D) (Fin (s + 1)) ℝ => Vᵀ * X) := by
      apply measurable_pi_lambda
      intro i
      apply measurable_pi_lambda
      intro j
      simp only [Matrix.mul_apply]
      fun_prop
    rw [← iidMatrixLaw_left_compression V hV (D : NNReal)⁻¹,
      Measure.map_apply hm (measurableSet_gram_lower_failure m (s + 1) _)] at hp
    simpa only [Set.preimage_setOf_eq, Matrix.transpose_mul, Matrix.transpose_transpose,
      Matrix.mul_assoc] using hp

/-- Source parameters after deleting `r` marked rows, before substituting
`D = k J`.  Only elementary integer size inequalities are assumed. -/
theorem deleted_gram_lower_tail {D r k : ℕ} (hk : 0 < k) (hkD : k < D)
    (hgap : 256 ≤ k - r) (hkr : 16 * r ≤ k)
    (V : Matrix (Fin D) (Fin (D - r)) ℝ) (hV : Vᵀ * V = 1) :
    (iidMatrixLaw D (D - k) (D : NNReal)⁻¹)
      {X | ¬LoewnerLE (((k : ℝ) ^ 2 / (64 * (D : ℝ) ^ 2)) • 1)
        (Xᵀ * (V * Vᵀ) * X)} ≤ ENNReal.ofReal (1 / 1000) := by
  have hp := compressed_gram_lower_tail (D := D) (m := D-r) (n := D-k) (h := k-r)
    (by omega) (by omega) (by omega) (by omega) hk (by omega) V hV
  apply hp.trans
  apply ENNReal.ofReal_le_ofReal
  calc
    (64 / 75 : ℝ) ^ ((k - r) / 4) ≤ (64 / 75 : ℝ) ^ 64 :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    _ ≤ 1 / 1000 := by norm_num

/-- The literal lower spectral threshold `1 / (64 J^2)` from `lem:good`,
under its size conditions.  `V` is any orthonormal basis of the unmarked
coordinate subspace, so `V * Vᵀ = I - P` for the manuscript's projector. -/
theorem manuscript_deleted_gram_lower_tail {J r κ k D : ℕ}
    (hJ : 4 ≤ J) (hr : 1 + 4096 * J ^ 2 ≤ r) (hκ : 16 ≤ κ)
    (hk : k = κ * r) (hD : D = k * J)
    (V : Matrix (Fin D) (Fin (D - r)) ℝ) (hV : Vᵀ * V = 1) :
    (iidMatrixLaw D (D - k) (D : NNReal)⁻¹)
      {X | ¬LoewnerLE ((1 / (64 * (J : ℝ) ^ 2)) • 1)
        (Xᵀ * (V * Vᵀ) * X)} ≤ ENNReal.ofReal (1 / 1000) := by
  have hr0 : 0 < r := by omega
  have hk0 : 0 < k := by rw [hk]; positivity
  have hkr : 16 * r ≤ k := by rw [hk]; exact Nat.mul_le_mul_right r hκ
  have hkD : k < D := by rw [hD]; nlinarith
  have hgap : 256 ≤ k - r := by nlinarith [Nat.sub_add_cancel (show r ≤ k by omega)]
  have hp := deleted_gram_lower_tail hk0 hkD hgap hkr V hV
  have he : (k : ℝ) ^ 2 / (64 * (D : ℝ) ^ 2) = 1 / (64 * (J : ℝ) ^ 2) := by
    rw [hD, Nat.cast_mul]
    have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk0.ne'
    field_simp
    ring
  rwa [he] at hp

end
end GradientHessian.MatrixGoodEvent
