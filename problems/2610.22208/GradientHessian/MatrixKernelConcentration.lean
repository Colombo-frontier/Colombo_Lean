import GradientHessian.GaussianTail
import GradientHessian.MatrixGoodEvent
import GradientHessian.MatrixGoodUpper
import LowRank.GaussianProjectionSquaredLaw
import LowRank.GaussianGaugeMatrix

/-!
# Concentration of normalized Gaussian projections

All probabilities below use actual product Gaussian measures.  In particular,
the ratio estimate does not posit a spherical concentration theorem or
independence between the numerator and denominator.  They may overlap.
-/

namespace GradientHessian.MatrixKernelConcentration

open Matrix MeasureTheory ProbabilityTheory LowRank
open scoped Matrix ENNReal InnerProductSpace
noncomputable section

/-- The two relative chi-square controls used in the manuscript imply its
fixed-direction tolerance `eta / 48`. -/
theorem ratio_control {a b k D : ℝ} (hk : 0 < k) (hD : 0 < D)
    (ha : |a / k - 1| ≤ 1 / 384) (hb : |b / D - 1| ≤ 1 / 384) :
    |a / b - k / D| ≤ (k / D) / 48 := by
  have hb0 : 0 < b / D := by have h := (abs_le.mp hb).1; linarith
  have hbpos : 0 < b := (div_pos_iff_of_pos_right hD).mp hb0
  have hd : |a / k - b / D| ≤ 1 / 192 := by
    calc
      _ = |(a / k - 1) - (b / D - 1)| := by congr 1; ring
      _ ≤ |a / k - 1| + |b / D - 1| := abs_sub _ _
      _ ≤ 1 / 192 := by linarith
  have hrel : |(a / k) / (b / D) - 1| ≤ 1 / 48 := by
    rw [div_sub_one hb0.ne', abs_div, abs_of_pos hb0]
    apply (div_le_iff₀ hb0).mpr
    have h := (abs_le.mp hb).1
    linarith
  have he : a / b - k / D = (k / D) * ((a / k) / (b / D) - 1) := by
    field_simp
    ring
  rw [he, abs_mul, abs_of_pos (div_pos hk hD)]
  exact (mul_le_mul_of_nonneg_left hrel (div_pos hk hD).le).trans_eq (by ring)

theorem projector_quadratic_tail {D k : ℕ} (hk : 0 < k)
    (P : Matrix (Fin D) (Fin D) ℝ) (hP : IsOrthogonalProjector P) (hrank : P.rank = k) :
    (iidVectorLaw D 1).real {z | (1 / 384 : ℝ) < |(z ⬝ᵥ (P *ᵥ z)) / k - 1|} ≤
      2 * Real.exp (-(k : ℝ) / 1179648) := by
  let bad : Set ℝ := {a | (1 / 384 : ℝ) < |a / k - 1|}
  have hbad : MeasurableSet bad := by
    apply measurableSet_lt measurable_const
    fun_prop
  have hquad : Measurable (fun z : Fin D → ℝ => z ⬝ᵥ (P *ᵥ z)) := by
    simp only [Matrix.mulVec, dotProduct]
    fun_prop
  have hself : Measurable (fun z : Fin k → ℝ => z ⬝ᵥ z) := measurable_dot_self k
  have he := congrArg (fun μ : Measure ℝ => μ.real bad)
    (iidVectorLaw_projector_quadratic P hP hrank 1)
  dsimp only at he
  rw [map_measureReal_apply hquad hbad, squaredGaussianLaw,
    map_measureReal_apply hself hbad] at he
  have hp := GradientHessian.GaussianSquare.chi_square_two_sided hk
    (by norm_num : (0 : ℝ) < 1 / 384) (by norm_num : (1 / 384 : ℝ) < 1)
  have hevent : {z : Fin k → ℝ | (1 / 384 : ℝ) <
      |GradientHessian.GaussianSquare.energy z / k - 1|} =
      (fun z : Fin k → ℝ => z ⬝ᵥ z) ⁻¹' bad := by
    ext z
    simp [bad, GradientHessian.GaussianSquare.energy, dotProduct, pow_two]
  rw [hevent] at hp
  change (iidVectorLaw k 1).real ((fun z => z ⬝ᵥ z) ⁻¹' bad) ≤ _ at hp
  change (iidVectorLaw D 1).real ((fun z => z ⬝ᵥ (P *ᵥ z)) ⁻¹' bad) ≤ _
  rw [he]
  convert hp using 1
  congr 2
  ring

/-- Fixed-projector concentration for the normalized Gaussian direction.
The exponential constant is explicit and valid for all `0 < k ≤ D`. -/
theorem normalized_projector_tail {D k : ℕ} (hk : 0 < k) (hkD : k ≤ D)
    (P : Matrix (Fin D) (Fin D) ℝ) (hP : IsOrthogonalProjector P) (hrank : P.rank = k) :
    (iidVectorLaw D 1).real
      {z | (k : ℝ) / D / 48 < |(z ⬝ᵥ (P *ᵥ z)) / (z ⬝ᵥ z) - (k : ℝ) / D|} ≤
        4 * Real.exp (-(k : ℝ) / 1179648) := by
  have hD : 0 < D := lt_of_lt_of_le hk hkD
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hDR : (0 : ℝ) < D := by exact_mod_cast hD
  let badN : Set (Fin D → ℝ) := {z | (1 / 384 : ℝ) < |(z ⬝ᵥ (P *ᵥ z)) / k - 1|}
  let badD : Set (Fin D → ℝ) := {z | (1 / 384 : ℝ) < |(z ⬝ᵥ z) / D - 1|}
  have hsub : {z : Fin D → ℝ | (k : ℝ) / D / 48 <
      |(z ⬝ᵥ (P *ᵥ z)) / (z ⬝ᵥ z) - (k : ℝ) / D|} ⊆ badN ∪ badD := by
    intro z hz
    by_contra h
    have hn : |(z ⬝ᵥ (P *ᵥ z)) / k - 1| ≤ 1 / 384 :=
      le_of_not_gt (fun hN => h (Or.inl hN))
    have hd : |(z ⬝ᵥ z) / D - 1| ≤ 1 / 384 :=
      le_of_not_gt (fun hD => h (Or.inr hD))
    exact (not_le_of_gt hz) (ratio_control hkR hDR hn hd)
  have hn := projector_quadratic_tail hk P hP hrank
  have hd := GradientHessian.GaussianSquare.chi_square_two_sided hD
    (by norm_num : (0 : ℝ) < 1 / 384) (by norm_num : (1 / 384 : ℝ) < 1)
  have hd' : (iidVectorLaw D 1).real badD ≤ 2 * Real.exp (-(D : ℝ) / 1179648) := by
    convert hd using 1
    · congr 2
      ext z
      simp [badD, GradientHessian.GaussianSquare.energy, dotProduct, pow_two]
    · congr 2
      ring
  have hexp : Real.exp (-(D : ℝ) / 1179648) ≤ Real.exp (-(k : ℝ) / 1179648) := by
    apply Real.exp_le_exp.mpr
    have h : (k : ℝ) ≤ D := by exact_mod_cast hkD
    linarith
  calc
    _ ≤ (iidVectorLaw D 1).real (badN ∪ badD) := measureReal_mono hsub
    _ ≤ (iidVectorLaw D 1).real badN + (iidVectorLaw D 1).real badD := measureReal_union_le _ _
    _ ≤ _ := by linarith

/-- Remove the arbitrary-basis interface from the previously proved lower
spectral edge: every rank-`r` orthogonal projector has an actual complement basis. -/
theorem manuscript_projected_gram_lower_tail {J r κ k D : ℕ}
    (hJ : 4 ≤ J) (hr : 1 + 4096 * J ^ 2 ≤ r) (hκ : 16 ≤ κ)
    (hk : k = κ * r) (hD : D = k * J)
    (P : Matrix (Fin D) (Fin D) ℝ) (hP : IsOrthogonalProjector P) (hrank : P.rank = r) :
    (gaussianMatrixLaw D (D - k))
      {X | ¬LoewnerLE ((1 / (64 * (J : ℝ) ^ 2)) • 1)
        (Xᵀ * (1 - P) * X)} ≤ ENNReal.ofReal (1 / 1000) := by
  have hdim := projector_rank_complement hP
  rw [hrank] at hdim
  obtain ⟨V, hV, hVV⟩ := projector_basis_factorization hP.complement
    (show (1 - P).rank = D - r by omega)
  have hp := GradientHessian.MatrixGoodEvent.manuscript_deleted_gram_lower_tail
    hJ hr hκ hk hD V hV
  rwa [hVV] at hp

def direction {D : ℕ} (z : Fin D → ℝ) : Fin D → ℝ :=
  (Real.sqrt (z ⬝ᵥ z))⁻¹ • z

theorem direction_measurable (D : ℕ) : Measurable (@direction D) :=
  (measurable_dot_self D).sqrt.inv.smul measurable_id

theorem direction_unit {D : ℕ} {z : Fin D → ℝ} (hz : z ≠ 0) :
    direction z ⬝ᵥ direction z = 1 := by
  have hn : 0 ≤ z ⬝ᵥ z := Finset.sum_nonneg fun i _ => mul_self_nonneg (z i)
  have hne : z ⬝ᵥ z ≠ 0 := fun h => hz (dotProduct_self_eq_zero.mp h)
  simp only [direction, smul_dotProduct, dotProduct_smul, smul_eq_mul,
    ← mul_assoc, ← pow_two, inv_pow, Real.sq_sqrt hn]
  exact inv_mul_cancel₀ hne

theorem direction_quadratic {D : ℕ} (P : Matrix (Fin D) (Fin D) ℝ) (z : Fin D → ℝ) :
    direction z ⬝ᵥ (P *ᵥ direction z) = (z ⬝ᵥ (P *ᵥ z)) / (z ⬝ᵥ z) := by
  have hn : 0 ≤ z ⬝ᵥ z := Finset.sum_nonneg fun i _ => mul_self_nonneg (z i)
  simp only [direction, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul,
    smul_eq_mul, ← mul_assoc, ← pow_two, inv_pow, Real.sq_sqrt hn]
  ring

theorem gaussian_nonzero_ae {D : ℕ} (hD : 0 < D) :
    ∀ᵐ z ∂iidVectorLaw D 1, z ≠ 0 := by
  cases D with
  | zero => omega
  | succ d =>
    have hp := rowGauge_pivot_positive_ae (EuclideanSpace.basisFun (Fin (d + 1)) ℝ)
      (by norm_num : (1 : NNReal) ≠ 0)
    filter_upwards [hp] with z hz
    intro he
    simp [he] at hz

theorem exists_orthogonal_map {D : ℕ} (u v : Fin D → ℝ)
    (hu : u ⬝ᵥ u = 1) (hv : v ⬝ᵥ v = 1) :
    ∃ O : Matrix (Fin D) (Fin D) ℝ, Oᵀ * O = 1 ∧ O *ᵥ u = v := by
  let b := EuclideanSpace.basisFun (Fin D) ℝ
  let U : EuclideanSpace ℝ (Fin D) := (WithLp.equiv 2 (Fin D → ℝ)).symm u
  let V : EuclideanSpace ℝ (Fin D) := (WithLp.equiv 2 (Fin D → ℝ)).symm v
  have hU : ‖U‖ = 1 := by
    have h := euclidean_dot_self U
    change u ⬝ᵥ u = ‖U‖ ^ 2 at h
    rw [hu] at h
    nlinarith [norm_nonneg U]
  have hV : ‖V‖ = 1 := by
    have h := euclidean_dot_self V
    change v ⬝ᵥ v = ‖V‖ ^ 2 at h
    rw [hv] at h
    nlinarith [norm_nonneg V]
  let e := householder (U - V)
  refine ⟨gaugeMatrix b e, gaugeMatrix_transpose_mul_self b e, ?_⟩
  rw [gaugeMatrix_mulVec, coordinateRotation_apply]
  change ⇑(e U) = v
  rw [show e U = V from householder_equal_norm (hU.trans hV.symm)]
  rfl

theorem kernel_quadratic_rotation {D n : ℕ} (X : Matrix (Fin D) (Fin n) ℝ)
    (O : Matrix (Fin D) (Fin D) ℝ) (hO : Oᵀ * O = 1) (u : Fin D → ℝ) :
    (O *ᵥ u) ⬝ᵥ (leftKernelProjector (O * X) *ᵥ (O *ᵥ u)) =
      u ⬝ᵥ (leftKernelProjector X *ᵥ u) := by
  rw [quadratic_coordinates, leftKernelProjector_orthogonal_conjugate X O hO]
  have he : Oᵀ * (O * leftKernelProjector X * Oᵀ) * O = leftKernelProjector X := by
    calc
      _ = (Oᵀ * O) * leftKernelProjector X * (Oᵀ * O) := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hO]; simp
  rw [he]

theorem measurable_kernel_quadratic {D n : ℕ} (u : Fin D → ℝ) :
    Measurable (fun X : Matrix (Fin D) (Fin n) ℝ => u ⬝ᵥ (leftKernelProjector X *ᵥ u)) := by
  have hK := measurable_leftKernelProjector (m := Fin D) (n := Fin n)
  simp only [dotProduct, Matrix.mulVec]
  apply Finset.measurable_sum
  intro i _
  apply Measurable.const_mul
  apply Finset.measurable_sum
  intro j _
  exact (((measurable_pi_apply j).comp ((measurable_pi_apply i).comp hK)).mul_const _)

theorem kernel_directional_law {D n : ℕ} (u w : Fin D → ℝ)
    (hu : u ⬝ᵥ u = 1) (hw : w ⬝ᵥ w = 1) (v : NNReal) :
    (iidMatrixLaw D n v).map (fun X => u ⬝ᵥ (leftKernelProjector X *ᵥ u)) =
      (iidMatrixLaw D n v).map (fun X => w ⬝ᵥ (leftKernelProjector X *ᵥ w)) := by
  obtain ⟨O, hO, huw⟩ := exists_orthogonal_map u w hu hw
  have hOt : O * Oᵀ = 1 := Matrix.mul_eq_one_comm.mp hO
  have hrot : (iidMatrixLaw D n v).map (fun X => O * X) = iidMatrixLaw D n v := by
    simpa only [Matrix.transpose_transpose] using
      iidMatrixLaw_left_compression Oᵀ (by simpa only [Matrix.transpose_transpose] using hOt) v
  have hm : Measurable (fun X : Matrix (Fin D) (Fin n) ℝ => O * X) := by
    apply measurable_pi_lambda
    intro i
    apply measurable_pi_lambda
    intro j
    simp only [Matrix.mul_apply]
    fun_prop
  nth_rw 2 [← hrot]
  rw [Measure.map_map (measurable_kernel_quadratic w) hm]
  congr 1
  funext X
  simpa only [Function.comp_def, ← huw] using (kernel_quadratic_rotation X O hO u).symm

/-- Rotational averaging and Fubini transfer the actual normalized-Gaussian
projection estimate to the actual random kernel, at every fixed unit vector. -/
theorem random_kernel_direction_tail {D n k : ℕ} (hsize : n + k = D) (hk : 0 < k)
    (u : Fin D → ℝ) (hu : u ⬝ᵥ u = 1) {v : NNReal} (hv : v ≠ 0) :
    (iidMatrixLaw D n v).real
      {X | (k : ℝ) / D / 48 < |u ⬝ᵥ (leftKernelProjector X *ᵥ u) - (k : ℝ) / D|} ≤
        4 * Real.exp (-(k : ℝ) / 1179648) := by
  let μ := iidMatrixLaw D n v
  let ν := iidVectorLaw D 1
  let η : ℝ := (k : ℝ) / D
  let a : ℝ := 4 * Real.exp (-(k : ℝ) / 1179648)
  let bad : Set ℝ := {t | η / 48 < |t - η|}
  let target : Set (Matrix (Fin D) (Fin n) ℝ) :=
    {X | η / 48 < |u ⬝ᵥ (leftKernelProjector X *ᵥ u) - η|}
  let joint : Set ((Fin D → ℝ) × Matrix (Fin D) (Fin n) ℝ) :=
    {p | η / 48 < |direction p.1 ⬝ᵥ (leftKernelProjector p.2 *ᵥ direction p.1) - η|}
  have hbad : MeasurableSet bad := by
    apply measurableSet_lt measurable_const
    fun_prop
  have hquad : Measurable (fun p : (Fin D → ℝ) × Matrix (Fin D) (Fin n) ℝ =>
      direction p.1 ⬝ᵥ (leftKernelProjector p.2 *ᵥ direction p.1)) := by
    have hd := (direction_measurable D).comp
      (measurable_fst : Measurable (Prod.fst : (Fin D → ℝ) × Matrix (Fin D) (Fin n) ℝ → _))
    have hK := (measurable_leftKernelProjector (m := Fin D) (n := Fin n)).comp
      (measurable_snd : Measurable (Prod.snd : (Fin D → ℝ) × Matrix (Fin D) (Fin n) ℝ → _))
    simp only [Matrix.mulVec, dotProduct]
    apply Finset.measurable_sum
    intro i _
    apply ((measurable_pi_apply i).comp hd).mul
    apply Finset.measurable_sum
    intro j _
    exact (((measurable_pi_apply j).comp ((measurable_pi_apply i).comp hK)).mul
      ((measurable_pi_apply j).comp hd))
  have hjoint : MeasurableSet joint := hquad hbad
  have hsections : ∀ᵐ z ∂ν, μ (Prod.mk z ⁻¹' joint) = μ target := by
    filter_upwards [gaussian_nonzero_ae (show 0 < D by omega)] with z hz
    have he := congrArg (fun ρ : Measure ℝ => ρ bad)
      (kernel_directional_law (n := n) u (direction z) hu (direction_unit hz) v)
    dsimp only at he
    rw [Measure.map_apply (measurable_kernel_quadratic u) hbad,
      Measure.map_apply (measurable_kernel_quadratic (direction z)) hbad] at he
    exact he.symm
  have havg : μ target = (ν.prod μ) joint := by
    rw [Measure.prod_apply hjoint]
    calc
      _ = ∫⁻ _z, μ target ∂ν := by simp
      _ = _ := lintegral_congr_ae (hsections.mono fun _ hz => hz.symm)
  have hbound : (ν.prod μ) joint ≤ ENNReal.ofReal a := by
    rw [Measure.prod_apply_symm hjoint]
    calc
      _ ≤ ∫⁻ _X, ENNReal.ofReal a ∂μ := by
        apply lintegral_mono_ae
        filter_upwards [iidMatrixLaw_mulVec_injective_ae D n (show n ≤ D by omega) hv] with X hX
        have hrank : (leftKernelProjector X).rank = k := by
          rw [leftKernelProjector_rank_full X hX (by omega)]
          omega
        have hp := normalized_projector_tail hk (show k ≤ D by omega)
          (leftKernelProjector X) (leftKernelProjector_isProjector X) hrank
        have he : (fun z : Fin D → ℝ => (z, X)) ⁻¹' joint =
            {z | η / 48 < |(z ⬝ᵥ (leftKernelProjector X *ᵥ z)) / (z ⬝ᵥ z) - η|} := by
          ext z
          simp only [joint, Set.mem_preimage, Set.mem_setOf_eq, direction_quadratic]
        rw [he]
        have hp' := ENNReal.ofReal_le_ofReal hp
        rwa [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)] at hp'
      _ = _ := by simp
  have hp := ENNReal.toReal_mono ENNReal.ofReal_ne_top (havg.trans_le hbound)
  simpa only [ENNReal.toReal_ofReal (show 0 ≤ a by positivity)] using hp

/-- For a real symmetric operator, controlling its quadratic form on the
unit sphere controls its operator norm, proved by polarization. -/
theorem opNorm_le_of_quadratic_bound {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (f : E →L[ℝ] E)
    (hf : ∀ x y, ⟪f x, y⟫_ℝ = ⟪x, f y⟫_ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hq : ∀ x, ‖x‖ = 1 → |⟪x, f x⟫_ℝ| ≤ C) : ‖f‖ ≤ C := by
  have hscale (x : E) : |⟪x, f x⟫_ℝ| ≤ C * ‖x‖ ^ 2 := by
    by_cases hx : x = 0
    · simp [hx]
    · let y := ‖x‖⁻¹ • x
      have hnorm : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
      have hy : ‖y‖ = 1 := by simp [y, norm_smul, hnorm]
      have hxy : x = ‖x‖ • y := by simp [y, smul_smul, hnorm]
      calc
        |⟪x, f x⟫_ℝ| = ‖x‖ ^ 2 * |⟪y, f y⟫_ℝ| := by
          rw [congrArg (fun t => ⟪t, f t⟫_ℝ) hxy]
          simp only [map_smul, real_inner_smul_left, inner_smul_right,
            abs_mul, abs_norm]
          ring
        _ ≤ ‖x‖ ^ 2 * C := mul_le_mul_of_nonneg_left (hq y hy) (sq_nonneg _)
        _ = _ := by ring
  apply ContinuousLinearMap.opNorm_le_of_unit_norm hC
  intro x hx
  have hlin : ‖innerSL ℝ (f x)‖ ≤ C := by
    apply ContinuousLinearMap.opNorm_le_of_unit_norm hC
    intro y hy
    change |⟪f x, y⟫_ℝ| ≤ C
    have hpol : 4 * ⟪f x, y⟫_ℝ = ⟪x + y, f (x + y)⟫_ℝ - ⟪x - y, f (x - y)⟫_ℝ := by
      simp only [map_add, map_sub, inner_add_left, inner_add_right, inner_sub_left, inner_sub_right]
      rw [← hf x y, real_inner_comm y (f x)]
      ring
    have habs := abs_sub ⟪x + y, f (x + y)⟫_ℝ ⟪x - y, f (x - y)⟫_ℝ
    rw [← hpol, abs_mul] at habs
    rw [abs_of_pos (by norm_num : (0 : ℝ) < 4)] at habs
    have hp := hscale (x + y)
    have hm := hscale (x - y)
    have hsum : ‖x + y‖ ^ 2 + ‖x - y‖ ^ 2 = 4 := by
      rw [norm_add_sq_real, norm_sub_sq_real, hx, hy]
      ring
    nlinarith [congrArg (fun t : ℝ => C * t) hsum]
  simpa only [innerSL_apply_norm] using hlin

/-- A quarter-net controls a symmetric quadratic form with the sharp factor
two required by the source compression event. -/
theorem opNorm_le_twice_quadratic_net {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (f : E →L[ℝ] E)
    (hf : ∀ x y, ⟪f x, y⟫_ℝ = ⟪x, f y⟫_ℝ) (S : Finset E)
    (hunit : ∀ y ∈ S, ‖y‖ = 1)
    (hnet : ∀ x : E, ‖x‖ = 1 → ∃ y ∈ S, ‖x - y‖ < (1 : ℝ) / 4)
    {B : ℝ} (hB : 0 ≤ B) (hval : ∀ y ∈ S, |⟪y, f y⟫_ℝ| ≤ B) :
    ‖f‖ ≤ 2 * B := by
  have hbound : ‖f‖ ≤ B + ‖f‖ / 2 := by
    apply opNorm_le_of_quadratic_bound f hf (by positivity)
    intro x hx
    obtain ⟨y, hy, hxy⟩ := hnet x hx
    have he : ⟪x, f x⟫_ℝ - ⟪y, f y⟫_ℝ =
        ⟪x - y, f x⟫_ℝ + ⟪y, f (x - y)⟫_ℝ := by
      simp only [map_sub, inner_sub_left, inner_sub_right]
      ring
    have hd : |⟪x, f x⟫_ℝ - ⟪y, f y⟫_ℝ| ≤ ‖f‖ / 2 := by
      rw [he]
      calc
        _ ≤ |⟪x - y, f x⟫_ℝ| + |⟪y, f (x - y)⟫_ℝ| := abs_add _ _
        _ ≤ ‖x - y‖ * ‖f x‖ + ‖y‖ * ‖f (x - y)‖ :=
          add_le_add (abs_real_inner_le_norm _ _) (abs_real_inner_le_norm _ _)
        _ ≤ ‖x - y‖ * (‖f‖ * ‖x‖) + ‖y‖ * (‖f‖ * ‖x - y‖) := by
          gcongr
          · exact f.le_opNorm _
          · exact f.le_opNorm _
        _ ≤ ‖f‖ / 2 := by rw [hx, hunit y hy]; nlinarith [norm_nonneg f]
    calc
      |⟪x, f x⟫_ℝ| = |(⟪x, f x⟫_ℝ - ⟪y, f y⟫_ℝ) + ⟪y, f y⟫_ℝ| := by rw [sub_add_cancel]
      _ ≤ |⟪x, f x⟫_ℝ - ⟪y, f y⟫_ℝ| + |⟪y, f y⟫_ℝ| := abs_add _ _
      _ ≤ B + ‖f‖ / 2 := by linarith [hval y hy]
  linarith

def compressedDeviation {D n r : ℕ} (B : Matrix (Fin D) (Fin r) ℝ) (η : ℝ)
    (X : Matrix (Fin D) (Fin n) ℝ) : Matrix (Fin r) (Fin r) ℝ :=
  Bᵀ * leftKernelProjector X * B - η • 1

theorem compressedDeviation_symmetric {D n r : ℕ} (B : Matrix (Fin D) (Fin r) ℝ)
    (η : ℝ) (X : Matrix (Fin D) (Fin n) ℝ) : (compressedDeviation B η X)ᵀ = compressedDeviation B η X := by
  simp only [compressedDeviation, Matrix.transpose_sub, Matrix.transpose_mul,
    Matrix.transpose_transpose, Matrix.transpose_smul, Matrix.transpose_one,
    (leftKernelProjector_isProjector X).symmetric, Matrix.mul_assoc]

theorem compressedDeviation_quadratic {D n r : ℕ} (B : Matrix (Fin D) (Fin r) ℝ)
    (η : ℝ) (X : Matrix (Fin D) (Fin n) ℝ) (u : EuclideanSpace ℝ (Fin r)) (hu : ‖u‖ = 1) :
    ⟪u, matrixEuclideanMap (compressedDeviation B η X) u⟫_ℝ =
      (B *ᵥ ⇑u) ⬝ᵥ (leftKernelProjector X *ᵥ (B *ᵥ ⇑u)) - η := by
  rw [matrixEuclideanMap_inner]
  simp only [compressedDeviation, Matrix.sub_mulVec, Matrix.smul_mulVec_assoc,
    Matrix.one_mulVec, dotProduct_sub, dotProduct_smul, smul_eq_mul]
  rw [← quadratic_coordinates, euclidean_dot_self, hu, one_pow, mul_one]

/-- Uniform concentration on an arbitrary deterministic `r`-dimensional
compression, obtained from the fixed-direction theorem and a quarter-net. -/
theorem compressed_kernel_operator_tail {D n k r : ℕ} (hsize : n + k = D) (hk : 0 < k)
    (B : Matrix (Fin D) (Fin r) ℝ) (hB : Bᵀ * B = 1) {v : NNReal} (hv : v ≠ 0) :
    (iidMatrixLaw D n v).real
      {X | (k : ℝ) / D / 24 < ‖matrixEuclideanMap (compressedDeviation B ((k : ℝ) / D) X)‖} ≤
        4 * (9 : ℝ) ^ r * Real.exp (-(k : ℝ) / 1179648) := by
  classical
  let η : ℝ := (k : ℝ) / D
  have hη : 0 ≤ η := by dsimp [η]; positivity
  obtain ⟨S, hcard, hunit, hnet⟩ :=
    GradientHessian.MatrixGoodUpper.exists_quarter_sphere_net (EuclideanSpace ℝ (Fin r))
  have hcardR : (S.card : ℝ) ≤ (9 : ℝ) ^ r := by
    exact_mod_cast (show S.card ≤ 9 ^ r by simpa using hcard)
  let bad := fun u : EuclideanSpace ℝ (Fin r) =>
    {X : Matrix (Fin D) (Fin n) ℝ |
      η / 48 < |(B *ᵥ ⇑u) ⬝ᵥ (leftKernelProjector X *ᵥ (B *ᵥ ⇑u)) - η|}
  have hsub : {X : Matrix (Fin D) (Fin n) ℝ |
      η / 24 < ‖matrixEuclideanMap (compressedDeviation B η X)‖} ⊆ ⋃ u ∈ S, bad u := by
    intro X hX
    by_contra hmem
    have hval : ∀ u ∈ S, |⟪u, matrixEuclideanMap (compressedDeviation B η X) u⟫_ℝ| ≤ η / 48 := by
      intro u hu
      rw [compressedDeviation_quadratic B η X u (hunit u hu)]
      exact le_of_not_gt (fun hb => hmem (Set.mem_iUnion.mpr ⟨u, Set.mem_iUnion.mpr ⟨hu, hb⟩⟩))
    have hs : (compressedDeviation B η X).IsHermitian := by
      simpa only [Matrix.IsHermitian, conjTranspose_eq_transpose_of_trivial]
        using compressedDeviation_symmetric B η X
    have hf := Matrix.isHermitian_iff_isSymmetric.mp hs
    have hp := opNorm_le_twice_quadratic_net (matrixEuclideanMap (compressedDeviation B η X))
      hf S hunit hnet (by positivity : 0 ≤ η / 48) hval
    change η / 24 < ‖matrixEuclideanMap (compressedDeviation B η X)‖ at hX
    linarith
  have htail : ∀ u ∈ S, (iidMatrixLaw D n v).real (bad u) ≤
      4 * Real.exp (-(k : ℝ) / 1179648) := by
    intro u hu
    apply random_kernel_direction_tail hsize hk _ _ hv
    rw [orthogonal_columns_dot B hB, euclidean_dot_self, hunit u hu, one_pow]
  calc
    _ ≤ (iidMatrixLaw D n v).real (⋃ u ∈ S, bad u) := measureReal_mono hsub
    _ ≤ ∑ u ∈ S, (iidMatrixLaw D n v).real (bad u) := measureReal_biUnion_finset_le _ _
    _ ≤ ∑ _u ∈ S, 4 * Real.exp (-(k : ℝ) / 1179648) := Finset.sum_le_sum htail
    _ = (S.card : ℝ) * (4 * Real.exp (-(k : ℝ) / 1179648)) := by simp
    _ ≤ _ := by nlinarith [Real.exp_pos (-(k : ℝ) / 1179648)]

theorem compressed_tail_numeric {r k : ℕ} (hr : 0 < r) (hk : 18874368 * r ≤ k) :
    4 * (9 : ℝ) ^ r * Real.exp (-(k : ℝ) / 1179648) ≤ 1 / 1000 := by
  have hkr : (18874368 : ℝ) * r ≤ k := by exact_mod_cast hk
  have hexp : Real.exp (-(k : ℝ) / 1179648) ≤ Real.exp ((r : ℝ) * (-16)) := by
    apply Real.exp_le_exp.mpr
    linarith
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp 1]
  have he16 : (65536 : ℝ) ≤ Real.exp 16 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) htwo 16
    rw [← Real.exp_nat_mul] at h
    norm_num at h
    exact h
  have hbase : 9 * Real.exp (-16 : ℝ) ≤ 1 / 4000 := by
    rw [Real.exp_neg, ← div_eq_mul_inv]
    apply (div_le_iff₀ (Real.exp_pos _)).mpr
    linarith
  calc
    _ ≤ 4 * (9 : ℝ) ^ r * Real.exp ((r : ℝ) * (-16)) :=
      mul_le_mul_of_nonneg_left hexp (by positivity)
    _ = 4 * (9 * Real.exp (-16 : ℝ)) ^ r := by rw [Real.exp_nat_mul, mul_pow]; ring
    _ ≤ 4 * (1 / 4000 : ℝ) ^ r := by gcongr
    _ ≤ 4 * (1 / 4000 : ℝ) := mul_le_mul_of_nonneg_left
      (pow_le_of_le_one (by norm_num) (by norm_num) hr.ne') (by norm_num)
    _ = _ := by norm_num

theorem orthonormal_matrix_norm_le_one {D r : ℕ} (B : Matrix (Fin D) (Fin r) ℝ)
    (hB : Bᵀ * B = 1) : ‖matrixEuclideanMap B‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro x
  have he := orthogonal_columns_dot B hB ⇑x
  have hl := euclidean_dot_self (matrixEuclideanMap B x)
  rw [matrixEuclideanMap_apply] at hl
  rw [hl, euclidean_dot_self] at he
  nlinarith [norm_nonneg (matrixEuclideanMap B x), norm_nonneg x]

theorem matrixEuclideanMap_mul {a b c : ℕ} (A : Matrix (Fin a) (Fin b) ℝ)
    (B : Matrix (Fin b) (Fin c) ℝ) :
    matrixEuclideanMap (A * B) = (matrixEuclideanMap A).comp (matrixEuclideanMap B) := by
  ext x i
  change ((A * B) *ᵥ ⇑x) i = (A *ᵥ (B *ᵥ ⇑x)) i
  rw [Matrix.mulVec_mulVec]

theorem compression_lift_norm_le {D r : ℕ} (B : Matrix (Fin D) (Fin r) ℝ)
    (hB : Bᵀ * B = 1) (C : Matrix (Fin r) (Fin r) ℝ) :
    ‖matrixEuclideanMap (B * C * Bᵀ)‖ ≤ ‖matrixEuclideanMap C‖ := by
  have hb := orthonormal_matrix_norm_le_one B hB
  have hbt : ‖matrixEuclideanMap Bᵀ‖ ≤ 1 := by
    rwa [GradientHessian.MatrixGoodUpper.matrixEuclideanMap_transpose_norm]
  rw [matrixEuclideanMap_mul, matrixEuclideanMap_mul]
  calc
    _ ≤ ‖(matrixEuclideanMap B).comp (matrixEuclideanMap C)‖ * ‖matrixEuclideanMap Bᵀ‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ (‖matrixEuclideanMap B‖ * ‖matrixEuclideanMap C‖) * ‖matrixEuclideanMap Bᵀ‖ := by
      gcongr
      exact ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ (1 * ‖matrixEuclideanMap C‖) * 1 := by gcongr
    _ = _ := by ring

/-- The uniform compressed random-kernel estimate in the original ambient
coordinates, with no assumption about the random event being bounded. -/
theorem random_kernel_compression_tail {D n k r : ℕ} (hsize : n + k = D) (hk : 0 < k)
    (P : Matrix (Fin D) (Fin D) ℝ) (hP : IsOrthogonalProjector P) (hrank : P.rank = r)
    {v : NNReal} (hv : v ≠ 0) :
    (iidMatrixLaw D n v).real
      {X | (k : ℝ) / D / 24 <
        ‖matrixEuclideanMap (P * leftKernelProjector X * P - ((k : ℝ) / D) • P)‖} ≤
      4 * (9 : ℝ) ^ r * Real.exp (-(k : ℝ) / 1179648) := by
  obtain ⟨B, hB, hBB⟩ := projector_basis_factorization hP hrank
  apply le_trans _ (compressed_kernel_operator_tail hsize hk B hB hv)
  refine measureReal_mono ?_ (measure_ne_top _ _)
  intro X hX
  change (k : ℝ) / D / 24 < ‖matrixEuclideanMap (compressedDeviation B ((k : ℝ) / D) X)‖
  have he : P * leftKernelProjector X * P - ((k : ℝ) / D) • P =
      B * compressedDeviation B ((k : ℝ) / D) X * Bᵀ := by
    rw [← hBB]
    simp only [compressedDeviation, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul,
      Matrix.smul_mul, Matrix.mul_one, Matrix.mul_assoc]
  exact lt_of_lt_of_le (show (k : ℝ) / D / 24 < _ from hX)
    (he ▸ compression_lift_norm_le B hB (compressedDeviation B ((k : ℝ) / D) X))

theorem manuscript_kernel_compression_tail {J r κ k D : ℕ}
    (hJ : 4 ≤ J) (hr : 1 + 4096 * J ^ 2 ≤ r) (hκ : 18874368 ≤ κ)
    (hk : k = κ * r) (hD : D = k * J)
    (P : Matrix (Fin D) (Fin D) ℝ) (hP : IsOrthogonalProjector P) (hrank : P.rank = r) :
    (gaussianMatrixLaw D (D - k)).real
      {X | (1 / (J : ℝ)) / 24 <
        ‖matrixEuclideanMap (P * leftKernelProjector X * P - (1 / (J : ℝ)) • P)‖} ≤
      1 / 1000 := by
  have hr0 : 0 < r := by omega
  have hk0 : 0 < k := by rw [hk]; positivity
  have hD0 : 0 < D := by rw [hD]; positivity
  have hkD : k ≤ D := by rw [hD]; nlinarith
  have hkr : 18874368 * r ≤ k := by rw [hk]; exact Nat.mul_le_mul_right r hκ
  have hv : (D : NNReal)⁻¹ ≠ 0 := inv_ne_zero (by exact_mod_cast hD0.ne')
  have hp := (random_kernel_compression_tail (n := D-k) (by omega) hk0 P hP hrank hv).trans
    (compressed_tail_numeric hr0 hkr)
  have hη : (k : ℝ) / D = 1 / (J : ℝ) := by
    rw [hD, Nat.cast_mul]
    have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk0.ne'
    field_simp
  rwa [hη] at hp

/-- The three tests in the manuscript source event, with the actual Euclidean
operator norm and the actual Gaussian left-kernel projector.  On full-column-
rank inputs this projector is exactly the projector onto `ker (X Xᵀ)`. -/
def sourceGoodEvent {D n : ℕ} (P : Matrix (Fin D) (Fin D) ℝ) (J : ℕ) :
    Set (Matrix (Fin D) (Fin n) ℝ) :=
  {X | ‖matrixEuclideanMap (wishart X)‖ ≤ 16 ∧
    LoewnerLE ((1 / (64 * (J : ℝ) ^ 2)) • 1) (Xᵀ * (1 - P) * X) ∧
    ‖matrixEuclideanMap (P * leftKernelProjector X * P - (1 / (J : ℝ)) • P)‖ ≤
      (1 / (J : ℝ)) / 24}

theorem measurableSet_sourceGoodEvent {D n : ℕ} (P : Matrix (Fin D) (Fin D) ℝ) (J : ℕ) :
    MeasurableSet (sourceGoodEvent (n := n) P J) := by
  have hu := ((continuous_matrixEuclideanMap D D).measurable.comp (measurable_wishart D n)).norm
  have hg : Measurable (fun X : Matrix (Fin D) (Fin n) ℝ =>
      Xᵀ * (1 - P) * X - (1 / (64 * (J : ℝ) ^ 2)) • 1) := by
    apply Continuous.measurable
    fun_prop
  have hc : Continuous (fun K : Matrix (Fin D) (Fin D) ℝ =>
      P * K * P - (1 / (J : ℝ)) • P) := by fun_prop
  have hk := ((continuous_matrixEuclideanMap D D).comp hc).measurable.comp
    (measurable_leftKernelProjector (m := Fin D) (n := Fin n))
  exact (measurableSet_le hu measurable_const).inter
    (((GradientHessian.MatrixGoodEvent.isClosed_positiveSemidefinite n).measurableSet.preimage hg).inter
      (measurableSet_le hk.norm measurable_const))

/-- The source event has probability at least `.997` for an explicit absolute
choice of the manuscript's sufficiently large parameter.  Every constituent
probability estimate is proved from the actual Gaussian law. -/
theorem sourceGoodEvent_probability {J r κ k D : ℕ}
    (hJ : 4 ≤ J) (hr : 1 + 4096 * J ^ 2 ≤ r) (hκ : 18874368 ≤ κ)
    (hk : k = κ * r) (hD : D = k * J)
    (P : Matrix (Fin D) (Fin D) ℝ) (hP : IsOrthogonalProjector P) (hrank : P.rank = r) :
    997 / 1000 ≤ (gaussianMatrixLaw D (D - k)).real (sourceGoodEvent P J) := by
  let μ := gaussianMatrixLaw D (D - k)
  let upper : Set (Matrix (Fin D) (Fin (D-k)) ℝ) := {X | 16 < ‖matrixEuclideanMap (wishart X)‖}
  let lower : Set (Matrix (Fin D) (Fin (D-k)) ℝ) :=
    {X | ¬LoewnerLE ((1 / (64 * (J : ℝ) ^ 2)) • 1) (Xᵀ * (1-P) * X)}
  let compression : Set (Matrix (Fin D) (Fin (D-k)) ℝ) :=
    {X | (1 / (J : ℝ)) / 24 <
      ‖matrixEuclideanMap (P * leftKernelProjector X * P - (1 / (J : ℝ)) • P)‖}
  have hr0 : 0 < r := by omega
  have hkr : 32 * r ≤ k := by rw [hk]; exact Nat.mul_le_mul_right r (by omega)
  have hD32 : 32 ≤ D := by rw [hD]; nlinarith
  have hu : μ.real upper ≤ 1 / 1000 :=
    GradientHessian.MatrixGoodUpper.wishart_operator_norm_tail hD32 (Nat.sub_le _ _)
  have hl : μ.real lower ≤ 1 / 1000 := by
    have hp := ENNReal.toReal_mono ENNReal.ofReal_ne_top
      (manuscript_projected_gram_lower_tail hJ hr (by omega) hk hD P hP hrank)
    norm_num only [ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 1 / 1000)] at hp
    exact hp
  have hc : μ.real compression ≤ 1 / 1000 :=
    manuscript_kernel_compression_tail hJ hr hκ hk hD P hP hrank
  have he : (sourceGoodEvent (n := D-k) P J)ᶜ = upper ∪ (lower ∪ compression) := by
    ext X
    simp only [sourceGoodEvent, upper, lower, compression, Set.mem_compl_iff,
      Set.mem_setOf_eq, Set.mem_union, not_and_or, not_le]
  have hbad : μ.real (sourceGoodEvent (n := D-k) P J)ᶜ ≤ 3 / 1000 := by
    rw [he]
    have hp := measureReal_union_le (μ := μ) upper (lower ∪ compression)
    have hq := measureReal_union_le (μ := μ) lower compression
    linarith
  have hsum := measureReal_add_measureReal_compl (μ := μ) (measurableSet_sourceGoodEvent (n := D-k) P J)
  rw [measureReal_univ_eq_one] at hsum
  change 997 / 1000 ≤ μ.real (sourceGoodEvent P J)
  linarith

/-- The literal `.99` probability assertion from source `lem:good`. -/
theorem manuscript_sourceGoodEvent_probability {J r κ k D : ℕ}
    (hJ : 4 ≤ J) (hr : 1 + 4096 * J ^ 2 ≤ r) (hκ : 18874368 ≤ κ)
    (hk : k = κ * r) (hD : D = k * J)
    (P : Matrix (Fin D) (Fin D) ℝ) (hP : IsOrthogonalProjector P) (hrank : P.rank = r) :
    99 / 100 ≤ (gaussianMatrixLaw D (D - k)).real (sourceGoodEvent P J) := by
  have hp := sourceGoodEvent_probability hJ hr hκ hk hD P hP hrank
  linarith

end
end GradientHessian.MatrixKernelConcentration
