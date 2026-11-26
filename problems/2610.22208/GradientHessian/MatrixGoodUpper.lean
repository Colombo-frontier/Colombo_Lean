import GradientHessian.GaussianSquare
import LowRank.GaussianMatrixCompression
import LowRank.MatrixNetBound
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# The upper edge of the manuscript's Gaussian source event

The net construction adapts `LowRank.HalfSphereNet` to radius `1/4`.
An exact Gaussian-square exponential moment then proves the literal upper
edge `W ≤ 16 I`.  No extreme-singular-value concentration is assumed.
-/

namespace GradientHessian.MatrixGoodUpper

open Matrix MeasureTheory ProbabilityTheory LowRank Module Metric Set
open scoped Matrix InnerProductSpace ENNReal Topology
noncomputable section

theorem quarter_separated_card_le {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (s : Finset E) (hs : ∀ x ∈ s, ‖x‖ ≤ 1)
    (hsep : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → (1 : ℝ) / 4 ≤ ‖x - y‖) :
    s.card ≤ 9 ^ finrank ℝ E := by
  borelize E
  let μ : Measure E := Measure.addHaar
  let δ : ℝ := 1 / 8
  let ρ : ℝ := 9 / 8
  have hρ : 0 < ρ := by norm_num
  set A := ⋃ c ∈ s, ball (c : E) δ with hA
  have hd : Set.Pairwise (s : Set E) (fun c d => Disjoint (ball (c : E) δ) (ball d δ)) := by
    intro c hc d hd hcd
    apply ball_disjoint_ball
    rw [dist_eq_norm]
    convert hsep c hc d hd hcd using 1
    norm_num [δ]
  have hsub : A ⊆ ball (0 : E) ρ := by
    refine iUnion₂_subset fun x hx => ?_
    apply ball_subset_ball'
    calc
      δ + dist x 0 ≤ δ + 1 := by rw [dist_zero_right]; exact add_le_add le_rfl (hs x hx)
      _ = ρ := by norm_num [δ, ρ]
  have hi : (s.card : ℝ≥0∞) * ENNReal.ofReal (δ ^ finrank ℝ E) * μ (ball 0 1) ≤
      ENNReal.ofReal (ρ ^ finrank ℝ E) * μ (ball 0 1) := by
    calc
      _ = μ A := by
        rw [hA, measure_biUnion_finset hd fun c _ => measurableSet_ball]
        have hδ : 0 < δ := by norm_num
        simp only [div_pow, μ.addHaar_ball_of_pos _ hδ]
        simp only [one_div, one_pow, Finset.sum_const, nsmul_eq_mul, mul_assoc]
      _ ≤ μ (ball (0 : E) ρ) := measure_mono hsub
      _ = _ := by simp only [μ.addHaar_ball_of_pos _ hρ]
  have hj : (s.card : ℝ≥0∞) * ENNReal.ofReal (δ ^ finrank ℝ E) ≤
      ENNReal.ofReal (ρ ^ finrank ℝ E) :=
    (ENNReal.mul_le_mul_right (measure_ball_pos _ _ zero_lt_one).ne' measure_ball_lt_top.ne).1 hi
  have hc : (s.card : ℝ) ≤ (9 : ℝ) ^ finrank ℝ E := by
    have := ENNReal.toReal_le_of_le_ofReal (pow_nonneg hρ.le _) hj
    simpa [ρ, δ, div_eq_mul_inv, mul_pow] using this
  exact_mod_cast hc

theorem exists_quarter_sphere_net (E : Type*) [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] :
    ∃ s : Finset E, s.card ≤ 9 ^ finrank ℝ E ∧ (∀ x ∈ s, ‖x‖ = 1) ∧
      ∀ x : E, ‖x‖ = 1 → ∃ y ∈ s, ‖x - y‖ < (1 : ℝ) / 4 := by
  classical
  let good := fun s : Finset E => (∀ x ∈ s, ‖x‖ = 1) ∧
    (∀ x ∈ s, ∀ y ∈ s, x ≠ y → (1 : ℝ) / 4 ≤ ‖x - y‖)
  let sizes : Set ℕ := {n | ∃ s : Finset E, good s ∧ s.card = n}
  have hnonempty : sizes.Nonempty := ⟨0, ∅, by simp [good], by simp⟩
  have hbound : BddAbove sizes := by
    refine ⟨9 ^ finrank ℝ E, ?_⟩
    rintro n ⟨s, hs, rfl⟩
    exact quarter_separated_card_le s (fun x hx => (hs.1 x hx).le) hs.2
  obtain ⟨s, hs, hcard⟩ := Nat.sSup_mem hnonempty hbound
  refine ⟨s, quarter_separated_card_le s (fun x hx => (hs.1 x hx).le) hs.2, hs.1, ?_⟩
  intro x hx
  by_contra! hfar
  have hxs : x ∉ s := by
    intro h
    have := hfar x h
    norm_num at this
  have hins : good (insert x s) := by
    constructor
    · intro y hy
      rcases Finset.mem_insert.mp hy with rfl | hy
      · exact hx
      · exact hs.1 y hy
    · intro y hy z hz hyz
      rcases Finset.mem_insert.mp hy with rfl | hy'
      · rcases Finset.mem_insert.mp hz with rfl | hz'
        · exact (hyz rfl).elim
        · exact hfar z hz'
      · rcases Finset.mem_insert.mp hz with rfl | hz'
        · simpa only [norm_sub_rev] using hfar y hy'
        · exact hs.2 y hy' z hz' hyz
  have hle := le_csSup hbound (show (insert x s).card ∈ sizes from ⟨_, hins, rfl⟩)
  rw [Finset.card_insert_of_not_mem hxs, ← hcard] at hle
  omega

theorem opNorm_le_four_of_quarter_net {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E →L[ℝ] F) (s : Finset E)
    (hnet : ∀ x : E, ‖x‖ = 1 → ∃ y ∈ s, ‖x - y‖ < (1 : ℝ) / 4)
    (hval : ∀ y ∈ s, ‖f y‖ ≤ 3) : ‖f‖ ≤ 4 := by
  have haux : ‖f‖ ≤ 3 + ‖f‖ / 4 := by
    apply ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity)
    intro x hx
    obtain ⟨y, hy, hxy⟩ := hnet x hx
    calc
      ‖f x‖ = ‖f y + f (x - y)‖ := by rw [← map_add, add_sub_cancel]
      _ ≤ ‖f y‖ + ‖f (x - y)‖ := norm_add_le _ _
      _ ≤ 3 + ‖f‖ * ‖x - y‖ := add_le_add (hval y hy) (f.le_opNorm _)
      _ ≤ 3 + ‖f‖ / 4 := by nlinarith [norm_nonneg f]
  linarith

theorem iidVectorLaw_fin_one_eval (v : NNReal) :
    (iidVectorLaw 1 v).map (fun x => x 0) = gaussianReal 0 v := by
  ext s hs
  rw [Measure.map_apply (measurable_pi_apply 0) hs]
  have he : (fun x : Fin 1 → ℝ => x 0) ⁻¹' s = Set.univ.pi (fun _ : Fin 1 => s) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, forall_true_left]
    exact ⟨fun h i => by simpa only [Fin.eq_zero i] using h, fun h => h 0⟩
  rw [he, iidVectorLaw, Measure.pi_pi]
  simp

theorem iidVectorLaw_unit_dot (n : ℕ) (v : NNReal) (u : Fin n → ℝ)
    (hu : u ⬝ᵥ u = 1) :
    (iidVectorLaw n v).map (fun x => x ⬝ᵥ u) = gaussianReal 0 v := by
  let B : Matrix (Fin n) (Fin 1) ℝ := fun i _ => u i
  have hB : Bᵀ * B = 1 := by
    ext i j
    fin_cases i
    fin_cases j
    simpa only [Matrix.mul_apply, Matrix.transpose_apply, B, Matrix.one_apply_eq, dotProduct]
      using hu
  have hm : Measurable (fun x : Fin n → ℝ => Bᵀ *ᵥ x) := by
    apply measurable_pi_lambda
    intro i
    simp only [Matrix.mulVec, dotProduct]
    fun_prop
  have hp := congrArg (fun μ : Measure (Fin 1 → ℝ) => μ.map (fun x => x 0))
    (iidVectorLaw_orthogonal_compression B hB v)
  dsimp only at hp
  rw [Measure.map_map (measurable_pi_apply 0) hm, iidVectorLaw_fin_one_eval] at hp
  simpa only [Function.comp_def, Matrix.mulVec, Matrix.transpose_apply, B,
    dotProduct_comm] using hp

theorem iidMatrixLaw_unit_mulVec (m n : ℕ) (v : NNReal) (u : Fin n → ℝ)
    (hu : u ⬝ᵥ u = 1) :
    (iidMatrixLaw m n v).map (fun X => X *ᵥ u) = iidVectorLaw m v := by
  have hm : Measurable (fun x : Fin n → ℝ => x ⬝ᵥ u) := by
    simp only [dotProduct]
    fun_prop
  exact (measurePreserving_pi (fun _ : Fin m => iidVectorLaw n v)
    (fun _ => gaussianReal 0 v)
    (fun _ => (show MeasurePreserving (fun x => x ⬝ᵥ u) (iidVectorLaw n v)
      (gaussianReal 0 v) from ⟨hm, iidVectorLaw_unit_dot n v u hu⟩))).map_eq

theorem standard_energy_nine_tail (D : ℕ) :
    (GradientHessian.GaussianSquare.gaussianVector D).real
      {z | 9 * (D : ℝ) ≤ GradientHessian.GaussianSquare.energy z} ≤
        (2 * Real.exp (-(27 / 8 : ℝ))) ^ D := by
  let μ := GradientHessian.GaussianSquare.gaussianVector D
  let e := @GradientHessian.GaussianSquare.energy D
  have hi : (∫ z, Real.exp ((3 / 8 : ℝ) * e z) ∂μ) = (2 : ℝ) ^ D := by
    rw [GradientHessian.GaussianSquare.energy_exponential_integral D (by norm_num)]
    norm_num
  have hm := mul_meas_ge_le_integral_of_nonneg
    (μ := μ) (f := fun z => Real.exp ((3 / 8 : ℝ) * e z))
    (ae_of_all _ fun _ => (Real.exp_pos _).le)
    (GradientHessian.GaussianSquare.energy_exponential_integrable D (by norm_num))
    (Real.exp ((27 / 8 : ℝ) * D))
  have he : {z : Fin D → ℝ | Real.exp ((27 / 8 : ℝ) * D) ≤
      Real.exp ((3 / 8 : ℝ) * e z)} = {z | 9 * (D : ℝ) ≤ e z} := by
    ext z
    simp only [Set.mem_setOf_eq, Real.exp_le_exp]
    constructor <;> intro h <;> linarith
  rw [he, hi] at hm
  have hb : μ.real {z | 9 * (D : ℝ) ≤ e z} ≤
      (2 : ℝ) ^ D / Real.exp ((27 / 8 : ℝ) * D) :=
    (le_div_iff₀ (Real.exp_pos _)).2 (by simpa only [mul_comm] using hm)
  calc
    _ ≤ _ := hb
    _ = _ := by
      rw [Real.exp_neg, mul_pow, inv_pow, ← div_eq_mul_inv, ← Real.exp_nat_mul]
      congr 2
      ring

theorem normalized_energy_nine_tail {D : ℕ} (hD : 0 < D) :
    (iidVectorLaw D (D : NNReal)⁻¹).real {z | 9 ≤ z ⬝ᵥ z} ≤
      (2 * Real.exp (-(27 / 8 : ℝ))) ^ D := by
  have hDR : (0 : ℝ) < D := by exact_mod_cast hD
  have hm : Measurable (fun z : Fin D → ℝ => Real.sqrt (((D : NNReal)⁻¹ : NNReal) : ℝ) • z) :=
    measurable_const.smul measurable_id
  have hs : MeasurableSet {z : Fin D → ℝ | 9 ≤ z ⬝ᵥ z} := by
    apply measurableSet_le measurable_const
    simp only [dotProduct]
    fun_prop
  have he (z : Fin D → ℝ) :
      (Real.sqrt (((D : NNReal)⁻¹ : NNReal) : ℝ) • z) ⬝ᵥ
        (Real.sqrt (((D : NNReal)⁻¹ : NNReal) : ℝ) • z) =
        GradientHessian.GaussianSquare.energy z / D := by
    rw [smul_dotProduct, dotProduct_smul]
    simp only [smul_eq_mul, ← mul_assoc, ← pow_two]
    rw [Real.sq_sqrt (NNReal.coe_nonneg _)]
    simp only [NNReal.coe_inv, NNReal.coe_natCast, div_eq_mul_inv,
      GradientHessian.GaussianSquare.energy, dotProduct, pow_two]
    ring
  have hset : (fun z : Fin D → ℝ => Real.sqrt (((D : NNReal)⁻¹ : NNReal) : ℝ) • z) ⁻¹'
      {z | 9 ≤ z ⬝ᵥ z} = {z | 9 * (D : ℝ) ≤ GradientHessian.GaussianSquare.energy z} := by
    ext z
    simp only [Set.mem_preimage, Set.mem_setOf_eq, he, le_div_iff₀ hDR]
  rw [measureReal_def, iidVectorLaw_as_scaled, Measure.map_apply hm hs, hset]
  exact standard_energy_nine_tail D

theorem matrix_unit_vector_tail {D n : ℕ} (hD : 0 < D)
    (u : EuclideanSpace ℝ (Fin n)) (hu : ‖u‖ = 1) :
    (iidMatrixLaw D n (D : NNReal)⁻¹).real {X | 3 ≤ ‖matrixEuclideanMap X u‖} ≤
      (2 * Real.exp (-(27 / 8 : ℝ))) ^ D := by
  have hunit : ⇑u ⬝ᵥ ⇑u = 1 := by rw [euclidean_dot_self, hu, one_pow]
  have hp := normalized_energy_nine_tail hD
  have hm : Measurable (fun X : Matrix (Fin D) (Fin n) ℝ => X *ᵥ ⇑u) := by
    apply measurable_pi_lambda
    intro i
    simp only [Matrix.mulVec, dotProduct]
    fun_prop
  have hs : MeasurableSet {z : Fin D → ℝ | 9 ≤ z ⬝ᵥ z} := by
    apply measurableSet_le measurable_const
    simp only [dotProduct]
    fun_prop
  rw [← iidMatrixLaw_unit_mulVec D n (D : NNReal)⁻¹ ⇑u hunit,
    measureReal_def, Measure.map_apply hm hs] at hp
  apply le_trans (measureReal_mono ?_) hp
  intro X hX
  change 3 ≤ ‖matrixEuclideanMap X u‖ at hX
  change 9 ≤ (X *ᵥ ⇑u) ⬝ᵥ (X *ᵥ ⇑u)
  have he := euclidean_dot_self (matrixEuclideanMap X u)
  rw [matrixEuclideanMap_apply] at he
  rw [he]
  nlinarith

/-- A single quarter-net suffices, because the full norm of each Gaussian
matrix-vector product is controlled by its chi-square exponential moment. -/
theorem matrix_operator_tail {D n : ℕ} (hD : 0 < D) (hn : n ≤ D) :
    (iidMatrixLaw D n (D : NNReal)⁻¹).real {X | 4 < ‖matrixEuclideanMap X‖} ≤
      (18 * Real.exp (-(27 / 8 : ℝ))) ^ D := by
  classical
  obtain ⟨S, hcard, hunit, hnet⟩ := exists_quarter_sphere_net (EuclideanSpace ℝ (Fin n))
  have hcardR : (S.card : ℝ) ≤ (9 : ℝ) ^ D := by
    have hc : S.card ≤ 9 ^ n := by simpa using hcard
    exact_mod_cast hc.trans (Nat.pow_le_pow_right (by norm_num : 0 < 9) hn)
  let bad := fun u : EuclideanSpace ℝ (Fin n) =>
    {X : Matrix (Fin D) (Fin n) ℝ | 3 ≤ ‖matrixEuclideanMap X u‖}
  have hsub : {X : Matrix (Fin D) (Fin n) ℝ | 4 < ‖matrixEuclideanMap X‖} ⊆
      ⋃ u ∈ S, bad u := by
    intro X hX
    by_contra hmem
    have hval : ∀ u ∈ S, ‖matrixEuclideanMap X u‖ ≤ 3 := by
      intro u hu
      apply le_of_not_ge
      intro hlarge
      exact hmem (Set.mem_iUnion.mpr ⟨u, Set.mem_iUnion.mpr ⟨hu, hlarge⟩⟩)
    exact (not_le_of_gt hX) (opNorm_le_four_of_quarter_net (matrixEuclideanMap X) S hnet hval)
  have htail : ∀ u ∈ S, (iidMatrixLaw D n (D : NNReal)⁻¹).real (bad u) ≤
      (2 * Real.exp (-(27 / 8 : ℝ))) ^ D :=
    fun u hu => matrix_unit_vector_tail hD u (hunit u hu)
  calc
    _ ≤ (iidMatrixLaw D n (D : NNReal)⁻¹).real (⋃ u ∈ S, bad u) := measureReal_mono hsub
    _ ≤ ∑ u ∈ S, (iidMatrixLaw D n (D : NNReal)⁻¹).real (bad u) :=
      measureReal_biUnion_finset_le _ _
    _ ≤ ∑ _u ∈ S, (2 * Real.exp (-(27 / 8 : ℝ))) ^ D := Finset.sum_le_sum htail
    _ = (S.card : ℝ) * (2 * Real.exp (-(27 / 8 : ℝ))) ^ D := by simp
    _ ≤ (9 : ℝ) ^ D * (2 * Real.exp (-(27 / 8 : ℝ))) ^ D :=
      mul_le_mul_of_nonneg_right hcardR (by positivity)
    _ = _ := by rw [← mul_pow]; congr 1; ring

theorem upper_tail_numeric {D : ℕ} (hD : 32 ≤ D) :
    (18 * Real.exp (-(27 / 8 : ℝ))) ^ D ≤ 1 / 1000 := by
  have he : (27 : ℝ) ≤ Real.exp (27 / 8) := by
    have hp := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 27 / 8) 8
    norm_num [Finset.sum_range_succ, Nat.factorial] at hp
    linarith
  have hb : 18 * Real.exp (-(27 / 8 : ℝ)) ≤ 2 / 3 := by
    rw [Real.exp_neg, ← div_eq_mul_inv]
    apply (div_le_iff₀ (Real.exp_pos _)).mpr
    linarith
  calc
    _ ≤ (2 / 3 : ℝ) ^ D := pow_le_pow_left₀ (by positivity) hb D
    _ ≤ (2 / 3 : ℝ) ^ 32 := pow_le_pow_of_le_one (by norm_num) (by norm_num) hD
    _ ≤ 1 / 1000 := by norm_num

theorem matrixEuclideanMap_transpose {D n : ℕ} (X : Matrix (Fin D) (Fin n) ℝ) :
    matrixEuclideanMap Xᵀ = ContinuousLinearMap.adjoint (matrixEuclideanMap X) := by
  unfold matrixEuclideanMap
  rw [← LinearMap.adjoint_toContinuousLinearMap]
  congr 1
  simpa only [conjTranspose_eq_transpose_of_trivial] using
    Matrix.toEuclideanLin_conjTranspose_eq_adjoint X

theorem matrixEuclideanMap_transpose_norm {D n : ℕ} (X : Matrix (Fin D) (Fin n) ℝ) :
    ‖matrixEuclideanMap Xᵀ‖ = ‖matrixEuclideanMap X‖ := by
  rw [matrixEuclideanMap_transpose]
  exact ContinuousLinearMap.adjoint.norm_map _

theorem wishart_norm_le_sqr {D n : ℕ} (X : Matrix (Fin D) (Fin n) ℝ) :
    ‖matrixEuclideanMap (wishart X)‖ ≤ ‖matrixEuclideanMap X‖ ^ 2 := by
  have he : matrixEuclideanMap (wishart X) =
      (matrixEuclideanMap X).comp (matrixEuclideanMap Xᵀ) := by
    ext v i
    change ((X * Xᵀ) *ᵥ ⇑v) i = (X *ᵥ (Xᵀ *ᵥ ⇑v)) i
    rw [Matrix.mulVec_mulVec]
  rw [he]
  calc
    _ ≤ ‖matrixEuclideanMap X‖ * ‖matrixEuclideanMap Xᵀ‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ = _ := by rw [matrixEuclideanMap_transpose_norm]; ring

/-- The literal `‖W‖ ≤ 16` event in the Euclidean operator norm. -/
theorem wishart_operator_norm_tail {D n : ℕ} (hD : 32 ≤ D) (hn : n ≤ D) :
    (gaussianMatrixLaw D n).real {X | 16 < ‖matrixEuclideanMap (wishart X)‖} ≤
      1 / 1000 := by
  apply le_trans _ ((matrix_operator_tail (by omega : 0 < D) hn).trans (upper_tail_numeric hD))
  refine measureReal_mono ?_ (measure_ne_top _ _)
  intro X hX
  change 4 < ‖matrixEuclideanMap X‖
  apply lt_of_not_ge
  intro hsmall
  have hn0 := norm_nonneg (matrixEuclideanMap X)
  have hb := wishart_norm_le_sqr X
  change 16 < ‖matrixEuclideanMap (wishart X)‖ at hX
  nlinarith

/-- Equivalent spectral upper bound, in a form convenient for the construction. -/
theorem wishart_loewner_upper_tail {D n : ℕ} (hD : 32 ≤ D) (hn : n ≤ D) :
    (gaussianMatrixLaw D n).real {X | ¬LoewnerLE (wishart X) ((16 : ℝ) • 1)} ≤
      1 / 1000 := by
  apply le_trans _ ((matrix_operator_tail (by omega : 0 < D) hn).trans (upper_tail_numeric hD))
  refine measureReal_mono ?_ (measure_ne_top _ _)
  intro X hX
  change 4 < ‖matrixEuclideanMap X‖
  apply lt_of_not_ge
  intro hsmall
  apply hX
  have ht : ‖matrixEuclideanMap Xᵀ‖ ≤ 4 := by rwa [matrixEuclideanMap_transpose_norm]
  convert wishart_le_of_transpose_opNorm X (by norm_num : (0 : ℝ) ≤ 4) ht using 1
  norm_num

end
end GradientHessian.MatrixGoodUpper
