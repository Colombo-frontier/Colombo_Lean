import UpperProgram

/-! Orthogonal vector-estimator bounds derived from the actual scalar clipping. -/

open MeasureTheory
open scoped BigOperators

namespace Task006.Full

noncomputable def orthogonalReconstruct {d : ℕ} (Q : Task006.HaarRebalancing.OrthogonalGroup d)
    (v : Fin d → ℝ) : Space d := ∑ i, v i • Task006.HaarRebalancing.column Q i

theorem orthogonalReconstruct_sub {d : ℕ} (Q : Task006.HaarRebalancing.OrthogonalGroup d)
    (v w : Fin d → ℝ) :
    orthogonalReconstruct Q v - orthogonalReconstruct Q w = orthogonalReconstruct Q (fun i => v i - w i) := by
  unfold orthogonalReconstruct
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [sub_smul]

theorem orthogonalReconstruct_norm_sq {d : ℕ} (Q : Task006.HaarRebalancing.OrthogonalGroup d)
    (v : Fin d → ℝ) : ‖orthogonalReconstruct Q v‖ ^ 2 = ∑ i, v i ^ 2 := by
  have hi := (Task006.HaarRebalancing.orthonormal_column Q).inner_sum v v Finset.univ
  rw [real_inner_self_eq_norm_sq] at hi
  simpa only [orthogonalReconstruct, RCLike.conj_to_real, pow_two] using hi

theorem orthogonalReconstruct_norm_le {d : ℕ} (Q : Task006.HaarRebalancing.OrthogonalGroup d)
    (v : Fin d → ℝ) {K : ℝ} (hK : 0 ≤ K) (hv : ∀ i, |v i| ≤ K) :
    ‖orthogonalReconstruct Q v‖ ≤ Real.sqrt d * K := by
  have hs : ∑ i, v i ^ 2 ≤ (d : ℝ) * K ^ 2 := by
    calc
      (∑ i, v i ^ 2) ≤ ∑ _i : Fin d, K ^ 2 := by
        apply Finset.sum_le_sum
        intro i _
        have hsq := (sq_le_sq₀ (abs_nonneg (v i)) hK).mpr (hv i)
        simpa only [sq_abs] using hsq
      _ = _ := by simp
  have hn := orthogonalReconstruct_norm_sq Q v
  have hroot := Real.sq_sqrt (Nat.cast_nonneg d : (0 : ℝ) ≤ d)
  have hnonneg := mul_nonneg (Real.sqrt_nonneg (d : ℝ)) hK
  nlinarith [norm_nonneg (orthogonalReconstruct Q v)]

theorem orthogonalReconstruct_coordinates {d : ℕ} (hd : 0 < d)
    (Q : Task006.HaarRebalancing.OrthogonalGroup d) (v : Space d) :
    orthogonalReconstruct Q (fun i => inner ℝ (Task006.HaarRebalancing.column Q i) v) = v := by
  letI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  let B := basisOfOrthonormalOfCardEqFinrank
    (Task006.HaarRebalancing.orthonormal_column Q) (by simp [Space])
  have hB : (B : Fin d → Space d) = Task006.HaarRebalancing.column Q := by
    simp only [B, coe_basisOfOrthonormalOfCardEqFinrank]
  let O := B.toOrthonormalBasis (by rw [hB]; exact Task006.HaarRebalancing.orthonormal_column Q)
  have hO : (O : Fin d → Space d) = Task006.HaarRebalancing.column Q := by
    simp only [O, Module.Basis.coe_toOrthonormalBasis, hB]
  simpa only [orthogonalReconstruct, hO] using O.sum_repr' v

theorem orthogonalReconstruct_error {d : ℕ} (hd : 0 < d)
    (Q : Task006.HaarRebalancing.OrthogonalGroup d) (c : Fin d → ℝ) (v : Space d)
    {a : ℝ} (ha : 0 ≤ a) (herror : ∀ i, |c i - inner ℝ (Task006.HaarRebalancing.column Q i) v| ≤ a) :
    ‖orthogonalReconstruct Q c - v‖ ≤ Real.sqrt d * a := by
  nth_rw 1 [← orthogonalReconstruct_coordinates hd Q v]
  rw [orthogonalReconstruct_sub]
  exact orthogonalReconstruct_norm_le Q _ ha herror

noncomputable def clippedVector {d : ℕ} {Ω : Type*}
    (Q : Task006.HaarRebalancing.OrthogonalGroup d) (b : ℝ) (D : Fin d → Ω → ℝ) (ω : Ω) : Space d :=
  orthogonalReconstruct Q (fun i => scalarClip b (D i ω))

/-- Exact good-basis estimator bounds. Only actual scalar moment budgets and
orthonormality are used; coordinate independence is not assumed or needed. -/
theorem clippedVector_moments {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (Q : Task006.HaarRebalancing.OrthogonalGroup d) {b M : ℝ} (hb : 0 < b) (hM : 0 ≤ M)
    (D : Fin d → Ω → ℝ) (hD : ∀ i, Measurable (D i))
    (hDi : ∀ i, Integrable (D i) μ)
    (hmi : ∀ i, Integrable (fun ω => |D i ω| ^ (3 / 2 : ℝ)) μ)
    (hm : ∀ i, (∫ ω, |D i ω| ^ (3 / 2 : ℝ) ∂μ) ≤ M) :
    Integrable (clippedVector Q b D) μ ∧
      Integrable (fun ω => ‖clippedVector Q b D ω‖ ^ 2) μ ∧
      ‖(∫ ω, clippedVector Q b D ω ∂μ) - orthogonalReconstruct Q (fun i => ∫ ω, D i ω ∂μ)‖ ≤
        Real.sqrt d * M * b ^ (-1 / 2 : ℝ) ∧
      (∫ ω, ‖clippedVector Q b D ω‖ ^ 2 ∂μ) ≤ d * M * b ^ (1 / 2 : ℝ) := by
  let Y : Fin d → Ω → ℝ := fun i ω => scalarClip b (D i ω)
  have hYi : ∀ i, Integrable (Y i) μ := by
    intro i
    apply Integrable.of_bound
      (((scalarClip_continuous hb.le).measurable.comp (hD i)).aestronglyMeasurable) b
    filter_upwards [] with ω
    simpa only [Y, Function.comp_def, Real.norm_eq_abs, abs_scalarClip hb.le] using min_le_right |D i ω| b
  have hYsq : ∀ i, Integrable (fun ω => (Y i ω) ^ 2) μ :=
    fun i => (scalarClip_integrable hb (hD i) (hmi i)).2
  have hYbounds := fun i => scalarClip_integral_bounds hb (hD i) (hmi i) (hm i)
  have hmeanBias : ∀ i, |(∫ ω, Y i ω ∂μ) - (∫ ω, D i ω ∂μ)| ≤ M * b ^ (-1 / 2 : ℝ) := by
    intro i
    calc
      _ = |∫ ω, D i ω - Y i ω ∂μ| := by
        rw [integral_sub (hDi i) (hYi i), abs_sub_comm]
      _ ≤ ∫ ω, |D i ω - Y i ω| ∂μ := abs_integral_le_integral_abs
      _ ≤ _ := (hYbounds i).1
  have hgv : Integrable (clippedVector Q b D) μ := by
    exact integrable_finsetSum Finset.univ
      (fun i _ => (hYi i).smul_const (Task006.HaarRebalancing.column Q i))
  have hsqeq : (fun ω => ‖clippedVector Q b D ω‖ ^ 2) = fun ω => ∑ i, (Y i ω) ^ 2 := by
    funext ω
    exact orthogonalReconstruct_norm_sq Q (fun i => Y i ω)
  have hgsq : Integrable (fun ω => ‖clippedVector Q b D ω‖ ^ 2) μ := by
    rw [hsqeq]
    exact integrable_finsetSum Finset.univ (fun i _ => hYsq i)
  have hmean : (∫ ω, clippedVector Q b D ω ∂μ) =
      orthogonalReconstruct Q (fun i => ∫ ω, Y i ω ∂μ) := by
    unfold clippedVector orthogonalReconstruct
    rw [integral_finsetSum Finset.univ
      (fun i _ => (hYi i).smul_const (Task006.HaarRebalancing.column Q i))]
    simp only [integral_smul_const]
  refine ⟨hgv, hgsq, ?_, ?_⟩
  · rw [hmean, orthogonalReconstruct_sub]
    have hk : 0 ≤ M * b ^ (-1 / 2 : ℝ) := mul_nonneg hM (Real.rpow_nonneg hb.le _)
    simpa only [mul_assoc] using orthogonalReconstruct_norm_le Q
      (fun i => (∫ ω, Y i ω ∂μ) - (∫ ω, D i ω ∂μ)) hk hmeanBias
  · rw [hsqeq, integral_finsetSum Finset.univ (fun i _ => hYsq i)]
    calc
      (∑ i, ∫ ω, Y i ω ^ 2 ∂μ) ≤ ∑ _i : Fin d, M * b ^ (1 / 2 : ℝ) :=
        Finset.sum_le_sum (fun i _ => (hYbounds i).2)
      _ = _ := by simp [mul_assoc]

#print axioms clippedVector_moments
#print axioms orthogonalReconstruct_coordinates

end Task006.Full
