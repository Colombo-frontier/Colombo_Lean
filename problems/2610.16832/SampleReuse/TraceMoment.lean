import SampleReuse.Model
import Mathlib.LinearAlgebra.Trace
import Mathlib.Analysis.InnerProductSpace.Spectrum

/-! Trace bounds for genuine Euclidean operator norms, used as deterministic
ingredients of a matrix moment argument. -/

open scoped BigOperators InnerProductSpace

namespace SampleReuse
noncomputable section
open Classical

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

def opTrace (H : E →L[ℝ] E) : ℝ := LinearMap.trace ℝ E H.toLinearMap

omit [FiniteDimensional ℝ E] in
theorem opTrace_eq_sum_inner {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ E) (H : E →L[ℝ] E) :
    opTrace H = ∑ i, ⟪b i, H (b i)⟫_ℝ := by
  rw [opTrace, LinearMap.trace_eq_matrix_trace ℝ b.toBasis]
  simp only [Matrix.trace, Matrix.diag, LinearMap.toMatrix_apply,
    OrthonormalBasis.coe_toBasis, OrthonormalBasis.coe_toBasis_repr_apply,
    OrthonormalBasis.repr_apply_apply, ContinuousLinearMap.coe_coe]

theorem abs_opTrace_le (H : E →L[ℝ] E) :
    |opTrace H| ≤ (Module.finrank ℝ E : ℝ) * ‖H‖ := by
  let b := stdOrthonormalBasis ℝ E
  rw [opTrace_eq_sum_inner b H]
  calc
    _ ≤ ∑ i, |⟪b i, H (b i)⟫_ℝ| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin (Module.finrank ℝ E), ‖H‖ := by
      apply Finset.sum_le_sum
      intro i _
      have hn : ‖b i‖ = 1 := b.orthonormal.norm_eq_one i
      have hc := norm_inner_le_norm (𝕜 := ℝ) (b i) (H (b i))
      have ho := H.le_opNorm (b i)
      simpa [hn, Real.norm_eq_abs] using hc.trans (by simpa [hn] using ho)
    _ = _ := by simp

/-- The same trace as a continuous linear map, permitting its passage through
Bochner integrals and finite sums without an additional assumption. -/
def opTraceL : (E →L[ℝ] E) →L[ℝ] ℝ :=
  LinearMap.mkContinuous
    { toFun := opTrace
      map_add' := by intros; simp [opTrace]
      map_smul' := by intros; simp [opTrace] }
    (Module.finrank ℝ E : ℝ)
    (fun H => by simpa only [Real.norm_eq_abs] using abs_opTrace_le H)

@[simp] theorem opTraceL_apply (H : E →L[ℝ] E) : opTraceL H = opTrace H := rfl

theorem abs_opTrace_list_prod_le (l : List (E →L[ℝ] E)) :
    |opTrace l.prod| ≤ (Module.finrank ℝ E : ℝ) * (l.map norm).prod := by
  by_cases hE : Nontrivial E
  · letI := hE
    exact (abs_opTrace_le l.prod).trans
      (mul_le_mul_of_nonneg_left (List.norm_prod_le l) (Nat.cast_nonneg _))
  · haveI : Subsingleton E := not_nontrivial_iff_subsingleton.mp hE
    have hz : l.prod = (0 : E →L[ℝ] E) := Subsingleton.elim _ _
    have hd : Module.finrank ℝ E = 0 := Module.finrank_zero_iff.mpr inferInstance
    simp [hz, opTrace, hd]

theorem eigenvector_pow_apply (H : E →L[ℝ] E)
    (hH : H.toLinearMap.IsSymmetric) (p : ℕ)
    (i : Fin (Module.finrank ℝ E)) :
    (H^p) (hH.eigenvectorBasis rfl i) =
      (hH.eigenvalues rfl i)^p • hH.eigenvectorBasis rfl i := by
  induction p with
  | zero => simp
  | succ p ih =>
    rw [pow_succ', ContinuousLinearMap.mul_apply, ih, map_smul]
    have he := hH.apply_eigenvectorBasis rfl i
    change H (hH.eigenvectorBasis rfl i) =
      hH.eigenvalues rfl i • hH.eigenvectorBasis rfl i at he
    rw [he, smul_smul, pow_succ]

theorem opTrace_pow_eq_sum (H : E →L[ℝ] E)
    (hH : H.toLinearMap.IsSymmetric) (p : ℕ) :
    opTrace (H^p) = ∑ i, (hH.eigenvalues rfl i)^p := by
  rw [opTrace_eq_sum_inner (hH.eigenvectorBasis rfl)]
  apply Finset.sum_congr rfl
  intro i _
  rw [eigenvector_pow_apply H hH]
  simp [real_inner_smul_right, real_inner_self_eq_norm_sq,
    (hH.eigenvectorBasis rfl).orthonormal.norm_eq_one i]

theorem opTrace_even_pow_nonneg (H : E →L[ℝ] E)
    (hH : H.toLinearMap.IsSymmetric) (k : ℕ) : 0 ≤ opTrace (H^(2*k)) := by
  rw [opTrace_pow_eq_sum H hH]
  apply Finset.sum_nonneg
  intro i _
  rw [pow_mul]
  exact pow_nonneg (sq_nonneg _) _

theorem opNorm_le_of_eigenvalues_le (H : E →L[ℝ] E)
    (hH : H.toLinearMap.IsSymmetric) (B : ℝ) (hB : 0 ≤ B)
    (hb : ∀ i : Fin (Module.finrank ℝ E), |hH.eigenvalues rfl i| ≤ B) :
    ‖H‖ ≤ B := by
  let b := hH.eigenvectorBasis rfl
  have he (x : E) (i : Fin (Module.finrank ℝ E)) :
      ⟪b i, H x⟫_ℝ = hH.eigenvalues rfl i * ⟪b i, x⟫_ℝ := by
    rw [← hH.apply_clm (b i) x]
    have hei := hH.apply_eigenvectorBasis rfl i
    change H (b i) = hH.eigenvalues rfl i • b i at hei
    rw [hei, real_inner_smul_left]
  apply H.opNorm_le_bound hB
  intro x
  have hs : ‖H x‖^2 ≤ B^2 * ‖x‖^2 := by
    calc
      _ = ∑ i, ‖⟪b i, H x⟫_ℝ‖^2 := (b.sum_sq_norm_inner (H x)).symm
      _ = ∑ i, (hH.eigenvalues rfl i)^2 * ‖⟪b i, x⟫_ℝ‖^2 := by
        apply Finset.sum_congr rfl
        intro i _
        rw [he x i, norm_mul, mul_pow, Real.norm_eq_abs, sq_abs]
      _ ≤ ∑ i, B^2 * ‖⟪b i, x⟫_ℝ‖^2 := by
        apply Finset.sum_le_sum
        intro i _
        have hi := pow_le_pow_left₀ (abs_nonneg _) (hb i) 2
        rw [sq_abs] at hi
        exact mul_le_mul_of_nonneg_right hi (sq_nonneg _)
      _ = _ := by rw [← Finset.mul_sum, b.sum_sq_norm_inner]
  nlinarith [norm_nonneg (H x), mul_nonneg hB (norm_nonneg x)]

/-- The operator norm, with no Frobenius or entrywise norm substitution. -/
theorem opNorm_even_pow_le_trace (H : E →L[ℝ] E)
    (hH : H.toLinearMap.IsSymmetric) {k : ℕ} (hk : 0 < k) :
    ‖H‖^(2*k) ≤ opTrace (H^(2*k)) := by
  by_cases hd : Module.finrank ℝ E = 0
  · haveI : Subsingleton E := Module.finrank_zero_iff.mp hd
    have hzero : H = 0 := Subsingleton.elim _ _
    rw [hzero]
    simp [opTrace, Nat.ne_of_gt (by omega : 0 < 2*k)]
  · have hn : 0 < Module.finrank ℝ E := Nat.pos_of_ne_zero hd
    obtain ⟨i, _, hi⟩ := Finset.exists_max_image
      (Finset.univ : Finset (Fin (Module.finrank ℝ E)))
      (fun j => |hH.eigenvalues rfl j|)
      ⟨⟨0, hn⟩, Finset.mem_univ _⟩
    have hnorm : ‖H‖ ≤ |hH.eigenvalues rfl i| :=
      opNorm_le_of_eigenvalues_le H hH _ (abs_nonneg _) (fun j => hi j (Finset.mem_univ _))
    rw [opTrace_pow_eq_sum H hH]
    calc
      _ ≤ |hH.eigenvalues rfl i|^(2*k) :=
        pow_le_pow_left₀ (norm_nonneg H) hnorm _
      _ = (hH.eigenvalues rfl i)^(2*k) := by rw [pow_mul, pow_mul, sq_abs]
      _ ≤ ∑ j, (hH.eigenvalues rfl j)^(2*k) := by
        apply Finset.single_le_sum _ (Finset.mem_univ i)
        intro j _
        rw [pow_mul]
        exact pow_nonneg (sq_nonneg _) _

end
end SampleReuse
