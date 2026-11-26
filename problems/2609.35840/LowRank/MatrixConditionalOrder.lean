import LowRank.GaussianKernelConditional

/-! Entrywise matrix conditional expectation preserves positive semidefinite
and Loewner order. Positivity is checked simultaneously on a countable dense
set of test vectors and extended to all vectors by continuity. -/

namespace LowRank
open Matrix MeasureTheory
open scoped Matrix BigOperators
noncomputable section

variable {Ω : Type*} (m : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω] (μ : Measure Ω)

theorem condExp_finite_weighted_sum {ι : Type*} [Fintype ι]
    (f : ι → Ω → ℝ) (hf : ∀ i, Integrable (f i) μ) (c : ι → ℝ) :
    μ[fun ω => ∑ i, c i * f i ω | m] =ᵐ[μ]
      (fun ω => ∑ i, c i * μ[f i | m] ω) := by
  have hs := condExp_finset_sum (s := Finset.univ) (f := fun i ω => c i * f i ω)
    (fun i _ => (hf i).const_mul (c i)) m
  have he : ∀ i, ∀ᵐ ω ∂μ, μ[fun z => c i * f i z | m] ω = c i * μ[f i | m] ω := by
    intro i
    simpa only [Pi.smul_apply, smul_eq_mul] using condExp_smul (μ := μ) (c i) (f i) m
  have hall := (ae_all_iff).mpr he
  simp only [Finset.sum_fn] at hs
  filter_upwards [hs, hall] with ω hsum hterm
  rw [hsum]
  exact Finset.sum_congr rfl (fun i _ => hterm i)

variable {n : Type*} [Fintype n] [DecidableEq n]

theorem matrixCondMean_quadratic (A : Ω → Matrix n n ℝ) (hA : EntryIntegrable A μ) (v : n → ℝ) :
    μ[fun ω => v ⬝ᵥ (A ω *ᵥ v) | m] =ᵐ[μ]
      (fun ω => v ⬝ᵥ (matrixCondMean μ m A ω *ᵥ v)) := by
  have he : ∀ M : Matrix n n ℝ, v ⬝ᵥ (M *ᵥ v) =
      ∑ ij : n × n, (v ij.1 * v ij.2) * M ij.1 ij.2 := by
    intro M
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  simpa only [he, matrixCondMean] using condExp_finite_weighted_sum m μ
    (fun ij : n × n => fun ω => A ω ij.1 ij.2) (fun ij => hA ij.1 ij.2)
    (fun ij => v ij.1 * v ij.2)

theorem matrixCondMean_trace (A : Ω → Matrix n n ℝ) (hA : EntryIntegrable A μ) :
    μ[fun ω => (A ω).trace | m] =ᵐ[μ] (fun ω => (matrixCondMean μ m A ω).trace) := by
  simpa only [one_mul, Matrix.trace, Matrix.diag, matrixCondMean] using
    condExp_finite_weighted_sum m μ (fun i ω => A ω i i) (fun i => hA i i) (fun _ => 1)

theorem matrixCondMean_symmetric (A : Ω → Matrix n n ℝ)
    (hA : ∀ᵐ ω ∂μ, (A ω)ᵀ = A ω) : ∀ᵐ ω ∂μ, (matrixCondMean μ m A ω)ᵀ = matrixCondMean μ m A ω := by
  have he : ∀ i j, ∀ᵐ ω ∂μ, matrixCondMean μ m A ω j i = matrixCondMean μ m A ω i j := by
    intro i j
    apply condExp_congr_ae
    filter_upwards [hA] with ω hω
    exact congrFun (congrFun hω i) j
  have hall := (ae_all_iff).mpr (fun i => (ae_all_iff).mpr (he i))
  filter_upwards [hall] with ω hω
  ext i j
  exact hω i j

theorem matrixCondMean_posSemidef (A : Ω → Matrix n n ℝ) (hA : EntryIntegrable A μ)
    (hpos : ∀ᵐ ω ∂μ, (A ω).PosSemidef) : ∀ᵐ ω ∂μ, (matrixCondMean μ m A ω).PosSemidef := by
  have hsym : ∀ᵐ ω ∂μ, (A ω)ᵀ = A ω := by
    filter_upwards [hpos] with ω hω
    simpa only [conjTranspose_eq_transpose_of_trivial] using hω.isHermitian.eq
  have hquad : ∀ v : n → ℝ, ∀ᵐ ω ∂μ, 0 ≤ v ⬝ᵥ (matrixCondMean μ m A ω *ᵥ v) := by
    intro v
    have hp : 0 ≤ᵐ[μ] (fun ω => v ⬝ᵥ (A ω *ᵥ v)) := by
      filter_upwards [hpos] with ω hω
      simpa only [star_trivial] using hω.2 v
    filter_upwards [condExp_nonneg (m := m) hp, matrixCondMean_quadratic m μ A hA v] with ω hp he
    rw [← he]
    exact hp
  obtain ⟨V, hVc, hVd⟩ := TopologicalSpace.exists_countable_dense (n → ℝ)
  letI : Countable V := hVc.to_subtype
  have hall : ∀ᵐ ω ∂μ, ∀ v : V, 0 ≤ (v : n → ℝ) ⬝ᵥ (matrixCondMean μ m A ω *ᵥ (v : n → ℝ)) :=
    (ae_all_iff).mpr (fun v => hquad v)
  filter_upwards [matrixCondMean_symmetric m μ A hsym, hall] with ω hs hp
  constructor
  · simpa only [Matrix.IsHermitian, conjTranspose_eq_transpose_of_trivial] using hs
  · intro v
    simp only [star_trivial]
    have hc : Continuous (fun z : n → ℝ => z ⬝ᵥ (matrixCondMean μ m A ω *ᵥ z)) := by
      simp only [dotProduct, Matrix.mulVec]
      fun_prop
    exact hVd.induction (fun z hz => hp ⟨z, hz⟩) (isClosed_le continuous_const hc) v

theorem matrixCondMean_sub (A B : Ω → Matrix n n ℝ)
    (hA : EntryIntegrable A μ) (hB : EntryIntegrable B μ) :
    matrixCondMean μ m (fun ω => A ω - B ω) =ᵐ[μ]
      (fun ω => matrixCondMean μ m A ω - matrixCondMean μ m B ω) := by
  have he : ∀ i j, ∀ᵐ ω ∂μ,
      matrixCondMean μ m (fun ω => A ω - B ω) ω i j =
        (matrixCondMean μ m A ω - matrixCondMean μ m B ω) i j := by
    intro i j
    exact condExp_sub (hA i j) (hB i j) m
  have hall := (ae_all_iff).mpr (fun i => (ae_all_iff).mpr (he i))
  filter_upwards [hall] with ω hω
  ext i j
  exact hω i j

theorem matrixCondMean_mono (A B : Ω → Matrix n n ℝ)
    (hA : EntryIntegrable A μ) (hB : EntryIntegrable B μ)
    (hAB : ∀ᵐ ω ∂μ, LoewnerLE (A ω) (B ω)) :
    ∀ᵐ ω ∂μ, LoewnerLE (matrixCondMean μ m A ω) (matrixCondMean μ m B ω) := by
  have h := matrixCondMean_posSemidef m μ (fun ω => B ω - A ω)
    (fun i j => (hB i j).sub (hA i j)) hAB
  filter_upwards [h, matrixCondMean_sub m μ B A hB hA] with ω hω he
  rw [he] at hω
  exact hω

end
end LowRank
