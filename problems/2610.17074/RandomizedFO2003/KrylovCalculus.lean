import RandomizedFO2003.MultiStart

namespace RandomizedFO2003

open scoped BigOperators

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- The first `m` powers of a marked vector, including no vector when `m = 0`. -/
def powerKrylovSpace (A : Module.End ℝ E) (u : E) (m : ℕ) : Submodule ℝ E :=
  Submodule.span ℝ (Set.range (fun i : Fin m => (A ^ i.val) u))

@[simp] theorem powerKrylovSpace_zero (A : Module.End ℝ E) (u : E) :
    powerKrylovSpace A u 0 = ⊥ := by
  simp [powerKrylovSpace]

theorem powerKrylovSpace_mono (A : Module.End ℝ E) (u : E) {m k : ℕ} (h : m ≤ k) :
    powerKrylovSpace A u m ≤ powerKrylovSpace A u k := by
  apply Submodule.span_mono
  rintro x ⟨i, rfl⟩
  exact ⟨⟨i.val, i.isLt.trans_le h⟩, rfl⟩

theorem self_mem_powerKrylovSpace (A : Module.End ℝ E) (u : E) {m : ℕ} (hm : 0 < m) :
    u ∈ powerKrylovSpace A u m := by
  exact Submodule.subset_span ⟨⟨0, hm⟩, by simp⟩

theorem map_powerKrylovSpace_le (A : Module.End ℝ E) (u : E) (m : ℕ) :
    (powerKrylovSpace A u m).map A ≤ powerKrylovSpace A u (m + 1) := by
  rw [Submodule.map_le_iff_le_comap]
  apply Submodule.span_le.mpr
  rintro x ⟨i, rfl⟩
  change A ((A ^ i.val) u) ∈ powerKrylovSpace A u (m + 1)
  have hi : i.val + 1 < m + 1 := Nat.succ_lt_succ i.isLt
  have hp : (A ^ (i.val + 1)) u = A ((A ^ i.val) u) := by
    rw [pow_succ']
    rfl
  exact Submodule.subset_span ⟨⟨i.val + 1, hi⟩, hp⟩

/-- A matrix response increases only the marked degree; any invariant nuisance
space absorbs all further matrix preprocessing of its independent starts. -/
theorem map_krylov_sup_le (A : Module.End ℝ E) (u : E) (m : ℕ) (N : Submodule ℝ E)
    (hN : N.map A ≤ N) :
    (powerKrylovSpace A u m ⊔ N).map A ≤ powerKrylovSpace A u (m + 1) ⊔ N := by
  rw [Submodule.map_sup]
  exact sup_le_sup (map_powerKrylovSpace_le A u m) hN

end RandomizedFO2003

namespace RandomizedFO2003.SpectralCoordinates

open scoped BigOperators

variable {J T : ℕ}

theorem spectralVectorMap_polynomialEval (K : Fin J → ℕ) (u : BlockSpace K)
    (node : Fin J → ℝ) {m : ℕ} (c : Fin m → ℝ) :
    spectralVectorMap K u (polynomialEvalMap node m c) =
      ∑ i : Fin m, c i • ((diagonal K node) ^ i.val) u := by
  ext j
  change _ = (PiLp.projₗ 2 (𝕜 := ℝ) (fun _ => ℝ) j) (∑ i : Fin m, c i • ((diagonal K node) ^ i.val) u)
  rw [map_sum]
  simp [spectralVectorMap, polynomialEvalMap, diagonal_pow_apply, Finset.sum_apply,
    Finset.sum_mul, mul_assoc]

/-- The algebraic chronological space is exactly the short space used in the
already proved residual/readout estimates. -/
theorem shortKrylovSpace_eq_powerKrylovSpace (K : Fin J → ℕ) (u : BlockSpace K)
    (node : Fin J → ℝ) (m : ℕ) :
    shortKrylovSpace K u node m = powerKrylovSpace (diagonal K node) u m := by
  ext x
  rw [powerKrylovSpace, Submodule.mem_span_range_iff_exists_fun]
  change (∃ c, spectralVectorMap K u (polynomialEvalMap node m c) = x) ↔ _
  simp only [spectralVectorMap_polynomialEval]

theorem start_mem_multiStartKrylovSpace (K : Fin J → ℕ) (node : Fin J → ℝ)
    (g : Fin T → BlockSpace K) (i : Fin T) : g i ∈ multiStartKrylovSpace K node g := by
  exact Submodule.subset_span ⟨(i, 1), by simp⟩

theorem map_multiStartKrylovSpace_le (K : Fin J → ℕ) (node : Fin J → ℝ)
    (g : Fin T → BlockSpace K) :
    (multiStartKrylovSpace K node g).map (diagonal K node) ≤ multiStartKrylovSpace K node g := by
  rw [Submodule.map_le_iff_le_comap]
  apply Submodule.span_le.mpr
  rintro x ⟨⟨i, p⟩, rfl⟩
  change diagonal K node
    ((p.eval₂ (algebraMap ℝ (Module.End ℝ (BlockSpace K))) (diagonal K node)) (g i)) ∈
      multiStartKrylovSpace K node g
  apply Submodule.subset_span
  refine ⟨(i, Polynomial.X * p), ?_⟩
  simp only [polynomial_diagonal]
  ext j
  simp [Polynomial.eval_mul, Polynomial.eval_X, mul_assoc]

end RandomizedFO2003.SpectralCoordinates
