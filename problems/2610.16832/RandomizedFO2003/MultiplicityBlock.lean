import RandomizedFO2003.BlockMomentBounds

namespace RandomizedFO2003.SpectralCoordinates

open scoped BigOperators

variable {J : ℕ}

abbrev BlockSpace (K : Fin J → ℕ) := EuclideanSpace ℝ (Σ j, Fin (K j))

theorem block_sum_apply (K : Fin J → ℕ) {I : Type*} (s : Finset I)
    (v : I → BlockSpace K) (i : Σ j, Fin (K j)) :
    (∑ t ∈ s, v t) i = ∑ t ∈ s, v t i := by
  change (PiLp.projₗ (𝕜 := ℝ) 2 (fun _ : Σ j, Fin (K j) => ℝ) i) (∑ t ∈ s, v t) = _
  exact map_sum _ _ _

noncomputable def diagonal (K : Fin J → ℕ) (f : Fin J → ℝ) :
    Module.End ℝ (BlockSpace K) where
  toFun x := (WithLp.equiv 2 ((Σ j, Fin (K j)) → ℝ)).symm (fun i => f i.1 * x i)
  map_add' x y := by ext i; simp [mul_add]
  map_smul' c x := by ext i; simp [mul_comm, mul_left_comm]

@[simp] theorem diagonal_apply (K : Fin J → ℕ) (f : Fin J → ℝ)
    (x : BlockSpace K) (i : Σ j, Fin (K j)) : diagonal K f x i = f i.1 * x i := rfl

theorem diagonal_one (K : Fin J → ℕ) : diagonal K (fun _ => 1) = 1 := by
  ext x i
  simp

theorem diagonal_mul (K : Fin J → ℕ) (f g : Fin J → ℝ) :
    diagonal K (fun j => f j * g j) = diagonal K f * diagonal K g := by
  ext x i
  simp [Module.End.mul_apply, mul_assoc]

theorem diagonal_pow_apply (K : Fin J → ℕ) (f : Fin J → ℝ) (n : ℕ)
    (x : BlockSpace K) (i : Σ j, Fin (K j)) :
    (diagonal K f ^ n) x i = f i.1 ^ n * x i := by
  induction n generalizing x with
  | zero => simp
  | succ n ih => simp [pow_succ, Module.End.mul_apply, ih, mul_assoc]

/-- Genuine polynomial evaluation of the linear operator equals the coordinate
functional calculus, including at arbitrary multiplicities. -/
theorem polynomial_diagonal_apply (K : Fin J → ℕ) (lam : Fin J → ℝ)
    (p : Polynomial ℝ) (x : BlockSpace K) (i : Σ j, Fin (K j)) :
    (p.eval₂ (algebraMap ℝ (Module.End ℝ (BlockSpace K))) (diagonal K lam)) x i =
      p.eval (lam i.1) * x i := by
  simp only [Polynomial.eval₂_eq_sum, Polynomial.eval_eq_sum, Polynomial.sum]
  simp only [LinearMap.sum_apply, block_sum_apply, Module.End.mul_apply]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro n _
  simp [diagonal_pow_apply, Algebra.algebraMap_eq_smul_one, mul_assoc]

theorem polynomial_diagonal (K : Fin J → ℕ) (lam : Fin J → ℝ) (p : Polynomial ℝ) :
    p.eval₂ (algebraMap ℝ (Module.End ℝ (BlockSpace K))) (diagonal K lam) =
      diagonal K (fun j => p.eval (lam j)) := by
  ext x i
  exact polynomial_diagonal_apply K lam p x i

theorem inverse_diagonal (K : Fin J → ℕ) (lam : Fin J → ℝ)
    (hlam : ∀ j, lam j ≠ 0) :
    diagonal K (fun j => (lam j)⁻¹) * diagonal K lam = 1 ∧
      diagonal K lam * diagonal K (fun j => (lam j)⁻¹) = 1 := by
  constructor <;> ext x i <;> simp [Module.End.mul_apply, ← mul_assoc, hlam]

def weight (K : Fin J → ℕ) (u : BlockSpace K) (j : Fin J) : ℝ :=
  ∑ k : Fin (K j), u ⟨j, k⟩ ^ 2

theorem weight_nonneg (K : Fin J → ℕ) (u : BlockSpace K) (j : Fin J) :
    0 ≤ weight K u j := Finset.sum_nonneg (fun _ _ => sq_nonneg _)

theorem weight_sum (K : Fin J → ℕ) (u : BlockSpace K) :
    (∑ j, weight K u j) = ‖u‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq]
  simp only [PiLp.inner_apply, weight, Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  change u ⟨j, k⟩ ^ 2 = u ⟨j, k⟩ * u ⟨j, k⟩
  ring

theorem unit_weight_sum (K : Fin J → ℕ) (u : BlockSpace K) (hu : ‖u‖ = 1) :
    (∑ j, weight K u j) = 1 := by rw [weight_sum, hu, one_pow]

theorem inner_diagonal (K : Fin J → ℕ) (u : BlockSpace K) (f g : Fin J → ℝ) :
    inner (𝕜 := ℝ) (diagonal K f u) (diagonal K g u) = weightedPair (weight K u) f g := by
  simp only [PiLp.inner_apply, Fintype.sum_sigma, weightedPair, weight]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_mul, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k _
  change (g j * u ⟨j, k⟩) * (f j * u ⟨j, k⟩) = _
  ring

theorem norm_diagonal_sq (K : Fin J → ℕ) (u : BlockSpace K) (f : Fin J → ℝ) :
    ‖diagonal K f u‖ ^ 2 = weightedEnergy (weight K u) f := by
  rw [← real_inner_self_eq_norm_sq, inner_diagonal]
  simp [weightedPair, weightedEnergy, sq, mul_assoc]

theorem norm_diagonal (K : Fin J → ℕ) (u : BlockSpace K) (f : Fin J → ℝ) :
    ‖diagonal K f u‖ = Real.sqrt (weightedEnergy (weight K u) f) := by
  rw [← norm_diagonal_sq, Real.sqrt_sq (norm_nonneg _)]

/-- Normalized residual direction in the full multiplicity space. -/
noncomputable def direction (K : Fin J → ℕ) (u : BlockSpace K) (r : Fin J → ℝ) :
    BlockSpace K := (‖diagonal K r u‖)⁻¹ • diagonal K r u

theorem direction_norm (K : Fin J → ℕ) (u : BlockSpace K) (r : Fin J → ℝ)
    (hR : 0 < weightedEnergy (weight K u) r) : ‖direction K u r‖ = 1 := by
  have hn : 0 < ‖diagonal K r u‖ := by rw [norm_diagonal]; exact Real.sqrt_pos.mpr hR
  simp [direction, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hn), hn.ne']

theorem direction_inner (K : Fin J → ℕ) (u : BlockSpace K) (r f : Fin J → ℝ) (h : ℝ) :
    inner (𝕜 := ℝ) (direction K u r) (h • diagonal K f u) =
      h * weightedPair (weight K u) r f / Real.sqrt (weightedEnergy (weight K u) r) := by
  rw [direction, inner_smul_left, inner_smul_right, inner_diagonal, norm_diagonal]
  simp only [RCLike.conj_to_real]
  ring

theorem direction_inverse_inner (K : Fin J → ℕ) (u : BlockSpace K)
    (r f : Fin J → ℝ) :
    inner (𝕜 := ℝ) (direction K u r) (diagonal K f (direction K u r)) =
      weightedEnergy (fun j => weight K u j * f j) r / weightedEnergy (weight K u) r := by
  have hc : diagonal K f (diagonal K r u) = diagonal K (fun j => f j * r j) u := by
    ext i
    simp [mul_assoc]
  have hp : weightedPair (weight K u) r (fun j => f j * r j) =
      weightedEnergy (fun j => weight K u j * f j) r := by
    apply Finset.sum_congr rfl
    intro j _
    ring
  simp only [direction, map_smul, real_inner_smul_left, real_inner_smul_right]
  rw [hc, inner_diagonal, hp, ← norm_diagonal_sq]
  ring

theorem scaled_inverse_inner (K : Fin J → ℕ) (u : BlockSpace K)
    (f : Fin J → ℝ) (h : ℝ) :
    inner (𝕜 := ℝ) (h • u) (diagonal K f (h • u)) =
      h ^ 2 * ∑ j, weight K u j * f j := by
  have hunit : diagonal K (fun _ => 1) u = u := by ext i; simp
  have hp : inner (𝕜 := ℝ) u (diagonal K f u) = ∑ j, weight K u j * f j := by
    simpa [hunit, weightedPair] using inner_diagonal K u (fun _ => 1) f
  simp only [map_smul, real_inner_smul_left, real_inner_smul_right, hp]
  ring

end RandomizedFO2003.SpectralCoordinates
