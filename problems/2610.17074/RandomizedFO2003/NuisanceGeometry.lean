import RandomizedFO2003.BlockDirections
import RandomizedFO2003.Geometry
import RandomizedFO2003.EuclideanBlock

namespace RandomizedFO2003.SpectralCoordinates

open scoped BigOperators

variable {J : ℕ}

noncomputable def spectralVectorMap (K : Fin J → ℕ) (u : BlockSpace K) :
    (Fin J → ℝ) →ₗ[ℝ] BlockSpace K where
  toFun f := diagonal K f u
  map_add' f g := by ext i; simp [add_mul]
  map_smul' c f := by ext i; simp [mul_assoc]

noncomputable def cyclicSpace (K : Fin J → ℕ) (u : BlockSpace K) :
    Submodule ℝ (BlockSpace K) := LinearMap.range (spectralVectorMap K u)

noncomputable def shortKrylovSpace (K : Fin J → ℕ) (u : BlockSpace K)
    (node : Fin J → ℝ) (m : ℕ) : Submodule ℝ (BlockSpace K) :=
  LinearMap.range ((spectralVectorMap K u).comp (polynomialEvalMap node m))

noncomputable def nuisanceSpace (K : Fin J → ℕ)
    (W : (j : Fin J) → Submodule ℝ (ComponentSpace K j)) : Submodule ℝ (BlockSpace K) where
  carrier := {v | ∀ j, slice K j v ∈ W j}
  zero_mem' := by intro j; simp [slice]
  add_mem' hv hw := by
    intro j
    simpa [slice] using (W j).add_mem (hv j) (hw j)
  smul_mem' c v hv := by
    intro j
    simpa [slice] using (W j).smul_mem c (hv j)

theorem shortKrylovSpace_le_cyclicSpace (K : Fin J → ℕ) (u : BlockSpace K)
    (node : Fin J → ℝ) (m : ℕ) : shortKrylovSpace K u node m ≤ cyclicSpace K u := by
  rintro x ⟨c, rfl⟩
  exact ⟨polynomialEvalMap node m c, rfl⟩

theorem direction_mem_cyclicSpace (K : Fin J → ℕ) (u : BlockSpace K) (r : Fin J → ℝ) :
    direction K u r ∈ cyclicSpace K u :=
  (cyclicSpace K u).smul_mem _ ⟨r, rfl⟩

theorem slice_diagonal (K : Fin J → ℕ) (u : BlockSpace K) (f : Fin J → ℝ) (j : Fin J) :
    slice K j (diagonal K f u) = f j • slice K j u := by ext k; simp

theorem slice_eq_norm_smul_direction (K : Fin J → ℕ) (u : BlockSpace K) (j : Fin J) :
    slice K j u = ‖slice K j u‖ • blockDirection K j u := by
  by_cases h : slice K j u = 0
  · simp [h]
  · simp [blockDirection, Spherical.radial, smul_smul, norm_ne_zero_iff.mpr h]

theorem slice_inner_bound (K : Fin J → ℕ) (u : BlockSpace K) (j : Fin J)
    (W : Submodule ℝ (ComponentSpace K j)) (v : ComponentSpace K j) (hv : v ∈ W)
    (η : ℝ) (hη : ‖W.orthogonalProjection (blockDirection K j u)‖ ≤ η) :
    |inner (𝕜 := ℝ) (slice K j u) v| ≤ η * ‖slice K j u‖ * ‖v‖ := by
  have hp : inner (𝕜 := ℝ) (blockDirection K j u) v =
      inner (𝕜 := ℝ) (W.orthogonalProjection (blockDirection K j u) : ComponentSpace K j) v := by
    simpa only [real_inner_comm] using
      (Submodule.inner_orthogonalProjection_eq_of_mem_left W (⟨v, hv⟩ : W)
        (blockDirection K j u)).symm
  calc
    _ = ‖slice K j u‖ * |inner (𝕜 := ℝ) (blockDirection K j u) v| := by
      conv_lhs => rw [slice_eq_norm_smul_direction K u j]
      rw [real_inner_smul_left, abs_mul, abs_of_nonneg (norm_nonneg _)]
    _ ≤ ‖slice K j u‖ * (η * ‖v‖) := by
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      rw [hp]
      exact (abs_real_inner_le_norm _ _).trans
        (mul_le_mul_of_nonneg_right hη (norm_nonneg _))
    _ = _ := by ring

theorem inner_eq_sum_slices (K : Fin J → ℕ) (x v : BlockSpace K) :
    inner (𝕜 := ℝ) x v = ∑ j, inner (𝕜 := ℝ) (slice K j x) (slice K j v) := by
  rw [← (splitBlocks K).inner_map_map x v, PiLp.inner_apply]
  rfl

theorem norm_sq_eq_sum_slices (K : Fin J → ℕ) (x : BlockSpace K) :
    ‖x‖ ^ 2 = ∑ j, ‖slice K j x‖ ^ 2 := by
  rw [← (splitBlocks K).norm_map x, PiLp.norm_sq_eq_of_L2]
  rfl

/-- A uniform bound on the block-direction projections controls the angle
between the entire cyclic space and the full blockwise nuisance space. -/
theorem cyclic_nuisance_angle (K : Fin J → ℕ) (u : BlockSpace K)
    (W : (j : Fin J) → Submodule ℝ (ComponentSpace K j)) (η : ℝ) (hη : 0 ≤ η)
    (hproj : ∀ j, ‖(W j).orthogonalProjection (blockDirection K j u)‖ ≤ η)
    (x v : BlockSpace K) (hx : x ∈ cyclicSpace K u) (hv : v ∈ nuisanceSpace K W) :
    |inner (𝕜 := ℝ) x v| ≤ η * ‖x‖ * ‖v‖ := by
  obtain ⟨f, rfl⟩ := hx
  have hs (j : Fin J) :
      |inner (𝕜 := ℝ) (slice K j (spectralVectorMap K u f)) (slice K j v)| ≤
        η * ‖slice K j (spectralVectorMap K u f)‖ * ‖slice K j v‖ := by
    change |inner (𝕜 := ℝ) (slice K j (diagonal K f u)) (slice K j v)| ≤
      η * ‖slice K j (diagonal K f u)‖ * ‖slice K j v‖
    rw [slice_diagonal, real_inner_smul_left, abs_mul, norm_smul, Real.norm_eq_abs]
    have hb := mul_le_mul_of_nonneg_left
      (slice_inner_bound K u j (W j) (slice K j v) (hv j) η (hproj j)) (abs_nonneg (f j))
    nlinarith only [hb]
  rw [inner_eq_sum_slices]
  calc
    _ ≤ ∑ j, |inner (𝕜 := ℝ) (slice K j (spectralVectorMap K u f)) (slice K j v)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, η * ‖slice K j (spectralVectorMap K u f)‖ * ‖slice K j v‖ :=
      Finset.sum_le_sum (fun j _ => hs j)
    _ = η * ∑ j, ‖slice K j (spectralVectorMap K u f)‖ * ‖slice K j v‖ := by
      rw [Finset.mul_sum]; congr 1; ext j; ring
    _ ≤ η * (Real.sqrt (∑ j, ‖slice K j (spectralVectorMap K u f)‖ ^ 2) *
        Real.sqrt (∑ j, ‖slice K j v‖ ^ 2)) :=
      mul_le_mul_of_nonneg_left (Real.sum_mul_le_sqrt_mul_sqrt Finset.univ _ _) hη
    _ = _ := by rw [← norm_sq_eq_sum_slices, ← norm_sq_eq_sum_slices,
      Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)]; ring

end RandomizedFO2003.SpectralCoordinates

namespace RandomizedFO2003.FiniteSpectralDesign

open SpectralCoordinates

variable {m : ℕ} {γ L : ℝ} (D : FiniteSpectralDesign m γ L (1 / (16 * γ)))

theorem shortKrylovSpace_readout (hγ : 0 < γ) (K : Fin D.size → ℕ)
    (u : BlockSpace K) (δ : ℝ) (hδ : 0 ≤ δ) (hδhalf : δ ≤ 1 / 2)
    (hweight : ∀ j, |SpectralCoordinates.weight K u j - D.weight j| ≤ δ * D.weight j)
    (x : BlockSpace K) (hx : x ∈ shortKrylovSpace K u D.node m) :
    |inner (𝕜 := ℝ) (direction K u D.residual) x| ≤ 2 * δ * ‖x‖ := by
  obtain ⟨c, rfl⟩ := hx
  have hm : 1 ≤ m := (Nat.succ_le_succ (Nat.zero_le _)).trans D.degree_lt
  have hp := D.euclidean_short_krylov_bound hγ K u 1 δ zero_le_one hδ hδhalf hweight
    (Polynomial.ofFn m c) (Polynomial.ofFn_natDegree_lt hm c)
  dsimp only at hp
  rw [one_smul, polynomial_diagonal] at hp
  have heval : polynomialEvalMap D.node m c = fun j => (Polynomial.ofFn m c).eval (D.node j) := by
    ext j
    exact polynomialEvalMap_apply D.node c j
  change |inner (𝕜 := ℝ) (direction K u D.residual)
    (diagonal K (polynomialEvalMap D.node m c) u)| ≤ _
  simpa only [LinearMap.comp_apply, spectralVectorMap, LinearMap.coe_mk, AddHom.coe_mk, heval] using hp

/-- The deterministic high-multiplicity conclusion for genuine Euclidean
subspaces. Both hypotheses describe observable geometric events. -/
theorem krylov_nuisance_readout (hγ : 0 < γ) (K : Fin D.size → ℕ)
    (u : BlockSpace K) (W : (j : Fin D.size) → Submodule ℝ (ComponentSpace K j))
    (δ η : ℝ) (hδ : 0 ≤ δ) (hδhalf : δ ≤ 1 / 2) (hη : 0 ≤ η) (hηhalf : η ≤ 1 / 2)
    (hweight : ∀ j, |SpectralCoordinates.weight K u j - D.weight j| ≤ δ * D.weight j)
    (hproj : ∀ j, ‖(W j).orthogonalProjection (blockDirection K j u)‖ ≤ η)
    (z : BlockSpace K) (hz : z ∈ shortKrylovSpace K u D.node m ⊔ nuisanceSpace K W) :
    |inner (𝕜 := ℝ) (direction K u D.residual) z| ≤ 4 * (δ + η) * ‖z‖ := by
  obtain ⟨k, hk, v, hv, rfl⟩ := Submodule.mem_sup.mp hz
  have hR := D.empirical_residual_energy_pos (by positivity : 0 < 1 / (16 * γ))
    (SpectralCoordinates.weight K u) δ (by linarith) hweight
  have ha := direction_norm K u D.residual hR
  have hvbound := cyclic_nuisance_angle K u W η hη hproj (direction K u D.residual) v
    (direction_mem_cyclicSpace K u D.residual) hv
  rw [ha, mul_one] at hvbound
  have hangle := cyclic_nuisance_angle K u W η hη hproj k v
    (shortKrylovSpace_le_cyclicSpace K u D.node m hk) hv
  have hhalf : |inner (𝕜 := ℝ) k v| ≤ (1 / 2 : ℝ) * ‖k‖ * ‖v‖ :=
    hangle.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hηhalf (norm_nonneg _)) (norm_nonneg _))
  have hs := readout_on_sum (direction K u D.residual) k v (2 * δ) η
    (by positivity) hη (D.shortKrylovSpace_readout hγ K u δ hδ hδhalf hweight k hk)
    hvbound hhalf
  exact hs.trans (by nlinarith [mul_nonneg hη (norm_nonneg (k + v))])

end RandomizedFO2003.FiniteSpectralDesign
