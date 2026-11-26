import Bilevel.TransportObserverAngle

/-! Protected-column form of the source-angle argument. The hard projector
is onto the full frame space; protected columns are removed only after proving
that the old unprotected basis and the new input are orthogonal to them. -/
noncomputable section
open scoped RealInnerProductSpace BigOperators
namespace Bilevel.TransportObserver
open ProjectionGeometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem hard_projection_bound_unprotected (H S : Submodule ℝ E)
    (b : OrthonormalBasis ι ℝ H) (K : Finset ι) {e : ℝ}
    (hsource : frameEnergy S (fun i => (b i : E)) (Finset.univ\K) ≤ e)
    (v : E) (hv : v ∈ S) (hprotected : ∀ i ∈ K, ⟪(b i : E),v⟫ = 0) :
    ‖project H v‖ ≤ Real.sqrt e*‖v‖ := by
  have he : 0 ≤ e := (frameEnergy_nonneg S (fun i => (b i : E)) (Finset.univ\K)).trans hsource
  have hparse : ‖project H v‖^2 = ∑ i ∈ Finset.univ\K, ⟪(b i : E),v⟫^2 := by
    have hh := b.sum_sq_norm_inner (H.orthogonalProjection v)
    have hbase : ‖project H v‖^2 = ∑ i, ⟪(b i : E),v⟫^2 := by
      simpa only [Submodule.inner_orthogonalProjection_eq_of_mem_left,Real.norm_eq_abs,sq_abs] using hh.symm
    rw [hbase]
    symm
    apply Finset.sum_subset (Finset.sdiff_subset : Finset.univ\K ⊆ Finset.univ)
    intro i _ hi
    have hiK : i ∈ K := by simpa only [Finset.mem_sdiff,Finset.mem_univ,true_and,not_not] using hi
    rw [hprotected i hiK,zero_pow (by decide : (2:ℕ) ≠ 0)]
  have hb (i : ι) : ⟪(b i : E),v⟫^2 ≤ energy S (b i : E)*‖v‖^2 := by
    rw [inner_project_mem S _ v hv]
    have hh := (sq_le_sq₀ (abs_nonneg _) (by positivity : 0 ≤ ‖project S (b i : E)‖*‖v‖)).mpr
      (abs_real_inner_le_norm (project S (b i : E)) v)
    simpa only [sq_abs,mul_pow,energy] using hh
  have hsum := Finset.sum_le_sum (s := Finset.univ\K) (fun i _ => hb i)
  rw [← Finset.sum_mul] at hsum
  have hsq : ‖project H v‖^2 ≤ e*‖v‖^2 := by
    rw [hparse]
    exact hsum.trans (mul_le_mul_of_nonneg_right hsource (sq_nonneg _))
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
  rwa [mul_pow,Real.sq_sqrt he]

variable {F G : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G]

/-- Deterministic part of `dt:lem:angle`, with source frame energy and the
fresh complementary projection event stated separately. -/
theorem protected_source_angle (H S W : Submodule ℝ E)
    (b : OrthonormalBasis ι ℝ H) (K : Finset ι) (O : E ≃ₗᵢ[ℝ] E)
    (A : F →ₗᵢ[ℝ] E) (U : G →ₗᵢ[ℝ] E) {e : ℝ}
    (hsource : frameEnergy S (fun i => (b i : E)) (Finset.univ\K) ≤ e)
    (hsmall : e ≤ (1:ℝ)/4096)
    (hAS : ∀ x, A x ∈ S) (hUS : ∀ u, U u ∈ S)
    (hAK : ∀ i ∈ K, ∀ x, ⟪(b i : E),A x⟫ = 0)
    (hUK : ∀ i ∈ K, ∀ u, ⟪(b i : E),U u⟫ = 0)
    (horth : ∀ x u, ⟪A x,U u⟫ = 0)
    (hfresh : ∀ u, ‖project W (O (ProjectionGeometry.residual (LinearMap.range (innovationMap H A).toLinearMap)
      (innovationMap H U u)))‖ ≤ ‖u‖/8) :
    (∀ u, ‖project W (O (U u))‖ ≤ ‖u‖/2) ∧
      (∀ u, ‖u‖/2 ≤ ‖innovationMap W (O.toLinearIsometry.comp U) u‖) := by
  have he : 0 ≤ e := (frameEnergy_nonneg S (fun i => (b i : E)) (Finset.univ\K)).trans hsource
  have hA (x : F) : ‖project H (A x)‖ ≤ Real.sqrt e*‖x‖ := by
    simpa only [A.norm_map] using hard_projection_bound_unprotected H S b K hsource (A x) (hAS x)
      (fun i hi => hAK i hi x)
  have hU (u : G) : ‖project H (U u)‖ ≤ Real.sqrt e*‖u‖ := by
    simpa only [U.norm_map] using hard_projection_bound_unprotected H S b K hsource (U u) (hUS u)
      (fun i hi => hUK i hi u)
  have hang := angle_of_fresh_complement H W O A U he hsmall hA hU horth hfresh
  exact ⟨hang,fun u => innovation_singular_lower_bound W (O.toLinearIsometry.comp U) hang u⟩

/-- The same actual protected-source geometry implies the source's complete
coefficient-eight frame-energy update for every unprotected tracked subset. -/
theorem protected_source_energy_update (H S W : Submodule ℝ E)
    (b : OrthonormalBasis ι ℝ H) (K I : Finset ι) (hIK : I ⊆ Finset.univ\K)
    (O : E ≃ₗᵢ[ℝ] E) (A : F →ₗᵢ[ℝ] E) (U : G →ₗᵢ[ℝ] E) {e : ℝ}
    (hsource : frameEnergy S (fun i => (b i : E)) (Finset.univ\K) ≤ e)
    (hsmall : e ≤ (1:ℝ)/4096)
    (hAS : ∀ x, A x ∈ S) (hUS : ∀ u, U u ∈ S)
    (hAK : ∀ i ∈ K, ∀ x, ⟪(b i : E),A x⟫ = 0)
    (hUK : ∀ i ∈ K, ∀ u, ⟪(b i : E),U u⟫ = 0)
    (horth : ∀ x u, ⟪A x,U u⟫ = 0)
    (hfresh : ∀ u, ‖project W (O (ProjectionGeometry.residual (LinearMap.range (innovationMap H A).toLinearMap)
      (innovationMap H U u)))‖ ≤ ‖u‖/8) :
    frameEnergy (W ⊔ (LinearMap.range U.toLinearMap).map O.toLinearEquiv.toLinearMap)
      (fun i => O (b i : E)) I-frameEnergy W (fun i => O (b i : E)) I ≤
        8*(e+frameEnergy W (fun i => O (b i : E)) I) := by
  have hang := (protected_source_angle H S W b K O A U hsource hsmall hAS hUS hAK hUK horth hfresh).1
  have hRS : LinearMap.range U.toLinearMap ≤ S := by
    intro v hv
    obtain ⟨u,hu⟩ := hv
    change U u = v at hu
    rw [← hu]
    exact hUS u
  have hangle : ∀ v ∈ (LinearMap.range U.toLinearMap).map O.toLinearEquiv.toLinearMap,
      ‖project W v‖ ≤ ‖v‖/2 := by
    intro v hv
    obtain ⟨w,hw,hwv⟩ := hv
    obtain ⟨u,hu⟩ := hw
    change U u = w at hu
    change O w = v at hwv
    rw [← hwv,← hu,O.norm_map,U.norm_map]
    exact hang u
  exact transported_frame_energy_update O W (LinearMap.range U.toLinearMap) S hRS
    (fun i => (b i : E)) I (Finset.univ\K) hIK hsource hangle

end Bilevel.TransportObserver
