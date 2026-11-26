import MatchingBounds1005.GaussianAngle
import MatchingBounds1005.GaussianStarts

/-! # High-multiplicity geometry of the complete Gaussian cyclic span

The block hypotheses describe a deterministic orthogonal spectral coordinate
system. All Gaussian laws and probability bounds are derived from actual
independent standard Gaussian starts. No random-angle or query-containment
hypothesis is used.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace BigOperators
open MatchingBounds1005.GaussianVector MatchingBounds1005.GaussianMatrix
open MatchingBounds1005.GaussianAngle MatchingBounds1005.ScheduledHaar
open MatchingBounds1005.GaussianHaar MatchingBounds1005.GaussianStarts
open RandomizedFO2003.Rotations

namespace MatchingBounds1005.GaussianBlockGeometry

theorem gaussian_isometric_adjoint {n d : ℕ} (e : Vec d →ₗᵢ[ℝ] Vec n) :
    MeasurePreserving e.toContinuousLinearMap.adjoint (standardGaussian n) (standardGaussian d) := by
  refine ⟨e.toContinuousLinearMap.adjoint.continuous.measurable, ?_⟩
  apply Measure.ext_of_charFun
  funext t
  rw [standardGaussian_linear_charFun, standardGaussian_charFun,
    ContinuousLinearMap.adjoint_adjoint]
  change Complex.exp (-((‖e t‖ : ℂ) ^ 2) / 2) = Complex.exp (-((‖t‖ : ℂ) ^ 2) / 2)
  rw [e.norm_map]

def blockCoordinates {n J : ℕ} {dim : Fin J → ℕ}
    (e : (j : Fin J) → Vec (dim j) →ₗᵢ[ℝ] Vec n) (j : Fin J) : Vec n →L[ℝ] Vec (dim j) :=
  (e j).toContinuousLinearMap.adjoint

def blockColumns {n J k : ℕ} {dim : Fin J → ℕ}
    (e : (j : Fin J) → Vec (dim j) →ₗᵢ[ℝ] Vec n) (g : Fin k → Vec n) (j : Fin J) :
    Fin k → Vec (dim j) := fun i => blockCoordinates e j (g i)

def blockSubspace {n J : ℕ} {dim : Fin J → ℕ}
    (e : (j : Fin J) → Vec (dim j) →ₗᵢ[ℝ] Vec n)
    (A : (j : Fin J) → Submodule ℝ (Vec (dim j))) : Submodule ℝ (Vec n) where
  carrier := {x | ∀ j, blockCoordinates e j x ∈ A j}
  zero_mem' := by intro j; simp
  add_mem' hx hy := by intro j; simpa using (A j).add_mem (hx j) (hy j)
  smul_mem' c x hx := by intro j; simpa using (A j).smul_mem c (hx j)

theorem blockColumns_preserving {n J k : ℕ} {dim : Fin J → ℕ}
    (e : (j : Fin J) → Vec (dim j) →ₗᵢ[ℝ] Vec n) (j : Fin J) :
    MeasurePreserving (fun g : Fin k → Vec n => blockColumns e g j)
      (gaussianMatrixLaw n k) (gaussianMatrixLaw (dim j) k) :=
  measurePreserving_pi _ _ (fun _ => gaussian_isometric_adjoint (e j))

theorem start_mem_columnSpace {d k : ℕ} (g : Fin k → Vec d) (i : Fin k) :
    g i ∈ columnSpace g := by
  refine ⟨EuclideanSpace.single i 1, ?_⟩
  change (∑ j, (EuclideanSpace.single i (1 : ℝ)) j • g j) = g i
  simp [EuclideanSpace.single_apply]

/-- In a deterministic spectral coordinate system, every power of every
original Gaussian start remains in the direct sum of the blockwise column
spaces. Arbitrary polynomial preprocessing therefore costs no new starts. -/
theorem cyclicSpan_le_blockSubspace {n J k : ℕ} {dim : Fin J → ℕ}
    (e : (j : Fin J) → Vec (dim j) →ₗᵢ[ℝ] Vec n) (Q : Vec n →L[ℝ] Vec n)
    (node : Fin J → ℝ)
    (hQ : ∀ j x, blockCoordinates e j (Q x) = node j • blockCoordinates e j x)
    (g : Fin k → Vec n) :
    cyclicSpan Q g ≤ blockSubspace e (fun j => columnSpace (blockColumns e g j)) := by
  have hp (q : ℕ) (j : Fin J) (x : Vec n) :
      blockCoordinates e j ((Q.toLinearMap ^ q) x) = node j ^ q • blockCoordinates e j x := by
    induction q generalizing x with
    | zero => simp
    | succ q ih =>
      rw [pow_succ', Module.End.mul_apply]
      change blockCoordinates e j (Q ((Q.toLinearMap ^ q) x)) = _
      rw [hQ, ih, smul_smul, pow_succ']
  apply Submodule.span_le.mpr
  rintro v ⟨⟨q, i⟩, rfl⟩ j
  change blockCoordinates e j ((Q.toLinearMap ^ q) (g i)) ∈ columnSpace (blockColumns e g j)
  rw [hp]
  exact (columnSpace (blockColumns e g j)).smul_mem _ (start_mem_columnSpace _ i)

theorem blockSubspace_inner_bound {n J : ℕ} {dim : Fin J → ℕ}
    (e : (j : Fin J) → Vec (dim j) →ₗᵢ[ℝ] Vec n)
    (hdecomp : ∀ x y : Vec n, ⟪x, y⟫_ℝ = ∑ j, ⟪blockCoordinates e j x, blockCoordinates e j y⟫_ℝ)
    (A W : (j : Fin J) → Submodule ℝ (Vec (dim j))) {η : ℝ} (hη : 0 ≤ η)
    (hangle : ∀ j a, a ∈ A j → ‖(W j).orthogonalProjection a‖ ≤ η * ‖a‖)
    (x v : Vec n) (hx : x ∈ blockSubspace e A) (hv : v ∈ blockSubspace e W) :
    |⟪x, v⟫_ℝ| ≤ η * ‖x‖ * ‖v‖ := by
  have hnorm (z : Vec n) : ‖z‖ ^ 2 = ∑ j, ‖blockCoordinates e j z‖ ^ 2 := by
    simpa only [real_inner_self_eq_norm_sq] using hdecomp z z
  have hs (j : Fin J) : |⟪blockCoordinates e j x, blockCoordinates e j v⟫_ℝ| ≤
      η * ‖blockCoordinates e j x‖ * ‖blockCoordinates e j v‖ := by
    have he : ⟪blockCoordinates e j x, blockCoordinates e j v⟫_ℝ =
        ⟪(W j).orthogonalProjection (blockCoordinates e j x),
          (⟨blockCoordinates e j v, hv j⟩ : W j)⟫_ℝ :=
      ((W j).inner_orthogonalProjection_eq_of_mem_right
        (⟨blockCoordinates e j v, hv j⟩ : W j) (blockCoordinates e j x)).symm
    rw [he]
    exact (abs_real_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_right (hangle j _ (hx j)) (norm_nonneg _))
  rw [hdecomp]
  calc
    _ ≤ ∑ j, |⟪blockCoordinates e j x, blockCoordinates e j v⟫_ℝ| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, η * ‖blockCoordinates e j x‖ * ‖blockCoordinates e j v‖ :=
      Finset.sum_le_sum (fun j _ => hs j)
    _ = η * ∑ j, ‖blockCoordinates e j x‖ * ‖blockCoordinates e j v‖ := by
      rw [Finset.mul_sum]
      congr 1
      funext j
      ring
    _ ≤ η * (Real.sqrt (∑ j, ‖blockCoordinates e j x‖ ^ 2) *
        Real.sqrt (∑ j, ‖blockCoordinates e j v‖ ^ 2)) :=
      mul_le_mul_of_nonneg_left (Real.sum_mul_le_sqrt_mul_sqrt Finset.univ _ _) hη
    _ = _ := by rw [← hnorm, ← hnorm, Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)]; ring

def CyclicAngleGood {n k : ℕ} (A : Submodule ℝ (Vec n))
    (Q : Vec n →L[ℝ] Vec n) (g : Fin k → Vec n) (η : ℝ) : Prop :=
  ∀ x ∈ A, ‖(cyclicSpan Q g).orthogonalProjection x‖ ≤ η * ‖x‖

theorem cyclicAngleGood_of_blocks {n J k : ℕ} {dim : Fin J → ℕ}
    (e : (j : Fin J) → Vec (dim j) →ₗᵢ[ℝ] Vec n)
    (hdecomp : ∀ x y : Vec n, ⟪x, y⟫_ℝ = ∑ j, ⟪blockCoordinates e j x, blockCoordinates e j y⟫_ℝ)
    (A : (j : Fin J) → Submodule ℝ (Vec (dim j))) (Q : Vec n →L[ℝ] Vec n)
    (node : Fin J → ℝ)
    (hQ : ∀ j x, blockCoordinates e j (Q x) = node j • blockCoordinates e j x)
    (g : Fin k → Vec n) {η : ℝ} (hη : 0 ≤ η)
    (hg : ∀ j, AngleGood (A j) (blockColumns e g j) η) :
    CyclicAngleGood (blockSubspace e A) Q g η := by
  intro x hx
  let R := cyclicSpan Q g
  let p : R := R.orthogonalProjection x
  have hp := cyclicSpan_le_blockSubspace e Q node hQ g p.property
  have hh := blockSubspace_inner_bound e hdecomp A
    (fun j => columnSpace (blockColumns e g j)) hη hg x p hx hp
  have he : ⟪x, (p : Vec n)⟫_ℝ = ‖p‖ ^ 2 := by
    have h := R.orthogonalProjection_inner_eq_zero x (p : Vec n) p.property
    rw [inner_sub_left] at h
    change ⟪x, (p : Vec n)⟫_ℝ - ⟪(p : Vec n), (p : Vec n)⟫_ℝ = 0 at h
    rw [real_inner_self_eq_norm_sq] at h
    exact sub_eq_zero.mp h
  rw [he, abs_of_nonneg (sq_nonneg _)] at hh
  change ‖p‖ ^ 2 ≤ η * ‖x‖ * ‖p‖ at hh
  change ‖p‖ ≤ η * ‖x‖
  by_cases hp0 : ‖p‖ = 0
  · rw [hp0]; positivity
  · have hpp : 0 < ‖p‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hp0)
    nlinarith

/-- Outer-measure pullback is enough for failure events, so no measurable
selection of a maximizing singular direction is introduced. -/
theorem preserving_failure_le {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    {μ : Measure Ω} {ν : Measure Ξ} [IsFiniteMeasure ν]
    {f : Ω → Ξ} (hf : MeasurePreserving f μ ν) (s : Set Ξ) :
    μ.real (f ⁻¹' s) ≤ ν.real s := by
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  rw [← hf.map_eq]
  exact Measure.le_map_apply hf.measurable.aemeasurable s

/-- High-multiplicity control of the *whole* quadratic cyclic span of the
actual iid Gaussian starts. The constants are uniform in all block dimensions;
only the number of blocks enters the union bound. -/
theorem high_multiplicity_cyclic_angle {n J k K : ℕ} {dim : Fin J → ℕ}
    (e : (j : Fin J) → Vec (dim j) →ₗᵢ[ℝ] Vec n)
    (hdecomp : ∀ x y : Vec n, ⟪x, y⟫_ℝ = ∑ j, ⟪blockCoordinates e j x, blockCoordinates e j y⟫_ℝ)
    (A : (j : Fin J) → Submodule ℝ (Vec (dim j)))
    (hm : ∀ j, 0 < Module.finrank ℝ (A j))
    (hd : ∀ j, dim j = (K + 1) * Module.finrank ℝ (A j))
    (Q : Vec n →L[ℝ] Vec n) (node : Fin J → ℝ)
    (hQ : ∀ j x, blockCoordinates e j (Q x) = node j • blockCoordinates e j x)
    {η s : ℝ} (hη : 0 ≤ η) (hηhalf : η ≤ 1 / 2) (hs : 0 ≤ s)
    (hK : 96 * ((k : ℝ) + 1) + 32 * s ≤ ((K + 1 : ℕ) : ℝ) * η ^ 2) :
    (gaussianMatrixLaw n k).real {g | ¬ CyclicAngleGood (blockSubspace e A) Q g η} ≤
      4 * (J : ℝ) * Real.exp (-s) := by
  let bad (j : Fin J) : Set (Fin k → Vec n) := {g | ¬ AngleGood (A j) (blockColumns e g j) η}
  have hsub : {g : Fin k → Vec n | ¬ CyclicAngleGood (blockSubspace e A) Q g η} ⊆ ⋃ j, bad j := by
    intro g hg
    by_contra hn
    have hj : ∀ j, AngleGood (A j) (blockColumns e g j) η := by
      intro j
      by_contra h
      exact hn (Set.mem_iUnion.mpr ⟨j, h⟩)
    exact hg (cyclicAngleGood_of_blocks e hdecomp A Q node hQ g hη hj)
  have hb (j : Fin J) : (gaussianMatrixLaw n k).real (bad j) ≤ 4 * Real.exp (-s) := by
    exact (preserving_failure_le (blockColumns_preserving e j)
      {a | ¬ AngleGood (A j) a η}).trans
      (high_multiplicity_angle (A j) (hm j) (hd j) hη hηhalf hs hK)
  calc
    _ ≤ (gaussianMatrixLaw n k).real (⋃ j, bad j) := measureReal_mono hsub
    _ ≤ ∑ j, (gaussianMatrixLaw n k).real (bad j) := measureReal_iUnion_fintype_le _
    _ ≤ ∑ _j : Fin J, 4 * Real.exp (-s) := Finset.sum_le_sum (fun j _ => hb j)
    _ = _ := by simp; ring

/-- A failure bound supplies a measurable good event contained in the full
pointwise conclusion, without asserting measurability of a supremum event. -/
theorem measurable_good_event {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (P : Ω → Prop) {ζ : ℝ}
    (hbad : μ.real {ω | ¬ P ω} ≤ ζ) :
    ∃ G : Set Ω, MeasurableSet G ∧ (∀ ω ∈ G, P ω) ∧ 1 - ζ ≤ μ.real G := by
  let C := toMeasurable μ {ω | ¬ P ω}
  have hC : MeasurableSet C := measurableSet_toMeasurable _ _
  have he : μ.real C = μ.real {ω | ¬ P ω} := by
    unfold Measure.real C
    rw [measure_toMeasurable]
  have hadd := measureReal_add_measureReal_compl (μ := μ) hC
  rw [measureReal_univ_eq_one, he] at hadd
  refine ⟨Cᶜ, hC.compl, ?_, by linarith⟩
  intro ω hω
  by_contra h
  exact hω (subset_toMeasurable μ _ h)

end MatchingBounds1005.GaussianBlockGeometry
