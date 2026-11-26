import GradientHessian.FoldHierarchy

/-!
# The actual common positive memory baseline

All blocks are embedded in the shared lower-coordinate space using continuous
linear coordinate projections (zero extension preserves each Euclidean norm).
The formula is exactly a finite sum of weighted squared norms and the public
radial potentials. The stationarity at zero is proved from this formula.
-/

noncomputable section

namespace GradientHessian.CommonBaseline

open Localized FoldHierarchy
open scoped BigOperators

variable {Y : Type*} [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]

/-- Numerical and old-register quadratics, plus public higher-level memory terms. -/
def scalar {m n : ℕ} (weight : Fin m → ℝ) (quadMap : Fin m → Y →L[ℝ] Y)
    (radius : Fin n → ℝ) (publicMap : Fin n → Y →L[ℝ] Y) (y : Y) : ℝ :=
  (∑ i, weight i * ‖quadMap i y‖ ^ 2) + ∑ i, publicPotential (radius i) (publicMap i y)

omit [CompleteSpace Y] in
theorem scalar_zero {m n : ℕ} (weight : Fin m → ℝ) (quadMap : Fin m → Y →L[ℝ] Y)
    (radius : Fin n → ℝ) (publicMap : Fin n → Y →L[ℝ] Y) (hr : ∀ i, 0 ≤ radius i) :
    scalar weight quadMap radius publicMap 0 = 0 := by
  simp [scalar, publicPotential_zero, hr]

omit [CompleteSpace Y] in
theorem scalar_nonneg {m n : ℕ} (weight : Fin m → ℝ) (quadMap : Fin m → Y →L[ℝ] Y)
    (radius : Fin n → ℝ) (publicMap : Fin n → Y →L[ℝ] Y)
    (hw : ∀ i, 0 ≤ weight i) (hr : ∀ i, 0 ≤ radius i) (y : Y) :
    0 ≤ scalar weight quadMap radius publicMap y := by
  apply add_nonneg
  · exact Finset.sum_nonneg fun i _ => mul_nonneg (hw i) (sq_nonneg _)
  · exact Finset.sum_nonneg fun i _ => publicPotential_nonneg (hr i) _

/-- The actual baseline has zero Frechet derivative at the origin. -/
theorem scalar_hasFDerivAt_zero {m n : ℕ}
    (weight : Fin m → ℝ) (quadMap : Fin m → Y →L[ℝ] Y)
    (radius : Fin n → ℝ) (publicMap : Fin n → Y →L[ℝ] Y) (hr : ∀ i, 0 < radius i) :
    HasFDerivAt (𝕜 := ℝ) (scalar weight quadMap radius publicMap) 0 0 := by
  have hquad : ∀ i : Fin m, HasFDerivAt (𝕜 := ℝ)
      (fun y => weight i * ‖quadMap i y‖ ^ 2) 0 0 := by
    intro i
    simpa using (((quadMap i).hasFDerivAt (x := (0 : Y))).norm_sq.const_mul (weight i))
  have hpublic : ∀ i : Fin n, HasFDerivAt (𝕜 := ℝ)
      (fun y => publicPotential (radius i) (publicMap i y)) 0 0 := by
    intro i
    have h : HasFDerivAt (𝕜 := ℝ) (publicPotential (radius i)) 0 (publicMap i 0) := by
      simpa using (publicPotential_hasGradientAt (hr i) (0 : Y)).hasFDerivAt
    have hc := h.comp (0 : Y) ((publicMap i).hasFDerivAt (x := (0 : Y)))
    simpa using hc
  have hq := HasFDerivAt.sum (u := Finset.univ) (fun i _ => hquad i)
  have hp := HasFDerivAt.sum (u := Finset.univ) (fun i _ => hpublic i)
  simpa [scalar] using hq.add hp

omit [CompleteSpace Y] in
theorem scalar_contDiff {m n : ℕ}
    (weight : Fin m → ℝ) (quadMap : Fin m → Y →L[ℝ] Y)
    (radius : Fin n → ℝ) (publicMap : Fin n → Y →L[ℝ] Y) (hr : ∀ i, 0 < radius i)
    (k : WithTop ℕ∞) : ContDiff ℝ k (scalar weight quadMap radius publicMap) := by
  apply ContDiff.add
  · apply ContDiff.sum
    intro i _
    exact contDiff_const.mul ((quadMap i).contDiff.norm_sq ℝ)
  · apply ContDiff.sum
    intro i _
    exact (publicPotential_contDiff (hr i) k).comp (publicMap i).contDiff

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [ProperSpace E]

/-- Adjacent identification for the literal two-level hierarchy with the explicit
common baseline. There is no assumed stationarity hypothesis on the baseline. -/
theorem diagonal_identification_has_uncertified_stationary {m n : ℕ}
    (weight : Fin m → ℝ) (quadMap : Fin m → Y →L[ℝ] Y)
    (radius : Fin n → ℝ) (publicMap : Fin n → Y →L[ℝ] Y) (hr : ∀ i, 0 < radius i)
    {R w : ℝ} (hw : 0 < w) (hscale : 16 * w ≤ R)
    (a b : Fin 8 → E) (ha : ∀ i, ‖a i‖ = R) (hb : ∀ i, ‖b i‖ = 6 * R)
    (S₀ S₁ : ℝ) (desc descPort siblings siblingPort : ℕ → (Y × (Fin 8 → E)) → ℝ) :
    ∃ U : Fin 8 → E,
      HasFDerivAt (𝕜 := ℝ)
        (diagonalNode (scalar weight quadMap radius publicMap) S₀ S₁ R w a b
          desc descPort siblings siblingPort) 0 (0, U) ∧
      (∀ i, port (3 * w) (b i) (U i) = 0) :=
  diagonalNode_has_uncertified_stationary hw hscale a b ha hb
    (scalar weight quadMap radius publicMap)
    (scalar_hasFDerivAt_zero weight quadMap radius publicMap hr) S₀ S₁
    desc descPort siblings siblingPort

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- Frechet stationarity transports from product coordinates to any equivalent
normed coordinate realization, including Euclidean concatenation. No operator
norm estimate for a Hessian-Lipschitz constant is asserted by this corollary. -/
theorem diagonal_identification_transport {m n : ℕ}
    (weight : Fin m → ℝ) (quadMap : Fin m → Y →L[ℝ] Y)
    (radius : Fin n → ℝ) (publicMap : Fin n → Y →L[ℝ] Y) (hr : ∀ i, 0 < radius i)
    {R w : ℝ} (hw : 0 < w) (hscale : 16 * w ≤ R)
    (a b : Fin 8 → E) (ha : ∀ i, ‖a i‖ = R) (hb : ∀ i, ‖b i‖ = 6 * R)
    (S₀ S₁ : ℝ) (desc descPort siblings siblingPort : ℕ → (Y × (Fin 8 → E)) → ℝ)
    (e : W ≃L[ℝ] (Y × (Fin 8 → E))) :
    ∃ x : W,
      HasFDerivAt (𝕜 := ℝ)
        ((diagonalNode (scalar weight quadMap radius publicMap) S₀ S₁ R w a b
          desc descPort siblings siblingPort) ∘ e) 0 x ∧
      (∀ i, port (3 * w) (b i) ((e x).2 i) = 0) := by
  obtain ⟨U, hd, hp⟩ := diagonal_identification_has_uncertified_stationary
    weight quadMap radius publicMap hr hw hscale a b ha hb S₀ S₁
    desc descPort siblings siblingPort
  refine ⟨e.symm (0, U), ?_, ?_⟩
  · have hd' : HasFDerivAt (𝕜 := ℝ)
        (diagonalNode (scalar weight quadMap radius publicMap) S₀ S₁ R w a b
          desc descPort siblings siblingPort) 0 (e (e.symm (0, U))) := by simpa using hd
    have h := hd'.comp (e.symm (0, U)) e.toContinuousLinearMap.hasFDerivAt
    simpa only [ContinuousLinearMap.zero_comp, Function.comp_def] using h
  · simpa using hp

end GradientHessian.CommonBaseline
