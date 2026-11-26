import NCConcave16991.DenseSmoothSmoothness
import NCConcave16991.DenseSmoothGradient
import NCConcave16991.SmoothProblemEmbedding

/-! # The actual smooth finite sum and its singleton-dual optimization problem -/

noncomputable section

namespace NCConcave16991.DenseSmooth

open Set
open scoped BigOperators InnerProductSpace ContDiff

set_option maxHeartbeats 900000
set_option synthInstance.maxSize 2048
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 4
set_option backward.isDefEq.respectTransparency false

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] (T : ℕ)

abbrev primalDimension := Module.finrank ℝ (Blocks E T)

def primalCoordinates : Blocks E T ≃ₗᵢ[ℝ] PrimalSpace (primalDimension E T) :=
  (stdOrthonormalBasis ℝ (Blocks E T)).repr

variable {E T} {n : ℕ}

def parameters (hn : 0 < n) {ρ : ℝ} (hρ : 0 < ρ) (T : ℕ) : ProblemParameters where
  n := n
  n_pos := hn
  L := smoothnessConstant / ρ
  L_pos := div_pos smoothnessConstant_pos hρ
  gap := 2 * (T + 1 : ℕ)
  gap_pos := by positivity
  epsilon := 1 / 1000
  epsilon_pos := by norm_num
  diameter := 0
  diameter_nonneg := le_rfl

def flatComponent (ρ : ℝ) (u : Fin (T + 1) → E) (rows : Fin n → Fin (T + 1) → E)
    (i : Fin n) (x : PrimalSpace (primalDimension E T)) : ℝ :=
  componentChain ρ u rows i ((primalCoordinates E T).symm x)

def flatMean (u : Fin (T + 1) → E) (x : PrimalSpace (primalDimension E T)) : ℝ :=
  meanChain u ((primalCoordinates E T).symm x)

theorem flatComponent_contDiff (ρ : ℝ) (u : Fin (T + 1) → E)
    (rows : Fin n → Fin (T + 1) → E) (i : Fin n) : ContDiff ℝ ∞ (flatComponent ρ u rows i) :=
  (componentChain_contDiff ρ u rows i).comp (primalCoordinates E T).symm.toContinuousLinearEquiv.contDiff

theorem flatComponent_gradient_sub_bound {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (u : Fin (T + 1) → E) (hu : ∀ j, ‖u j‖ = 1)
    (rows : Fin n → Fin (T + 1) → E) (hr : ∀ i j, ‖rows i j‖ = 1)
    (i : Fin n) (x y : PrimalSpace (primalDimension E T)) :
    ‖gradient (flatComponent ρ u rows i) x - gradient (flatComponent ρ u rows i) y‖ ≤
      (smoothnessConstant / ρ) * ‖x - y‖ := by
  rw [← (InnerProductSpace.toDual ℝ (PrimalSpace (primalDimension E T))).norm_map,
    map_sub, toDual_gradient, toDual_gradient]
  let e := (primalCoordinates E T).symm.toContinuousLinearEquiv.toContinuousLinearMap
  have hd (z : PrimalSpace (primalDimension E T)) :
      fderiv ℝ (flatComponent ρ u rows i) z =
        (fderiv ℝ (componentChain ρ u rows i) ((primalCoordinates E T).symm z)).comp e :=
    (((componentChain_contDiff ρ u rows i).differentiable (by simp) _).hasFDerivAt.comp z
      (primalCoordinates E T).symm.toContinuousLinearEquiv.hasFDerivAt).fderiv
  rw [hd, hd, ← ContinuousLinearMap.sub_comp]
  have he : ‖e‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
    intro z
    exact ((primalCoordinates E T).symm.norm_map z).le.trans_eq (one_mul _).symm
  have hb := componentChain_fderiv_sub_bound hρ hρ1 u hu rows hr i
    ((primalCoordinates E T).symm x) ((primalCoordinates E T).symm y)
  rw [← map_sub, LinearIsometryEquiv.norm_map] at hb
  exact ((fderiv ℝ (componentChain ρ u rows i) ((primalCoordinates E T).symm x) -
      fderiv ℝ (componentChain ρ u rows i) ((primalCoordinates E T).symm y)).opNorm_comp_le e).trans
    ((mul_le_mul hb he (norm_nonneg _) (mul_nonneg (div_pos smoothnessConstant_pos hρ).le (norm_nonneg _))).trans_eq (mul_one _))

theorem flat_average (hn : 0 < n) {ρ : ℝ} (hρ : ρ ≠ 0) (A : Table E n T ρ)
    (x : PrimalSpace (primalDimension E T)) :
    smoothSumAverage (flatComponent ρ A.direction A.row) x = flatMean A.direction x := by
  letI : NeZero n := ⟨hn.ne'⟩
  have hh := componentChain_average hρ A.direction A.row A.row_sum ((primalCoordinates E T).symm x)
  simpa only [smoothSumAverage, flatComponent, flatMean, div_eq_mul_inv, mul_comm] using hh

def finiteSum (hn : 0 < n) {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (A : Table E n T ρ) :
    SmoothFiniteSum (parameters hn hρ T) (primalDimension E T) where
  component := flatComponent ρ A.direction A.row
  componentGradient := fun i ↦ gradient (flatComponent ρ A.direction A.row i)
  gradient_correct := fun i x ↦ ((flatComponent_contDiff ρ A.direction A.row i).differentiable (by simp) x).hasGradientAt
  individualSmooth := flatComponent_gradient_sub_bound hρ hρ1 A.direction A.direction_unit A.row A.row_unit
  initialPoint := 0
  boundedBelow := ⟨-2 * (T + 1 : ℕ), by
    rintro z ⟨x, rfl⟩
    rw [flat_average hn hρ.ne']
    exact meanChain_lower A.direction A.direction_unit _⟩
  initialGap := by
    have hne : (range (smoothSumAverage (flatComponent ρ A.direction A.row))).Nonempty := range_nonempty _
    have hl := le_csInf hne (show ∀ z ∈ range (smoothSumAverage (flatComponent ρ A.direction A.row)),
        -2 * (T + 1 : ℕ) ≤ z by
      rintro z ⟨x, rfl⟩
      rw [flat_average hn hρ.ne']
      exact meanChain_lower A.direction A.direction_unit _)
    rw [flat_average hn hρ.ne']
    change meanChain A.direction ((primalCoordinates E T).symm 0) - _ ≤ _
    rw [map_zero, meanChain_zero]
    change (0 : ℝ) - _ ≤ (2 : ℝ) * (T + 1 : ℕ)
    linarith

theorem flatMean_hasGradientAt (u : Fin (T + 1) → E) (x : PrimalSpace (primalDimension E T)) :
    HasGradientAt (flatMean u) ((primalCoordinates E T) (meanGradient u ((primalCoordinates E T).symm x))) x := by
  rw [hasGradientAt_iff_hasFDerivAt]
  have hh := (meanChain_hasFDerivAt u ((primalCoordinates E T).symm x)).comp x
    (primalCoordinates E T).symm.toContinuousLinearEquiv.hasFDerivAt
  convert hh using 1
  · rfl
  · ext h
    change ⟪(primalCoordinates E T) (meanGradient u ((primalCoordinates E T).symm x)), h⟫_ℝ =
      ⟪meanGradient u ((primalCoordinates E T).symm x), (primalCoordinates E T).symm h⟫_ℝ
    simpa only [LinearIsometryEquiv.apply_symm_apply] using
      ((primalCoordinates E T).inner_map_map (meanGradient u ((primalCoordinates E T).symm x)) ((primalCoordinates E T).symm h))

theorem stationary_all_stages (hn : 0 < n) {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (A : Table E n T ρ) (x : PrimalSpace (primalDimension E T))
    (hx : StationaryOutput (finiteSum hn hρ hρ1 A).toProblem x) :
    ∀ j, 9 / 32 ≤ coordinate A.direction ((primalCoordinates E T).symm x) j := by
  have hh := (finiteSum hn hρ hρ1 A).stationary_implies_direct_gradient x hx
  have he : smoothSumAverage (finiteSum hn hρ hρ1 A).component = flatMean A.direction :=
    funext (flat_average hn hρ.ne' A)
  rw [he, (flatMean_hasGradientAt A.direction x).gradient, LinearIsometryEquiv.norm_map] at hh
  intro j
  by_contra hj
  have hb := unfinished_gradient_barrier A.direction A.direction_unit ((primalCoordinates E T).symm x)
    ⟨j, lt_of_not_ge hj⟩
  rw [(meanChain_hasGradientAt A.direction _).gradient] at hb
  change ‖meanGradient A.direction ((primalCoordinates E T).symm x)‖ ≤ (3 / 2 : ℝ) * (1 / 1000) at hh
  linarith

end NCConcave16991.DenseSmooth
