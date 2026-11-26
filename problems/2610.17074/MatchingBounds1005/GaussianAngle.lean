import MatchingBounds1005.GaussianBilinear
import Mathlib.Analysis.InnerProductSpace.Projection

/-! # Uniform angle bounds for actual Gaussian column spaces -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace BigOperators
open MatchingBounds1005.GaussianVector MatchingBounds1005.GaussianMatrix
open MatchingBounds1005.GaussianBilinear

namespace MatchingBounds1005.GaussianAngle

def projectedCoordinates {d : ℕ} (A : Submodule ℝ (Vec d)) :
    Vec d →L[ℝ] Vec (Module.finrank ℝ A) :=
  (stdOrthonormalBasis ℝ A).repr.toContinuousLinearMap.comp A.orthogonalProjection

theorem projectedCoordinates_norm {d : ℕ} (A : Submodule ℝ (Vec d)) (x : Vec d) :
    ‖projectedCoordinates A x‖ = ‖A.orthogonalProjection x‖ :=
  (stdOrthonormalBasis ℝ A).repr.norm_map _

theorem projectedCoordinates_norm_le {d : ℕ} (A : Submodule ℝ (Vec d)) :
    ‖projectedCoordinates A‖ ≤ 1 := by
  refine (projectedCoordinates A).opNorm_le_bound zero_le_one (fun x => ?_)
  rw [projectedCoordinates_norm]
  exact (A.orthogonalProjection.le_opNorm x).trans
    (mul_le_mul_of_nonneg_right A.orthogonalProjection_norm_le (norm_nonneg x))

def columnSpace {d k : ℕ} (a : Fin k → Vec d) : Submodule ℝ (Vec d) :=
  LinearMap.range (synthesis a).toLinearMap

/-- The deterministic singular-value argument for the angle between a
fixed active subspace and an actual linear range. -/
theorem projection_range_bound {d k : ℕ} (A : Submodule ℝ (Vec d))
    (G : Vec k →L[ℝ] Vec d) {σ M : ℝ} (hσ : 0 < σ) (hM : 0 ≤ M)
    (hmin : ∀ u, σ * ‖u‖ ≤ ‖G u‖)
    (hmax : ∀ u, ‖A.orthogonalProjection (G u)‖ ≤ M * ‖u‖)
    (x : Vec d) (hx : x ∈ A) :
    ‖(LinearMap.range G.toLinearMap).orthogonalProjection x‖ ≤ (M / σ) * ‖x‖ := by
  let R := LinearMap.range G.toLinearMap
  let p : R := R.orthogonalProjection x
  obtain ⟨u, hu⟩ := p.property
  change G u = (p : Vec d) at hu
  have hself : ⟪(p : Vec d), x⟫_ℝ = ‖p‖ ^ 2 := by
    have h := R.orthogonalProjection_inner_eq_zero x (p : Vec d) p.property
    rw [inner_sub_left] at h
    have hp : ⟪(p : Vec d), (p : Vec d)⟫_ℝ = ‖p‖ ^ 2 := real_inner_self_eq_norm_sq _
    change ⟪x, (p : Vec d)⟫_ℝ - ⟪(p : Vec d), (p : Vec d)⟫_ℝ = 0 at h
    rw [real_inner_comm] at h
    linarith
  have hip : ⟪x, G u⟫_ℝ = ‖p‖ ^ 2 := by
    rw [hu, real_inner_comm]
    exact hself
  have hp : ‖p‖ ^ 2 ≤ ‖x‖ * M * ‖u‖ := by
    calc
      _ = ⟪x, G u⟫_ℝ := hip.symm
      _ = ⟪(⟨x, hx⟩ : A), A.orthogonalProjection (G u)⟫_ℝ :=
        (A.inner_orthogonalProjection_eq_of_mem_left ⟨x, hx⟩ (G u)).symm
      _ ≤ ‖x‖ * ‖A.orthogonalProjection (G u)‖ := real_inner_le_norm _ _
      _ ≤ ‖x‖ * (M * ‖u‖) := mul_le_mul_of_nonneg_left (hmax u) (norm_nonneg x)
      _ = _ := by ring
  have hlu : σ * ‖u‖ ≤ ‖p‖ := by simpa only [hu] using hmin u
  have hbound : σ * ‖p‖ ^ 2 ≤ (M * ‖x‖) * ‖p‖ := by
    calc
      _ ≤ σ * (‖x‖ * M * ‖u‖) := mul_le_mul_of_nonneg_left hp hσ.le
      _ = (M * ‖x‖) * (σ * ‖u‖) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hlu (mul_nonneg hM (norm_nonneg x))
  change ‖p‖ ≤ (M / σ) * ‖x‖
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hσ).2
  by_cases hp0 : ‖p‖ = 0
  · rw [hp0, zero_mul]
    positivity
  · have hpp : 0 < ‖p‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hp0)
    nlinarith

theorem wellConditioned_lower {d k : ℕ} (hd : 0 < d) (a : Fin k → Vec d)
    (ha : WellConditioned a) (u : Vec k) :
    (Real.sqrt (d : ℝ) / 2) * ‖u‖ ≤ ‖synthesis a u‖ := by
  have hs : 0 < Real.sqrt (d : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hd)
  have h := ha.2 u
  have he : ‖scaledSynthesis a u‖ = (Real.sqrt (d : ℝ))⁻¹ * ‖synthesis a u‖ := by
    simp only [scaledSynthesis, ContinuousLinearMap.smul_apply, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hs)]
  rw [he] at h
  have hm := mul_le_mul_of_nonneg_left h hs.le
  rw [← mul_assoc, mul_inv_cancel₀ hs.ne', one_mul] at hm
  nlinarith

def AngleGood {d k : ℕ} (A : Submodule ℝ (Vec d)) (a : Fin k → Vec d) (η : ℝ) : Prop :=
  ∀ x ∈ A, ‖(columnSpace a).orthogonalProjection x‖ ≤ η * ‖x‖

theorem angleGood_of_matrix_bounds {d k : ℕ} (hd : 0 < d) (A : Submodule ℝ (Vec d))
    (a : Fin k → Vec d) {r : ℝ} (hr : 0 ≤ r) (ha : WellConditioned a)
    (hB : ‖(projectedCoordinates A).comp (synthesis a)‖ ≤ 2 * r) :
    AngleGood A a (4 * r / Real.sqrt (d : ℝ)) := by
  intro x hx
  have hs : 0 < Real.sqrt (d : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hd)
  have hmax (u : Vec k) : ‖A.orthogonalProjection (synthesis a u)‖ ≤ (2 * r) * ‖u‖ := by
    rw [← projectedCoordinates_norm]
    exact (((projectedCoordinates A).comp (synthesis a)).le_opNorm u).trans
      (mul_le_mul_of_nonneg_right hB (norm_nonneg u))
  have hh := projection_range_bound A (synthesis a) (by positivity : 0 < Real.sqrt (d : ℝ) / 2)
    (by positivity : 0 ≤ 2 * r) (wellConditioned_lower hd a ha) hmax x hx
  convert hh using 1
  ring

theorem angle_failure_bound {d k : ℕ} (hd : 0 < d) (A : Submodule ℝ (Vec d))
    {r : ℝ} (hr : 0 ≤ r) :
    (gaussianMatrixLaw d k).real {a | ¬ AngleGood A a (4 * r / Real.sqrt (d : ℝ))} ≤
      (17 : ℝ) ^ k * (2 * Real.exp (-(d : ℝ) / 32)) +
        (17 : ℝ) ^ (k + Module.finrank ℝ A) * (2 * Real.exp (-r ^ 2 / 2)) := by
  have hsub : {a : Fin k → Vec d | ¬ AngleGood A a (4 * r / Real.sqrt (d : ℝ))} ⊆
      {a | ¬ WellConditioned a} ∪
        {a | 2 * r < ‖(projectedCoordinates A).comp (synthesis a)‖} := by
    intro a ha
    by_cases hw : WellConditioned a
    · right
      by_contra h
      exact ha (angleGood_of_matrix_bounds hd A a hr hw (le_of_not_gt h))
    · exact Or.inl hw
  exact (measureReal_mono hsub).trans ((measureReal_union_le _ _).trans
    (add_le_add (singular_failure_bound hd)
      (projected_operator_tail (projectedCoordinates A) (projectedCoordinates_norm_le A) hr)))

/-- A uniform angle estimate with exponential failure. Both numerical
conditions are on dimensions and the desired angle, not on random geometry. -/
theorem angle_failure_exponential {d k : ℕ} (hd : 0 < d) (A : Submodule ℝ (Vec d))
    {η s : ℝ} (hη : 0 ≤ η) (hk : (k : ℝ) ≤ (d : ℝ) / 192)
    (hs : 64 * s ≤ (d : ℝ))
    (hsize : 16 * (6 * ((k + Module.finrank ℝ A : ℕ) : ℝ) + 2 * s) ≤ η ^ 2 * (d : ℝ)) :
    (gaussianMatrixLaw d k).real {a | ¬ AngleGood A a η} ≤ 4 * Real.exp (-s) := by
  let r := η * Real.sqrt (d : ℝ) / 4
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hsqrt : 0 < Real.sqrt (d : ℝ) := Real.sqrt_pos.mpr hd'
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hrsize : 6 * ((k + Module.finrank ℝ A : ℕ) : ℝ) + 2 * s ≤ r ^ 2 := by
    have he : r ^ 2 = η ^ 2 * (d : ℝ) / 16 := by
      dsimp [r]
      rw [div_pow, mul_pow, Real.sq_sqrt hd'.le]
      norm_num
    rw [he]
    linarith
  have he : 4 * r / Real.sqrt (d : ℝ) = η := by
    dsimp [r]
    field_simp
  have hsub : {a : Fin k → Vec d | ¬ AngleGood A a η} ⊆
      {a | ¬ WellConditioned a} ∪
        {a | 2 * r < ‖(projectedCoordinates A).comp (synthesis a)‖} := by
    intro a ha
    by_cases hw : WellConditioned a
    · right
      by_contra h
      have hg := angleGood_of_matrix_bounds hd A a hr hw (le_of_not_gt h)
      rw [he] at hg
      exact ha hg
    · exact Or.inl hw
  have hsing := singular_failure_exponential hd hk
  have hupper := projected_operator_exponential (projectedCoordinates A)
    (projectedCoordinates_norm_le A) hr hrsize
  have hexp : Real.exp (-(d : ℝ) / 64) ≤ Real.exp (-s) := by
    apply Real.exp_le_exp.mpr
    linarith
  exact (measureReal_mono hsub).trans ((measureReal_union_le _ _).trans
    ((add_le_add hsing hupper).trans (by nlinarith)))

/-- The high-multiplicity scaling from the manuscript, with a slightly
larger universal constant: `multiplicity * η²` only needs to dominate
the number of starts and the logarithmic confidence parameter. -/
theorem high_multiplicity_angle {d k K : ℕ} (A : Submodule ℝ (Vec d))
    (hm : 0 < Module.finrank ℝ A) (hd : d = (K + 1) * Module.finrank ℝ A)
    {η s : ℝ} (hη : 0 ≤ η) (hηhalf : η ≤ 1 / 2) (hs : 0 ≤ s)
    (hK : 96 * ((k : ℝ) + 1) + 32 * s ≤ ((K + 1 : ℕ) : ℝ) * η ^ 2) :
    (gaussianMatrixLaw d k).real {a | ¬ AngleGood A a η} ≤ 4 * Real.exp (-s) := by
  have hm' : (1 : ℝ) ≤ Module.finrank ℝ A := by exact_mod_cast hm
  have hK' : (1 : ℝ) ≤ (K + 1 : ℕ) := by exact_mod_cast Nat.succ_pos K
  have hd' : (d : ℝ) = ((K + 1 : ℕ) : ℝ) * (Module.finrank ℝ A : ℝ) := by
    exact_mod_cast hd
  have hD : ((K + 1 : ℕ) : ℝ) ≤ (d : ℝ) := by nlinarith
  have hηsq : η ^ 2 ≤ 1 / 4 := by nlinarith
  have hKmul := mul_le_mul_of_nonneg_left hηsq (by positivity : (0 : ℝ) ≤ (K + 1 : ℕ))
  have hdpos : 0 < d := by rw [hd]; exact Nat.mul_pos (Nat.succ_pos K) hm
  apply angle_failure_exponential hdpos A hη
  · nlinarith
  · nlinarith
  · have hh := mul_le_mul_of_nonneg_right hK (by positivity : (0 : ℝ) ≤ Module.finrank ℝ A)
    have hkm : 0 ≤ (k : ℝ) * ((Module.finrank ℝ A : ℝ) - 1) :=
      mul_nonneg (Nat.cast_nonneg _) (by linarith)
    have hsm : 0 ≤ s * ((Module.finrank ℝ A : ℝ) - 1) := mul_nonneg hs (by linarith)
    rw [Nat.cast_add] at *
    nlinarith [mul_nonneg hη (show (0 : ℝ) ≤ d by positivity)]

end MatchingBounds1005.GaussianAngle
