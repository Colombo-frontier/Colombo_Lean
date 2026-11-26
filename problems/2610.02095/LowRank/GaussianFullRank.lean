import LowRank.GaussianQueryAlgebra
import Mathlib.Data.Matrix.Rank

/-! Actual rectangular Gaussian matrices have trivial column kernel almost
surely when there are at least as many rows as columns and variance is nonzero.
The proof inducts using the explicit one-step Gaussian revelation law. -/

namespace LowRank
open MeasureTheory
open scoped Matrix BigOperators
noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] {r s : ℕ}

theorem rotateMatrixRows_mulVec_rotated (b : OrthonormalBasis (Fin s) ℝ E)
    (e : E ≃ₗᵢ[ℝ] E) (X : Matrix (Fin r) (Fin s) ℝ) (z : Fin s → ℝ) :
    rotateMatrixRows b e X *ᵥ coordinateRotation b e z = X *ᵥ z := by
  funext i
  exact coordinateRotation_dot b e (X i) z

theorem trivial_kernel_of_reveal (b : OrthonormalBasis (Fin (s + 1)) ℝ E)
    (X : Matrix (Fin (r + 1)) (Fin (s + 1)) ℝ)
    (hρ : ‖(basisCoordinates b).symm (X 0)‖ ≠ 0)
    (hD : ∀ w, (revealGaussianBlock b X).2 *ᵥ w = 0 → w = 0) :
    ∀ z, X *ᵥ z = 0 → z = 0 := by
  intro z hz
  let U := coordinateRotation b (rowGauge b (X 0))
  have hrot : rotateMatrixRows b (rowGauge b (X 0)) X *ᵥ U z = 0 := by
    rw [rotateMatrixRows_mulVec_rotated, hz]
  have hfirst := congrFun hrot 0
  change (∑ j, coordinateRotation b (rowGauge b (X 0)) (X 0) j * U z j) = 0 at hfirst
  simp_rw [rowGauge_aligns] at hfirst
  have hzero : U z 0 = 0 := by
    have hp : ‖(basisCoordinates b).symm (X 0)‖ * U z 0 = 0 := by simpa using hfirst
    exact (mul_eq_zero.mp hp).resolve_left hρ
  have htail : (revealGaussianBlock b X).2 *ᵥ (fun j => U z j.succ) = 0 := by
    funext i
    have hi := congrFun hrot i.succ
    change (∑ j : Fin (s + 1),
      coordinateRotation b (rowGauge b (X 0)) (X i.succ) j * U z j) = 0 at hi
    rw [Fin.sum_univ_succ] at hi
    simp only [hzero, mul_zero, zero_add] at hi
    exact hi
  have htailzero := hD _ htail
  have huzero : U z = 0 := by
    funext j
    exact Fin.cases hzero (fun i => congrFun htailzero i) j
  apply U.injective
  rw [huzero, map_zero]

theorem iidMatrixLaw_trivial_kernel_ae (k s : ℕ) {v : NNReal} (hv : v ≠ 0) :
    ∀ᵐ X ∂iidMatrixLaw (k + s) s v, ∀ z, X *ᵥ z = 0 → z = 0 := by
  induction s with
  | zero => exact Filter.Eventually.of_forall (fun _ _ _ => Subsingleton.elim _ _)
  | succ s ih =>
    let b := EuclideanSpace.basisFun (Fin (s + 1)) ℝ
    have hrow : MeasurePreserving
        (fun X : Matrix (Fin (k + s + 1)) (Fin (s + 1)) ℝ => X 0)
        (iidMatrixLaw (k + s + 1) (s + 1) v) (iidVectorLaw (s + 1) v) := by
      have h := splitFirstRow_preserving (k + s) (s + 1) v
      refine ⟨h.measurable.fst, ?_⟩
      calc
        _ = ((iidMatrixLaw (k + s + 1) (s + 1) v).map (splitFirstRow (r := k + s))).map
            Prod.fst := (Measure.map_map measurable_fst h.measurable).symm
        _ = _ := by rw [h.map_eq]; simp
    have hpivot := hrow.quasiMeasurePreserving.ae (rowGauge_pivot_positive_ae b hv)
    have hres : MeasurePreserving
        (fun X : Matrix (Fin (k + s + 1)) (Fin (s + 1)) ℝ => (revealGaussianBlock b X).2)
        (iidMatrixLaw (k + s + 1) (s + 1) v) (iidMatrixLaw (k + s) s v) :=
      ⟨(revealGaussianBlock_preserving b v).measurable.snd, revealGaussianBlock_residual_law b v⟩
    have hrest := hres.quasiMeasurePreserving.ae ih
    filter_upwards [hpivot, hrest] with X hρ hD
    exact trivial_kernel_of_reveal b X (ne_of_gt hρ) hD

theorem iidMatrixLaw_mulVec_injective_ae (d s : ℕ) (hs : s ≤ d) {v : NNReal} (hv : v ≠ 0) :
    ∀ᵐ X ∂iidMatrixLaw d s v, Function.Injective (Matrix.mulVec X) := by
  have h := iidMatrixLaw_trivial_kernel_ae (d - s) s hv
  rw [Nat.sub_add_cancel hs] at h
  filter_upwards [h] with X hX
  intro z w hzw
  apply sub_eq_zero.mp
  apply hX
  rw [Matrix.mulVec_sub, hzw, sub_self]

theorem iidMatrixLaw_rank_ae (d s : ℕ) (hs : s ≤ d) {v : NNReal} (hv : v ≠ 0) :
    ∀ᵐ X ∂iidMatrixLaw d s v, X.rank = s := by
  filter_upwards [iidMatrixLaw_mulVec_injective_ae d s hs hv] with X hX
  have h := LinearMap.finrank_range_of_inj (f := X.mulVecLin) hX
  simpa [Matrix.rank] using h

theorem iidMatrixLaw_wishart_rank_ae (d s : ℕ) (hs : s ≤ d) {v : NNReal} (hv : v ≠ 0) :
    ∀ᵐ X ∂iidMatrixLaw d s v, (wishart X).rank = s := by
  filter_upwards [iidMatrixLaw_rank_ae d s hs hv] with X hX
  simpa only [wishart, Matrix.rank_self_mul_transpose] using hX

theorem gaussianMatrixLaw_wishart_rank_ae (d s : ℕ) (hd : 0 < d) (hs : s ≤ d) :
    ∀ᵐ X ∂gaussianMatrixLaw d s, (wishart X).rank = s := by
  rw [gaussianMatrixLaw_eq_iidMatrixLaw]
  apply iidMatrixLaw_wishart_rank_ae d s hs
  apply inv_ne_zero
  exact_mod_cast (Nat.ne_of_gt hd)

theorem gaussianMatrixLaw_wishart_nullity_ae (d k : ℕ) (hd : 0 < d) (hk : k ≤ d) :
    ∀ᵐ X ∂gaussianMatrixLaw d (d - k),
      Module.finrank ℝ (LinearMap.ker (wishart X).mulVecLin) = k := by
  filter_upwards [gaussianMatrixLaw_wishart_rank_ae d (d - k) hd (Nat.sub_le d k)] with X hX
  have hdim : (wishart X).rank + Module.finrank ℝ (LinearMap.ker (wishart X).mulVecLin) = d := by
    simpa [Matrix.rank] using (wishart X).mulVecLin.finrank_range_add_finrank_ker
  omega

end
end LowRank
