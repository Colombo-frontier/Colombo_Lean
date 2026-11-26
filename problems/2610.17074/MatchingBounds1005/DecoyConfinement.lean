import MatchingBounds1005.DecoySmoothness
import MatchingBounds1005.IsometricTransfer
import MatchingBounds1005.FiniteSmoothnessBudget

/-! The actual calibrated chain, inactive copies, Euclidean transport, tensor
masks, radial confinement, and regularizer assembled into one objective. -/
noncomputable section
open scoped InnerProductSpace ContDiff

namespace MatchingBounds1005.EpsilonCalibration
open PathGreen TensorGeometry

abbrev CalibratedCopySpace (a L t : ℝ) (K : ℕ) :=
  BlockGeometry.CopySpace
    (E := EuclideanSpace ℝ (Fin (pathEdges (pathScale a L t) + 1))) (phaseCount a t - 1) K

variable (a L t : ℝ) (ha : 0 < a) (hL : 0 < L) (ht : 0 < t)
  (hhsmall : pathScale a L t ≤ 1 / 4)
local notation "G" => geometry a L t ha hL ht hhsmall

def transportedDecoy (K : ℕ) {d : ℕ} (I : CalibratedCopySpace a L t K ≃ₗᵢ[ℝ] Vec d) : Vec d → ℝ :=
  IsometricTransfer.transport I ((G).decoyObjective (amplitude a t) (phaseCount a t - 1) K)

def transportedTail (K : ℕ) {d : ℕ} (I : CalibratedCopySpace a L t K ≃ₗᵢ[ℝ] Vec d) : Vec d :=
  I (BlockGeometry.decoyReadout (phaseCount a t - 1) K (G).a (amplitude a t)
    (Fin.last (phaseCount a t - 1)))

def confinedDecoy (K : ℕ) {d : ℕ} (I : CalibratedCopySpace a L t K ≃ₗᵢ[ℝ] Vec d)
    (T₃ : Tensor d 3) (T₄ : Tensor d 4) : Vec d → ℝ :=
  Confinement.objective
    (fun y => transportedDecoy a L t ha hL ht hhsmall K I y + mask T₃ T₄ y)
    (t ^ 3)⁻¹ (4 * (t ^ 3) ^ 2)

theorem transportedDecoy_smooth (K : ℕ) {d : ℕ}
    (I : CalibratedCopySpace a L t K ≃ₗᵢ[ℝ] Vec d) :
    ContDiff ℝ ∞ (transportedDecoy a L t ha hL ht hhsmall K I) :=
  IsometricTransfer.smooth I ((G).decoyObjective_smooth _ _ _)

theorem transportedTail_norm (K : ℕ) {d : ℕ}
    (I : CalibratedCopySpace a L t K ≃ₗᵢ[ℝ] Vec d) :
    ‖transportedTail a L t ha hL ht hhsmall K I‖ = 1 := by
  rw [transportedTail, I.norm_map]
  exact (BlockGeometry.decoyReadout_orthonormal _ _ (amplitude_pos a t ha ht)
    (suffixVector_norm (amplitude a t) (amplitude_pos a t ha ht).le _)).norm_eq_one _

theorem transportedDecoy_gap (hr : t ≤ a) (hphase : 1 ≤ phaseCount a t)
    (hsmall : 10368 * 8192 * t ^ 4 ≤ a) (K : ℕ) {d : ℕ}
    (I : CalibratedCopySpace a L t K ≃ₗᵢ[ℝ] Vec d) (y : Vec d) :
    transportedDecoy a L t ha hL ht hhsmall K I 0 -
      transportedDecoy a L t ha hL ht hhsmall K I y ≤ 1 / 4 := by
  rw [transportedDecoy, IsometricTransfer.gap]
  exact calibrated_decoy_gap a L t ha hL ht hhsmall hr hphase hsmall K (I.symm y)

theorem transportedDecoy_radial (hr : t ≤ a) (hphase : 1 ≤ phaseCount a t)
    (hsmall : 10368 * 8192 * t ^ 4 ≤ a) (K : ℕ) {d : ℕ}
    (I : CalibratedCopySpace a L t K ≃ₗᵢ[ℝ] Vec d) (y : Vec d) :
    -(81 / 256 : ℝ) ≤
      ⟪y, gradient (transportedDecoy a L t ha hL ht hhsmall K I) y⟫_ℝ := by
  rw [transportedDecoy, IsometricTransfer.radial_pairing I
    (((G).decoyObjective_smooth _ _ _).differentiable (by norm_num))]
  exact calibrated_decoy_radial a L t ha hL ht hhsmall hr hphase hsmall K (I.symm y)

theorem transportedDecoy_certificate (hr : t ≤ a) (K : ℕ) {d : ℕ}
    (I : CalibratedCopySpace a L t K ≃ₗᵢ[ℝ] Vec d) (y : Vec d)
    (hzero : ⟪transportedTail a L t ha hL ht hhsmall K I, y⟫_ℝ = 0) :
    32 * t ^ 3 ≤ ‖gradient (transportedDecoy a L t ha hL ht hhsmall K I) y‖ := by
  rw [transportedDecoy, IsometricTransfer.gradient_norm I
    (((G).decoyObjective_smooth _ _ _).differentiable (by norm_num))]
  rw [transportedTail, IsometricTransfer.readout] at hzero
  exact calibrated_decoy_normalized_gradient a L t ha hL ht hhsmall hr _ K (I.symm y) hzero

theorem transportedDecoy_firstjet (hr : t ≤ a) (hpath : pathScale a L t ≤ 1 / 37)
    (K : ℕ) {d : ℕ} (I : CalibratedCopySpace a L t K ≃ₗᵢ[ℝ] Vec d) :
    ‖iteratedFDeriv ℝ 1 (transportedDecoy a L t ha hL ht hhsmall K I) 0‖ ≤ 16 * L := by
  rw [transportedDecoy, IsometricTransfer.jet_norm I ((G).decoyObjective_smooth _ _ _), map_zero]
  exact calibrated_decoy_firstjet a L t ha hL ht hhsmall hr hpath _ K

variable (p : ℕ) (C : ℝ) (hC : 0 ≤ C)
  (hprim : ∀ q, 1 ≤ q → q ≤ p → ∀ r, 1 ≤ r → ∀ u,
    |iteratedDeriv (q + 1) (Primitive.potential r) u| ≤ C * r ^ 3 / r ^ q)
  (hbudget : 18 * 8192 * C * a ^ 3 ≤ 4 * L)
  (hr : t ≤ a) (hpath : pathScale a L t ≤ 1 / 37)

include C hC hprim hbudget hr hpath

theorem transportedDecoy_jet (q : ℕ) (hq : 1 ≤ q) (hqp : q ≤ p)
    (K : ℕ) {d : ℕ} (I : CalibratedCopySpace a L t K ≃ₗᵢ[ℝ] Vec d) (y : Vec d) :
    ‖iteratedFDeriv ℝ (q + 1) (transportedDecoy a L t ha hL ht hhsmall K I) y‖ ≤ 16 * L := by
  rw [transportedDecoy, IsometricTransfer.jet_norm I ((G).decoyObjective_smooth _ _ _)]
  exact calibrated_decoy_jet_bound a L t ha hL ht hhsmall p C hC hprim hbudget hr hpath
    q hq hqp _ K (I.symm y)

theorem transportedDecoy_lipschitz (hp : 1 ≤ p) (K : ℕ) {d : ℕ}
    (I : CalibratedCopySpace a L t K ≃ₗᵢ[ℝ] Vec d) (x y : Vec d) :
    ‖gradient (transportedDecoy a L t ha hL ht hhsmall K I) x -
      gradient (transportedDecoy a L t ha hL ht hhsmall K I) y‖ ≤ 16 * L * ‖x - y‖ :=
  gradient_lipschitz_of_hessian_bound (transportedDecoy_smooth a L t ha hL ht hhsmall K I)
    (transportedDecoy_jet a L t ha hL ht hhsmall p C hC hprim hbudget hr hpath 1 le_rfl hp K I) y x

/-- No analytic hypotheses about the base objective remain: the source
stationarity certificate is instantiated with the actual calibrated chain. -/
theorem confinedDecoy_stationarity (hp : 1 ≤ p) (hphase : 1 ≤ phaseCount a t)
    (hsmall : 10368 * 8192 * t ^ 4 ≤ a) (K : ℕ) {d : ℕ}
    (I : CalibratedCopySpace a L t K ≃ₗᵢ[ℝ] Vec d)
    (T₃ : Tensor d 3) (T₄ : Tensor d 4)
    (h3 : ‖tensorForm T₃‖ ≤ (t ^ 3) ^ 3 / 8)
    (h4 : ‖tensorForm T₄‖ ≤ (t ^ 3) ^ 4 / 8) (x : Vec d)
    (hread : |⟪transportedTail a L t ha hL ht hhsmall K I, radial (t ^ 3)⁻¹ x⟫_ℝ| ≤
      16 * t ^ 3 / (16 * L)) :
    t ^ 3 < ‖gradient (confinedDecoy a L t ha hL ht hhsmall K I T₃ T₄) x‖ := by
  exact source_confined_stationarity (transportedDecoy a L t ha hL ht hhsmall K I)
    T₃ T₄ (transportedTail a L t ha hL ht hhsmall K I) x
    ((transportedDecoy_smooth a L t ha hL ht hhsmall K I).differentiable (by norm_num))
    (pow_pos ht 3) (transportedTail_norm a L t ha hL ht hhsmall K I) (by positivity)
    (transportedDecoy_lipschitz a L t ha hL ht hhsmall p C hC hprim hbudget hr hpath hp K I)
    (transportedDecoy_certificate a L t ha hL ht hhsmall hr K I)
    (transportedDecoy_radial a L t ha hL ht hhsmall hr hphase hsmall K I) h3 h4 hread

/-- Explicit finite-order scalar budgets imply membership in the manuscript's
smooth function class for the actual masked and confined decoy objective. -/
theorem confinedDecoy_inFunctionClass (hphase : 1 ≤ phaseCount a t)
    (hsmall : 10368 * 8192 * t ^ 4 ≤ a)
    (hbase : 16 * L ≤ RadialHigher.baseBudget p)
    (haccuracy : t ^ 3 ≤ RadialHigher.accuracyThreshold p)
    (K : ℕ) {d : ℕ} (I : CalibratedCopySpace a L t K ≃ₗᵢ[ℝ] Vec d)
    (T₃ : Tensor d 3) (T₄ : Tensor d 4)
    (h3 : ‖tensorForm T₃‖ ≤ (t ^ 3) ^ 3 / 8)
    (h4 : ‖tensorForm T₄‖ ≤ (t ^ 3) ^ 4 / 8) :
    Model.InFunctionClass p (confinedDecoy a L t ha hL ht hhsmall K I T₃ T₄) := by
  apply source_confined_class (transportedDecoy_smooth a L t ha hL ht hhsmall K I)
    T₃ T₄ (pow_pos ht 3) haccuracy
  · exact (transportedDecoy_firstjet a L t ha hL ht hhsmall hr hpath K I).trans hbase
  · intro q hq hqp y
    exact (transportedDecoy_jet a L t ha hL ht hhsmall p C hC hprim hbudget hr hpath q hq hqp K I y).trans hbase
  · exact transportedDecoy_gap a L t ha hL ht hhsmall hr hphase hsmall K I
  · exact h3
  · exact h4

end MatchingBounds1005.EpsilonCalibration
