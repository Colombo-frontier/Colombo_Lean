import MatchingBounds1005.OracleMeasurability
import MatchingBounds1005.IsometricTransfer
import MatchingBounds1005.Radial
import MatchingBounds1005.ReadoutPrefixEvent

/-! The finite measurable trace of every actual confined query and the
unqueried candidate, reconstructed only from rotation, private seed and
retained oracle responses. -/
noncomputable section
open MeasureTheory RandomizedFO2003.Rotations
open scoped InnerProductSpace ContDiff

namespace MatchingBounds1005.Model
open ScheduledPrefix
variable {Seed : Type} [MeasurableSpace Seed] {d : ℕ}

def queryTrace (R : ℝ) (A : Algorithm d Seed) (T : ℕ)
    (z : Seed × (Fin T → Response d)) : Fin (T + 1) → Space d :=
  Fin.snoc (fun j => radial R (A.query j.val z.1 (fun i => z.2 ⟨i.val, i.isLt.trans j.isLt⟩)))
    (radial R (A.output T z.1 z.2))

theorem queryTrace_query (R : ℝ) (A : Algorithm d Seed) (T : ℕ)
    (z : Seed × (Fin T → Response d)) (j : Fin T) :
    queryTrace R A T z j.castSucc =
      radial R (A.query j.val z.1 (fun i => z.2 ⟨i.val, i.isLt.trans j.isLt⟩)) :=
  Fin.snoc_castSucc _ _ _

theorem queryTrace_output (R : ℝ) (A : Algorithm d Seed) (T : ℕ)
    (z : Seed × (Fin T → Response d)) :
    queryTrace R A T z (Fin.last T) = radial R (A.output T z.1 z.2) := Fin.snoc_last _ _

theorem queryTrace_measurable (R : ℝ) (A : Algorithm d Seed) (T : ℕ) :
    Measurable (queryTrace R A T) := by
  apply measurable_pi_lambda
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simpa only [queryTrace_output] using
      (radial_contDiff (E := Space d) R ∞).continuous.measurable.comp (A.output_measurable T)
  · have hp : Measurable (fun z : Seed × (Fin T → Response d) =>
        fun i : Fin j.val => z.2 ⟨i.val, i.isLt.trans j.isLt⟩) := by
      apply measurable_pi_lambda
      intro i
      exact (measurable_pi_apply (⟨i.val, i.isLt.trans j.isLt⟩ : Fin T)).comp measurable_snd
    simpa only [queryTrace_query] using
      (radial_contDiff (E := Space d) R ∞).continuous.measurable.comp
        ((A.query_measurable j.val).comp (measurable_fst.prodMk hp))

def canonicalQueryTrace (R : ℝ) (A : Algorithm d Seed) (T : ℕ)
    (z : (Rotation (Space d) × Seed) × (Fin T → Response d)) : Fin (T + 1) → Space d :=
  fun i => (isometry _ z.1.1).symm (queryTrace R A T (z.1.2, z.2) i)

attribute [local irreducible] RandomizedFO2003.Rotations.isometry queryTrace

theorem canonicalQueryTrace_measurable (R : ℝ) (A : Algorithm d Seed) (T : ℕ) :
    Measurable (canonicalQueryTrace R A T) := by
  apply measurable_pi_lambda
  intro i
  have hp : Measurable (fun z : (Rotation (Space d) × Seed) × (Fin T → Response d) =>
      (z.1.2, z.2)) := measurable_fst.snd.prodMk measurable_snd
  have hq : Measurable (fun z : (Rotation (Space d) × Seed) × (Fin T → Response d) =>
      queryTrace R A T (z.1.2, z.2) i) :=
    (measurable_pi_apply i).comp ((queryTrace_measurable R A T).comp hp)
  have hi : Measurable (fun z : Rotation (Space d) × Space d => (isometry _ z.1).symm z.2) :=
    (IsometricTransfer.continuous_inverse_action (E := Space d)).measurable
  have hrot : Measurable (fun z : (Rotation (Space d) × Seed) × (Fin T → Response d) =>
      z.1.1) := measurable_fst.fst
  exact hi.comp (hrot.prodMk hq)

theorem queryTrace_norm_lt {R : ℝ} (hR : 0 < R) (A : Algorithm d Seed) (T : ℕ)
    (z : Seed × (Fin T → Response d)) (i : Fin (T + 1)) : ‖queryTrace R A T z i‖ < R := by
  refine Fin.lastCases ?_ (fun j => ?_) i
  · rw [queryTrace_output]
    exact radial_norm_lt hR _
  · rw [queryTrace_query]
    exact radial_norm_lt hR _

theorem canonicalQueryTrace_norm_lt {R : ℝ} (hR : 0 < R) (A : Algorithm d Seed) (T : ℕ)
    (z : (Rotation (Space d) × Seed) × (Fin T → Response d)) (i : Fin (T + 1)) :
    ‖canonicalQueryTrace R A T z i‖ < R := by
  rw [canonicalQueryTrace, LinearIsometryEquiv.norm_map]
  exact queryTrace_norm_lt hR A T _ i

def geometryEvent {ι : Type*} (R : ℝ) (A : Algorithm d Seed) (T : ℕ)
    (b : ι → Space d) (ell : ι → ℕ) (θ : ℝ) :=
  canonicalQueryTrace R A T ⁻¹' readoutEvent b ell θ

theorem geometryEvent_measurable {ι : Type*} (R : ℝ) (A : Algorithm d Seed) (T : ℕ)
    (b : ι → Space d) (ell : ι → ℕ) (θ : ℝ) : MeasurableSet (geometryEvent R A T b ell θ) :=
  (measurableSet_readoutEvent b ell θ).preimage (canonicalQueryTrace_measurable R A T)

theorem geometryEvent_physical_readout {ι : Type*} {R θ : ℝ} (hR : 0 < R) (hθ : 0 ≤ θ)
    (A : Algorithm d Seed) (T : ℕ) (b : ι → Space d) (ell : ι → ℕ)
    (z : (Rotation (Space d) × Seed) × (Fin T → Response d))
    (hz : z ∈ geometryEvent R A T b ell θ) (s : ι) (i : Fin (T + 1)) (hi : i.val < ell s) :
    |⟪isometry _ z.1.1 (b s), queryTrace R A T (z.1.2, z.2) i⟫_ℝ| ≤ θ * ‖b s‖ * R := by
  rw [(isometry _ z.1.1).inner_map_eq_flip]
  exact (readoutEvent_coordinate hz s i hi).trans
    (mul_le_mul_of_nonneg_left (canonicalQueryTrace_norm_lt hR A T z i).le
      (mul_nonneg hθ (norm_nonneg _)))

end MatchingBounds1005.Model
