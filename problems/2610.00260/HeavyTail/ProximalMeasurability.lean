import HeavyTail.ProximalSearch
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-! Nonexpansiveness is derived from the public proximal minimization contract.
It makes the actual finite halving search and its selected query measurable. -/
noncomputable section
open Set MeasureTheory
open scoped InnerProductSpace
namespace HeavyTail
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem proximalOracle_firm {S : Set E} {h : E → ℝ} {η : ℝ}
    (P : ProximalOracle S h) (hh : ConvexOn ℝ S h) (hη : 0 < η) (z w : E) :
    ‖P.point η z - P.point η w‖ ^ 2 ≤ ⟪z - w, P.point η z - P.point η w⟫_ℝ := by
  have hz := proximalOracle_subgradient P hh hη z (P.point η w) (P.feasible η hη w)
  have hw := proximalOracle_subgradient P hh hη w (P.point η z) (P.feasible η hη z)
  have hid :
      ⟪η⁻¹ • (z - P.point η z), P.point η z - P.point η w⟫_ℝ +
      ⟪η⁻¹ • (w - P.point η w), P.point η w - P.point η z⟫_ℝ =
      η⁻¹ * (⟪z - w, P.point η z - P.point η w⟫_ℝ - ‖P.point η z - P.point η w‖ ^ 2) := by
    simp only [real_inner_smul_left, inner_sub_left, inner_sub_right,
      norm_sub_sq_real, real_inner_self_eq_norm_sq]
    rw [real_inner_comm (P.point η w) (P.point η z)]
    ring
  have hp : η⁻¹ * 0 ≤
      η⁻¹ * (⟪z - w, P.point η z - P.point η w⟫_ℝ - ‖P.point η z - P.point η w‖ ^ 2) := by
    rw [← hid]
    linarith only [hz, hw]
  exact sub_nonneg.mp ((mul_le_mul_left (inv_pos.mpr hη)).mp hp)

theorem proximalOracle_nonexpansive {S : Set E} {h : E → ℝ} {η : ℝ}
    (P : ProximalOracle S h) (hh : ConvexOn ℝ S h) (hη : 0 < η) (z w : E) :
    ‖P.point η z - P.point η w‖ ≤ ‖z - w‖ := by
  have h := (proximalOracle_firm P hh hη z w).trans (real_inner_le_norm _ _)
  by_contra hn
  have hgt := lt_of_not_ge hn
  have hp : 0 < ‖P.point η z - P.point η w‖ := (norm_nonneg (z - w)).trans_lt hgt
  have hprod := mul_pos (sub_pos.mpr hgt) hp
  nlinarith only [h, hprod]

theorem proximalOracle_lipschitz {S : Set E} {h : E → ℝ} {η : ℝ}
    (P : ProximalOracle S h) (hh : ConvexOn ℝ S h) (hη : 0 < η) :
    LipschitzWith 1 (P.point η) := by
  apply LipschitzWith.of_dist_le_mul
  intro z w
  simpa only [dist_eq_norm, NNReal.coe_one, one_mul] using proximalOracle_nonexpansive P hh hη z w

theorem proximalCorrection_continuous {S : Set E} {h : E → ℝ} {η : ℝ}
    (P : ProximalOracle S h) (hh : ConvexOn ℝ S h) (hη : 0 < η) :
    Continuous (proximalCorrection P η) := by
  exact continuous_const.smul (continuous_id.sub (proximalOracle_lipschitz P hh hη).continuous)

def proximalHalvingCondition {S : Set E} {h : E → ℝ} (P : ProximalOracle S h)
    (G R : ℝ) (n k : ℕ) (z : E) : Prop :=
  k ≤ Nat.clog 2 (2 * n) ∧
    (G ≤ ‖proximalCorrection P (proximalScale G R k) z‖ ∨
      proximalScale G R k ≤ R / (G * n))

theorem proximalHalving_exists {S : Set E} {h : E → ℝ} (P : ProximalOracle S h)
    {G R : ℝ} {n : ℕ} (hG : 0 < G) (hR : 0 < R) (hn : 0 < n) (z : E) :
    ∃ k, proximalHalvingCondition P G R n k z :=
  ⟨Nat.clog 2 (2 * n), le_rfl, Or.inr (proximalScale_deadline hG hR hn)⟩

def proximalHalvingIndex {S : Set E} {h : E → ℝ} (P : ProximalOracle S h)
    {G R : ℝ} {n : ℕ} (hG : 0 < G) (hR : 0 < R) (hn : 0 < n) (z : E) : ℕ := by
  classical
  exact Nat.find (proximalHalving_exists P hG hR hn z)

def selectedProximalPoint {S : Set E} {h : E → ℝ} (P : ProximalOracle S h)
    {G R : ℝ} {n : ℕ} (hG : 0 < G) (hR : 0 < R) (hn : 0 < n) (z : E) : E :=
  P.point (proximalScale G R (proximalHalvingIndex P hG hR hn z)) z

def selectedProximalCorrection {S : Set E} {h : E → ℝ} (P : ProximalOracle S h)
    {G R : ℝ} {n : ℕ} (hG : 0 < G) (hR : 0 < R) (hn : 0 < n) (z : E) : E :=
  proximalCorrection P (proximalScale G R (proximalHalvingIndex P hG hR hn z)) z

section Measurable
variable [MeasurableSpace E] [BorelSpace E]

theorem proximalHalvingCondition_measurable {S : Set E} {h : E → ℝ}
    (P : ProximalOracle S h) (hh : ConvexOn ℝ S h) {G R : ℝ} (n k : ℕ)
    (hG : 0 < G) (hR : 0 < R) :
    MeasurableSet {z | proximalHalvingCondition P G R n k z} := by
  have hc := (proximalCorrection_continuous P hh (proximalScale_pos hG hR k)).norm.measurable
  exact MeasurableSet.inter (MeasurableSet.const _) ((measurableSet_le measurable_const hc).union
    (MeasurableSet.const _))

theorem proximalHalvingIndex_measurable {S : Set E} {h : E → ℝ}
    (P : ProximalOracle S h) (hh : ConvexOn ℝ S h) {G R : ℝ} {n : ℕ}
    (hG : 0 < G) (hR : 0 < R) (hn : 0 < n) :
    Measurable (proximalHalvingIndex P hG hR hn) := by
  classical
  exact measurable_find (proximalHalving_exists P hG hR hn)
    (fun k => proximalHalvingCondition_measurable P hh n k hG hR)

theorem selectedProximalPoint_measurable {S : Set E} {h : E → ℝ}
    (P : ProximalOracle S h) (hh : ConvexOn ℝ S h) {G R : ℝ} {n : ℕ}
    (hG : 0 < G) (hR : 0 < R) (hn : 0 < n) :
    Measurable (selectedProximalPoint P hG hR hn) := by
  classical
  exact Measurable.find (fun k => (proximalOracle_lipschitz P hh (proximalScale_pos hG hR k)).continuous.measurable)
    (fun k => proximalHalvingCondition_measurable P hh n k hG hR) (proximalHalving_exists P hG hR hn)

theorem selectedProximalCorrection_measurable {S : Set E} {h : E → ℝ}
    (P : ProximalOracle S h) (hh : ConvexOn ℝ S h) {G R : ℝ} {n : ℕ}
    (hG : 0 < G) (hR : 0 < R) (hn : 0 < n) :
    Measurable (selectedProximalCorrection P hG hR hn) := by
  classical
  exact Measurable.find (fun k => (proximalCorrection_continuous P hh (proximalScale_pos hG hR k)).measurable)
    (fun k => proximalHalvingCondition_measurable P hh n k hG hR) (proximalHalving_exists P hG hR hn)

end Measurable

theorem proximalHalvingIndex_spec {S : Set E} {h : E → ℝ} (P : ProximalOracle S h)
    {G R : ℝ} {n : ℕ} (hG : 0 < G) (hR : 0 < R) (hn : 0 < n) (z : E) :
    proximalHalvingCondition P G R n (proximalHalvingIndex P hG hR hn z) z := by
  classical
  exact Nat.find_spec (proximalHalving_exists P hG hR hn z)

theorem selectedProximalPoint_feasible {S : Set E} {h : E → ℝ} (P : ProximalOracle S h)
    {G R : ℝ} {n : ℕ} (hG : 0 < G) (hR : 0 < R) (hn : 0 < n) (z : E) :
    selectedProximalPoint P hG hR hn z ∈ S :=
  P.feasible _ (proximalScale_pos hG hR _) z

theorem selectedProximalCorrection_bound {S : Set E} {h : E → ℝ} {G R : ℝ} {n : ℕ}
    (P : ProximalOracle S h) (hG : 0 < G) (hR : 0 < R) (hn : 0 < n)
    (z xstar : E) (hx : xstar ∈ S) (hz : ‖z - xstar‖ ≤ 2 * R)
    (hlower : ∀ u ∈ S, h xstar - G * ‖u - xstar‖ ≤ h u) :
    ‖selectedProximalCorrection P hG hR hn z‖ ≤ 3 * G := by
  classical
  let k := proximalHalvingIndex P hG hR hn z
  have hk := proximalHalvingIndex_spec P hG hR hn z
  change k ≤ Nat.clog 2 (2 * n) ∧ _ at hk
  change ‖proximalCorrection P (proximalScale G R k) z‖ ≤ 3 * G
  cases hkind : k with
  | zero => exact proximalCorrection_initial_bound P hG hR z xstar hx hz hlower
  | succ j =>
      have hj : j < k := by omega
      have hmin : ¬proximalHalvingCondition P G R n j z :=
        Nat.find_min (proximalHalving_exists P hG hR hn z) hj
      have hsmall : ‖proximalCorrection P (proximalScale G R j) z‖ < G := by
        apply lt_of_not_ge
        intro hg
        exact hmin ⟨by omega, Or.inl hg⟩
      rw [proximalScale_succ]
      have hd := proximalCorrection_halving P (proximalScale_pos hG hR j) z
      linarith only [hd, hsmall, hG]

theorem selectedProximalCorrection_identity {S : Set E} {h : E → ℝ} (P : ProximalOracle S h)
    {G R : ℝ} {n : ℕ} (hG : 0 < G) (hR : 0 < R) (hn : 0 < n) (z : E) :
    z - selectedProximalPoint P hG hR hn z =
      proximalScale G R (proximalHalvingIndex P hG hR hn z) • selectedProximalCorrection P hG hR hn z := by
  simp only [selectedProximalPoint, selectedProximalCorrection, proximalCorrection, smul_smul,
    mul_inv_cancel₀ (proximalScale_pos hG hR _).ne', one_smul]

theorem selectedProximalCorrection_subgradient {S : Set E} {h : E → ℝ}
    (P : ProximalOracle S h) (hh : ConvexOn ℝ S h) {G R : ℝ} {n : ℕ}
    (hG : 0 < G) (hR : 0 < R) (hn : 0 < n) (z u : E) (hu : u ∈ S) :
    h (selectedProximalPoint P hG hR hn z) - h u ≤
      ⟪selectedProximalCorrection P hG hR hn z, selectedProximalPoint P hG hR hn z - u⟫_ℝ :=
  proximalOracle_subgradient P hh (proximalScale_pos hG hR _) z u hu

end HeavyTail
