import MinimaxAudit.HardInstance
import MinimaxAudit.Deterministic
import MinimaxAudit.SourcePotential

/-! Shared exact oracle lower-bound scales and scalar-potential identity. -/
namespace MinimaxAudit

/-- The concrete potential used in transcript construction is exactly the
concrete potential whose analytic admissibility has been proved. -/
theorem deterministic_potential_eq {N dx dy : ℕ} (profile : GateProfile)
    (tau lam c q : ℝ) {U : Fin (N + 1) → Primal dx} {V : Fin (N + 1) → Dual dy}
    (hU : Orthonormal ℝ U) (hV : Orthonormal ℝ V) :
    Deterministic.hardPotential profile tau lam c q U V =
      minimaxHardPotential profile tau lam q c hU hV := by
  unfold Deterministic.hardPotential
  change chainPotential profile tau lam c q Deterministic.publicQuadratic (pairedA U V) (pairedB U V) = _
  rw [source_chainPotential_eq_block profile tau lam q c Deterministic.publicQuadratic hU hV]
  funext z
  have hi := join_blocks_inner (primalBlock z) (primalBlock z) (-dualBlock z) (dualBlock z)
  rw [join_blocks z, ← saddle_sign_blocks] at hi
  simp only [inner_neg_left, real_inner_self_eq_norm_sq] at hi
  change lam * (Deterministic.publicQuadratic z - _) = lam * (signedQuadratic _ z - _)
  unfold Deterministic.publicQuadratic signedQuadratic
  rw [hi]
  ring

noncomputable def oracleRateExponent (p : ℕ) : ℝ := (3 * (p : ℝ) - 1) / 2

noncomputable def tangentRateConstant (profile : GateProfile) (p : ℕ) : ℝ :=
  geometryEta ^ (p - 1) * geometryKappa ^ p /
    (2 * chainSmoothnessConstant p profile * (2 * Real.sqrt 2) ^ p)

noncomputable def gapRateConstant (profile : GateProfile) (p : ℕ) : ℝ :=
  geometryEta ^ (p - 1) * geometryKappa ^ (p + 1) /
    (16 * chainSmoothnessConstant p profile * (2 * Real.sqrt 2) ^ (p + 1))

theorem tangentRateConstant_pos (profile : GateProfile) (p : ℕ) :
    0 < tangentRateConstant profile p := by
  unfold tangentRateConstant geometryEta geometryKappa
  exact div_pos (by positivity)
    (mul_pos (mul_pos (by norm_num) (chainSmoothnessConstant_pos p profile)) (by positivity))

theorem gapRateConstant_pos (profile : GateProfile) (p : ℕ) :
    0 < gapRateConstant profile p := by
  unfold gapRateConstant geometryEta geometryKappa
  exact div_pos (by positivity)
    (mul_pos (mul_pos (by norm_num) (chainSmoothnessConstant_pos p profile)) (by positivity))

/-- Exact n^(-3/2) gate-width expression. -/
theorem hard_width_sqrt_form (N : ℕ) (R : ℝ) :
    hardGateWidth N R = geometryEta * geometryKappa * R / (Real.sqrt (N + 1)) ^ 3 := by
  let s := Real.sqrt (N + 1 : ℝ)
  have hs : 0 < s := Real.sqrt_pos.mpr (by positivity)
  have hsquare : s ^ 2 = (N + 1 : ℝ) := Real.sq_sqrt (by positivity)
  change geometryEta * (geometryKappa * R / s) / (N + 1 : ℝ) =
    geometryEta * geometryKappa * R / s ^ 3
  rw [← hsquare]
  field_simp

/-- Radius-normalized actual tangent obstruction scale. -/
theorem hard_tangent_scale_radius (profile : GateProfile) {p : ℕ} (hp : 2 ≤ p)
    (N : ℕ) (L R : ℝ) :
    hardAmplitude profile p N L R * hardSeed N R / (2 * Real.sqrt (N + 1)) =
      L * geometryEta ^ (p - 1) * geometryKappa ^ p * R ^ p /
        (2 * chainSmoothnessConstant p profile * (N + 1 : ℝ) ^ oracleRateExponent p) := by
  have hs : Real.sqrt (N + 1 : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by positivity))
  have hC := ne_of_gt (chainSmoothnessConstant_pos p profile)
  have hnat : p - 1 + 1 = p := by omega
  have hcast : ((p - 1 : ℕ) : ℝ) + 1 = p := by exact_mod_cast hnat
  have h := tangent_scale_identity L geometryEta geometryKappa R
    (chainSmoothnessConstant p profile) (Real.sqrt (N + 1)) (p - 1) hs hC
  rw [hnat, sqrt_power_accuracy_exponent (N + 1 : ℝ) (by positivity) (p - 1), hcast] at h
  unfold hardAmplitude hardSeed
  rw [hard_width_sqrt_form]
  calc
    _ = ((L * (geometryEta * geometryKappa * R / Real.sqrt (N + 1) ^ 3) ^ (p - 1) /
        chainSmoothnessConstant p profile) * (geometryKappa * R / Real.sqrt (N + 1)) /
          Real.sqrt (N + 1)) / 2 := by ring
    _ = _ := by rw [h]; unfold oracleRateExponent; ring

/-- Radius-normalized actual gap obstruction scale. -/
theorem hard_gap_scale_radius (profile : GateProfile) {p : ℕ} (hp : 2 ≤ p)
    (N : ℕ) (L R : ℝ) :
    hardAmplitude profile p N L R * hardSeed N R ^ 2 / 16 =
      L * geometryEta ^ (p - 1) * geometryKappa ^ (p + 1) * R ^ (p + 1) /
        (16 * chainSmoothnessConstant p profile * (N + 1 : ℝ) ^ oracleRateExponent p) := by
  have hs : Real.sqrt (N + 1 : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by positivity))
  have hC := ne_of_gt (chainSmoothnessConstant_pos p profile)
  have hnat : p - 1 + 2 = p + 1 := by omega
  have hcast : ((p - 1 : ℕ) : ℝ) + 1 = p := by exact_mod_cast (show p - 1 + 1 = p by omega)
  have h := gap_scale_identity L geometryEta geometryKappa R
    (chainSmoothnessConstant p profile) (Real.sqrt (N + 1)) (p - 1) hs hC
  rw [hnat, sqrt_power_accuracy_exponent (N + 1 : ℝ) (by positivity) (p - 1), hcast] at h
  unfold hardAmplitude hardSeed
  rw [hard_width_sqrt_form]
  calc
    _ = ((L * (geometryEta * geometryKappa * R / Real.sqrt (N + 1) ^ 3) ^ (p - 1) /
        chainSmoothnessConstant p profile) * (geometryKappa * R / Real.sqrt (N + 1)) ^ 2) / 16 := by ring
    _ = _ := by rw [h]; unfold oracleRateExponent; ring

/-- Exact diameter-normalized tangent scale, shared by deterministic/randomized proofs. -/
theorem hard_tangent_scale (profile : GateProfile) {p : ℕ} (hp : 2 ≤ p)
    (N : ℕ) (L D : ℝ) :
    hardAmplitude profile p N L (D / (2 * Real.sqrt 2)) * hardSeed N (D / (2 * Real.sqrt 2)) /
      (2 * Real.sqrt (N + 1)) =
    tangentRateConstant profile p * L * D ^ p / (N + 1 : ℝ) ^ oracleRateExponent p := by
  rw [hard_tangent_scale_radius profile hp]
  unfold tangentRateConstant
  simp only [div_pow, div_eq_mul_inv, mul_inv_rev]
  ring_nf
  congr 3 <;> norm_num

/-- Exact diameter-normalized gap scale, shared by deterministic/randomized proofs. -/
theorem hard_gap_scale (profile : GateProfile) {p : ℕ} (hp : 2 ≤ p)
    (N : ℕ) (L D : ℝ) :
    hardAmplitude profile p N L (D / (2 * Real.sqrt 2)) * hardSeed N (D / (2 * Real.sqrt 2)) ^ 2 / 16 =
    gapRateConstant profile p * L * D ^ (p + 1) / (N + 1 : ℝ) ^ oracleRateExponent p := by
  rw [hard_gap_scale_radius profile hp]
  unfold gapRateConstant
  simp only [div_pow, div_eq_mul_inv, mul_inv_rev]
  ring_nf
  congr 3 <;> norm_num

end MinimaxAudit
