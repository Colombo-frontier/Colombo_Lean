import SecondOrder.SampledShiftedHessian
import SecondOrder.RayleighProbe

open MeasureTheory
open scoped InnerProductSpace

namespace SecondOrder
noncomputable section

/-- The unnormalized stochastic power update. -/
def ojaUpdate {d : ℕ} (η : ℝ) (A : Point d →L[ℝ] Point d) (v : Point d) : Point d :=
  v + η • A v

/-- The normalization is total at zero; positivity proves that a nonzero
initial vector never reaches this branch on valid samples. -/
def ojaStep {d : ℕ} (η : ℝ) (A : Point d →L[ℝ] Point d) (v : Point d) : Point d :=
  normalizeProbe (ojaUpdate η A v)

theorem normalizeProbe_measurable {d : ℕ} : Measurable (@normalizeProbe d) :=
  measurable_id.norm.inv.smul measurable_id

theorem normalizeProbe_norm {d : ℕ} {v : Point d} (hv : v ≠ 0) :
    ‖normalizeProbe v‖ = 1 := by
  simp [normalizeProbe, norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg v)),
    norm_ne_zero_iff.mpr hv]

theorem ojaUpdate_norm_lower {d : ℕ} {η : ℝ} (hη : 0 ≤ η)
    {A : Point d →L[ℝ] Point d} {v : Point d} (hA : 0 ≤ ⟪A v, v⟫_ℝ) :
    ‖v‖ ≤ ‖ojaUpdate η A v‖ := by
  have hcross : 0 ≤ η * ⟪v, A v⟫_ℝ := by
    rw [real_inner_comm]
    exact mul_nonneg hη hA
  have he := norm_add_sq_real v (η • A v)
  rw [inner_smul_right] at he
  change ‖v‖ ≤ ‖v + η • A v‖
  nlinarith [sq_nonneg ‖η • A v‖, norm_nonneg v, norm_nonneg (v + η • A v)]

theorem ojaUpdate_norm_upper {d : ℕ} {η : ℝ} (hη : 0 ≤ η)
    {A : Point d →L[ℝ] Point d} (hA : ‖A‖ ≤ 1) (v : Point d) :
    ‖ojaUpdate η A v‖ ≤ (1 + η) * ‖v‖ := by
  have hv : ‖A v‖ ≤ ‖v‖ := by
    simpa using (A.le_opNorm v).trans (mul_le_mul_of_nonneg_right hA (norm_nonneg v))
  calc
    _ ≤ ‖v‖ + ‖η • A v‖ := norm_add_le _ _
    _ = ‖v‖ + η * ‖A v‖ := by rw [norm_smul, Real.norm_of_nonneg hη]
    _ ≤ ‖v‖ + η * ‖v‖ := add_le_add_left (mul_le_mul_of_nonneg_left hv hη) _
    _ = _ := by ring

theorem ojaUpdate_ne_zero {d : ℕ} {η : ℝ} (hη : 0 ≤ η)
    {A : Point d →L[ℝ] Point d} {v : Point d} (hA : 0 ≤ ⟪A v, v⟫_ℝ) (hv : v ≠ 0) :
    ojaUpdate η A v ≠ 0 := by
  apply norm_ne_zero_iff.mp
  exact ne_of_gt ((norm_pos_iff.mpr hv).trans_le (ojaUpdate_norm_lower hη hA))

theorem ojaStep_norm {d : ℕ} {η : ℝ} (hη : 0 ≤ η)
    {A : Point d →L[ℝ] Point d} {v : Point d} (hA : 0 ≤ ⟪A v, v⟫_ℝ) (hv : v ≠ 0) :
    ‖ojaStep η A v‖ = 1 :=
  normalizeProbe_norm (ojaUpdate_ne_zero hη hA hv)

theorem ojaStep_measurable {d : ℕ} (η : ℝ) :
    Measurable (fun av : (Point d →L[ℝ] Point d) × Point d => ojaStep η av.1 av.2) :=
  normalizeProbe_measurable.comp
    (measurable_snd.add ((continuous_fst.clm_apply continuous_snd).measurable.const_smul η))

/-- The update expressed only in terms of one already obtained oracle reply. -/
def ojaStepFromHvp {d : ℕ} (P : Parameters) (η : ℝ) (v reply : Point d) : Point d :=
  normalizeProbe (v + η • ((2 * eigenHessianBound P)⁻¹ • (eigenHessianBound P • v - reply)))

theorem ojaStep_one_hvp {Ω : Type*} {d : ℕ} (P : Parameters)
    (f : Ω → Point d → ℝ) (η : ℝ) (x v : Point d) (z : Ω) :
    ojaStep η (sampledShiftedHessian P f x z) v =
      ojaStepFromHvp P η v (hvpReply f z (.hvp x v)) := rfl

end
end SecondOrder
