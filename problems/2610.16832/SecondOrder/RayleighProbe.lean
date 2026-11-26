import SecondOrder.MoveDecision

open MeasureTheory
open scoped InnerProductSpace Classical

namespace SecondOrder
noncomputable section

def RayleighCertificate {d : ℕ} (γ : ℝ) (H : Point d →L[ℝ] Point d) : Prop :=
  ∀ v, -γ*‖v‖^2 ≤ ⟪H v,v⟫_ℝ

/-- A fixed dense sequence of vectors. Its choice is made once, independently
of the Hessian and all random data. Zero-dimensional spaces are allowed. -/
def denseProbe (d : ℕ) : ℕ → Point d := TopologicalSpace.denseSeq (Point d)

def strictRayleigh {d : ℕ} (γ : ℝ) (H : Point d →L[ℝ] Point d) (v : Point d) : Prop :=
  ⟪H v,v⟫_ℝ < (-γ/2)*‖v‖^2

theorem strictRayleigh_nonzero {d : ℕ} {γ : ℝ} {H : Point d →L[ℝ] Point d}
    {v : Point d} (hv : strictRayleigh γ H v) : v ≠ 0 := by
  intro he
  subst v
  simpa [strictRayleigh] using hv

def normalizeProbe {d : ℕ} (v : Point d) : Point d := ‖v‖⁻¹ • v

theorem strictRayleigh_normalize {d : ℕ} {γ : ℝ} {H : Point d →L[ℝ] Point d}
    {v : Point d} (hv : strictRayleigh γ H v) :
    ‖normalizeProbe v‖ = 1 ∧ ⟪H (normalizeProbe v),normalizeProbe v⟫_ℝ ≤ -γ/2 := by
  have hn : 0 < ‖v‖ := norm_pos_iff.mpr (strictRayleigh_nonzero hv)
  constructor
  · simp [normalizeProbe, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hn), hn.ne']
  · have he : ⟪H (normalizeProbe v),normalizeProbe v⟫_ℝ = ‖v‖⁻¹^2*⟪H v,v⟫_ℝ := by
      simp only [normalizeProbe, map_smul, inner_smul_left, inner_smul_right, conj_trivial]
      ring
    rw [he]
    have hm := mul_lt_mul_of_pos_left hv (sq_pos_of_pos (inv_pos.mpr hn))
    have heq : ‖v‖⁻¹^2*((-γ/2)*‖v‖^2) = -γ/2 := by field_simp; ring
    rw [heq] at hm
    exact hm.le

theorem exists_strictRayleigh_probe {d : ℕ} {γ : ℝ} (hγ : 0 < γ)
    (H : Point d →L[ℝ] Point d) (hc : ¬ RayleighCertificate γ H) :
    ∃ n, strictRayleigh γ H (denseProbe d n) := by
  unfold RayleighCertificate at hc
  push_neg at hc
  obtain ⟨v, hv⟩ := hc
  have hv0 : v ≠ 0 := by intro he; subst v; simp at hv
  have hn := norm_pos_iff.mpr hv0
  have ho : IsOpen {v : Point d | strictRayleigh γ H v} := by
    apply isOpen_lt <;> fun_prop
  have hmem : strictRayleigh γ H v := by
    change ⟪H v,v⟫_ℝ < (-γ/2)*‖v‖^2
    nlinarith [mul_pos hγ (sq_pos_of_pos hn)]
  exact (TopologicalSpace.denseRange_denseSeq (Point d)).exists_mem_open ho ⟨v,hmem⟩

theorem rayleighCertificate_closed {d : ℕ} (γ : ℝ) :
    IsClosed {H : Point d →L[ℝ] Point d | RayleighCertificate γ H} := by
  simp only [RayleighCertificate, Set.setOf_forall]
  apply isClosed_iInter
  intro v
  apply isClosed_le <;> fun_prop

theorem strictRayleigh_measurableSet {d : ℕ} (γ : ℝ) (v : Point d) :
    MeasurableSet {H : Point d →L[ℝ] Point d | strictRayleigh γ H v} := by
  apply IsOpen.measurableSet
  apply isOpen_lt <;> fun_prop

/-- Index zero means certificate; positive indices enumerate strict witnesses. -/
def rayleighProbePred {d : ℕ} (γ : ℝ) (H : Point d →L[ℝ] Point d) (n : ℕ) : Prop :=
  if n = 0 then RayleighCertificate γ H else strictRayleigh γ H (denseProbe d (n-1))

theorem exists_rayleighProbePred {d : ℕ} {γ : ℝ} (hγ : 0 < γ)
    (H : Point d →L[ℝ] Point d) : ∃ n, rayleighProbePred γ H n := by
  by_cases hc : RayleighCertificate γ H
  · exact ⟨0, by simpa [rayleighProbePred] using hc⟩
  · obtain ⟨n, hn⟩ := exists_strictRayleigh_probe hγ H hc
    exact ⟨n+1, by simpa [rayleighProbePred] using hn⟩

def rayleighIndex {d : ℕ} {γ : ℝ} (hγ : 0 < γ) (H : Point d →L[ℝ] Point d) : ℕ :=
  Nat.find (exists_rayleighProbePred hγ H)

theorem rayleighIndex_spec {d : ℕ} {γ : ℝ} (hγ : 0 < γ) (H : Point d →L[ℝ] Point d) :
    rayleighProbePred γ H (rayleighIndex hγ H) := Nat.find_spec (exists_rayleighProbePred hγ H)

theorem rayleighIndex_measurable {d : ℕ} {γ : ℝ} (hγ : 0 < γ) :
    Measurable (rayleighIndex (d := d) hγ) := by
  apply measurable_find
  intro n
  by_cases hn : n = 0
  · simpa [rayleighProbePred, hn] using (rayleighCertificate_closed (d := d) γ).measurableSet
  · simpa [rayleighProbePred, hn] using strictRayleigh_measurableSet γ (denseProbe d (n-1))

end
end SecondOrder
