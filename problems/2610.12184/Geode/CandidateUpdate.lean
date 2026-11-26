import Geode.Candidates

/-! Exact equality of the old latitude and the recentered residual sphere. -/
namespace Geode.Lorentz

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def expandedSpace (W : Submodule ℝ (Ambient E)) (e : Ambient E) : Submodule ℝ (Ambient E) :=
  W ⊔ Submodule.span ℝ {e}

theorem mem_expandedSpace_self (W : Submodule ℝ (Ambient E)) (e : Ambient E) :
    e ∈ expandedSpace W e := Submodule.mem_sup_right (Submodule.subset_span (Set.mem_singleton e))

theorem isResidual_expandedSpace_iff (W : Submodule ℝ (Ambient E)) (e v : Ambient E) :
    IsResidual (expandedSpace W e) v ↔ IsResidual W v ∧ form E v e = 0 := by
  constructor
  · intro h
    exact ⟨fun w hw => h w (Submodule.mem_sup_left hw), h e (mem_expandedSpace_self W e)⟩
  · rintro ⟨hW, he⟩ w hw
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hw
    obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp hb
    rw [form_add_right, hW a ha, ← ht, form_smul_right, he]
    ring

theorem updatedRadius_le {η S : ℝ} (hη : η ^ 2 ≤ 1) (hS : 0 ≤ S) :
    updatedRadius η S ≤ S := by
  have hσ : latitudeContraction η ≤ 1 := by
    apply (Real.sqrt_le_left (by norm_num : (0:ℝ) ≤ 1)).mpr
    nlinarith [sq_nonneg η]
  apply Real.sinh_le_sinh.mp
  rw [sinh_updatedRadius]
  simpa using mul_le_mul_of_nonneg_right hσ (Real.sinh_nonneg_iff.mpr hS)

theorem recenteredCenter_mem {W : Submodule ℝ (Ambient E)} {c : Point E} {e : Ambient E}
    (hc : c.val ∈ W) (he : IsResidual W e) (he1 : form E e e = 1)
    (η S : ℝ) (hη : η ^ 2 ≤ 1) :
    (recenteredCenter c e (residual_tangent hc he) he1 η S hη).val ∈ expandedSpace W e := by
  apply (expandedSpace W e).smul_mem
  exact (expandedSpace W e).sub_mem ((expandedSpace W e).smul_mem _ (Submodule.mem_sup_left hc))
    ((expandedSpace W e).smul_mem _ (mem_expandedSpace_self W e))

noncomputable def latitudeResidual (e v : Ambient E) (η : ℝ) : Ambient E :=
  (latitudeContraction η)⁻¹ • (v + η • e)

theorem latitudeResidual_decomposition (e v : Ambient E) {η : ℝ} (hη : η ^ 2 < 1) :
    v = (-η) • e + latitudeContraction η • latitudeResidual e v η := by
  rw [latitudeResidual, smul_smul, mul_inv_cancel₀ (latitudeContraction_pos hη).ne', one_smul]
  module

theorem latitudeResidual_unit (e v : Ambient E) {η : ℝ} (hη : η ^ 2 < 1)
    (he1 : form E e e = 1) (hv1 : form E v v = 1) (hlat : form E e v = -η) :
    form E (latitudeResidual e v η) (latitudeResidual e v η) = 1 := by
  have hve : form E v e = -η := by rw [form_comm]; exact hlat
  have hs : latitudeContraction η ^ 2 = 1 - η ^ 2 := Real.sq_sqrt (by linarith)
  have hn : form E (v + η • e) (v + η • e) = latitudeContraction η ^ 2 := by
    simp only [form_add_left, form_add_right, form_smul_left, form_smul_right,
      he1, hv1, hlat, hve]
    nlinarith only [hs]
  simp only [latitudeResidual, form_smul_left, form_smul_right, hn]
  have hσ := (latitudeContraction_pos hη).ne'
  field_simp
  ring

theorem latitudeResidual_residual {W : Submodule ℝ (Ambient E)} {e v : Ambient E}
    {η : ℝ} (he : IsResidual W e) (hv : IsResidual W v)
    (he1 : form E e e = 1) (hlat : form E e v = -η) :
    IsResidual (expandedSpace W e) (latitudeResidual e v η) := by
  apply (isResidual_expandedSpace_iff W e _).mpr
  constructor
  · intro w hw
    simp [latitudeResidual, hv w hw, he w hw]
  · have hve : form E v e = -η := by rw [form_comm]; exact hlat
    simp [latitudeResidual, hve, he1]

theorem candidateSet_latitude_update {W : Submodule ℝ (Ambient E)} {c : Point E}
    {e : Ambient E} (hc : c.val ∈ W) (he : IsResidual W e) (he1 : form E e e = 1)
    {η S : ℝ} (hη : η ^ 2 < 1) (hS : 0 < S) :
    candidateSet (expandedSpace W e)
        (recenteredCenter c e (residual_tangent hc he) he1 η S hη.le) (updatedRadius η S) =
      {p ∈ candidateSet W c S | form E e p.val = -η * Real.sinh S} := by
  have hec := he c.val hc
  have hsσ : latitudeContraction η ^ 2 = 1 - η ^ 2 := Real.sq_sqrt (by linarith)
  ext p
  constructor
  · rintro ⟨w, hw, hw1, hp⟩
    obtain ⟨hwW, hwe⟩ := (isResidual_expandedSpace_iff W e w).mp hw
    have hew : form E e w = 0 := by rw [form_comm]; exact hwe
    let v := (-η) • e + latitudeContraction η • w
    have hvW : IsResidual W v := by
      intro a ha
      simp [v, he a ha, hwW a ha]
    have hv1 : form E v v = 1 := by
      simp only [v, form_add_left, form_add_right, form_smul_left, form_smul_right,
        he1, hw1, hew, hwe]
      nlinarith only [hsσ]
    have hid := physical_candidate_recentered c e v w (residual_tangent hc he) he1 η S hη.le rfl
    have hpold := hp.trans hid.symm
    refine ⟨⟨v, hvW, hv1, hpold⟩, ?_⟩
    rw [hpold]
    simp only [v, form_add_right, form_smul_right, hec, he1, hew]
    ring
  · rintro ⟨⟨v, hv, hv1, hp⟩, hlat⟩
    have hsv : Real.sinh S ≠ 0 := (Real.sinh_pos_iff.mpr hS).ne'
    have hev : form E e v = -η := by
      rw [hp, form_add_right, form_smul_right, form_smul_right, hec] at hlat
      have hm : Real.sinh S * (form E e v + η) = 0 := by nlinarith only [hlat]
      have hz := (mul_eq_zero.mp hm).resolve_left hsv
      linarith
    refine ⟨latitudeResidual e v η, latitudeResidual_residual he hv he1 hev,
      latitudeResidual_unit e v hη he1 hv1 hev, ?_⟩
    exact hp.trans (physical_candidate_recentered c e v (latitudeResidual e v η)
      (residual_tangent hc he) he1 η S hη.le (latitudeResidual_decomposition e v hη))

end Geode.Lorentz


