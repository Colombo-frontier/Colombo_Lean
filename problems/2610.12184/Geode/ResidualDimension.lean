import Geode.LorentzProjection
import Geode.CandidateUpdate
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! Dimension and nonemptiness of the actual Lorentz residual space. -/
namespace Geode.Lorentz

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def residualSpace (W : Submodule ℝ (Ambient E)) : Submodule ℝ (Ambient E) where
  carrier := {v | IsResidual W v}
  zero_mem' := by intro w hw; simp
  add_mem' := by intro u v hu hv w hw; simp [hu w hw, hv w hw]
  smul_mem' := by intro a v hv w hw; simp [hv w hw]

@[simp] theorem mem_residualSpace (W : Submodule ℝ (Ambient E)) (v : Ambient E) :
    v ∈ residualSpace W ↔ IsResidual W v := Iff.rfl

theorem residualSpace_nonneg {W : Submodule ℝ (Ambient E)} {c : Point E}
    (hc : c.val ∈ W) {v : Ambient E} (hv : v ∈ residualSpace W) : 0 ≤ form E v v :=
  tangent_nonneg c (residual_tangent hc hv)

theorem residualSpace_pos {W : Submodule ℝ (Ambient E)} {c : Point E}
    (hc : c.val ∈ W) {v : Ambient E} (hv : v ∈ residualSpace W) (hne : v ≠ 0) :
    0 < form E v v := tangent_pos c (residual_tangent hc hv) hne

theorem residual_unit_of_ne_zero {W : Submodule ℝ (Ambient E)} {c : Point E}
    (hc : c.val ∈ W) {v : Ambient E} (hv : IsResidual W v) (hne : v ≠ 0) :
    ∃ e : Ambient E, IsResidual W e ∧ form E e e = 1 := by
  have hpos : 0 < tangentNorm v := Real.sqrt_pos.mpr (residualSpace_pos hc hv hne)
  have hsq : tangentNorm v ^ 2 = form E v v := Real.sq_sqrt (residualSpace_nonneg hc hv)
  refine ⟨(tangentNorm v)⁻¹ • v, ?_, ?_⟩
  · intro w hw
    simp only [form_smul_left, hv w hw, mul_zero]
  · simp only [form_smul_left, form_smul_right]
    rw [← hsq]
    field_simp
    ring

variable [FiniteDimensional ℝ E]

theorem publicPart_eq_zero_iff (W : Submodule ℝ (Ambient E)) {c : Point E}
    (hc : c.val ∈ W) (q : Ambient E) :
    publicPart W c q = 0 ↔ IsResidual W q := by
  constructor
  · intro hp
    have hr : residualPart W c q = q := by
      change q - publicPart W c q = q
      rw [hp, sub_zero]
    intro w hw
    rw [← hr]
    exact residualPart_orthogonal W hc q hw
  · intro hq
    have hp := publicPart_mem W hc q
    have ht := publicPart_tangent W hc hc (residual_tangent hc hq)
    apply (tangent_eq_zero_iff c ht).mp
    have hs := congrArg (fun v => form E v (publicPart W c q))
      (publicPart_add_residualPart W c q)
    simpa only [form_add_left, residualPart_orthogonal W hc q hp,
      hq (publicPart W c q) hp, add_zero] using hs

theorem publicPart_ker (W : Submodule ℝ (Ambient E)) {c : Point E}
    (hc : c.val ∈ W) : LinearMap.ker (publicPart W c) = residualSpace W := by
  ext q
  exact publicPart_eq_zero_iff W hc q

theorem publicPart_range (W : Submodule ℝ (Ambient E)) {c : Point E}
    (hc : c.val ∈ W) : LinearMap.range (publicPart W c) = W := by
  ext q
  constructor
  · rintro ⟨v, rfl⟩
    exact publicPart_mem W hc v
  · intro hq
    exact ⟨q, publicPart_eq_self W hc hq⟩

theorem finrank_public_add_residual (W : Submodule ℝ (Ambient E)) {c : Point E}
    (hc : c.val ∈ W) :
    Module.finrank ℝ W + Module.finrank ℝ (residualSpace W) =
      Module.finrank ℝ (Ambient E) := by
  have h := (publicPart W c).finrank_range_add_finrank_ker
  rw [publicPart_range W hc, publicPart_ker W hc] at h
  exact h

theorem exists_residual_unit (W : Submodule ℝ (Ambient E)) {c : Point E}
    (hc : c.val ∈ W) (hdim : Module.finrank ℝ W < Module.finrank ℝ (Ambient E)) :
    ∃ e : Ambient E, IsResidual W e ∧ form E e e = 1 := by
  have hpos : 0 < Module.finrank ℝ (residualSpace W) := by
    have h := finrank_public_add_residual W hc
    omega
  obtain ⟨v, hv⟩ := Module.finrank_pos_iff_exists_ne_zero.mp hpos
  have hv0 : (v : Ambient E) ≠ 0 := by
    intro h
    exact hv (Subtype.ext h)
  exact residual_unit_of_ne_zero hc v.property hv0

theorem finrank_adjoin_unit_le (W : Submodule ℝ (Ambient E)) {e : Ambient E}
    (he1 : form E e e = 1) :
    Module.finrank ℝ (W ⊔ Submodule.span ℝ {e} : Submodule ℝ (Ambient E)) ≤
      Module.finrank ℝ W + 1 := by
  have he0 : e ≠ 0 := by intro h; simp [h] at he1
  have h := Submodule.finrank_add_le_finrank_add_finrank W (Submodule.span ℝ {e})
  simpa only [finrank_span_singleton he0] using h

theorem exists_residual_unit_orthogonal (W : Submodule ℝ (Ambient E)) {c : Point E}
    (hc : c.val ∈ W) {e : Ambient E} (he1 : form E e e = 1)
    (hdim : Module.finrank ℝ W + 1 < Module.finrank ℝ (Ambient E)) :
    ∃ w : Ambient E, IsResidual W w ∧ form E w e = 0 ∧ form E w w = 1 := by
  let W' := W ⊔ Submodule.span ℝ {e}
  have hc' : c.val ∈ W' := Submodule.mem_sup_left hc
  have hd' : Module.finrank ℝ W' < Module.finrank ℝ (Ambient E) :=
    lt_of_le_of_lt (finrank_adjoin_unit_le W he1) hdim
  obtain ⟨w, hw, hw1⟩ := exists_residual_unit W' hc' hd'
  refine ⟨w, ?_, ?_, hw1⟩
  · intro v hv
    exact hw v (Submodule.mem_sup_left hv)
  · exact hw e (Submodule.mem_sup_right (Submodule.subset_span (Set.mem_singleton e)))

theorem candidateSet_nonempty (W : Submodule ℝ (Ambient E)) {c : Point E}
    (hc : c.val ∈ W) (hdim : Module.finrank ℝ W < Module.finrank ℝ (Ambient E))
    (S : ℝ) : (candidateSet W c S).Nonempty := by
  obtain ⟨e, he, he1⟩ := exists_residual_unit W hc hdim
  exact ⟨_, candidate_from_residual hc he he1 S⟩

theorem finrank_expandedSpace (W : Submodule ℝ (Ambient E)) {e : Ambient E}
    (he : IsResidual W e) (he1 : form E e e = 1) :
    Module.finrank ℝ (expandedSpace W e) = Module.finrank ℝ W + 1 := by
  have he0 : e ≠ 0 := by intro h; simp [h] at he1
  have hinf : W ⊓ Submodule.span ℝ {e} = ⊥ := by
    apply le_antisymm ?_ bot_le
    intro v hv
    change v = 0
    obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp hv.2
    have ht0 : t = 0 := by simpa [← ht, he1] using he v hv.1
    rw [← ht, ht0, zero_smul]
  have h := Submodule.finrank_sup_add_finrank_inf_eq W (Submodule.span ℝ {e})
  rw [hinf, finrank_bot, add_zero, finrank_span_singleton he0] at h
  exact h

theorem candidateSet_latitude_nonempty (W : Submodule ℝ (Ambient E)) {c : Point E}
    (hc : c.val ∈ W) {e : Ambient E} (he : IsResidual W e) (he1 : form E e e = 1)
    (hdim : Module.finrank ℝ W + 1 < Module.finrank ℝ (Ambient E))
    {η S : ℝ} (hη : η ^ 2 < 1) (hS : 0 < S) :
    {p ∈ candidateSet W c S | form E e p.val = -η * Real.sinh S}.Nonempty := by
  rw [← candidateSet_latitude_update hc he he1 hη hS]
  apply candidateSet_nonempty (expandedSpace W e)
    (recenteredCenter_mem hc he he1 η S hη.le)
  rw [finrank_expandedSpace W he he1]
  exact hdim

end Geode.Lorentz
