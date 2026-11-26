import SecondOrder.OjaStep
import Mathlib.Analysis.InnerProductSpace.Spectrum

open scoped InnerProductSpace

namespace SecondOrder
noncomputable section

/-- The variational top eigenvalue, over nonzero vectors. The spectral
statements below explicitly require positive dimension. -/
def topRayleigh {d : ℕ} (A : Point d →L[ℝ] Point d) : ℝ :=
  ⨆ v : {v : Point d // v ≠ 0}, ⟪A v, v⟫_ℝ / ‖(v : Point d)‖^2

theorem topRayleigh_bddAbove {d : ℕ} {A : Point d →L[ℝ] Point d}
    (hA : ∀ v, ⟪A v, v⟫_ℝ ≤ ‖v‖^2) :
    BddAbove (Set.range (fun v : {v : Point d // v ≠ 0} =>
      ⟪A v, v⟫_ℝ / ‖(v : Point d)‖^2)) := by
  refine ⟨1, ?_⟩
  rintro _ ⟨v, rfl⟩
  exact (div_le_iff₀ (sq_pos_of_pos (norm_pos_iff.mpr v.2))).mpr (by simpa using hA v)

theorem rayleigh_le_topRayleigh {d : ℕ} {A : Point d →L[ℝ] Point d}
    (hA : ∀ v, ⟪A v, v⟫_ℝ ≤ ‖v‖^2) (v : Point d) :
    ⟪A v, v⟫_ℝ ≤ topRayleigh A * ‖v‖^2 := by
  by_cases hv : v = 0
  · simp [hv]
  · have ht := le_ciSup (topRayleigh_bddAbove hA) (⟨v,hv⟩ : {v : Point d // v ≠ 0})
    exact (div_le_iff₀ (sq_pos_of_pos (norm_pos_iff.mpr hv))).mp ht

/-- A genuine unit eigenvector attains the largest Rayleigh value. This
vector is used only for analysis, not supplied to the oracle algorithm. -/
theorem topRayleigh_eigenvector {d : ℕ} (hd : 0 < d) {A : Point d →L[ℝ] Point d}
    (hA : A.toLinearMap.IsSymmetric) :
    ∃ v : Point d, ‖v‖ = 1 ∧ A v = topRayleigh A • v := by
  letI : Nonempty (Fin d) := ⟨⟨0,hd⟩⟩
  have he : Module.End.HasEigenvalue A.toLinearMap (topRayleigh A) := by
    simpa [topRayleigh] using hA.hasEigenvalue_iSup_of_finiteDimensional
  obtain ⟨v, hv⟩ := he.exists_hasEigenvector
  have hev : A v = topRayleigh A • v := Module.End.mem_eigenspace_iff.mp hv.1
  refine ⟨normalizeProbe v, normalizeProbe_norm hv.2, ?_⟩
  simp only [normalizeProbe, map_smul, hev, smul_smul]
  rw [mul_comm]

theorem topRayleigh_bounds {d : ℕ} (hd : 0 < d) {A : Point d →L[ℝ] Point d}
    (hs : A.toLinearMap.IsSymmetric)
    (hA : ∀ v, 0 ≤ ⟪A v, v⟫_ℝ ∧ ⟪A v, v⟫_ℝ ≤ ‖v‖^2) :
    0 ≤ topRayleigh A ∧ topRayleigh A ≤ 1 := by
  obtain ⟨v, hv, he⟩ := topRayleigh_eigenvector hd hs
  have hb := hA v
  rw [he, inner_smul_left, conj_trivial, real_inner_self_eq_norm_sq, hv] at hb
  simpa using hb

open MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} {μ : Measure Ω}
  [IsProbabilityMeasure μ] {P : Parameters} {ν : ℝ}
  {F : Point d → ℝ} {f : Ω → Point d → ℝ}

theorem CommonLoss.mean_shifted_top_eigenpair (h : CommonLoss μ P ν F f)
    (hd : 0 < d) (x : Point d) :
    let A := shiftedHessian (eigenHessianBound P) (hessian F x)
    0 ≤ topRayleigh A ∧ topRayleigh A ≤ 1 ∧
      (∀ u, ⟪A u, u⟫_ℝ ≤ topRayleigh A * ‖u‖^2) ∧
      ∃ v : Point d, ‖v‖ = 1 ∧ A v = topRayleigh A • v := by
  have hg := h.mean_shifted_hessian_good x
  have hb := topRayleigh_bounds hd hg.1 hg.2.2
  exact ⟨hb.1, hb.2, rayleigh_le_topRayleigh (fun u => (hg.2.2 u).2),
    topRayleigh_eigenvector hd hg.1⟩

end
end SecondOrder
