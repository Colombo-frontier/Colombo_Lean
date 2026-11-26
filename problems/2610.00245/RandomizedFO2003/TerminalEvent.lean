import RandomizedFO2003.SampledCascadeLaw

namespace RandomizedFO2003.FiniteSpectralDesign

open MeasureTheory SpectralCoordinates Cascade Rotations Primitives
open scoped BigOperators ENNReal

variable {m : ℕ} {γ L : ℝ} (S : FiniteSpectralDesign m γ L (1 / (16 * γ)))
variable {Seed : Type} [MeasurableSpace Seed]

noncomputable def sampledBlockOutput (K : Fin S.size → ℕ) (N : ℕ) (h : ℝ)
    (A : Model.Algorithm ((N + 1) * ∑ j, K j) Seed) (T : ℕ)
    (p : Sample K N × Seed) : BlockProduct (N + 1) (BlockSpace K) :=
  (cascadeCoordinates K N).symm
    (A.output T p.2 (Model.transcript A (S.sampledCascadeFunction K N h p.1) p.2 T))

theorem measurable_sampledBlockOutput (K : Fin S.size → ℕ) (N : ℕ) (h : ℝ)
    (A : Model.Algorithm ((N + 1) * ∑ j, K j) Seed) (T : ℕ) :
    Measurable (S.sampledBlockOutput K N h A T) :=
  (cascadeCoordinates K N).symm.continuous.measurable.comp
    (S.measurable_sampledCascadeOutput K N h A T)

/-- The actual radial readout at the algorithm's arbitrary terminal point. -/
noncomputable def terminalReadout (K : Fin S.size → ℕ) (N : ℕ) (h : ℝ)
    (A : Model.Algorithm ((N + 1) * ∑ j, K j) Seed) (T : ℕ) (i : Fin (N + 1))
    (p : Sample K N × Seed) : ℝ :=
  radialReadout (isometry _ (p.1.2 i) (direction K (p.1.1 i) S.residual))
    (radiusCoefficient * h / γ) (h / (64 * γ)) (S.sampledBlockOutput K N h A T p i)

theorem measurable_terminalReadout (K : Fin S.size → ℕ) (N : ℕ) (h : ℝ)
    (A : Model.Algorithm ((N + 1) * ∑ j, K j) Seed) (T : ℕ) (i : Fin (N + 1)) :
    Measurable (S.terminalReadout K N h A T i) := by
  have ha : Measurable (fun p : Sample K N × Seed =>
      isometry _ (p.1.2 i) (direction K (p.1.1 i) S.residual)) :=
    ((measurable_pi_apply i).comp (S.measurable_cascadeCoefficients K N h).snd.fst).comp measurable_fst
  have hx : Measurable (fun p : Sample K N × Seed => S.sampledBlockOutput K N h A T p i) :=
    (blockProjection (E := BlockSpace K) (N + 1) i).continuous.measurable.comp
      (S.measurable_sampledBlockOutput K N h A T)
  exact (ha.inner (((radialSquash_contDiff (radiusCoefficient * h / γ) 0).continuous.measurable).comp hx)).div_const _

def terminalFlatEvent (K : Fin S.size → ℕ) (N : ℕ) (h : ℝ)
    (A : Model.Algorithm ((N + 1) * ∑ j, K j) Seed) (T : ℕ) (i : Fin (N + 1)) :
    Set (Sample K N × Seed) := {p | |S.terminalReadout K N h A T i p| ≤ 1 / 4}

theorem measurableSet_terminalFlatEvent (K : Fin S.size → ℕ) (N : ℕ) (h : ℝ)
    (A : Model.Algorithm ((N + 1) * ∑ j, K j) Seed) (T : ℕ) (i : Fin (N + 1)) :
    MeasurableSet (S.terminalFlatEvent K N h A T i) :=
  measurableSet_le (continuous_abs.measurable.comp (S.measurable_terminalReadout K N h A T i)) measurable_const

/-- On the common spectral event, success is incompatible with a flat
terminal gate, for every block and every realized private seed. -/
theorem success_not_terminalFlat (hγ : 0 < γ) (K : Fin S.size → ℕ) (N : ℕ)
    {h ε : ℝ} (hh : 0 < h) (hε : 0 ≤ ε) (hH : 512 * ε ≤ h)
    (A : Model.Algorithm ((N + 1) * ∑ j, K j) Seed) (T : ℕ) (i : Fin (N + 1))
    {p : Sample K N × Seed} (hgood : p.1.1 ∈ S.cascadeGoodEvent K N)
    (hs : p.2 ∈ Model.Success A (S.sampledCascadeFunction K N h p.1) ε T) :
    p ∉ S.terminalFlatEvent K N h A T i := by
  intro hflat
  have hstat := S.cascadeFunction_stationarity hγ K N (fun j => isometry _ (p.1.2 j)) p.1.1
    hh hε hH (fun j => (hgood j).1) (fun j => (hgood j).2)
    (A.output T p.2 (Model.transcript A (S.sampledCascadeFunction K N h p.1) p.2 T)) hs
  have hone := hstat.2.2.1 i
  have hzero := radialGate_zero
    (isometry _ (p.1.2 i) (direction K (p.1.1 i) S.residual))
    (radiusCoefficient * h / γ) (h / (64 * γ)) hflat
  change radialGate _ _ _ (S.sampledBlockOutput K N h A T p i) = 1 at hone
  exact zero_ne_one (hzero.symm.trans hone)

/-- A concrete probability reduction for the actual oracle: only bad
spectral weights or a non-flat terminal gate can permit success. The
terminal probability still has to be bounded by the stopping argument. -/
theorem sampled_success_probability_bound (hγ : 0 < γ) (K : Fin S.size → ℕ) (N : ℕ)
    {h ε : ℝ} (hh : 0 < h) (hε : 0 ≤ ε) (hH : 512 * ε ≤ h)
    (ν : Measure Seed) [IsProbabilityMeasure ν]
    (A : Model.Algorithm ((N + 1) * ∑ j, K j) Seed) (T : ℕ) (i : Fin (N + 1)) :
    ((S.cascadeParameterLaw K N).prod ν)
      (Model.familySuccess A (S.sampledCascadeFunction K N h) ε T) ≤
      Measure.pi (fun _ : Fin (N + 1) => Spherical.sphereLaw (BlockSpace K)) (S.cascadeGoodEvent K N)ᶜ +
        ((S.cascadeParameterLaw K N).prod ν) (S.terminalFlatEvent K N h A T i)ᶜ := by
  have hsub : Model.familySuccess A (S.sampledCascadeFunction K N h) ε T ⊆
      (((S.cascadeGoodEvent K N)ᶜ ×ˢ Set.univ) ×ˢ Set.univ) ∪
        (S.terminalFlatEvent K N h A T i)ᶜ := by
    intro p hs
    by_cases hg : p.1.1 ∈ S.cascadeGoodEvent K N
    · exact Or.inr (S.success_not_terminalFlat hγ K N hh hε hH A T i hg hs)
    · exact Or.inl ⟨⟨hg, Set.mem_univ _⟩, Set.mem_univ _⟩
  calc
    _ ≤ ((S.cascadeParameterLaw K N).prod ν)
        ((((S.cascadeGoodEvent K N)ᶜ ×ˢ Set.univ) ×ˢ Set.univ) ∪
          (S.terminalFlatEvent K N h A T i)ᶜ) := measure_mono hsub
    _ ≤ ((S.cascadeParameterLaw K N).prod ν)
          (((S.cascadeGoodEvent K N)ᶜ ×ˢ Set.univ) ×ˢ Set.univ) +
        ((S.cascadeParameterLaw K N).prod ν) (S.terminalFlatEvent K N h A T i)ᶜ := measure_union_le _ _
    _ = _ := by simp only [cascadeParameterLaw, Measure.prod_prod, measure_univ, mul_one]

end RandomizedFO2003.FiniteSpectralDesign
