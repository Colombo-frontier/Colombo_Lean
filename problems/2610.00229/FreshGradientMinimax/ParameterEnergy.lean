import FreshGradientMinimax.ParameterValue

/-! Energy contraction for arbitrary correlated laws of a regularizer
parameter and an initial state. Only the unconditional initial mean is
bounded; no conditional or pointwise initialization bound is required. -/

set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section
namespace FreshGradientMinimax
open MeasureTheory ProbabilityTheory
namespace SCObjective
variable {dx dy : ℕ} {Θ : Type} [MeasurableSpace Θ]
variable {ℓ μ α σ : ℝ} (S : SCObjective dx dy ℓ μ α)

def parameterGap (Q : Θ × Euclid dy → ℝ) (v : Θ → Euclid dy) (z : Θ × Joint dx dy) : ℝ :=
  Q (z.1, z.2.2) - Q (z.1, v z.1)

def parameterEnergy (Q : Θ × Euclid dy → ℝ) (m : ℝ) (v : Θ → Euclid dy) (z : Θ × Joint dx dy) : ℝ :=
  S.solverEnergy (fun y => Q (z.1, y)) m (v z.1) z.2

theorem parameterGap_measurable (Q : Θ × Euclid dy → ℝ) (hQ : Measurable Q)
    (v : Θ → Euclid dy) (hv : Measurable v) : Measurable (parameterGap (dx := dx) Q v) :=
  (hQ.comp (measurable_fst.prodMk measurable_snd.snd)).sub
    (hQ.comp (measurable_fst.prodMk (hv.comp measurable_fst)))

theorem parameterEnergy_measurable (Q : Θ × Euclid dy → ℝ) (hQ : Measurable Q) (m : ℝ)
    (v : Θ → Euclid dy) (hv : Measurable v) : Measurable (S.parameterEnergy Q m v) := by
  exact (parameterGap_measurable Q hQ v hv).add (measurable_const.mul
    ((measurable_snd.fst.sub (S.sliceMin_continuous.measurable.comp (hv.comp measurable_fst))).norm.pow_const 2))

def parameterEpochOutput (O : FreshOracle S.toNCObjective σ) (m H e E : ℝ)
    (r : Θ × Euclid dy → Euclid dy) (hr : Measurable r) : Kernel (Θ × Joint dx dy) (Θ × Joint dx dy) :=
  ((parameterFullEpochProgram dx dy ℓ α σ m H e E r hr).lawKernel O.kernel).map Prod.fst

instance parameterEpochOutput_markov (O : FreshOracle S.toNCObjective σ) (m H e E : ℝ)
    (r : Θ × Euclid dy → Euclid dy) (hr : Measurable r) :
    IsMarkovKernel (S.parameterEpochOutput O m H e E r hr) :=
  Kernel.IsMarkovKernel.map _ measurable_fst

theorem parameterEpochOutput_fiber (O : FreshOracle S.toNCObjective σ) (m H e E : ℝ)
    (r : Θ × Euclid dy → Euclid dy) (hr : Measurable r) (θ : Θ) :
    (S.parameterEpochOutput O m H e E r hr).comap (fun x => (θ, x)) measurable_prodMk_left =
      (S.fullEpochKernel O m H e E (fun v => r (θ, v)) (hr.comp measurable_prodMk_left)).map
        (fun x => (θ, x)) := by
  have h := costed_transport_first _ _ _ measurable_prodMk_left _ measurable_prodMk_left
    (S.parameterFullEpochProgram_fiber O m H e E r hr θ)
  rw [S.costedFullEpochKernel_first] at h
  exact h

theorem parameterEpochOutput_apply (O : FreshOracle S.toNCObjective σ) (m H e E : ℝ)
    (r : Θ × Euclid dy → Euclid dy) (hr : Measurable r) (z : Θ × Joint dx dy) :
    S.parameterEpochOutput O m H e E r hr z =
      (S.fullEpochKernel O m H e E (fun v => r (z.1, v)) (hr.comp measurable_prodMk_left) z.2).map
        (fun x => (z.1, x)) := by
  have h := congrArg (fun L : Kernel (Joint dx dy) (Θ × Joint dx dy) => L z.2)
    (S.parameterEpochOutput_fiber O m H e E r hr z.1)
  dsimp only at h
  rw [Kernel.comap_apply, Kernel.map_apply _ measurable_prodMk_left] at h
  exact h

theorem parameterEpochOutput_contract (O : FreshOracle S.toNCObjective σ)
    (hαℓ : α ≤ ℓ) (hfast : ℓ / 4 ≤ α) {m H e E : ℝ}
    (hm : 0 < m) (hmH : m ≤ H) (he : 0 < e) (heE : e ≤ E)
    (r : Θ × Euclid dy → Euclid dy) (hr : Measurable r)
    (Q : Θ × Euclid dy → ℝ) (hQ : Measurable Q)
    (model : ∀ θ, SmoothStrongModel (fun y => Q (θ, y)) (fun y => gradient S.effectiveValue y + r (θ, y)) m H)
    (v : Θ → Euclid dy) (hv : Measurable v) (hmin : ∀ θ y, Q (θ, v θ) ≤ Q (θ, y))
    (z : Θ × Joint dx dy) :
    Integrable (S.parameterEnergy Q m v) (S.parameterEpochOutput O m H e E r hr z) ∧
    (∫ w, S.parameterEnergy Q m v w ∂S.parameterEpochOutput O m H e E r hr z) ≤
      S.parameterEnergy Q m v z / 100000 + E / 100000 := by
  rw [S.parameterEpochOutput_apply]
  have h := S.fullEpochKernel_contract O hαℓ hfast hm hmH he heE (fun y => r (z.1, y))
    (hr.comp measurable_prodMk_left) (model z.1) (v z.1) (hmin z.1) z.2
  have hV := (S.parameterEnergy_measurable Q hQ m v hv).stronglyMeasurable
  constructor
  · exact (integrable_map_measure (g := S.parameterEnergy Q m v) hV.aestronglyMeasurable
      (measurable_prodMk_left (x := z.1)).aemeasurable).mpr h.1
  · rw [integral_map (φ := fun x : Joint dx dy => (z.1, x))
      measurable_prodMk_left.aemeasurable hV.aestronglyMeasurable]
    exact h.2

theorem parameterEpochOutput_random_accuracy (O : FreshOracle S.toNCObjective σ)
    (hαℓ : α ≤ ℓ) (hfast : ℓ / 4 ≤ α) {m H e E : ℝ}
    (hm : 0 < m) (hmH : m ≤ H) (he : 0 < e) (heE : e ≤ E)
    (r : Θ × Euclid dy → Euclid dy) (hr : Measurable r)
    (Q : Θ × Euclid dy → ℝ) (hQ : Measurable Q)
    (model : ∀ θ, SmoothStrongModel (fun y => Q (θ, y)) (fun y => gradient S.effectiveValue y + r (θ, y)) m H)
    (v : Θ → Euclid dy) (hv : Measurable v) (hmin : ∀ θ y, Q (θ, v θ) ≤ Q (θ, y))
    (ν : Measure (Θ × Joint dx dy)) [IsProbabilityMeasure ν]
    (hInit : Integrable (S.parameterEnergy Q m v) ν)
    (hEnergy : (∫ z, S.parameterEnergy Q m v z ∂ν) ≤ E) :
    Integrable (S.parameterEnergy Q m v) (S.parameterEpochOutput O m H e E r hr ∘ₘ ν) ∧
    (∫ z, S.parameterEnergy Q m v z ∂S.parameterEpochOutput O m H e E r hr ∘ₘ ν) ≤ E / 50000 := by
  have h (z : Θ × Joint dx dy) := S.parameterEpochOutput_contract O hαℓ hfast hm hmH he heE
    r hr Q hQ model v hv hmin z
  obtain ⟨hi, hb⟩ := kernel_moment_from_envelope (S.parameterEpochOutput O m H e E r hr) ν
    (S.parameterEnergy Q m v) (S.parameterEnergy_measurable Q hQ m v hv).stronglyMeasurable
    (fun z => S.solverEnergy_nonneg hm.le (v z.1) (hmin z.1) z.2)
    (fun z => S.parameterEnergy Q m v z / 100000 + E / 100000)
    ((hInit.div_const 100000).add (integrable_const _)) (fun z => (h z).1) (fun z => (h z).2)
  refine ⟨hi, ?_⟩
  rw [integral_add (hInit.div_const 100000) (integrable_const _), integral_div,
    integral_const, measureReal_univ_eq_one, one_smul] at hb
  linarith only [hb, hEnergy]

end SCObjective
end FreshGradientMinimax
