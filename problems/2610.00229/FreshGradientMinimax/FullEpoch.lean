import FreshGradientMinimax.FastRefresh

/-! A complete F.3 epoch: accelerated phase followed by fast refresh.
The energy contracts for arbitrary input laws controlled only in mean. -/

set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section
namespace FreshGradientMinimax
open MeasureTheory ProbabilityTheory
namespace SCObjective
variable {dx dy : ℕ} {ℓ μ α σ : ℝ} (S : SCObjective dx dy ℓ μ α)

def refreshFromStateKernel (O : FreshOracle S.toNCObjective σ) (m E : ℝ) :
    Kernel (EpochState dx dy) (Joint dx dy) :=
  (S.refreshKernel O m E).comap (fun t => (t.1, t.2.1)) (measurable_fst.prodMk measurable_snd.fst)

instance refreshFromStateKernel_markov (O : FreshOracle S.toNCObjective σ) (m E : ℝ) :
    IsMarkovKernel (S.refreshFromStateKernel O m E) := by unfold refreshFromStateKernel; infer_instance

def fullEpochKernel (O : FreshOracle S.toNCObjective σ) (m H e E : ℝ)
    (r : Euclid dy → Euclid dy) (hr : Measurable r) : Kernel (Joint dx dy) (Joint dx dy) :=
  S.refreshFromStateKernel O m E ∘ₖ S.epochPhaseStateKernel O m H e E r hr

instance fullEpochKernel_markov (O : FreshOracle S.toNCObjective σ) (m H e E : ℝ)
    (r : Euclid dy → Euclid dy) (hr : Measurable r) :
    IsMarkovKernel (S.fullEpochKernel O m H e E r hr) := by unfold fullEpochKernel; infer_instance

theorem refreshFromStateKernel_energy_bound (O : FreshOracle S.toNCObjective σ)
    (hαℓ : α ≤ ℓ) (hfast : ℓ / 4 ≤ α) {m H E : ℝ} (hm : 0 < m) (hE : 0 < E)
    {Q : Euclid dy → ℝ} {grad : Euclid dy → Euclid dy} (model : SmoothStrongModel Q grad m H)
    (v : Euclid dy) (hmin : ∀ x, Q v ≤ Q x) (t : EpochState dx dy) :
    (∫ w, S.solverEnergy Q m v w ∂S.refreshFromStateKernel O m E t) ≤
      66 * statePotential Q m v t.2 + 4 * (m * ‖t.1 - S.sliceMin v‖ ^ 2) / 1000000 + 2 * E / 1000000 := by
  have hb := S.refreshKernel_energy_bound O hαℓ hfast hm hE model.continuous v (t.1, t.2.1)
  have hd := (model.gap_quadratic_bounds v hmin t.2.1).1
  have hp := SmoothStrongModel.potential_nonneg hm.le v hmin t.2.1 t.2.2
  have hz : 0 ≤ m / 2 * ‖t.2.2 - v‖ ^ 2 := by positivity
  have hf := model.reference_query_distance hm (a := 0) (k := 4) (by norm_num) (by norm_num)
    v hmin S.sliceMin (S.sliceMin_lip_four hfast) t.1 t.2.1 t.2.2
  simp only [acceleratedY, add_zero, inv_one, zero_smul, one_smul] at hf
  change (∫ w, S.solverEnergy Q m v w ∂S.refreshKernel O m E (t.1, t.2.1)) ≤ _
  dsimp only [fastError, Prod.fst, Prod.snd] at hb
  dsimp only [statePotential, acceleratedPotential] at hp hf ⊢
  nlinarith only [hb, hd, hp, hz, hf]

theorem epochPhaseStateKernel_reference (O : FreshOracle S.toNCObjective σ) (m H e E : ℝ)
    (r : Euclid dy → Euclid dy) (hr : Measurable r) (v : Euclid dy) (z : Joint dx dy) :
    Integrable (fun t : EpochState dx dy => m * ‖t.1 - S.sliceMin v‖ ^ 2)
      (S.epochPhaseStateKernel O m H e E r hr z) ∧
    (∫ t, m * ‖t.1 - S.sliceMin v‖ ^ 2 ∂S.epochPhaseStateKernel O m H e E r hr z) =
      m * ‖z.1 - S.sliceMin v‖ ^ 2 := by
  rcases z with ⟨u, x⟩
  rw [S.epochPhaseStateKernel_apply]
  have hR : StronglyMeasurable (fun t : EpochState dx dy => m * ‖t.1 - S.sliceMin v‖ ^ 2) :=
    (continuous_const.mul ((continuous_fst.sub continuous_const).norm.pow 2)).stronglyMeasurable
  constructor
  · apply (integrable_map_measure (f := fun s : Joint dy dy => (u, s))
      (g := fun t : EpochState dx dy => m * ‖t.1 - S.sliceMin v‖ ^ 2)
      (μ := S.epochAcceleratedKernel O epochRho m H e r hr (epochBatch m H e σ E) u (epochSteps m H) (x, x))
      hR.aestronglyMeasurable (measurable_const.prodMk measurable_id).aemeasurable).mpr
    exact integrable_const (μ := S.epochAcceleratedKernel O epochRho m H e r hr
      (epochBatch m H e σ E) u (epochSteps m H) (x, x)) (m * ‖u - S.sliceMin v‖ ^ 2)
  · rw [integral_map (f := fun t : EpochState dx dy => m * ‖t.1 - S.sliceMin v‖ ^ 2)
      (φ := fun s : Joint dy dy => (u, s)) (measurable_const.prodMk measurable_id).aemeasurable
      hR.aestronglyMeasurable]
    simp only [integral_const, measureReal_univ_eq_one, one_smul]

theorem fullEpochKernel_contract (O : FreshOracle S.toNCObjective σ)
    (hαℓ : α ≤ ℓ) (hfast : ℓ / 4 ≤ α) {m H e E : ℝ}
    (hm : 0 < m) (hmH : m ≤ H) (he : 0 < e) (heE : e ≤ E)
    (r : Euclid dy → Euclid dy) (hr : Measurable r) {Q : Euclid dy → ℝ}
    (model : SmoothStrongModel Q (fun v => gradient S.effectiveValue v + r v) m H)
    (v : Euclid dy) (hmin : ∀ x, Q v ≤ Q x) (z : Joint dx dy) :
    Integrable (S.solverEnergy Q m v) (S.fullEpochKernel O m H e E r hr z) ∧
    (∫ w, S.solverEnergy Q m v w ∂S.fullEpochKernel O m H e E r hr z) ≤
      S.solverEnergy Q m v z / 100000 + E / 100000 := by
  obtain ⟨hP, hPb⟩ := S.epochPhaseStateKernel_contract O hαℓ hfast hm hmH he heE r hr model v hmin z
  obtain ⟨hR, hRe⟩ := S.epochPhaseStateKernel_reference O m H e E r hr v z
  have hW : Integrable (fun t : EpochState dx dy =>
      66 * statePotential Q m v t.2 + 4 * (m * ‖t.1 - S.sliceMin v‖ ^ 2) / 1000000 + 2 * E / 1000000)
      (S.epochPhaseStateKernel O m H e E r hr z) :=
    ((hP.const_mul 66).add ((hR.const_mul 4).div_const 1000000)).add (integrable_const _)
  obtain ⟨hi, hb⟩ := kernel_moment_from_envelope (S.refreshFromStateKernel O m E)
    (S.epochPhaseStateKernel O m H e E r hr z) (S.solverEnergy Q m v)
    (S.solverEnergy_continuous model.continuous m v).stronglyMeasurable
    (S.solverEnergy_nonneg hm.le v hmin) _ hW
    (fun t => S.refreshKernel_energy_integrable O m E model.continuous v (t.1, t.2.1))
    (S.refreshFromStateKernel_energy_bound O hαℓ hfast hm (he.trans_le heE) model v hmin)
  change Integrable (S.solverEnergy Q m v) (S.fullEpochKernel O m H e E r hr z) at hi
  refine ⟨hi, ?_⟩
  have hsum : Integrable (fun t : EpochState dx dy =>
      66 * statePotential Q m v t.2 + 4 * (m * ‖t.1 - S.sliceMin v‖ ^ 2) / 1000000)
      (S.epochPhaseStateKernel O m H e E r hr z) :=
    (hP.const_mul 66).add ((hR.const_mul 4).div_const 1000000)
  rw [integral_add hsum (integrable_const _),
    integral_add (hP.const_mul 66) ((hR.const_mul 4).div_const 1000000),
    integral_const_mul, integral_div, integral_const_mul, hRe,
    integral_const, measureReal_univ_eq_one, one_smul] at hb
  change (∫ w, S.solverEnergy Q m v w ∂S.fullEpochKernel O m H e E r hr z) ≤ _ at hb
  have hEn := S.solverEnergy_nonneg hm.le v hmin z
  have hRle := S.referenceError_le_solverEnergy m v hmin z
  have hE := he.trans_le heE
  change (∫ t, statePotential Q m v t.2 ∂S.epochPhaseStateKernel O m H e E r hr z) ≤
    S.solverEnergy Q m v z / (1000000 * 17) + E / (1000000 * 17) at hPb
  linarith only [hb, hPb, hEn, hRle, hE]

theorem fullEpochKernel_random_accuracy (O : FreshOracle S.toNCObjective σ)
    (hαℓ : α ≤ ℓ) (hfast : ℓ / 4 ≤ α) {m H e E : ℝ}
    (hm : 0 < m) (hmH : m ≤ H) (he : 0 < e) (heE : e ≤ E)
    (r : Euclid dy → Euclid dy) (hr : Measurable r) {Q : Euclid dy → ℝ}
    (model : SmoothStrongModel Q (fun v => gradient S.effectiveValue v + r v) m H)
    (v : Euclid dy) (hmin : ∀ x, Q v ≤ Q x) (ν : Measure (Joint dx dy)) [IsProbabilityMeasure ν]
    (hInit : Integrable (S.solverEnergy Q m v) ν)
    (hEnergy : (∫ z, S.solverEnergy Q m v z ∂ν) ≤ E) :
    Integrable (S.solverEnergy Q m v) (S.fullEpochKernel O m H e E r hr ∘ₘ ν) ∧
    (∫ z, S.solverEnergy Q m v z ∂S.fullEpochKernel O m H e E r hr ∘ₘ ν) ≤ E / 50000 := by
  have hW : Integrable (fun z => S.solverEnergy Q m v z / 100000 + E / 100000) ν :=
    (hInit.div_const 100000).add (integrable_const _)
  obtain ⟨hi, hb⟩ := kernel_moment_from_envelope (S.fullEpochKernel O m H e E r hr) ν
    (S.solverEnergy Q m v) (S.solverEnergy_continuous model.continuous m v).stronglyMeasurable
    (S.solverEnergy_nonneg hm.le v hmin) _ hW
    (fun z => (S.fullEpochKernel_contract O hαℓ hfast hm hmH he heE r hr model v hmin z).1)
    (fun z => (S.fullEpochKernel_contract O hαℓ hfast hm hmH he heE r hr model v hmin z).2)
  refine ⟨hi, ?_⟩
  rw [integral_add (hInit.div_const 100000) (integrable_const _), integral_div,
    integral_const, measureReal_univ_eq_one, one_smul] at hb
  linarith only [hb, hEnergy]

theorem fullEpochKernel_halving (O : FreshOracle S.toNCObjective σ)
    (hαℓ : α ≤ ℓ) (hfast : ℓ / 4 ≤ α) {m H e E : ℝ}
    (hm : 0 < m) (hmH : m ≤ H) (he : 0 < e) (heE : e ≤ E)
    (r : Euclid dy → Euclid dy) (hr : Measurable r) {Q : Euclid dy → ℝ}
    (model : SmoothStrongModel Q (fun v => gradient S.effectiveValue v + r v) m H)
    (v : Euclid dy) (hmin : ∀ x, Q v ≤ Q x) (ν : Measure (Joint dx dy)) [IsProbabilityMeasure ν]
    (hInit : Integrable (S.solverEnergy Q m v) ν)
    (hEnergy : (∫ z, S.solverEnergy Q m v z ∂ν) ≤ E) :
    (∫ z, S.solverEnergy Q m v z ∂S.fullEpochKernel O m H e E r hr ∘ₘ ν) ≤ E / 2 := by
  have h := (S.fullEpochKernel_random_accuracy O hαℓ hfast hm hmH he heE r hr model v hmin ν hInit hEnergy).2
  have hE := he.trans_le heE
  linarith

end SCObjective
end FreshGradientMinimax
