import Bilevel.TransportNetworkGauge

/-! Product stabilizers of the actually known subspaces at all physical
layers. They act on the same latent network, retaining shared edge maps. -/
noncomputable section
open MeasureTheory
namespace Bilevel.TransportNetwork
open EuclideanGaussian OrthogonalAction
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 400000

abbrev Known (n d : ℕ) := Vertex n → Submodule ℝ (Space d)
abbrev LocalGauge {n d : ℕ} (W : Known n d) :=
  ∀ v : Vertex n, ProjectionStabilizer.subgroup d (W v)

def lift {n d : ℕ} {W : Known n d} (R : LocalGauge W) : Gauge n d := fun v => (R v).val

instance localAction {n d : ℕ} (W : Known n d) : MulAction (LocalGauge W) (Latent n d) where
  smul R z := gauge (lift R) z
  one_smul z := by
    change (1 : Gauge n d) • z = z
    exact one_smul _ _
  mul_smul R S z := by
    change (lift R*lift S) • z = lift R • (lift S • z)
    exact mul_smul _ _ _

theorem lift_continuous {n d : ℕ} (W : Known n d) : Continuous (lift (W := W)) := by
  apply continuous_pi
  intro v
  exact continuous_subtype_val.comp (continuous_apply v)

instance localMeasurableAction {n d : ℕ} (W : Known n d) :
    MeasurableSMul₂ (LocalGauge W) (Latent n d) :=
  ⟨((gauge_continuous n d).comp
    (((lift_continuous W).comp continuous_fst).prodMk continuous_snd)).measurable⟩

def localLaw {n d : ℕ} (W : Known n d) : Measure (LocalGauge W) :=
  Measure.pi (fun v => ProjectionStabilizer.law d (W v))

instance localLaw_probability {n d : ℕ} (W : Known n d) : IsProbabilityMeasure (localLaw W) := by
  unfold localLaw
  infer_instance

instance localLaw_leftInvariant {n d : ℕ} (W : Known n d) :
    Measure.IsMulLeftInvariant (localLaw W) := by
  unfold localLaw
  infer_instance

def Invariant {n d : ℕ} (W : Known n d) (μ : Measure (Latent n d)) : Prop :=
  ∀ R : LocalGauge W, MeasurePreserving (fun z : Latent n d => R • z) μ μ

theorem law_invariant {n d : ℕ} (W : Known n d) : Invariant W (law n d) :=
  fun R => gauge_preserving n d (lift R)

def restrictGauge {n d : ℕ} {W S : Known n d} (hWS : ∀ v, W v ≤ S v)
    (R : LocalGauge S) : LocalGauge W := fun v =>
  ⟨(R v).val,(ProjectionStabilizer.membership d (W v) (R v).val).mpr
    (fun y hy => (ProjectionStabilizer.membership d (S v) (R v).val).mp
      (R v).property y (hWS v hy))⟩

theorem restrictGauge_action {n d : ℕ} {W S : Known n d} (hWS : ∀ v, W v ≤ S v)
    (R : LocalGauge S) (z : Latent n d) : restrictGauge hWS R • z = R • z := rfl

theorem invariant_mono {n d : ℕ} {W S : Known n d} (hWS : ∀ v, W v ≤ S v)
    (μ : Measure (Latent n d)) (hμ : Invariant W μ) : Invariant S μ :=
  fun R => hμ (restrictGauge hWS R)

def insert {n d : ℕ} (W : Known n d) (v : Vertex n) (q : Space d) : Known n d :=
  Function.update W v (W v ⊔ Submodule.span ℝ {q})

theorem le_insert {n d : ℕ} (W : Known n d) (v : Vertex n) (q : Space d) :
    ∀ j, W j ≤ insert W v q j := by
  intro j
  by_cases h : j = v
  · subst j
    simpa only [insert,Function.update_self] using
      (show W v ≤ W v ⊔ Submodule.span ℝ {q} from le_sup_left)
  · simp only [insert,Function.update_of_ne h,le_refl]

theorem mem_insert {n d : ℕ} (W : Known n d) (v : Vertex n) (q : Space d) :
    q ∈ insert W v q v := by
  simp only [insert,Function.update_self]
  exact (show Submodule.span ℝ {q} ≤ W v ⊔ Submodule.span ℝ {q} from le_sup_right)
    (Submodule.mem_span_singleton_self q)

theorem fixed_vector {n d : ℕ} {W : Known n d} (R : LocalGauge W)
    (v : Vertex n) (q : Space d) (hq : q ∈ W v) : (R v).val • q = q :=
  (ProjectionStabilizer.membership d (W v) (R v).val).mp (R v).property q hq

/-- The output action at a specified physical layer. Kept explicit because
the same gauge group has different actions at different layers. -/
def layerAction {n d : ℕ} (W : Known n d) (v : Vertex n) :
    MulAction (LocalGauge W) (Space d) where
  smul R q := (R v).val • q
  one_smul q := by
    change (1 : OrthogonalHaar.Group d) • q = q
    exact one_smul _ q
  mul_smul R S q := by
    change ((R v).val*(S v).val) • q = (R v).val • ((S v).val • q)
    exact mul_smul _ _ _

theorem layer_action_measurable {n d : ℕ} (W : Known n d) (v : Vertex n) :
    Measurable (fun p : LocalGauge W × Space d => (p.1 v).val • p.2) := by
  have hm : Measurable (fun R : LocalGauge W => (R v).val) :=
    (continuous_subtype_val.comp (continuous_apply v)).measurable
  exact (hm.comp measurable_fst).smul measurable_snd

end Bilevel.TransportNetwork
