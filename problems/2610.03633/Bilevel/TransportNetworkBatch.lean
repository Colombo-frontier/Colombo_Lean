import Bilevel.TransportNetworkObservation

/-! A genuine frozen transport batch. Every input is fixed before observing
any batch output, and lies in the pre-batch known space at its input layer.
All outputs use the same latent edge maps. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace Bilevel.TransportNetwork
open EuclideanGaussian OrthogonalAction
set_option maxHeartbeats 500000
set_option synthInstance.maxHeartbeats 100000

/-- false is forward; true is reverse. -/
abbrev Probe (n d : ℕ) := Bool × Edge n × Space d

def inputLayer {n d : ℕ} (p : Probe n d) : Vertex n := if p.1 then dst p.2.1 else src p.2.1
def outputLayer {n d : ℕ} (p : Probe n d) : Vertex n := if p.1 then src p.2.1 else dst p.2.1

def probeObservation {n d : ℕ} (p : Probe n d) (z : Latent n d) : Space d :=
  if p.1 then reverseObservation p.2.1 p.2.2 z else forwardObservation p.2.1 p.2.2 z

theorem probe_measurable {n d : ℕ} (p : Probe n d) : Measurable (probeObservation p) := by
  rcases p with ⟨b,e,q⟩
  cases b
  · exact forward_measurable e q
  · exact reverse_measurable e q

def batchObservation {n d k : ℕ} (p : Fin k → Probe n d) (z : Latent n d) : Fin k → Space d :=
  fun i => probeObservation (p i) z

theorem batch_measurable {n d k : ℕ} (p : Fin k → Probe n d) : Measurable (batchObservation p) :=
  measurable_pi_lambda _ (fun i => probe_measurable (p i))

def batchKnown {n d k : ℕ} (W : Known n d) (p : Fin k → Probe n d)
    (y : Fin k → Space d) : Known n d := fun v =>
  W v ⊔ Submodule.span ℝ (Set.range (fun i : {i : Fin k // outputLayer (p i) = v} => y i.val))

theorem le_batchKnown {n d k : ℕ} (W : Known n d) (p : Fin k → Probe n d) (y : Fin k → Space d) :
    ∀ v, W v ≤ batchKnown W p y v := fun _ => le_sup_left

theorem mem_batchKnown {n d k : ℕ} (W : Known n d) (p : Fin k → Probe n d)
    (y : Fin k → Space d) (i : Fin k) : y i ∈ batchKnown W p y (outputLayer (p i)) :=
  (show Submodule.span ℝ (Set.range
    (fun j : {j : Fin k // outputLayer (p j) = outputLayer (p i)} => y j.val)) ≤
      batchKnown W p y (outputLayer (p i)) from le_sup_right)
    (Submodule.subset_span ⟨⟨i,rfl⟩,rfl⟩)

def batchAction {n d k : ℕ} (W : Known n d) (p : Fin k → Probe n d) :
    MulAction (LocalGauge W) (Fin k → Space d) where
  smul R y := fun i => (R (outputLayer (p i))).val • y i
  one_smul y := by
    funext i
    change (1 : OrthogonalHaar.Group d) • y i = y i
    exact one_smul _ _
  mul_smul R S y := by
    funext i
    change ((R (outputLayer (p i))).val*(S (outputLayer (p i))).val) • y i =
      (R (outputLayer (p i))).val • ((S (outputLayer (p i))).val • y i)
    exact mul_smul _ _ _

theorem batch_action_measurable {n d k : ℕ} (W : Known n d) (p : Fin k → Probe n d) :
    Measurable (fun z : LocalGauge W × (Fin k → Space d) =>
      fun i => (z.1 (outputLayer (p i))).val • z.2 i) := by
  apply measurable_pi_lambda
  intro i
  have hm : Measurable (fun R : LocalGauge W => (R (outputLayer (p i))).val) :=
    (continuous_subtype_val.comp (continuous_apply (outputLayer (p i)))).measurable
  exact (hm.comp measurable_fst).smul ((measurable_pi_apply i).comp measurable_snd)

theorem probe_equivariant {n d : ℕ} (W : Known n d) (p : Probe n d)
    (hp : p.2.2 ∈ W (inputLayer p)) (R : LocalGauge W) (z : Latent n d) :
    probeObservation p (R • z) = (R (outputLayer p)).val • probeObservation p z := by
  rcases p with ⟨b,e,q⟩
  cases b
  · exact forward_equivariant W e q hp R z
  · exact reverse_equivariant W e q hp R z

/-- Full-vector conditioning after the frozen batch retains all stabilizers
fixing both the old spaces and the actually returned vectors. The required
input membership refers to W before the batch, not an updated source space. -/
theorem batch_posterior_invariant {n d k : ℕ} (W : Known n d)
    (μ : Measure (Latent n d)) [IsProbabilityMeasure μ] (hμ : Invariant W μ)
    (p : Fin k → Probe n d) (hp : ∀ i, (p i).2.2 ∈ W (inputLayer (p i))) :
    ∀ᵐ y ∂μ.map (batchObservation p),
      Invariant (batchKnown W p y) (condDistrib id (batchObservation p) μ y) := by
  letI : MulAction (LocalGauge W) (Fin k → Space d) := batchAction W p
  letI : MeasurableSMul₂ (LocalGauge W) (Fin k → Space d) := ⟨batch_action_measurable W p⟩
  have he : ∀ R : LocalGauge W, ∀ z, batchObservation p (R • z) = R • batchObservation p z := by
    intro R z
    funext i
    exact probe_equivariant W (p i) (hp i) R z
  have hh := ConditionalSupport.equivariant_observation μ (batchObservation p)
    (batch_measurable p) (localLaw W) hμ he
  filter_upwards [hh] with y hy
  intro R
  let B : LocalGauge W := restrictGauge (le_batchKnown W p y) R
  have hf : B • y = y := by
    funext i
    exact fixed_vector R (outputLayer (p i)) (y i) (mem_batchKnown W p y i)
  exact hy B hf

end Bilevel.TransportNetwork
