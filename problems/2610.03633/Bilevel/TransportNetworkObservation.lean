import Bilevel.TransportNetworkStandardBorel

/-! Actual frame queries, named-column observations, and forward/reverse edge
actions preserve the appropriate layerwise stabilizers of the genuine regular
conditional network law. Both directions observe the SAME edge variable. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace
namespace Bilevel.TransportNetwork
open EuclideanGaussian OrthogonalAction
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 600000

def queryObservation {n d : ℕ} (T : ℕ) (hT : T ≤ d)
    (v : Vertex n) (q : Space d) (z : Latent n d) : Fin T → ℝ :=
  fun i => ⟪q,frame T hT z v i⟫

def namedObservation {n d : ℕ} (T : ℕ) (hT : T ≤ d)
    (v : Vertex n) (i : Fin T) (z : Latent n d) : Space d := frame T hT z v i

def forwardObservation {n d : ℕ} (e : Edge n) (q : Space d) (z : Latent n d) : Space d :=
  z.2 e • q

def reverseObservation {n d : ℕ} (e : Edge n) (q : Space d) (z : Latent n d) : Space d :=
  (z.2 e)⁻¹ • q

theorem named_measurable {n d : ℕ} (T : ℕ) (hT : T ≤ d) (v : Vertex n) (i : Fin T) :
    Measurable (namedObservation T hT v i) :=
  (measurable_pi_apply i).comp ((measurable_pi_apply v).comp (frame_measurable n d T hT))

theorem query_measurable {n d : ℕ} (T : ℕ) (hT : T ≤ d) (v : Vertex n) (q : Space d) :
    Measurable (queryObservation T hT v q) := by
  apply measurable_pi_lambda
  intro i
  exact (continuous_const.inner continuous_id).measurable.comp (named_measurable T hT v i)

theorem forward_measurable {n d : ℕ} (e : Edge n) (q : Space d) :
    Measurable (forwardObservation (d := d) e q) :=
  ((measurable_pi_apply e).comp measurable_snd).smul measurable_const

theorem reverse_measurable {n d : ℕ} (e : Edge n) (q : Space d) :
    Measurable (reverseObservation (d := d) e q) :=
  (((measurable_pi_apply e).comp measurable_snd).inv).smul measurable_const

theorem query_invariant {n d : ℕ} (T : ℕ) (hT : T ≤ d) (W : Known n d)
    (v : Vertex n) (q : Space d) (hq : q ∈ W v) (R : LocalGauge W) (z : Latent n d) :
    queryObservation T hT v q (R • z) = queryObservation T hT v q z := by
  funext i
  change ⟪q,frame T hT (gauge (lift R) z) v i⟫ = ⟪q,frame T hT z v i⟫
  rw [frame_gauge]
  have hh := (isometry d (R v).val).inner_map_map q (frame T hT z v i)
  change ⟪(R v).val • q,(R v).val • frame T hT z v i⟫ = _ at hh
  rwa [fixed_vector R v q hq] at hh

theorem forward_equivariant {n d : ℕ} (W : Known n d) (e : Edge n)
    (q : Space d) (hq : q ∈ W (src e)) (R : LocalGauge W) (z : Latent n d) :
    forwardObservation e q (R • z) = (R (dst e)).val • forwardObservation e q z := by
  have hf := fixed_vector (R⁻¹) (src e) q hq
  change (R (src e)).val⁻¹ • q = q at hf
  change ((R (dst e)).val*z.2 e*(R (src e)).val⁻¹) • q =
    (R (dst e)).val • (z.2 e • q)
  rw [mul_smul,mul_smul,hf]

theorem reverse_equivariant {n d : ℕ} (W : Known n d) (e : Edge n)
    (q : Space d) (hq : q ∈ W (dst e)) (R : LocalGauge W) (z : Latent n d) :
    reverseObservation e q (R • z) = (R (src e)).val • reverseObservation e q z := by
  have hf := fixed_vector (R⁻¹) (dst e) q hq
  change (R (dst e)).val⁻¹ • q = q at hf
  change ((R (dst e)).val*z.2 e*(R (src e)).val⁻¹)⁻¹ • q =
    (R (src e)).val • ((z.2 e)⁻¹ • q)
  simp only [mul_inv_rev,inv_inv,mul_smul,hf]

theorem query_posterior_invariant {n d : ℕ} (T : ℕ) (hT : T ≤ d)
    (W : Known n d) (μ : Measure (Latent n d)) [IsProbabilityMeasure μ]
    (hμ : Invariant W μ) (v : Vertex n) (q : Space d) :
    ∀ᵐ y ∂μ.map (queryObservation T hT v q),
      Invariant (insert W v q) (condDistrib id (queryObservation T hT v q) μ y) := by
  have hp := invariant_mono (le_insert W v q) μ hμ
  exact ConditionalSupport.invariant_observation μ (queryObservation T hT v q)
    (query_measurable T hT v q) (localLaw (insert W v q)) hp
    (fun R z => query_invariant T hT (insert W v q) v q (mem_insert W v q) R z)

/-- An actual equivariant vector observation inserts its observed value into
the corresponding known space, and its posterior retains the resulting
product stabilizer. This is applied below to each concrete oracle observation. -/
theorem vector_posterior_invariant {n d : ℕ} (W : Known n d)
    (μ : Measure (Latent n d)) [IsProbabilityMeasure μ] (hμ : Invariant W μ)
    (v : Vertex n) (o : Latent n d → Space d) (ho : Measurable o)
    (he : ∀ R : LocalGauge W, ∀ z, o (R • z) = (R v).val • o z) :
    ∀ᵐ y ∂μ.map o, Invariant (insert W v y) (condDistrib id o μ y) := by
  letI : MulAction (LocalGauge W) (Space d) := layerAction W v
  letI : MeasurableSMul₂ (LocalGauge W) (Space d) := ⟨layer_action_measurable W v⟩
  have hp := ConditionalSupport.equivariant_observation μ o ho (localLaw W) hμ he
  filter_upwards [hp] with y hy
  intro R
  let B : LocalGauge W := restrictGauge (le_insert W v y) R
  have hf : B • y = y := fixed_vector R v y (mem_insert W v y)
  exact hy B hf

theorem named_posterior_invariant {n d : ℕ} (T : ℕ) (hT : T ≤ d)
    (W : Known n d) (μ : Measure (Latent n d)) [IsProbabilityMeasure μ]
    (hμ : Invariant W μ) (v : Vertex n) (i : Fin T) :
    ∀ᵐ y ∂μ.map (namedObservation T hT v i),
      Invariant (insert W v y) (condDistrib id (namedObservation T hT v i) μ y) :=
  vector_posterior_invariant W μ hμ v _ (named_measurable T hT v i)
    (fun R z => frame_gauge T hT (lift R) z v i)

theorem forward_posterior_invariant {n d : ℕ} (W : Known n d)
    (μ : Measure (Latent n d)) [IsProbabilityMeasure μ] (hμ : Invariant W μ)
    (e : Edge n) (q : Space d) (hq : q ∈ W (src e)) :
    ∀ᵐ y ∂μ.map (forwardObservation e q),
      Invariant (insert W (dst e) y) (condDistrib id (forwardObservation e q) μ y) :=
  vector_posterior_invariant W μ hμ (dst e) _ (forward_measurable e q)
    (forward_equivariant W e q hq)

theorem reverse_posterior_invariant {n d : ℕ} (W : Known n d)
    (μ : Measure (Latent n d)) [IsProbabilityMeasure μ] (hμ : Invariant W μ)
    (e : Edge n) (q : Space d) (hq : q ∈ W (dst e)) :
    ∀ᵐ y ∂μ.map (reverseObservation e q),
      Invariant (insert W (src e) y) (condDistrib id (reverseObservation e q) μ y) :=
  vector_posterior_invariant W μ hμ (src e) _ (reverse_measurable e q)
    (reverse_equivariant W e q hq)

end Bilevel.TransportNetwork
