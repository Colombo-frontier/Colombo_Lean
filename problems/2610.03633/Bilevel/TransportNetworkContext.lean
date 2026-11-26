import Bilevel.TransportNetworkObservation

/-! The SECOND conditioning used for a transport edge: all full transported
hard frames and every other complete edge map. It is separate from the
algorithm-observer transcript conditioning used for fresh-query moments. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace Bilevel.TransportNetwork
open EuclideanGaussian OrthogonalAction
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 600000

abbrev OtherEdge {n : ℕ} (e : Edge n) := {f : Edge n // f ≠ e}
abbrev Context {n d : ℕ} (e : Edge n) (T : ℕ) :=
  (Vertex n → Fin T → Space d) × (OtherEdge e → OrthogonalHaar.Group d)

def context {n d : ℕ} (T : ℕ) (hT : T ≤ d) (e : Edge n) (z : Latent n d) : Context (d := d) e T :=
  (frame T hT z,fun f => z.2 f.val)

def contextGauge {n d T : ℕ} {e : Edge n} (R : Gauge n d) (c : Context (d := d) e T) :
    Context (d := d) e T :=
  (fun v i => R v • c.1 v i,fun f => R (dst f.val)*c.2 f*(R (src f.val))⁻¹)

instance contextAction {n d T : ℕ} (e : Edge n) : MulAction (Gauge n d) (Context (d := d) e T) where
  smul := contextGauge
  one_smul c := by
    change contextGauge 1 c = c
    apply Prod.ext
    · funext v i; simp [contextGauge]
    · funext f; simp [contextGauge]
  mul_smul R S c := by
    change contextGauge (R*S) c = contextGauge R (contextGauge S c)
    apply Prod.ext
    · funext v i; simp [contextGauge,mul_smul]
    · funext f; simp [contextGauge,mul_assoc]

theorem context_gauge_measurable {n d T : ℕ} (e : Edge n) :
    Measurable (fun p : Gauge n d × Context (d := d) e T => contextGauge p.1 p.2) := by
  apply Measurable.prodMk
  · apply measurable_pi_lambda
    intro v
    apply measurable_pi_lambda
    intro i
    have hR : Measurable (fun p : Gauge n d × Context (d := d) e T => p.1 v) :=
      (measurable_pi_apply v).comp measurable_fst
    have hC : Measurable (fun p : Gauge n d × Context (d := d) e T => p.2.1 v i) :=
      (measurable_pi_apply i).comp ((measurable_pi_apply v).comp (measurable_fst.comp measurable_snd))
    exact hR.smul hC
  · apply measurable_pi_lambda
    intro f
    exact (((measurable_pi_apply (dst f.val)).comp measurable_fst).mul
      ((measurable_pi_apply f).comp (measurable_snd.comp measurable_snd))).mul
      (((measurable_pi_apply (src f.val)).comp measurable_fst).inv)

instance contextMeasurableAction {n d T : ℕ} (e : Edge n) :
    MeasurableSMul₂ (Gauge n d) (Context (d := d) e T) := ⟨context_gauge_measurable e⟩

def gaugeLaw (n d : ℕ) : Measure (Gauge n d) :=
  Measure.pi (fun _ : Vertex n => OrthogonalHaar.law d)

instance gaugeLaw_probability (n d : ℕ) : IsProbabilityMeasure (gaugeLaw n d) := by
  unfold gaugeLaw
  infer_instance

instance gaugeLaw_leftInvariant (n d : ℕ) : Measure.IsMulLeftInvariant (gaugeLaw n d) := by
  unfold gaugeLaw
  infer_instance

theorem context_measurable {n d : ℕ} (T : ℕ) (hT : T ≤ d) (e : Edge n) :
    Measurable (context (n := n) T hT e) :=
  (frame_measurable n d T hT).prodMk
    (measurable_pi_lambda _ (fun f => (measurable_pi_apply f.val).comp measurable_snd))

theorem context_equivariant {n d : ℕ} (T : ℕ) (hT : T ≤ d) (e : Edge n)
    (R : Gauge n d) (z : Latent n d) : context T hT e (R • z) = R • context T hT e z := by
  apply Prod.ext
  · funext v i
    exact frame_gauge T hT R z v i
  · rfl

/-- Actual regular conditional laws after full-frame/other-edge conditioning
are invariant under every gauge fixing the observed context. This conclusion
is not substituted for the separate query-transcript invariance theorem. -/
theorem context_posterior_isotropy {n d : ℕ} (T : ℕ) (hT : T ≤ d) (e : Edge n) :
    ∀ᵐ c ∂(law n d).map (context T hT e),
      ∀ R : Gauge n d, R • c = c →
        MeasurePreserving (fun z : Latent n d => R • z)
          (condDistrib id (context T hT e) (law n d) c)
          (condDistrib id (context T hT e) (law n d) c) :=
  ConditionalSupport.equivariant_observation (law n d) (context T hT e)
    (context_measurable T hT e) (gaugeLaw n d) (gauge_preserving n d)
    (context_equivariant T hT e)

theorem context_posterior_fiber {n d : ℕ} (T : ℕ) (hT : T ≤ d) (e : Edge n) :
    ∀ᵐ c ∂(law n d).map (context T hT e),
      ∀ᵐ z ∂condDistrib id (context T hT e) (law n d) c, context T hT e z = c := by
  apply ConditionalSupport.fiber (law n d) (context T hT e) (context_measurable T hT e)
  have hf : Measurable (fun p : Context (d := d) e T × Latent n d => context T hT e p.2) :=
    (context_measurable T hT e).comp measurable_snd
  have hA := measurableSet_eq_fun hf.fst (measurable_fst.fst)
  have hB : MeasurableSet {p : Context (d := d) e T × Latent n d |
      (context T hT e p.2).2 = p.1.2} := by
    have he : {p : Context (d := d) e T × Latent n d |
        (context T hT e p.2).2 = p.1.2} =
        {p | (context T hT e p.2).2*(p.1.2)⁻¹ = 1} := by
      ext p
      simp only [Set.mem_setOf_eq,mul_inv_eq_one]
    rw [he]
    exact (hf.snd.mul (measurable_fst.snd.inv)) (measurableSet_singleton 1)
  convert hA.inter hB using 1
  ext p
  simp only [Set.mem_setOf_eq,Set.mem_inter_iff,Prod.ext_iff]

end Bilevel.TransportNetwork
