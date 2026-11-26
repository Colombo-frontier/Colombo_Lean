import Bilevel.TransportNetworkAuxiliary
import Bilevel.TransportNetworkEdgeInitialization

/-! Full-frame edge conditioning with independent auxiliary hierarchy frames.
Conditioning even on their complete orientations leaves the network-only
gauge symmetry intact; the residual edge dimension is not charged for them. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace Bilevel.TransportNetworkAuxiliary
open TransportNetwork EuclideanGaussian OrthogonalAction
set_option maxHeartbeats 600000
set_option synthInstance.maxHeartbeats 100000

abbrev FullContext {n D : ℕ} (e : Edge n) (T k : ℕ) :=
  Context (d := D) e T × (Fin k → OrthogonalHaar.Group D)

def fullContext {n D k : ℕ} (T : ℕ) (hT : T ≤ D) (e : Edge n) (s : Sample n D k) :
    FullContext (D := D) e T k := (context T hT e s.1,s.2)

def fullContextGauge {n D T k : ℕ} {e : Edge n} (R : Gauge n D)
    (c : FullContext (D := D) e T k) : FullContext (D := D) e T k :=
  (contextGauge R c.1,c.2)

def fullContextAction {n D T k : ℕ} (e : Edge n) :
    MulAction (Gauge n D) (FullContext (D := D) e T k) where
  smul := fullContextGauge
  one_smul c := by
    change (contextGauge 1 c.1,c.2) = c
    exact Prod.ext (one_smul (Gauge n D) c.1) rfl
  mul_smul R S c := by
    change (contextGauge (R*S) c.1,c.2) = (contextGauge R (contextGauge S c.1),c.2)
    exact Prod.ext (mul_smul R S c.1) rfl

theorem fullContext_measurable {n D k : ℕ} (T : ℕ) (hT : T ≤ D) (e : Edge n) :
    Measurable (fullContext (k := k) T hT e) :=
  ((context_measurable T hT e).comp measurable_fst).prodMk measurable_snd

theorem fullContextGauge_measurable {n D T k : ℕ} (e : Edge n) :
    Measurable (fun p : Gauge n D × FullContext (D := D) e T k => fullContextGauge p.1 p.2) :=
  ((context_gauge_measurable e).comp
    (measurable_fst.prodMk (measurable_fst.comp measurable_snd))).prodMk (measurable_snd.comp measurable_snd)

theorem fullContext_posterior_isotropy {n D k : ℕ} (T : ℕ) (hT : T ≤ D) (e : Edge n) :
    ∀ᵐ c ∂(law n D k).map (fullContext T hT e), ∀ R : Gauge n D,
      fullContextGauge R c = c →
      MeasurePreserving (networkGauge R)
        (condDistrib id (fullContext T hT e) (law n D k) c)
        (condDistrib id (fullContext T hT e) (law n D k) c) := by
  letI : MulAction (Gauge n D) (Sample n D k) := networkAction n D k
  letI : MeasurableSMul₂ (Gauge n D) (Sample n D k) := ⟨network_measurable n D k⟩
  letI : MulAction (Gauge n D) (FullContext (D := D) e T k) := fullContextAction e
  letI : MeasurableSMul₂ (Gauge n D) (FullContext (D := D) e T k) := ⟨fullContextGauge_measurable e⟩
  apply ConditionalSupport.equivariant_observation (law n D k) (fullContext T hT e)
    (fullContext_measurable T hT e) (gaugeLaw n D) (network_preserving)
  intro R s
  exact Prod.ext (context_equivariant T hT e R s.1) rfl

theorem fullContext_network_fiber {n D k : ℕ} (T : ℕ) (hT : T ≤ D) (e : Edge n) :
    ∀ᵐ c ∂(law n D k).map (fullContext T hT e),
      ∀ᵐ s ∂condDistrib id (fullContext T hT e) (law n D k) c,
        context T hT e s.1 = c.1 := by
  let o := fullContext (k := k) T hT e
  have ho : Measurable o := fullContext_measurable T hT e
  have hf : Measurable (fun p : FullContext (D := D) e T k × Sample n D k => context T hT e p.2.1) :=
    (context_measurable T hT e).comp (measurable_fst.comp measurable_snd)
  have hA := measurableSet_eq_fun hf.fst (measurable_fst.fst.fst)
  have hB : MeasurableSet {p : FullContext (D := D) e T k × Sample n D k |
      (context T hT e p.2.1).2 = p.1.1.2} := by
    have he : {p : FullContext (D := D) e T k × Sample n D k |
        (context T hT e p.2.1).2 = p.1.1.2} =
        {p | (context T hT e p.2.1).2*(p.1.1.2)⁻¹ = 1} := by
      ext p; simp only [Set.mem_setOf_eq,mul_inv_eq_one]
    rw [he]
    exact (hf.snd.mul (measurable_fst.fst.snd.inv)) (measurableSet_singleton 1)
  have hgraph : MeasurableSet {p : FullContext (D := D) e T k × Sample n D k |
      context T hT e p.2.1 = p.1.1} := by
    convert hA.inter hB using 1
    ext p; simp only [Set.mem_setOf_eq,Set.mem_inter_iff,Prod.ext_iff]
  have hm : Measurable (fun s : Sample n D k => (o s,s)) := ho.prodMk measurable_id
  have hj : ∀ᵐ p ∂(law n D k).map (fun s => (o s,s)), context T hT e p.2.1 = p.1.1 :=
    (ae_map_iff hm.aemeasurable hgraph).mpr (Filter.Eventually.of_forall (fun _ => rfl))
  rw [← ConditionalSupport.joint_law (law n D k) o] at hj
  exact Measure.ae_ae_of_ae_compProd hj

def edgePosterior {n D k : ℕ} (T : ℕ) (hT : T ≤ D) (e : Edge n) (s₀ : Sample n D k) :
    Measure (OrthogonalHaar.Group D) :=
  (condDistrib id (fullContext T hT e) (law n D k) (fullContext T hT e s₀)).map (fun s => s.1.2 e)

instance edgePosterior_probability {n D k : ℕ} (T : ℕ) (hT : T ≤ D) (e : Edge n) (s₀ : Sample n D k) :
    IsProbabilityMeasure (edgePosterior T hT e s₀) :=
  isProbabilityMeasure_map (((measurable_pi_apply e).comp (measurable_snd.comp measurable_fst)).aemeasurable)

theorem edgePosterior_initialized {n D k : ℕ} (T : ℕ) (hT : T ≤ D) (e : Edge n) :
    ∀ᵐ s₀ ∂law n D k,
      TransportEdgePosterior.Invariant (TransportEdgePosterior.range (hardPairs T hT e s₀.1))
        (edgePosterior T hT e s₀) ∧
      (∀ᵐ O ∂edgePosterior T hT e s₀, TransportEdgePosterior.Supports (hardPairs T hT e s₀.1) O) := by
  have hp := ae_of_ae_map (fullContext_measurable (k := k) T hT e).aemeasurable
    (fullContext_posterior_isotropy (k := k) T hT e)
  have hf := ae_of_ae_map (fullContext_measurable (k := k) T hT e).aemeasurable
    (fullContext_network_fiber (k := k) T hT e)
  filter_upwards [hp,hf] with s₀ hs₀ hsFiber
  constructor
  · intro S
    let R := rightGauge e s₀.1 S.val
    have hfix : fullContextGauge R (fullContext T hT e s₀) = fullContext T hT e s₀ := by
      apply Prod.ext
      · apply rightGauge_context_fixed T hT e s₀.1 S.val
        intro i
        exact (ProjectionStabilizer.membership D (TransportEdgePosterior.range (hardPairs T hT e s₀.1))
          S.val).mp S.property _ (hardPairs_output_mem T hT e s₀.1 i)
      · rfl
    have hm : Measurable (fun s : Sample n D k => s.1.2 e) :=
      (measurable_pi_apply e).comp (measurable_snd.comp measurable_fst)
    apply ConditionalSymmetry.pushforward_preserving _ (fun s : Sample n D k => s.1.2 e) hm
      (networkGauge R) (fun O : OrthogonalHaar.Group D => S.val*O) (hs₀ R hfix)
      (measurable_const.mul measurable_id)
    exact fun s => rightGauge_edge_action e s₀.1 s.1 S.val
  · apply (ae_map_iff (((measurable_pi_apply e).comp (measurable_snd.comp measurable_fst)).aemeasurable)
      (TransportEdgePosterior.support_measurable (hardPairs T hT e s₀.1))).mpr
    filter_upwards [hsFiber] with s hs
    apply (supports_iff_pairs _ _).mpr
    intro p hp
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hp
    have hsrc := congrArg (fun c : Context (d := D) e T => c.1 (src e) i) hs
    have hdst := congrArg (fun c : Context (d := D) e T => c.1 (dst e) i) hs
    change frame T hT s.1 (src e) i = frame T hT s₀.1 (src e) i at hsrc
    change frame T hT s.1 (dst e) i = frame T hT s₀.1 (dst e) i at hdst
    simpa only [hsrc,hdst] using edge_frame T hT s.1 e i

end Bilevel.TransportNetworkAuxiliary
