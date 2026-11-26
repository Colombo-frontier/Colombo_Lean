import Bilevel.TransportNetworkContext

/-! Independent auxiliary hierarchy frame orientations on physical layers.
Two genuine prior symmetries are distinguished: the joint layerwise gauge for
query conditioning, and network-only gauges fixing every auxiliary variable
for full-frame/other-edge conditioning. -/
noncomputable section
open MeasureTheory
namespace Bilevel.TransportNetworkAuxiliary
open Bilevel.TransportNetwork Bilevel.EuclideanGaussian Bilevel.OrthogonalAction
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 100000

abbrev Sample (n D k : ℕ) := Latent n D × (Fin k → Bilevel.OrthogonalHaar.Group D)

def law (n D k : ℕ) : Measure (Sample n D k) :=
  (TransportNetwork.law n D).prod (Measure.pi (fun _ : Fin k => Bilevel.OrthogonalHaar.law D))

instance probability (n D k : ℕ) : IsProbabilityMeasure (law n D k) := by
  unfold law
  infer_instance

def jointGauge {n D k : ℕ} (loc : Fin k → Vertex n) (R : Gauge n D)
    (s : Sample n D k) : Sample n D k :=
  (gauge R s.1,fun i => R (loc i)*s.2 i)

def networkGauge {n D k : ℕ} (R : Gauge n D) (s : Sample n D k) : Sample n D k :=
  (gauge R s.1,s.2)

theorem joint_preserving {n D k : ℕ} (loc : Fin k → Vertex n) (R : Gauge n D) :
    MeasurePreserving (jointGauge loc R) (law n D k) (law n D k) :=
  (gauge_preserving n D R).prod (measurePreserving_pi _ _
    (fun i : Fin k => measurePreserving_mul_left (Bilevel.OrthogonalHaar.law D) (R (loc i))))

theorem network_preserving {n D k : ℕ} (R : Gauge n D) :
    MeasurePreserving (networkGauge R) (law n D k) (law n D k) :=
  (gauge_preserving n D R).prod (MeasurePreserving.id _)

def jointAction {n D k : ℕ} (loc : Fin k → Vertex n) : MulAction (Gauge n D) (Sample n D k) where
  smul := jointGauge loc
  one_smul s := by
    change jointGauge loc 1 s = s
    apply Prod.ext
    · exact one_smul (Gauge n D) s.1
    · funext i; simp [jointGauge]
  mul_smul R S s := by
    change jointGauge loc (R*S) s = jointGauge loc R (jointGauge loc S s)
    apply Prod.ext
    · exact mul_smul R S s.1
    · funext i; simp [jointGauge,mul_assoc]

def networkAction (n D k : ℕ) : MulAction (Gauge n D) (Sample n D k) where
  smul := networkGauge
  one_smul s := by
    change networkGauge 1 s = s
    exact Prod.ext (one_smul (Gauge n D) s.1) rfl
  mul_smul R S s := by
    change networkGauge (R*S) s = networkGauge R (networkGauge S s)
    exact Prod.ext (mul_smul R S s.1) rfl

theorem joint_measurable {n D k : ℕ} (loc : Fin k → Vertex n) :
    Measurable (fun p : Gauge n D × Sample n D k => jointGauge loc p.1 p.2) := by
  apply Measurable.prodMk
  · exact (gauge_continuous n D).measurable.comp
      (measurable_fst.prodMk (measurable_fst.comp measurable_snd))
  · apply measurable_pi_lambda
    intro i
    exact ((measurable_pi_apply (loc i)).comp measurable_fst).mul
      ((measurable_pi_apply i).comp (measurable_snd.comp measurable_snd))

theorem network_measurable (n D k : ℕ) :
    Measurable (fun p : Gauge n D × Sample n D k => networkGauge p.1 p.2) :=
  ((gauge_continuous n D).measurable.comp
    (measurable_fst.prodMk (measurable_fst.comp measurable_snd))).prodMk
    (measurable_snd.comp measurable_snd)

def auxiliaryFrame {n D k : ℕ} (T : ℕ) (hT : T ≤ D) (i : Fin k) (s : Sample n D k) : Fin T → Space D :=
  Bilevel.HaarFrame.frame D T hT (s.2 i)

theorem auxiliary_frame_measurable {n D k : ℕ} (T : ℕ) (hT : T ≤ D) (i : Fin k) :
    Measurable (auxiliaryFrame (n := n) T hT i) :=
  (Bilevel.HaarFrame.frame_measurable D T hT).comp ((measurable_pi_apply i).comp measurable_snd)

theorem auxiliary_frame_orthonormal {n D k : ℕ} (T : ℕ) (hT : T ≤ D)
    (i : Fin k) (s : Sample n D k) : Orthonormal ℝ (auxiliaryFrame T hT i s) :=
  Bilevel.HaarFrame.frame_orthonormal D T hT (s.2 i)

theorem auxiliary_frame_joint {n D k : ℕ} (T : ℕ) (hT : T ≤ D)
    (loc : Fin k → Vertex n) (R : Gauge n D) (i : Fin k) (s : Sample n D k) (j : Fin T) :
    auxiliaryFrame T hT i (jointGauge loc R s) j = R (loc i) • auxiliaryFrame T hT i s j :=
  mul_smul (R (loc i)) (s.2 i) _

theorem auxiliary_frame_network_fixed {n D k : ℕ} (T : ℕ) (hT : T ≤ D)
    (R : Gauge n D) (i : Fin k) (s : Sample n D k) :
    auxiliaryFrame T hT i (networkGauge R s) = auxiliaryFrame T hT i s := rfl

end Bilevel.TransportNetworkAuxiliary
