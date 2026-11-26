import Bilevel.TransportAuxiliaryFrameReplay
import Bilevel.AuxiliaryFrameBatchObserver

/-! Selected auxiliary-frame factorization under the original augmented
network prior. Complementary full orientations and the whole network are
independent context; the selected full orientation is never in memory. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
universe u v
namespace Bilevel.TransportAuxiliaryFrame
open EuclideanGaussian ProjectionPosterior TransportControllerMachine
set_option autoImplicit false

def otherColumns {D T k : ℕ} (hT : T+1 ≤ D) (i : Fin (k+1))
    (a : Fin k → OrthogonalHaar.Group D) : Columns (k+1) T D :=
  fun j => HaarFrame.frame D (T+1) hT
    (Fin.insertNth (α:=fun _ : Fin (k+1) => OrthogonalHaar.Group D) i 1 a j)

theorem otherColumns_measurable {D T k : ℕ} (hT : T+1 ≤ D) (i : Fin (k+1)) :
    Measurable (otherColumns hT i) := by
  have hi : Measurable (fun a : Fin k → OrthogonalHaar.Group D =>
      Fin.insertNth (α:=fun _ : Fin (k+1) => OrthogonalHaar.Group D) i 1 a) :=
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k+1) => OrthogonalHaar.Group D) i).symm.measurable.comp
      (measurable_const.prodMk measurable_id)
  apply measurable_pi_lambda
  intro j
  exact (HaarFrame.frame_measurable D (T+1) hT).comp ((measurable_pi_apply j).comp hi)

def originalColumns {n D T k : ℕ} (hT : T+1 ≤ D)
    (s : TransportNetworkAuxiliary.Sample n D (k+1)) : Columns (k+1) T D :=
  fun i => TransportNetworkAuxiliary.auxiliaryFrame (T+1) hT i s

theorem otherColumns_agree {n D T k : ℕ} (hT : T+1 ≤ D) (i : Fin (k+1))
    (s : TransportNetworkAuxiliary.Sample n D (k+1)) (j : Fin (k+1)) (hj : j ≠ i) :
    otherColumns hT i (fun l => s.2 (i.succAbove l)) j = originalColumns hT s j := by
  obtain ⟨l,hl⟩ := Fin.exists_succAbove_eq hj
  unfold otherColumns originalColumns TransportNetworkAuxiliary.auxiliaryFrame
  rw [←hl,Fin.insertNth_apply_succAbove]

def selectedInitial {C : Type u} {S : Type v} [MeasurableSpace C] [MeasurableSpace S]
    {n D T k : ℕ} (hT : T+1 ≤ D) (i : Fin (k+1))
    (initial : C × TransportNetwork.Latent n D → S)
    (p : IndependentFrame.Context (C × TransportNetwork.Latent n D) D k) :
    SelectedMemory (C × TransportNetwork.Latent n D) S (k+1) T D :=
  (otherColumns hT i p.2,(p.1,(initial p.1,initialStore (k+1) T D)))

theorem selectedInitial_measurable {C : Type u} {S : Type v} [MeasurableSpace C] [MeasurableSpace S]
    {n D T k : ℕ} (hT : T+1 ≤ D) (i : Fin (k+1))
    (initial : C × TransportNetwork.Latent n D → S) (hi : Measurable initial) :
    Measurable (selectedInitial hT i initial) :=
  ((otherColumns_measurable hT i).comp measurable_snd).prodMk
    (measurable_fst.prodMk ((hi.comp measurable_fst).prodMk measurable_const))

theorem auxiliary_observer_general {C : Type*} [MeasurableSpace C] (ρ : Measure C)
    [IsProbabilityMeasure ρ] {n D k T N R r : ℕ} {H : Memory}
    (hT : T ≤ D) (i : Fin (k+1)) (L : OrdinaryFrame.Rules H D T)
    (initial : IndependentFrame.Context (C × TransportNetwork.Latent n D) D k → H)
    (hi : Measurable initial) (t : ℕ) (b : ℝ) (hb : 0 < b) (hb2 : b ≤ 2)
    (hdim : (2*N+1)+R+(r+1) ≤ D) (hcap : (R:ℝ)*(((2*N+1:ℕ):ℝ)*b) ≤ 1/2) :
    (ρ.prod (TransportNetworkAuxiliary.law n D (k+1))) {s | ¬OrdinaryFrame.Observed L
      (2*((2*N+1:ℕ):ℝ)*b) N R t
      (initial (IndependentFrame.auxiliaryExpose hT i s).1,(⊥,∅))
      (IndependentFrame.auxiliaryExpose hT i s).2} ≤
      ((2*N+1:ℕ):ℝ≥0∞)*GenieProtocol.failurePerQuery T r b := by
  have hd' : OrdinaryFrame.queryCount N+R+(r+1) ≤ D := by
    simpa only [OrdinaryFrame.queryCount_eq] using hdim
  have hc' : (R:ℝ)*((OrdinaryFrame.queryCount N:ℝ)*b) ≤ 1/2 := by
    simpa only [OrdinaryFrame.queryCount_eq] using hcap
  have hp := IndependentFrame.auxiliary_policy_failure ρ hT i
    (OrdinaryFrame.policy L N R t) initial hi b hb hb2 hd' hc'
  have he := GenieProtocol.envelope_twice (OrdinaryFrame.queryCount N) R b hb.le hc'
  have hh : (ρ.prod (TransportNetworkAuxiliary.law n D (k+1))) {s | ¬OrdinaryFrame.Observed L
      (2*(OrdinaryFrame.queryCount N:ℝ)*b) N R t
      (initial (IndependentFrame.auxiliaryExpose hT i s).1,(⊥,∅))
      (IndependentFrame.auxiliaryExpose hT i s).2} ≤
      (OrdinaryFrame.queryCount N:ℝ≥0∞)*GenieProtocol.failurePerQuery T r b := by
    refine (measure_mono ?_).trans hp
    intro s hbad hsafe
    exact hbad (OrdinaryFrame.observed_mono L he N R t _ _
      (OrdinaryFrame.safe_observed L _ N R t _ _ hsafe))
  simpa only [OrdinaryFrame.queryCount_eq] using hh

end Bilevel.TransportAuxiliaryFrame
