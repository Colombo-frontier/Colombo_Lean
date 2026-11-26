import Bilevel.TransportAugmentedPrior

/-! Network query/terminal projection control for the common augmented
run, transferred to the SAME original network-plus-auxiliary prior used
by the auxiliary observer. The prior permutation is proved exactly. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
universe u v
namespace Bilevel.TransportAugmented
open EuclideanGaussian TransportNetwork TransportRound TransportControllerMachine ProjectionGeometry
set_option autoImplicit false

theorem generator_projection_measurable {H : Type*} [MeasurableSpace H] {n D T m : ℕ}
    (hT : T ≤ D) (t : ℕ) (b : ℝ) (g : H × Latent n D → Generators n D m) (hg : Measurable g) :
    MeasurableSet {s : H × Latent n D | ∀ v i, ¬Protected t v i →
      ‖project (known (g s) v) (frame T hT s.2 v i)‖ ≤ b} := by
  simp only [Set.setOf_forall]
  apply MeasurableSet.iInter
  intro v
  apply MeasurableSet.iInter
  intro i
  apply MeasurableSet.iInter
  intro _
  have hP := known_projector_measurable _ hg v
  have hf := (measurable_pi_apply i).comp
    (frame_layer_measurable (Ω:=H × Latent n D) hT Prod.snd measurable_snd v)
  have hp := ProjectionStore.apply_measurable D _ hP _ hf
  simp only [ProjectionStore.apply_subspace] at hp
  exact measurableSet_le hp.norm measurable_const

theorem networkProjectionGood_measurable {H : Type*} [MeasurableSpace H] {n D T p : ℕ}
    (hT : T ≤ D)
    (choose : ∀ t,H × Generators n D (size n p 1 1 t) → Queries n D p) (hc : ∀ t,Measurable (choose t))
    (respond : ∀ t,StepData H n D (size n p 1 1 t) p T → H) (hr : ∀ t,Measurable (respond t))
    (M : ℕ) (b : ℝ) :
    MeasurableSet {s : H × Latent n D | ProjectionGood hT choose respond M b s.1 s.2} := by
  change MeasurableSet ({s : H × Latent n D | ∀ t ≤ M, ∀ v i, ¬Protected t v i →
      ‖project (known (run T hT choose respond (prefixNames n T) (s.1,seed T hT s.2) s.2 t).2 v)
        (frame T hT s.2 v i)‖ ≤ b} ∩
    {s | ∀ t < M, ∀ v i, ¬Protected t v i →
      ‖project (known (frozenAt hT choose respond (prefixNames n T) (s.1,seed T hT s.2) s.2 t) v)
        (frame T hT s.2 v i)‖ ≤ b})
  apply MeasurableSet.inter
  · simp only [Set.setOf_forall]
    apply MeasurableSet.iInter
    intro t
    apply MeasurableSet.iInter
    intro _
    simpa only [Set.setOf_forall] using generator_projection_measurable hT t b _
      (measurable_snd.comp (runState_joint_measurable hT choose hc respond hr t))
  · simp only [Set.setOf_forall]
    apply MeasurableSet.iInter
    intro t
    apply MeasurableSet.iInter
    intro _
    simpa only [Set.setOf_forall] using generator_projection_measurable hT t b _
      (frozenAt_joint_measurable hT choose hc respond hr t)

variable {C : Type u} {S : Type v} [MeasurableSpace C] [MeasurableSpace S]
  {n D p Tnet k T B : ℕ}

def NetworkGood (P : TransportAuxiliaryFrame.Schedule (k+1) T)
    (A : Controller C S n D p Tnet (k+1) T B) (hTnet : Tnet ≤ D) (hT : T+1 ≤ D)
    (initial : C → S) (M : ℕ) (b : ℝ) (s : C × TransportNetworkAuxiliary.Sample n D (k+1)) : Prop :=
  ProjectionGood hTnet (networkChoose A) (networkRespond P A) M b
    (networkView hT initial s).1 s.2.1 ∧
  TerminalGood hTnet (networkChoose A) (networkRespond P A) (networkOutput A) M b
    (networkView hT initial s).1 s.2.1

theorem networkGood_measurable (ρ : Measure C) [IsProbabilityMeasure ρ]
    (P : TransportAuxiliaryFrame.Schedule (k+1) T)
    (A : Controller C S n D p Tnet (k+1) T B) (hTnet : Tnet ≤ D) (hT : T+1 ≤ D)
    (initial : C → S) (hi : Measurable initial) (M : ℕ) (b : ℝ) :
    MeasurableSet {s | NetworkGood P A hTnet hT initial M b s} := by
  have hp := networkProjectionGood_measurable hTnet (networkChoose A) (networkChoose_measurable A)
    (networkRespond P A) (networkRespond_measurable P A) M b
  have ht := terminalGood_measurable hTnet (networkChoose A) (networkChoose_measurable A)
    (networkRespond P A) (networkRespond_measurable P A) (networkOutput A) (networkOutput_measurable A) M b
  exact (hp.inter ht).preimage (networkView_preserving (n:=n) ρ hT initial hi).measurable

theorem network_failure_original (ρ : Measure C) [IsProbabilityMeasure ρ]
    (P : TransportAuxiliaryFrame.Schedule (k+1) T)
    (A : Controller C S n D p Tnet (k+1) T B) (hTnet : Tnet ≤ D) (hT : T+1 ≤ D)
    (hn : 0 < n) (hpos : 0 < Tnet) (initial : C → S) (hi : Measurable initial)
    (M : ℕ) {b δ : ℝ} (hb : 0 < b) (hδ : 0 < δ)
    (hD : observerDimension n p Tnet (M+1) b δ ≤ D) :
    (ρ.prod (TransportNetworkAuxiliary.law n D (k+1)))
      {s | ¬NetworkGood P A hTnet hT initial M b s} ≤ ENNReal.ofReal δ := by
  let ν := memoryLaw (k:=k) ρ hT initial
  letI : IsProbabilityMeasure ν :=
    isProbabilityMeasure_map (initialMemory_measurable hT initial hi).aemeasurable
  let H := Memory.of (NetworkMemory C S (k+1) T D)
  have hp := network_observer_with_terminal (k:=0) H hTnet hn hpos
    (networkChoose A) (networkChoose_measurable A) (networkRespond P A) (networkRespond_measurable P A)
    (networkOutput A) (networkOutput_measurable A) ν M hb hδ hD
  have hproj := networkProjectionGood_measurable hTnet (networkChoose A) (networkChoose_measurable A)
    (networkRespond P A) (networkRespond_measurable P A) M b
  have hterm := terminalGood_measurable hTnet (networkChoose A) (networkChoose_measurable A)
    (networkRespond P A) (networkRespond_measurable P A) (networkOutput A) (networkOutput_measurable A) M b
  have hbad := (hproj.inter hterm).compl
  have he := TransportNetworkAuxiliary.private_network_event ν n D 0 _ hbad
  simp only [Set.mem_compl_iff,Set.mem_inter_iff,Set.mem_setOf_eq] at he
  rw [he] at hp
  have hv := (networkView_preserving (n:=n) ρ hT initial hi).measure_preimage hbad.nullMeasurableSet
  change (ρ.prod (TransportNetworkAuxiliary.law n D (k+1)))
    {s | ¬NetworkGood P A hTnet hT initial M b s} = _ at hv
  rw [hv]
  exact hp

end Bilevel.TransportAugmented
