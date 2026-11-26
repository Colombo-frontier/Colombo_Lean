import Bilevel.TransportControllerEdgeTheorem

/-! The concrete Borel monitor interface also applies to the inverse current
edge under the same original augmented network law. This uses the proved
prefix-gauge posterior, not an independence assertion between directions. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace Bilevel.TransportControllerEdgePolicy
open EuclideanGaussian TransportNetwork TransportNetworkAuxiliary TransportControllerEdge
set_option maxHeartbeats 800000

def inverseContextStore {n D k T : ℕ} (e : Edge n) (c : FullContext (D := D) e T k) :
    TransportControllerPairedStore.State D T := (contextStore e c).swap

theorem inverseContextStore_measurable {n D k T : ℕ} (e : Edge n) :
    Measurable (inverseContextStore (D := D) (k := k) (T := T) e) :=
  (measurable_snd.comp (contextStore_measurable e)).prodMk (measurable_fst.comp (contextStore_measurable e))

theorem network_inverse_policy_angle_failure {H : Type*} [MeasurableSpace H] {n D k T d h : ℕ}
    (hT : T≤D) (e : Edge n) (P : Spec H D d T h)
    (initial : FullContext (D := D) e T k → H) (hi : Measurable initial)
    (r : ℕ) (hr : 0<r) (hD : T+h+r≤D) :
    TransportNetworkAuxiliary.law n D k {s |
      failure P (initial (fullContext T hT e s),inverseContextStore e (fullContext T hT e s)) ((s.1.2 e)⁻¹)} ≤
      (h:ℝ≥0∞)*budget d r := by
  let prog := fun c : FullContext (D := D) e T k => compile P (initial c,inverseContextStore e c)
  have hreg : ∀ c, Regular (prog c) := fun c => compile_regular P _
  have hvalid : ∀ s : Sample n D k, Valid d (prog (fullContext T hT e s)) (reverseHardPairs T hT e s.1) := by
    intro s
    exact compile_valid P _
  have hmeas : MeasurableSet {p : FullContext (D := D) e T k × OrthogonalHaar.Group D | bad (prog p.1) p.2} := by
    have hm : Measurable (fun p : FullContext (D := D) e T k × OrthogonalHaar.Group D =>
        ((initial p.1,inverseContextStore e p.1),p.2)) :=
      (((hi.comp measurable_fst).prodMk ((inverseContextStore_measurable e).comp measurable_fst)).prodMk measurable_snd)
    have hh := hm (failure_measurable P)
    simpa only [prog,Set.mem_preimage,Set.mem_setOf_eq,← compile_failure] using hh
  have hh := network_reverse_angle_failure T hT e d r hr hD prog hreg hvalid hmeas
  simpa only [prog,compile_failure] using hh

theorem randomized_network_inverse_policy_angle_failure {M H : Type*} [MeasurableSpace M] [MeasurableSpace H]
    {n D k T d h : ℕ} (hT : T≤D) (e : Edge n) (P : Spec H D d T h)
    (initial : M × FullContext (D := D) e T k → H) (hi : Measurable initial)
    (ρ : Measure M) [IsProbabilityMeasure ρ] (r : ℕ) (hr : 0<r) (hD : T+h+r≤D) :
    (ρ.prod (TransportNetworkAuxiliary.law n D k)) {p |
      failure P (initial (p.1,fullContext T hT e p.2),inverseContextStore e (fullContext T hT e p.2)) ((p.2.1.2 e)⁻¹)} ≤
      (h:ℝ≥0∞)*budget d r := by
  letI : IsProbabilityMeasure (TransportNetworkAuxiliary.law n D k) := TransportNetworkAuxiliary.probability n D k
  letI : IsFiniteMeasure (TransportNetworkAuxiliary.law n D k) := inferInstance
  letI : SigmaFinite (TransportNetworkAuxiliary.law n D k) := inferInstance
  letI : SFinite (TransportNetworkAuxiliary.law n D k) := inferInstance
  have hc : Measurable (fun p : M × Sample n D k => fullContext T hT e p.2) :=
    (fullContext_measurable T hT e).comp measurable_snd
  have hs : Measurable (fun p : M × Sample n D k =>
      (initial (p.1,fullContext T hT e p.2),inverseContextStore e (fullContext T hT e p.2))) :=
    (hi.comp (measurable_fst.prodMk hc)).prodMk ((inverseContextStore_measurable e).comp hc)
  have he : Measurable (fun p : M × Sample n D k => (p.2.1.2 e)⁻¹) :=
    ((measurable_pi_apply e).comp (measurable_snd.comp (measurable_fst.comp measurable_snd))).inv
  have hb : MeasurableSet {p : M × Sample n D k |
      failure P (initial (p.1,fullContext T hT e p.2),inverseContextStore e (fullContext T hT e p.2)) ((p.2.1.2 e)⁻¹)} :=
    (hs.prodMk he) (failure_measurable P)
  rw [Measure.prod_apply (μ := ρ) (ν := TransportNetworkAuxiliary.law n D k) hb]
  calc
    _ ≤ ∫⁻ _memory, (h:ℝ≥0∞)*budget d r ∂ρ := by
      apply lintegral_mono
      intro memory
      exact network_inverse_policy_angle_failure hT e P (fun c => initial (memory,c))
        (hi.comp (measurable_const.prodMk measurable_id)) r hr hD
    _ = _ := by simp

end Bilevel.TransportControllerEdgePolicy
