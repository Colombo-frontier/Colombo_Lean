import Bilevel.TransportRoundQueryProbability
import Bilevel.TransportControllerEnergyMeasurable

/-! Concrete finite-generator realization of sequential raw-query insertion,
and Borel failure events for the actual fixed-location query arrays of a round. -/
noncomputable section
open MeasureTheory
namespace Bilevel.TransportRound
open EuclideanGaussian TransportNetwork ProjectionGeometry
set_option maxHeartbeats 700000
set_option synthInstance.maxHeartbeats 100000

def insertGenerator {n D m : ℕ} (g : Generators n D m) (v : Vertex n) (q : Space D) :
    Generators n D (m+1) := fun w => Fin.cons (if w=v then q else 0) (g w)

theorem known_insertGenerator {n D m : ℕ} (g : Generators n D m) (v : Vertex n) (q : Space D) :
    known (insertGenerator g v q) = TransportNetwork.insert (known g) v q := by
  funext w
  change TransportGeneratorStore.span (Fin.cons (if w=v then q else 0) (g w)) = _
  rw [TransportGeneratorStore.span_cons]
  by_cases hw : w=v
  · subst w
    simp only [ite_true,TransportNetwork.insert,Function.update_self,known]
  · simp only [if_neg hw,Submodule.span_zero_singleton,sup_bot_eq,TransportNetwork.insert,Function.update_of_ne hw,known]

theorem insertGenerator_measurable {n D m : ℕ} (v : Vertex n) :
    Measurable (fun p : Generators n D m × Space D => insertGenerator p.1 v p.2) := by
  apply measurable_pi_lambda
  intro w
  apply measurable_pi_lambda
  intro i
  cases i using Fin.cases with
  | zero =>
    by_cases hw : w=v
    · simpa only [insertGenerator,Fin.cons_zero,if_pos hw] using
        (measurable_snd : Measurable (fun p : Generators n D m × Space D => p.2))
    · simp only [insertGenerator,Fin.cons_zero,if_neg hw]
      exact measurable_const
  | succ i => exact (measurable_pi_apply i).comp ((measurable_pi_apply w).comp measurable_fst)

theorem phase_bad_joint_measurable {Ω : Type*} [MeasurableSpace Ω]
    {n D T b : ℕ} (hT : T≤D) (a : ℝ) (loc : Fin b → Vertex n) :
    ∀ m : ℕ, ∀ (g : Ω → Generators n D m), Measurable g →
      ∀ (q : Ω → Fin b → Space D), Measurable q →
        ∀ (z : Ω → Latent n D), Measurable z →
          MeasurableSet {ω | TransportRoundQuery.queryPhaseBad T hT a
            (List.ofFn (fun i => (loc i,q ω i))) (known (g ω)) (z ω)} := by
  induction b with
  | zero =>
    intro m g hg q hq z hz
    simp only [List.ofFn_zero,TransportRoundQuery.queryPhaseBad,Set.setOf_false]
    exact MeasurableSet.empty
  | succ b ih =>
    intro m g hg q hq z hz
    simp only [List.ofFn_succ,TransportRoundQuery.queryPhaseBad]
    apply MeasurableSet.union
    · have hinput : Measurable (fun ω => (g ω (loc 0),q ω 0,frame T hT (z ω) (loc 0))) :=
        ((measurable_pi_apply (loc 0)).comp hg).prodMk
          (((measurable_pi_apply 0).comp hq).prodMk
            (((measurable_pi_apply (loc 0)).comp (frame_measurable n D T hT)).comp hz))
      have hm := (TransportControllerQuery.raw_increment_measurable D m T).comp hinput
      exact measurableSet_lt measurable_const hm
    · have hg' : Measurable (fun ω => insertGenerator (g ω) (loc 0) (q ω 0)) :=
        (insertGenerator_measurable (loc 0)).comp (hg.prodMk ((measurable_pi_apply 0).comp hq))
      have hq' : Measurable (fun ω => fun i : Fin b => q ω i.succ) :=
        measurable_pi_lambda _ (fun i => (measurable_pi_apply i.succ).comp hq)
      have hh := ih (fun i => loc i.succ) (m+1) _ hg' _ hq' z hz
      simpa only [known_insertGenerator] using hh

theorem requests_bad_joint_measurable {Ω : Type*} [MeasurableSpace Ω]
    {n D m p T : ℕ} (hT : T≤D) (a : ℝ)
    (g : Ω → Generators n D m) (hg : Measurable g)
    (q : Ω → Queries n D p) (hq : Measurable q) (z : Ω → Latent n D) (hz : Measurable z) :
    MeasurableSet {ω | TransportRoundQuery.queryPhaseBad T hT a (requests (q ω)) (known (g ω)) (z ω)} := by
  let loc : Fin ((n+1)*p) → Vertex n := fun i => (finProdFinEquiv.symm i).1
  let vectors : Ω → Fin ((n+1)*p) → Space D := fun ω i =>
    q ω (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2
  have hv : Measurable vectors := measurable_pi_lambda _ (fun i =>
    (measurable_pi_apply (finProdFinEquiv.symm i).2).comp
      ((measurable_pi_apply (finProdFinEquiv.symm i).1).comp hq))
  exact phase_bad_joint_measurable hT a loc m g hg vectors hv z hz

end Bilevel.TransportRound
