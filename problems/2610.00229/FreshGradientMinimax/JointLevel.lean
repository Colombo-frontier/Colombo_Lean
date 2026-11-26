import FreshGradientMinimax.LevelAccuracy
import FreshGradientMinimax.KernelTransport

/-! Jointly measurable level estimators in the reference and query point.
The query coordinate is retained through every fast-variable update.
Their restrictions to a fixed query equal the previously analysed laws. -/

set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section
namespace FreshGradientMinimax
open MeasureTheory ProbabilityTheory
namespace SCObjective
variable {dx dy : ℕ} {ℓ μ α σ : ℝ} (S : SCObjective dx dy ℓ μ α)

def jointFastStepKernel (O : FreshOracle S.toNCObjective σ) (b : ℕ) :
    Kernel (Joint dx dy) (Joint dx dy) :=
  (Kernel.id ×ₖ batchKernel O.primalKernel b).map
    (fun z : Joint dx dy × Euclid dx => (z.1.1 - ℓ⁻¹ • z.2, z.1.2))

instance jointFastStepKernel_markov (O : FreshOracle S.toNCObjective σ) (b : ℕ) :
    IsMarkovKernel (S.jointFastStepKernel O b) :=
  Kernel.IsMarkovKernel.map _
    ((measurable_fst.fst.sub (measurable_const.smul measurable_snd)).prodMk measurable_fst.snd)

theorem jointFastStepKernel_apply (O : FreshOracle S.toNCObjective σ) (b : ℕ) (u : Euclid dx) (v : Euclid dy) :
    S.jointFastStepKernel O b (u, v) =
      (batchKernel O.primalKernel b (u, v)).map (fun r => (u - ℓ⁻¹ • r, v)) := by
  rw [jointFastStepKernel, Kernel.map_apply _
    ((measurable_fst.fst.sub (measurable_const.smul measurable_snd)).prodMk measurable_fst.snd),
    Kernel.prod_apply, Kernel.id_apply, Measure.dirac_prod,
    Measure.map_map
      ((measurable_fst.fst.sub (measurable_const.smul measurable_snd)).prodMk measurable_fst.snd)
      measurable_prodMk_left]
  rfl

theorem jointFastStepKernel_fixed (O : FreshOracle S.toNCObjective σ) (b : ℕ) (v : Euclid dy) :
    (S.jointFastStepKernel O b).comap (fun u => (u, v)) (measurable_id.prodMk measurable_const) =
      (S.fastStepKernel O b v).map (fun u => (u, v)) := by
  apply Kernel.ext
  intro u
  rw [Kernel.comap_apply, S.jointFastStepKernel_apply,
    Kernel.map_apply (f := fun u : Euclid dx => (u, v)) _ (measurable_id.prodMk measurable_const),
    S.fastStepKernel_apply, Measure.map_map (f := fun r : Euclid dx => u - ℓ⁻¹ • r)
      (g := fun w : Euclid dx => (w, v)) (measurable_id.prodMk measurable_const)
      (measurable_const.sub (measurable_const.smul measurable_id))]
  rfl

def jointFastRunKernel (O : FreshOracle S.toNCObjective σ) (b n : ℕ) :
    Kernel (Joint dx dy) (Joint dx dy) := iterateKernel (S.jointFastStepKernel O b) n

instance jointFastRunKernel_markov (O : FreshOracle S.toNCObjective σ) (b n : ℕ) :
    IsMarkovKernel (S.jointFastRunKernel O b n) := by unfold jointFastRunKernel; infer_instance

theorem jointFastRunKernel_fixed (O : FreshOracle S.toNCObjective σ) (b n : ℕ) (v : Euclid dy) :
    (S.jointFastRunKernel O b n).comap (fun u => (u, v)) (measurable_id.prodMk measurable_const) =
      (S.fastRunKernel O b v n).map (fun u => (u, v)) :=
  iterateKernel_transport _ _ _ _ (S.jointFastStepKernel_fixed O b v) n

def jointLevelReadKernel (O : FreshOracle S.toNCObjective σ) (b : ℕ)
    (a : Euclid dy → Euclid dy) (ha : Measurable a) : Kernel (Joint dx dy) (Euclid dy) :=
  (batchKernel O.dualKernel b ×ₖ Kernel.deterministic (fun z : Joint dx dy => a z.2)
    (ha.comp measurable_snd)).map (fun z : Euclid dy × Euclid dy => -z.1 + z.2)

instance jointLevelReadKernel_markov (O : FreshOracle S.toNCObjective σ) (b : ℕ)
    (a : Euclid dy → Euclid dy) (ha : Measurable a) :
    IsMarkovKernel (S.jointLevelReadKernel O b a ha) :=
  Kernel.IsMarkovKernel.map _ (measurable_fst.neg.add measurable_snd)

theorem jointLevelReadKernel_apply (O : FreshOracle S.toNCObjective σ) (b : ℕ)
    (a : Euclid dy → Euclid dy) (ha : Measurable a) (u : Euclid dx) (v : Euclid dy) :
    S.jointLevelReadKernel O b a ha (u, v) = S.levelReadKernel O b v (a v) u := by
  rw [jointLevelReadKernel, Kernel.map_apply _ (measurable_fst.neg.add measurable_snd),
    Kernel.prod_apply, Kernel.deterministic_apply, Measure.prod_dirac,
    Measure.map_map (measurable_fst.neg.add measurable_snd) measurable_prodMk_right,
    S.levelReadKernel_apply]
  rfl

theorem jointLevelReadKernel_fixed (O : FreshOracle S.toNCObjective σ) (b : ℕ)
    (a : Euclid dy → Euclid dy) (ha : Measurable a) (v : Euclid dy) :
    (S.jointLevelReadKernel O b a ha).comap (fun u => (u, v)) (measurable_id.prodMk measurable_const) =
      S.levelReadKernel O b v (a v) := by
  apply Kernel.ext
  intro u
  exact S.jointLevelReadKernel_apply O b a ha u v

def jointLevelKernel (O : FreshOracle S.toNCObjective σ) (b n : ℕ)
    (a : Euclid dy → Euclid dy) (ha : Measurable a) : Kernel (Joint dx dy) (Euclid dy) :=
  S.jointLevelReadKernel O b a ha ∘ₖ S.jointFastRunKernel O b n

instance jointLevelKernel_markov (O : FreshOracle S.toNCObjective σ) (b n : ℕ)
    (a : Euclid dy → Euclid dy) (ha : Measurable a) :
    IsMarkovKernel (S.jointLevelKernel O b n a ha) := by unfold jointLevelKernel; infer_instance

theorem jointLevelKernel_fixed (O : FreshOracle S.toNCObjective σ) (b n : ℕ)
    (a : Euclid dy → Euclid dy) (ha : Measurable a) (v : Euclid dy) :
    (S.jointLevelKernel O b n a ha).comap (fun u => (u, v)) (measurable_id.prodMk measurable_const) =
      S.levelKernel O b n v (a v) := by
  rw [jointLevelKernel, ← Kernel.comp_deterministic_eq_comap, Kernel.comp_assoc,
    Kernel.comp_deterministic_eq_comap, S.jointFastRunKernel_fixed,
    Kernel.comp_map (f := fun u : Euclid dx => (u, v)) _ _ (measurable_id.prodMk measurable_const),
    S.jointLevelReadKernel_fixed]
  rfl

theorem jointLevelKernel_apply (O : FreshOracle S.toNCObjective σ) (b n : ℕ)
    (a : Euclid dy → Euclid dy) (ha : Measurable a) (u : Euclid dx) (v : Euclid dy) :
    S.jointLevelKernel O b n a ha (u, v) = S.levelKernel O b n v (a v) u :=
  congrArg (fun K : Kernel (Euclid dx) (Euclid dy) => K u) (S.jointLevelKernel_fixed O b n a ha v)

end SCObjective
end FreshGradientMinimax
