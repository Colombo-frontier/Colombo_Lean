import Bilevel.TransportControllerStore
import Bilevel.TransportNetworkBatch
import Mathlib.Logic.Equiv.Fin.Basic

/-! Executed whole-space transport round. Every edge probes the frozen
finite generator family in both directions. All returned vectors are stored
only after the full batch. Thus no current-batch output is a batch input. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace Bilevel.TransportRound
open EuclideanGaussian TransportNetwork OrthogonalAction

set_option maxHeartbeats 600000
set_option synthInstance.maxHeartbeats 100000

abbrev Generators (n D m : ℕ) := Vertex n → Fin m → Space D

def known {n D m : ℕ} (g : Generators n D m) : Known n D := fun v => TransportGeneratorStore.span (g v)

def appendOutputs {n D m k : ℕ} (g : Generators n D m) (out : Fin k → Vertex n)
    (y : Fin k → Space D) : Generators n D (m+k) :=
  fun v => Fin.append (g v) (fun i => if out i = v then y i else 0)

theorem appendOutputs_span {n D m k : ℕ} (g : Generators n D m)
    (p : Fin k → Probe n D) (y : Fin k → Space D) (v : Vertex n) :
    known (appendOutputs g (fun i => outputLayer (p i)) y) v = batchKnown (known g) p y v := by
  change TransportGeneratorStore.span (Fin.append (g v) (fun i => if outputLayer (p i) = v then y i else 0)) = _
  rw [TransportGeneratorStore.span_append]
  congr 1
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro x ⟨i,rfl⟩
    by_cases hi : outputLayer (p i) = v
    · simp only [hi,ite_true]
      exact Submodule.subset_span ⟨⟨i,hi⟩,rfl⟩
    · simp only [hi,ite_false]
      exact Submodule.zero_mem _
  · apply Submodule.span_le.mpr
    rintro x ⟨i,rfl⟩
    exact Submodule.subset_span ⟨i.val,by simp only [i.property,ite_true]⟩

theorem appendOutputs_measurable {n D m k : ℕ} (out : Fin k → Vertex n) :
    Measurable (fun p : Generators n D m × (Fin k → Space D) => appendOutputs p.1 out p.2) := by
  apply measurable_pi_lambda
  intro v
  have hg : Measurable (fun p : Generators n D m × (Fin k → Space D) => p.1 v) :=
    (measurable_pi_apply v).comp measurable_fst
  have hy : Measurable (fun p : Generators n D m × (Fin k → Space D) =>
      fun i => if out i = v then p.2 i else 0) := by
    apply measurable_pi_lambda
    intro i
    by_cases hi : out i = v
    · simp only [hi,ite_true]
      exact (measurable_pi_apply i).comp measurable_snd
    · simp only [hi,ite_false]
      exact measurable_const
  exact (TransportGeneratorStore.append_measurable D m k).comp (hg.prodMk hy)

def forwardProbes {n D m : ℕ} (g : Generators n D m) : Fin (n*m) → Probe n D := fun i =>
  let ei : Edge n × Fin m := finProdFinEquiv.symm i
  (false,ei.1,g (src ei.1) ei.2)

def reverseProbes {n D m : ℕ} (g : Generators n D m) : Fin (n*m) → Probe n D := fun i =>
  let ei : Edge n × Fin m := finProdFinEquiv.symm i
  (true,ei.1,g (dst ei.1) ei.2)

def probes {n D m : ℕ} (g : Generators n D m) : Fin (n*m+n*m) → Probe n D :=
  Fin.append (forwardProbes g) (reverseProbes g)

theorem probes_frozen {n D m : ℕ} (g : Generators n D m) (i : Fin (n*m+n*m)) :
    (probes g i).2.2 ∈ known g (inputLayer (probes g i)) := by
  refine Fin.addCases ?_ ?_ i
  · intro j
    simp only [probes,Fin.append_left,forwardProbes,inputLayer,Bool.false_eq_true,ite_false]
    exact TransportGeneratorStore.generator_mem _ _
  · intro j
    simp only [probes,Fin.append_right,reverseProbes,inputLayer,ite_true]
    exact TransportGeneratorStore.generator_mem _ _

theorem outputLayer_independent {n D m : ℕ} (g h : Generators n D m) (i : Fin (n*m+n*m)) :
    outputLayer (probes g i) = outputLayer (probes h i) := by
  refine Fin.addCases ?_ ?_ i
  · intro j; simp only [probes,Fin.append_left,forwardProbes,outputLayer]
  · intro j; simp only [probes,Fin.append_right,reverseProbes,outputLayer]

def batch {n D m : ℕ} (g : Generators n D m) (z : Latent n D) : Fin (n*m+n*m) → Space D :=
  batchObservation (probes g) z

theorem batch_joint_measurable (n D m : ℕ) :
    Measurable (fun p : Generators n D m × Latent n D => batch p.1 p.2) := by
  apply measurable_pi_lambda
  intro i
  refine Fin.addCases ?_ ?_ i
  · intro j
    let ei : Edge n × Fin m := finProdFinEquiv.symm j
    simp only [batch,batchObservation,probes,Fin.append_left,forwardProbes,
      probeObservation,Bool.false_eq_true,ite_false,forwardObservation]
    change Measurable (fun p : Generators n D m × Latent n D => p.2.2 ei.1 • p.1 (src ei.1) ei.2)
    exact ((measurable_pi_apply ei.1).comp (measurable_snd.comp measurable_snd)).smul
      ((measurable_pi_apply ei.2).comp ((measurable_pi_apply (src ei.1)).comp measurable_fst))
  · intro j
    let ei : Edge n × Fin m := finProdFinEquiv.symm j
    simp only [batch,batchObservation,probes,Fin.append_right,reverseProbes,
      probeObservation,ite_true,reverseObservation]
    change Measurable (fun p : Generators n D m × Latent n D => (p.2.2 ei.1)⁻¹ • p.1 (dst ei.1) ei.2)
    exact (((measurable_pi_apply ei.1).comp (measurable_snd.comp measurable_snd)).inv).smul
      ((measurable_pi_apply ei.2).comp ((measurable_pi_apply (dst ei.1)).comp measurable_fst))

def outputs {n D m : ℕ} (g : Generators n D m) (y : Fin (n*m+n*m) → Space D) :
    Generators n D (m+(n*m+n*m)) := appendOutputs g (fun i => outputLayer (probes g i)) y

theorem outputs_measurable (n D m : ℕ) :
    Measurable (fun p : Generators n D m × (Fin (n*m+n*m) → Space D) => outputs p.1 p.2) := by
  have he : (fun p : Generators n D m × (Fin (n*m+n*m) → Space D) => outputs p.1 p.2) =
      (fun p => appendOutputs p.1 (fun i => outputLayer (probes (fun _ _ => (0 : Space D)) i)) p.2) := by
    funext p v i
    simp only [outputs,appendOutputs]
    congr 2
    funext j
    simp only [outputLayer_independent p.1 (fun _ _ => 0) j]
  rw [he]
  exact appendOutputs_measurable _

def execute {n D m : ℕ} (g : Generators n D m) (z : Latent n D) :
    Generators n D (m+(n*m+n*m)) := outputs g (batch g z)

theorem execute_measurable (n D m : ℕ) :
    Measurable (fun p : Generators n D m × Latent n D => execute p.1 p.2) :=
  (outputs_measurable n D m).comp (measurable_fst.prodMk (batch_joint_measurable n D m))

theorem execute_span {n D m : ℕ} (g : Generators n D m) (z : Latent n D) (v : Vertex n) :
    known (execute g z) v = batchKnown (known g) (probes g) (batch g z) v :=
  appendOutputs_span g (probes g) (batch g z) v

theorem keeps_old {n D m : ℕ} (g : Generators n D m) (z : Latent n D) (v : Vertex n) :
    known g v ≤ known (execute g z) v := by
  rw [execute_span]
  exact le_batchKnown _ _ _ _

theorem forward_whole_space {n D m : ℕ} (g : Generators n D m) (z : Latent n D) (e : Edge n) :
    (known g (src e)).map (isometry D (z.2 e)).toLinearEquiv.toLinearMap ≤
      known (execute g z) (dst e) := by
  apply Submodule.map_le_iff_le_comap.mpr
  change Submodule.span ℝ (Set.range (g (src e))) ≤ _
  apply Submodule.span_le.mpr
  rintro x ⟨i,rfl⟩
  change z.2 e • g (src e) i ∈ known (execute g z) (dst e)
  rw [execute_span]
  have hh := mem_batchKnown (known g) (probes g) (batch g z)
    (Fin.castAdd (n*m) (finProdFinEquiv (e,i)))
  simpa only [batch,batchObservation,probes,Fin.append_left,forwardProbes,
    Equiv.symm_apply_apply,probeObservation,forwardObservation,outputLayer,Bool.false_eq_true,ite_false] using hh

theorem reverse_whole_space {n D m : ℕ} (g : Generators n D m) (z : Latent n D) (e : Edge n) :
    (known g (dst e)).map (isometry D (z.2 e)⁻¹).toLinearEquiv.toLinearMap ≤
      known (execute g z) (src e) := by
  apply Submodule.map_le_iff_le_comap.mpr
  change Submodule.span ℝ (Set.range (g (dst e))) ≤ _
  apply Submodule.span_le.mpr
  rintro x ⟨i,rfl⟩
  change (z.2 e)⁻¹ • g (dst e) i ∈ known (execute g z) (src e)
  rw [execute_span]
  have hh := mem_batchKnown (known g) (probes g) (batch g z)
    (Fin.natAdd (n*m) (finProdFinEquiv (e,i)))
  simpa only [batch,batchObservation,probes,Fin.append_right,reverseProbes,
    Equiv.symm_apply_apply,probeObservation,reverseObservation,outputLayer,ite_true] using hh

theorem outputs_dimension {n D m : ℕ} (g : Generators n D m)
    (y : Fin (n*m+n*m) → Space D) (v : Vertex n) :
    Module.finrank ℝ (known (outputs g y) v) ≤ m+(n*m+n*m) := TransportGeneratorStore.span_rank_le _

theorem actual_batch_posterior {n D m : ℕ} (g : Generators n D m)
    (μ : Measure (Latent n D)) [IsProbabilityMeasure μ] (hμ : Invariant (known g) μ) :
    ∀ᵐ y ∂μ.map (batch g), Invariant (known (outputs g y)) (condDistrib id (batch g) μ y) := by
  have hh := batch_posterior_invariant (known g) μ hμ (probes g) (probes_frozen g)
  filter_upwards [hh] with y hy
  have he : known (outputs g y) = batchKnown (known g) (probes g) y :=
    funext (appendOutputs_span g (probes g) y)
  rwa [he]

def store {n D m : ℕ} (g : Generators n D m) : Vertex n → TransportGeneratorStore.State D m :=
  fun v => TransportGeneratorStore.fromGenerators (g v)

theorem store_measurable (n D m : ℕ) : Measurable (store : Generators n D m → Vertex n → TransportGeneratorStore.State D m) :=
  measurable_pi_lambda _ (fun v => (TransportGeneratorStore.fromGenerators_measurable D m).comp (measurable_pi_apply v))

theorem store_consistent {n D m : ℕ} (g : Generators n D m) (v : Vertex n) :
    TransportGeneratorStore.Consistent (store g v) := TransportGeneratorStore.fromGenerators_consistent _

end Bilevel.TransportRound

