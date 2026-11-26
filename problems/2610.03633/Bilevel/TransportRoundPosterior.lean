import Bilevel.TransportRoundController

/-! The actual joint round transcript preserves the known-space posterior
invariant. Its scalar answers, transport vectors, and post-response named
vectors all come from one latent network. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace Bilevel.TransportRound
open EuclideanGaussian TransportNetwork OrthogonalAction
set_option maxHeartbeats 600000
set_option synthInstance.maxHeartbeats 100000

abbrev Observed (n D m p c T : ℕ) := Answers n p T ×
  (Fin (n*(m+p)+n*(m+p)) → Space D) × Generators n D c

def observe {n D m p c : ℕ} (T : ℕ) (hT : T ≤ D) (g : Generators n D m)
    (q : Queries n D p) (names : Vertex n → Fin c → Option (Fin T)) (z : Latent n D) :
    Observed n D m p c T := (queryAnswers T hT q z,batch (augment g q) z,disclosures T hT names z)

theorem observe_measurable {n D m p c : ℕ} (T : ℕ) (hT : T ≤ D) (g : Generators n D m)
    (q : Queries n D p) (names : Vertex n → Fin c → Option (Fin T)) :
    Measurable (observe T hT g q names) :=
  ((queryAnswers_measurable T hT).comp (measurable_const.prodMk measurable_id)).prodMk
    ((batch_measurable (probes (augment g q))).prodMk (disclosures_measurable T hT names))

def observedKnown {n D m p c T : ℕ} (g : Generators n D m) (q : Queries n D p)
    (o : Observed n D m p c T) : Known n D := known (augment (outputs (augment g q) o.2.1) o.2.2)

theorem le_observedKnown {n D m p c T : ℕ} (g : Generators n D m) (q : Queries n D p)
    (o : Observed n D m p c T) : ∀ v, known (augment g q) v ≤ observedKnown g q o v := by
  intro v
  change known (augment g q) v ≤ known (augment (outputs (augment g q) o.2.1) o.2.2) v
  conv_rhs => rw [augment_span]
  apply le_trans _ le_sup_left
  rw [show known (outputs (augment g q) o.2.1) v =
      batchKnown (known (augment g q)) (probes (augment g q)) o.2.1 v from
    appendOutputs_span _ _ _ _]
  exact le_batchKnown _ _ _ _

theorem output_mem_observedKnown {n D m p c T : ℕ} (g : Generators n D m) (q : Queries n D p)
    (o : Observed n D m p c T) (i : Fin (n*(m+p)+n*(m+p))) :
    o.2.1 i ∈ observedKnown g q o (outputLayer (probes (augment g q) i)) := by
  unfold observedKnown
  rw [augment_span]
  apply (show known (outputs (augment g q) o.2.1) (outputLayer (probes (augment g q) i)) ≤ _ from le_sup_left)
  rw [show known (outputs (augment g q) o.2.1) (outputLayer (probes (augment g q) i)) =
      batchKnown (known (augment g q)) (probes (augment g q)) o.2.1 (outputLayer (probes (augment g q) i)) from
    appendOutputs_span _ _ _ _]
  exact mem_batchKnown _ _ _ _

theorem named_mem_observedKnown {n D m p c T : ℕ} (g : Generators n D m) (q : Queries n D p)
    (o : Observed n D m p c T) (v : Vertex n) (i : Fin c) : o.2.2 v i ∈ observedKnown g q o v := by
  unfold observedKnown
  rw [augment_span]
  exact (show TransportGeneratorStore.span (o.2.2 v) ≤ _ from le_sup_right)
    (TransportGeneratorStore.generator_mem _ _)

def observedAction {n D m p c T : ℕ} (g : Generators n D m) (q : Queries n D p) :
    MulAction (LocalGauge (known (augment g q))) (Observed n D m p c T) where
  smul R o := (o.1,fun i => (R (outputLayer (probes (augment g q) i))).val • o.2.1 i,
    fun v i => (R v).val • o.2.2 v i)
  one_smul o := by
    change (o.1,(fun i => (1 : OrthogonalHaar.Group D) • o.2.1 i),
      (fun v i => (1 : OrthogonalHaar.Group D) • o.2.2 v i)) = o
    apply Prod.ext
    · rfl
    apply Prod.ext
    · funext i; exact one_smul (OrthogonalHaar.Group D) _
    · funext v i; exact one_smul (OrthogonalHaar.Group D) _
  mul_smul R S o := by
    change (o.1,(fun i => ((R (outputLayer (probes (augment g q) i))).val*
      (S (outputLayer (probes (augment g q) i))).val) • o.2.1 i),
      (fun v i => ((R v).val*(S v).val) • o.2.2 v i)) =
      (o.1,(fun i => (R (outputLayer (probes (augment g q) i))).val •
        ((S (outputLayer (probes (augment g q) i))).val • o.2.1 i)),
        (fun v i => (R v).val • ((S v).val • o.2.2 v i)))
    apply Prod.ext
    · rfl
    apply Prod.ext
    · funext i; exact mul_smul (R _).val (S _).val _
    · funext v i; exact mul_smul (R v).val (S v).val _

theorem observed_action_measurable {n D m p c T : ℕ} (g : Generators n D m) (q : Queries n D p) :
    Measurable (fun z : LocalGauge (known (augment g q)) × Observed n D m p c T =>
      (z.2.1,fun i => (z.1 (outputLayer (probes (augment g q) i))).val • z.2.2.1 i,
        fun v i => (z.1 v).val • z.2.2.2 v i)) := by
  apply Measurable.prodMk (measurable_fst.comp measurable_snd)
  apply Measurable.prodMk
  · apply measurable_pi_lambda
    intro i
    have hm : Measurable (fun R : LocalGauge (known (augment g q)) =>
        (R (outputLayer (probes (augment g q) i))).val) :=
      (continuous_subtype_val.comp (continuous_apply _)).measurable
    exact (hm.comp measurable_fst).smul
      ((measurable_pi_apply i).comp (measurable_fst.comp (measurable_snd.comp measurable_snd)))
  · apply measurable_pi_lambda
    intro v
    apply measurable_pi_lambda
    intro i
    have hm : Measurable (fun R : LocalGauge (known (augment g q)) => (R v).val) :=
      (continuous_subtype_val.comp (continuous_apply v)).measurable
    exact (hm.comp measurable_fst).smul ((measurable_pi_apply i).comp
      ((measurable_pi_apply v).comp (measurable_snd.comp (measurable_snd.comp measurable_snd))))

theorem observed_fixed {n D m p c T : ℕ} (g : Generators n D m) (q : Queries n D p)
    (o : Observed n D m p c T) (R : LocalGauge (observedKnown g q o)) :
    (o.1,(fun i => (R (outputLayer (probes (augment g q) i))).val • o.2.1 i),
      (fun v i => (R v).val • o.2.2 v i)) = o := by
  apply Prod.ext
  · rfl
  apply Prod.ext
  · funext i
    exact fixed_vector (W := observedKnown g q o) R (outputLayer (probes (augment g q) i))
      (o.2.1 i) (output_mem_observedKnown g q o i)
  · funext v i
    exact fixed_vector (W := observedKnown g q o) R v (o.2.2 v i) (named_mem_observedKnown g q o v i)

theorem actual_round_posterior {n D m p c : ℕ} (T : ℕ) (hT : T ≤ D) (g : Generators n D m)
    (q : Queries n D p) (names : Vertex n → Fin c → Option (Fin T))
    (μ : Measure (Latent n D)) [IsProbabilityMeasure μ] (hμ : Invariant (known g) μ) :
    ∀ᵐ o ∂μ.map (observe T hT g q names),
      Invariant (observedKnown g q o) (condDistrib id (observe T hT g q names) μ o) := by
  let W := known (augment g q)
  have hle : ∀ v, known g v ≤ W v := by
    intro v
    dsimp [W]
    rw [augment_span]
    exact le_sup_left
  have hμW := invariant_mono hle μ hμ
  letI : MulAction (LocalGauge W) (Observed n D m p c T) := observedAction g q
  letI : MeasurableSMul₂ (LocalGauge W) (Observed n D m p c T) := ⟨observed_action_measurable g q⟩
  have he : ∀ R : LocalGauge W, ∀ z, observe T hT g q names (R • z) = R • observe T hT g q names z := by
    intro R z
    apply Prod.ext
    · funext v i
      have hq : q v i ∈ W v := by
        dsimp [W]
        rw [augment_span]
        exact (show TransportGeneratorStore.span (q v) ≤ _ from le_sup_right)
          (TransportGeneratorStore.generator_mem _ _)
      exact query_invariant T hT W v (q v i) hq R z
    · apply Prod.ext
      · funext i
        exact probe_equivariant W (probes (augment g q) i) (probes_frozen (augment g q) i) R z
      · funext v i
        change disclosures T hT names (R • z) v i = (R v).val • disclosures T hT names z v i
        cases hn : names v i with
        | none =>
          simp only [disclosures,hn]
          exact (map_zero (isometry D (R v).val)).symm
        | some j =>
          simp only [disclosures,hn]
          exact frame_gauge T hT (lift R) z v j
  have hp := ConditionalSupport.equivariant_observation μ (observe T hT g q names)
    (observe_measurable T hT g q names) (localLaw W) hμW he
  filter_upwards [hp] with o ho
  intro R
  let B : LocalGauge W := restrictGauge (le_observedKnown g q o) R
  have hf : B • o = o := by
    change (o.1,(fun i => (B (outputLayer (probes (augment g q) i))).val • o.2.1 i),
      (fun v i => (B v).val • o.2.2 v i)) = o
    exact observed_fixed g q o R
  exact ho B hf

end Bilevel.TransportRound
