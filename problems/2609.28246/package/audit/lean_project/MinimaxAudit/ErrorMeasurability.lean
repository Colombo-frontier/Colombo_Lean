import MinimaxAudit.CriterionFull
import MinimaxAudit.MeasurableExecution

/-! Borel measurability of the actual error criteria. The tangent result uses
the closed normal-cone graph and compact normal minimizers, not a measurable
certificate chosen as an extra premise. -/

open Set MeasureTheory
open scoped ContDiff
namespace MinimaxAudit

section NormalDistance
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Closed graph for the manuscript's normal-cone sign convention. -/
theorem audited_normal_graph_closed (X : Set E) :
    IsClosed {w : E × E | IsNormalAt X w.1 w.2} := by
  rw [show {w : E × E | IsNormalAt X w.1 w.2} =
      ⋂ y, ⋂ (_hy : y ∈ X), {w | inner ℝ w.2 (y - w.1) ≤ 0} by
    ext w
    simp [IsNormalAt]]
  apply isClosed_iInter
  intro y
  apply isClosed_iInter
  intro _
  apply isClosed_le <;> fun_prop

/-- A fixed normal cone is closed. -/
theorem audited_normal_set_closed (X : Set E) (z : E) :
    IsClosed {v : E | IsNormalAt X z v} := by
  exact (audited_normal_graph_closed X).preimage (continuous_const.prodMk continuous_id)

/-- Translating the closed normal cone gives the actual correction set. -/
theorem audited_corrections_closed (X : Set E) (F : E → E) (z : E) :
    IsClosed (normalCorrections X F z) := by
  have hset : normalCorrections X F z = {u : E | IsNormalAt X z (u - F z)} := by
    ext u
    constructor
    · rintro ⟨v, hv, rfl⟩
      simpa using hv
    · intro hu
      exact ⟨u - F z, hu, by abel⟩
  rw [hset]
  exact (audited_normal_set_closed X z).preimage (continuous_id.sub continuous_const)

variable [FiniteDimensional ℝ E]

/-- The actual distance infimum has an optimal normal correction. Its norm
is controlled by twice the operator norm because zero is always a normal. -/
theorem audited_tangent_attains_normal (X : Set E) (F : E → E) (z : E) :
    ∃ v : E, IsNormalAt X z v ∧
      auditedTangentResidual X F z = ‖F z + v‖ ∧ ‖v‖ ≤ 2 * ‖F z‖ := by
  obtain ⟨u, hu, hdist⟩ := (audited_corrections_closed X F z).exists_infDist_eq_dist
    (normalCorrections_nonempty X F z) (0 : E)
  obtain ⟨v, hv, rfl⟩ := hu
  have heq : auditedTangentResidual X F z = ‖F z + v‖ := by
    simpa only [auditedTangentResidual, dist_zero_left] using hdist
  have hzero : F z ∈ normalCorrections X F z := by
    refine ⟨0, ?_, by simp⟩
    intro y hy
    simp
  have hres : auditedTangentResidual X F z ≤ ‖F z‖ := by
    simpa only [auditedTangentResidual, dist_zero_left] using Metric.infDist_le_dist_of_mem (x := (0 : E)) hzero
  have htri : ‖v‖ ≤ ‖F z + v‖ + ‖F z‖ := by
    have h := norm_sub_le (F z + v) (F z)
    simpa using h
  exact ⟨v, hv, heq, by linarith⟩

/-- Sublevels of the true tangent residual are closed on a compact feasible
set. Uniform boundedness of optimal normals makes the projection compact. -/
theorem audited_tangent_sublevel_closed {X : Set E} (hX : IsCompact X)
    {F : E → E} (hF : ContinuousOn F X) (r : ℝ) :
    IsClosed {z : X | auditedTangentResidual X F z ≤ r} := by
  letI : CompactSpace X := isCompact_iff_compactSpace.mp hX
  obtain ⟨M0, hM0⟩ := hX.bddAbove_image hF.norm
  let M := max 0 M0
  have hM : 0 ≤ M := le_max_left _ _
  have hbound (z : X) : ‖F z‖ ≤ M :=
    (hM0 (mem_image_of_mem (fun z => ‖F z‖) z.property)).trans (le_max_right _ _)
  let C : Set (X × E) := {w | IsNormalAt X w.1 w.2 ∧
    ‖F w.1 + w.2‖ ≤ r ∧ ‖w.2‖ ≤ 2 * M}
  have hnormal : IsClosed {w : X × E | IsNormalAt X w.1 w.2} :=
    (audited_normal_graph_closed X).preimage
      ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
  have hFsub : Continuous (fun z : X => F z) := hF.restrict
  have hclosed : IsClosed C := hnormal.inter
    ((isClosed_le ((hFsub.comp continuous_fst).add continuous_snd).norm continuous_const).inter
      (isClosed_le continuous_snd.norm continuous_const))
  have hcompact : IsCompact C :=
    ((isCompact_univ : IsCompact (Set.univ : Set X)).prod
      (isCompact_closedBall (0 : E) (2 * M))).of_isClosed_subset hclosed (by
        intro w hw
        exact ⟨Set.mem_univ _, by simpa only [Metric.mem_closedBall, dist_zero_right] using hw.2.2⟩)
  have heq : {z : X | auditedTangentResidual X F z ≤ r} = Prod.fst '' C := by
    ext z
    constructor
    · intro hz
      obtain ⟨v, hv, heq, hvbound⟩ := audited_tangent_attains_normal X F z
      exact ⟨(z, v), ⟨hv, by rwa [← heq], hvbound.trans (by nlinarith [hbound z])⟩, rfl⟩
    · rintro ⟨⟨z', v⟩, ⟨hv, hvres, hvbound⟩, heq⟩
      change z' = z at heq
      subst z'
      have hmem : F z + v ∈ normalCorrections X F z := ⟨v, hv, rfl⟩
      have hdist : auditedTangentResidual X F z ≤ ‖F z + v‖ := by
        simpa only [auditedTangentResidual, dist_zero_left] using Metric.infDist_le_dist_of_mem (x := (0 : E)) hmem
      exact hdist.trans hvres
  rw [heq]
  exact (hcompact.image continuous_fst).isClosed

variable [MeasurableSpace E] [BorelSpace E]

/-- The true tangent error is a Borel function on the feasible compact set. -/
theorem audited_tangent_measurable {X : Set E} (hX : IsCompact X)
    {F : E → E} (hF : ContinuousOn F X) :
    Measurable (fun z : X => auditedTangentResidual X F z) := by
  apply measurable_of_Iic
  intro r
  exact (audited_tangent_sublevel_closed hX hF r).measurableSet

end NormalDistance

/-- Joint continuity of the actual Euclidean block assembly. -/
theorem continuous_source_join (dx dy : ℕ) :
    Continuous (fun w : Primal dx × Dual dy => joinBlocks w.1 w.2) := by
  have heq : (fun w : Primal dx × Dual dy => joinBlocks w.1 w.2) =
      fun w => primalEmbedding dx dy w.1 + dualEmbedding dx dy w.2 := by
    funext w
    exact join_blocks_embedding_sum w.1 w.2
  rw [heq]
  exact ((primalEmbedding dx dy).continuous.comp continuous_fst).add
    ((dualEmbedding dx dy).continuous.comp continuous_snd)

/-- The actual saddle gap is continuous for a continuous scalar potential on
compact primal and dual domains, including the max/min extrema. -/
theorem audited_gap_continuous {dx dy : ℕ} {X : Set (Primal dx)} {Y : Set (Dual dy)}
    (hX : IsCompact X) (hY : IsCompact Y) (hneX : X.Nonempty) (hneY : Y.Nonempty)
    {phi : SaddleSpace dx dy → ℝ} (hphi : Continuous phi) :
    Continuous (fun z : SaddleSpace dx dy =>
      auditedSaddleGap X Y (fun x y => phi (joinBlocks x y)) (primalBlock z) (dualBlock z)) := by
  have hp : Continuous (fun z : SaddleSpace dx dy => primalBlock z) := by
    have heq : (fun z : SaddleSpace dx dy => primalBlock z) = primalProjection dx dy := by
      funext z
      exact (primal_projection_apply z).symm
    rw [heq]
    exact (primalProjection dx dy).continuous
  have hd : Continuous (fun z : SaddleSpace dx dy => dualBlock z) := by
    have heq : (fun z : SaddleSpace dx dy => dualBlock z) = dualProjection dx dy := by
      funext z
      exact (dual_projection_apply z).symm
    rw [heq]
    exact (dualProjection dx dy).continuous
  have hmax : Continuous (fun z : SaddleSpace dx dy =>
      sSup ((fun y => phi (joinBlocks (primalBlock z) y)) '' Y)) :=
    hY.continuous_sSup (hphi.comp ((continuous_source_join dx dy).comp
      ((hp.comp continuous_fst).prodMk continuous_snd)))
  have hmin : Continuous (fun z : SaddleSpace dx dy =>
      sInf ((fun x => phi (joinBlocks x (dualBlock z))) '' X)) :=
    hX.continuous_sInf (hphi.comp ((continuous_source_join dx dy).comp
      (continuous_snd.prodMk (hd.comp continuous_fst))))
  have heq : (fun z : SaddleSpace dx dy =>
      auditedSaddleGap X Y (fun x y => phi (joinBlocks x y)) (primalBlock z) (dualBlock z)) =
      fun z => sSup ((fun y => phi (joinBlocks (primalBlock z) y)) '' Y) -
        sInf ((fun x => phi (joinBlocks x (dualBlock z))) '' X) := by
    funext z
    exact saddle_gap_eq_sup_sub_inf _ hX hY hneX hneY _ _
      (hphi.comp (continuous_join_primal _)).continuousOn
      (hphi.comp (continuous_join_dual _)).continuousOn
  rw [heq]
  exact hmax.sub hmin

/-- Smooth scalar potentials have a continuous true saddle operator. -/
theorem scalarSaddleOperator_continuous {dx dy : ℕ} {phi : SaddleSpace dx dy → ℝ}
    (hphi : ContDiff ℝ ∞ phi) : Continuous (scalarSaddleOperator phi) := by
  have hf := (contDiff_infty.mp hphi 1).continuous_fderiv (by norm_num)
  exact (euclideanSaddleSign dx dy).continuous.comp
    ((InnerProductSpace.toDual ℝ (SaddleSpace dx dy)).symm.continuous.comp hf)

/-- The actual complete finite scalar jet is continuous for a globally smooth
potential, with the canonical finite-product tensor topology. -/
theorem exactScalarJet_continuous {p dx dy : ℕ} {phi : SaddleSpace dx dy → ℝ}
    (hphi : ContDiff ℝ ∞ phi) : Continuous (exactScalarJet p phi) := by
  apply continuous_pi
  intro k
  exact (contDiff_infty.mp hphi k.1).continuous_iteratedFDeriv'

/-- Executing a source randomized policy against a fixed smooth scalar
potential gives a Borel saved output, including early stops. -/
theorem source_saved_output_measurable {p dx dy N : ℕ}
    {X : Set (Primal dx)} {Y : Set (Dual dy)}
    {Seed : Type*} [MeasurableSpace Seed] {mu : Measure Seed}
    (A : RandomizedScalarPolicy p dx dy N X Y Seed mu)
    (fill : productDomain X Y) {phi : SaddleSpace dx dy → ℝ}
    (hphi : ContDiff ℝ ∞ phi) :
    Measurable (fun seed => Deterministic.runScalarPolicy (A.policy seed)
      (exactScalarJet p phi) N []) := by
  letI : BorelSpace (ScalarJet p (SaddleSpace dx dy)) := ⟨rfl⟩
  have hjet := (exactScalarJet_continuous (p := p) hphi).measurable
  have hm := (MeasurableExecution.scalar_runner_jointly_measurable A fill
    (fun (_ : Unit) (_ : Fin N) => exactScalarJet p phi)
    (fun _ => hjet.comp measurable_snd)).2
  have heq : (fun seed => Deterministic.runScalarPolicy (A.policy seed)
      (exactScalarJet p phi) N []) =
      fun seed => MeasurableExecution.scalarRunnerOutput A fill
        (fun (_ : Unit) (_ : Fin N) => exactScalarJet p phi) ((), seed) := by
    funext seed
    exact (MeasurableExecution.scalar_runner_fixed_eq_source_run A fill
      (fun (_ : Unit) => exactScalarJet p phi) ((), seed)).symm
  rw [heq]
  exact hm.comp (measurable_const.prodMk measurable_id)

/-- Actual tangent-error threshold events of the saved policy output are
Borel. No measurability of the error event is added as a policy premise. -/
theorem source_tangent_event_measurable {p dx dy N : ℕ}
    {X : Set (Primal dx)} {Y : Set (Dual dy)}
    {Seed : Type*} [MeasurableSpace Seed] {mu : Measure Seed}
    (A : RandomizedScalarPolicy p dx dy N X Y Seed mu)
    (fill : productDomain X Y) (hZ : IsCompact (productDomain X Y))
    {phi : SaddleSpace dx dy → ℝ} (hphi : ContDiff ℝ ∞ phi) (r : ℝ) :
    MeasurableSet {seed | r ≤ auditedTangentResidual (productDomain X Y)
      (scalarSaddleOperator phi)
      (Deterministic.runScalarPolicy (A.policy seed) (exactScalarJet p phi) N [])} := by
  have hout := source_saved_output_measurable A fill hphi
  have hsub : Measurable (fun seed => (⟨Deterministic.runScalarPolicy
      (A.policy seed) (exactScalarJet p phi) N [],
      Deterministic.runScalarPolicy_feasible _ _ _ _⟩ : productDomain X Y)) :=
    hout.subtype_mk
  have herror := (audited_tangent_measurable hZ
    (scalarSaddleOperator_continuous hphi).continuousOn).comp hsub
  exact measurableSet_le measurable_const herror

/-- Actual max/min saddle-gap threshold events of the saved policy output
are Borel on compact nonempty primal and dual domains. -/
theorem source_gap_event_measurable {p dx dy N : ℕ}
    {X : Set (Primal dx)} {Y : Set (Dual dy)}
    {Seed : Type*} [MeasurableSpace Seed] {mu : Measure Seed}
    (A : RandomizedScalarPolicy p dx dy N X Y Seed mu)
    (fill : productDomain X Y) (hX : IsCompact X) (hY : IsCompact Y)
    (hneX : X.Nonempty) (hneY : Y.Nonempty)
    {phi : SaddleSpace dx dy → ℝ} (hphi : ContDiff ℝ ∞ phi) (r : ℝ) :
    MeasurableSet {seed |
      let z := Deterministic.runScalarPolicy (A.policy seed) (exactScalarJet p phi) N []
      r ≤ auditedSaddleGap X Y (fun x y => phi (joinBlocks x y))
        (primalBlock z) (dualBlock z)} := by
  exact measurableSet_le measurable_const
    ((audited_gap_continuous hX hY hneX hneY hphi.continuous).measurable.comp
      (source_saved_output_measurable A fill hphi))

/-- Both actual error thresholds on the same saved output form a Borel
event. This is the literal simultaneous event of the main lower theorem. -/
theorem source_joint_error_event_measurable {p dx dy N : ℕ}
    {X : Set (Primal dx)} {Y : Set (Dual dy)}
    {Seed : Type*} [MeasurableSpace Seed] {mu : Measure Seed}
    (A : RandomizedScalarPolicy p dx dy N X Y Seed mu)
    (fill : productDomain X Y) (hX : IsCompact X) (hY : IsCompact Y)
    (hneX : X.Nonempty) (hneY : Y.Nonempty)
    {phi : SaddleSpace dx dy → ℝ} (hphi : ContDiff ℝ ∞ phi) (r s : ℝ) :
    MeasurableSet {seed |
      let z := Deterministic.runScalarPolicy (A.policy seed) (exactScalarJet p phi) N []
      r ≤ auditedTangentResidual (productDomain X Y) (scalarSaddleOperator phi) z ∧
      s ≤ auditedSaddleGap X Y (fun x y => phi (joinBlocks x y))
        (primalBlock z) (dualBlock z)} := by
  have hZ : IsCompact (productDomain X Y) := by
    have heq : productDomain X Y =
        (fun w : Primal dx × Dual dy => joinBlocks w.1 w.2) '' (X ×ˢ Y) := by
      ext z
      constructor
      · intro hz
        exact ⟨(primalBlock z, dualBlock z), hz, join_blocks z⟩
      · rintro ⟨⟨x,y⟩, ⟨hx,hy⟩, rfl⟩
        simpa [productDomain] using And.intro hx hy
    rw [heq]
    exact (hX.prod hY).image (continuous_source_join dx dy)
  exact (source_tangent_event_measurable A fill hZ hphi r).inter
    (source_gap_event_measurable A fill hX hY hneX hneY hphi s)

end MinimaxAudit
