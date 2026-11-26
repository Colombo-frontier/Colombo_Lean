import MinimaxAudit.ErrorMeasurability
import MinimaxAudit.ScalarVI

/-! Actual Borel execution and error criteria for the source class. Only the
source neighborhood C^p regularity is used; no globally smooth extension of
an admissible objective or measurable error certificate is assumed. -/
open Set MeasureTheory
open scoped ContDiff
namespace MinimaxAudit
noncomputable section
set_option maxHeartbeats 150000

/-- The actual full jet is continuous on the feasible set when the potential
is C^p on an open neighborhood, including every returned derivative 0..p. -/
theorem scalarJet_continuousOn_of_neighborhood {p dx dy : ℕ}
    {Z O : Set (SaddleSpace dx dy)} {phi : SaddleSpace dx dy → ℝ}
    (hO : IsOpen O) (hZO : Z ⊆ O) (hphi : ContDiffOn ℝ p phi O) :
    ContinuousOn (exactScalarJet p phi) Z := by
  apply continuousOn_pi.mpr
  intro k
  exact (ContinuousOn.continuousOn_iteratedFDeriv hphi hO (by exact_mod_cast Nat.le_of_lt_succ k.2)).mono hZO

/-- The source scalar saddle operator is continuous on the feasible set
under the actual source neighborhood differentiability assumption. -/
theorem scalarSaddleOperator_continuousOn_of_neighborhood {p dx dy : ℕ}
    {Z O : Set (SaddleSpace dx dy)} {phi : SaddleSpace dx dy → ℝ}
    (hp : 1 ≤ p) (hO : IsOpen O) (hZO : Z ⊆ O) (hphi : ContDiffOn ℝ p phi O) :
    ContinuousOn (scalarSaddleOperator phi) Z := by
  have hf := (hphi.continuousOn_fderiv_of_isOpen hO (by exact_mod_cast hp)).mono hZO
  exact ((euclideanSaddleSign dx dy).continuous.comp_continuousOn
    ((InnerProductSpace.toDual ℝ (SaddleSpace dx dy)).symm.continuous.comp_continuousOn hf))

/-- Analysis facts are derived for each actual admissible scalar objective. -/
theorem admissible_error_analysis {p dx dy : ℕ} {L D : ℝ}
    {X : Set (Primal dx)} {Y : Set (Dual dy)} {phi : SaddleSpace dx dy → ℝ}
    (h : AdmissibleScalar p L D X Y phi) :
    IsCompact (productDomain X Y) ∧ (productDomain X Y).Nonempty ∧
    ContinuousOn phi (productDomain X Y) ∧
    ContinuousOn (exactScalarJet p phi) (productDomain X Y) ∧
    ContinuousOn (scalarSaddleOperator phi) (productDomain X Y) := by
  rcases h with ⟨hp, _, _, hneX, hneY, hX, hY, _, _, _, ⟨O,hO,hZO,hphi⟩, _⟩
  refine ⟨ScalarVI.product_domain_compact hX hY, ?_, hphi.continuousOn.mono hZO,
    scalarJet_continuousOn_of_neighborhood hO hZO hphi,
    scalarSaddleOperator_continuousOn_of_neighborhood (by omega) hO hZO hphi⟩
  obtain ⟨x,hx⟩ := hneX
  obtain ⟨y,hy⟩ := hneY
  exact ⟨joinBlocks x y, by simpa [productDomain] using And.intro hx hy⟩

/-- Changing an oracle away from the feasible set does not change any
source-policy execution, including an arbitrary saved output and early stop. -/
theorem source_run_eq_of_feasible_oracle_eq {p dx dy N : ℕ}
    {X : Set (Primal dx)} {Y : Set (Dual dy)}
    (A : DeterministicScalarPolicy p dx dy N X Y)
    (f g : SaddleSpace dx dy → ScalarJet p (SaddleSpace dx dy))
    (hfg : ∀ z ∈ productDomain X Y, f z = g z) (fuel : ℕ) (hist : ScalarHistory p dx dy) :
    Deterministic.runScalarPolicy A f fuel hist =
      Deterministic.runScalarPolicy A g fuel hist := by
  induction fuel generalizing hist with
  | zero => rfl
  | succ fuel ih =>
    cases hq : A.query hist with
    | none => simp [Deterministic.runScalarPolicy, hq]
    | some z =>
      have heq := hfg z (A.feasible_query hist z hq)
      simpa only [Deterministic.runScalarPolicy, hq, heq] using ih (hist ++ [(z,g z)])

/-- A Borel extension of the actual feasible full jet exists by a piecewise
zero extension. It is only an analysis device and never changes a query answer. -/
theorem admissible_jet_borel_extension {p dx dy : ℕ} {L D : ℝ}
    {X : Set (Primal dx)} {Y : Set (Dual dy)} {phi : SaddleSpace dx dy → ℝ}
    (h : AdmissibleScalar p L D X Y phi) :
    ∃ f : SaddleSpace dx dy → ScalarJet p (SaddleSpace dx dy), Measurable f ∧
      ∀ z ∈ productDomain X Y, f z = exactScalarJet p phi z := by
  classical
  letI : BorelSpace (ScalarJet p (SaddleSpace dx dy)) := ⟨rfl⟩
  obtain ⟨hZ, _, _, hjet, _⟩ := admissible_error_analysis h
  exact ⟨(productDomain X Y).piecewise (exactScalarJet p phi) 0,
    hjet.measurable_piecewise continuousOn_const hZ.isClosed.measurableSet,
    fun z hz => by simp [hz]⟩

/-- The actual saved output for every source-admissible objective is Borel.
This uses only local C^p regularity and the policy's feasible-query guarantee. -/
theorem admissible_saved_output_measurable {p dx dy N : ℕ} {L D : ℝ}
    {X : Set (Primal dx)} {Y : Set (Dual dy)}
    {Seed : Type*} [MeasurableSpace Seed] {mu : Measure Seed}
    (A : RandomizedScalarPolicy p dx dy N X Y Seed mu)
    {phi : SaddleSpace dx dy → ℝ} (hphi : AdmissibleScalar p L D X Y phi) :
    Measurable (fun seed => Deterministic.runScalarPolicy (A.policy seed)
      (exactScalarJet p phi) N []) := by
  obtain ⟨_, hne, _, _, _⟩ := admissible_error_analysis hphi
  let fill : productDomain X Y := ⟨hne.choose, hne.choose_spec⟩
  obtain ⟨f, hfm, hfeq⟩ := admissible_jet_borel_extension hphi
  have hm := (MeasurableExecution.scalar_runner_jointly_measurable A fill
    (fun (_ : Unit) (_ : Fin N) => f)
    (fun _ => hfm.comp measurable_snd)).2
  have heq : (fun seed => Deterministic.runScalarPolicy (A.policy seed)
      (exactScalarJet p phi) N []) =
      fun seed => MeasurableExecution.scalarRunnerOutput A fill
        (fun (_ : Unit) (_ : Fin N) => f) ((), seed) := by
    funext seed
    rw [MeasurableExecution.scalar_runner_fixed_eq_source_run A fill (fun (_ : Unit) => f)]
    exact source_run_eq_of_feasible_oracle_eq _ _ _ (fun z hz => (hfeq z hz).symm) N []
  rw [heq]
  exact hm.comp (measurable_const.prodMk measurable_id)

/-- The actual saddle gap is continuous on the feasible product even when
no regularity is imposed outside that product. -/
theorem audited_gap_continuous_feasible {dx dy : ℕ}
    {X : Set (Primal dx)} {Y : Set (Dual dy)}
    (hX : IsCompact X) (hY : IsCompact Y) (hneX : X.Nonempty) (hneY : Y.Nonempty)
    {phi : SaddleSpace dx dy → ℝ} (hphi : ContinuousOn phi (productDomain X Y)) :
    Continuous (fun z : productDomain X Y =>
      auditedSaddleGap X Y (fun x y => phi (joinBlocks x y))
        (primalBlock (z : SaddleSpace dx dy)) (dualBlock (z : SaddleSpace dx dy))) := by
  let Z : Set (SaddleSpace dx dy) := productDomain X Y
  letI : CompactSpace X := isCompact_iff_compactSpace.mp hX
  letI : CompactSpace Y := isCompact_iff_compactSpace.mp hY
  have hp : Continuous (fun z : Z => primalBlock (z : SaddleSpace dx dy)) := by
    have heq : (fun z : Z => primalBlock (z : SaddleSpace dx dy)) =
        fun z : Z => primalProjection dx dy (z : SaddleSpace dx dy) := by
      funext z
      exact (primal_projection_apply (z : SaddleSpace dx dy)).symm
    rw [heq]
    exact (primalProjection dx dy).continuous.comp continuous_subtype_val
  have hd : Continuous (fun z : Z => dualBlock (z : SaddleSpace dx dy)) := by
    have heq : (fun z : Z => dualBlock (z : SaddleSpace dx dy)) =
        fun z : Z => dualProjection dx dy (z : SaddleSpace dx dy) := by
      funext z
      exact (dual_projection_apply (z : SaddleSpace dx dy)).symm
    rw [heq]
    exact (dualProjection dx dy).continuous.comp continuous_subtype_val
  have hjoinY : Continuous (fun w : Z × Y =>
      (⟨joinBlocks (primalBlock (w.1 : SaddleSpace dx dy)) w.2, by
        constructor
        · simpa using w.1.property.1
        · simpa using w.2.property⟩ : Z)) := by
    apply Continuous.subtype_mk
    exact (continuous_source_join dx dy).comp
      ((hp.comp continuous_fst).prodMk (continuous_subtype_val.comp continuous_snd))
  have hjoinX : Continuous (fun w : Z × X =>
      (⟨joinBlocks w.2 (dualBlock (w.1 : SaddleSpace dx dy)), by
        constructor
        · simpa using w.2.property
        · simpa using w.1.property.2⟩ : Z)) := by
    apply Continuous.subtype_mk
    exact (continuous_source_join dx dy).comp
      ((continuous_subtype_val.comp continuous_snd).prodMk (hd.comp continuous_fst))
  have hmax : Continuous (fun z : Z =>
      sSup ((fun y : Y => phi (joinBlocks (primalBlock (z : SaddleSpace dx dy)) y)) '' Set.univ)) :=
    (isCompact_univ : IsCompact (Set.univ : Set Y)).continuous_sSup
      (hphi.restrict.comp hjoinY)
  have hmin : Continuous (fun z : Z =>
      sInf ((fun x : X => phi (joinBlocks x (dualBlock (z : SaddleSpace dx dy)))) '' Set.univ)) :=
    (isCompact_univ : IsCompact (Set.univ : Set X)).continuous_sInf
      (hphi.restrict.comp hjoinX)
  have himgY (z : Z) :
      (fun y : Y => phi (joinBlocks (primalBlock (z : SaddleSpace dx dy)) y)) '' Set.univ =
      (fun y => phi (joinBlocks (primalBlock (z : SaddleSpace dx dy)) y)) '' Y := by
    ext r
    constructor
    · rintro ⟨y,_,rfl⟩
      exact ⟨y,y.property,rfl⟩
    · rintro ⟨y,hy,rfl⟩
      exact ⟨⟨y,hy⟩,Set.mem_univ _,rfl⟩
  have himgX (z : Z) :
      (fun x : X => phi (joinBlocks x (dualBlock (z : SaddleSpace dx dy)))) '' Set.univ =
      (fun x => phi (joinBlocks x (dualBlock (z : SaddleSpace dx dy)))) '' X := by
    ext r
    constructor
    · rintro ⟨x,_,rfl⟩
      exact ⟨x,x.property,rfl⟩
    · rintro ⟨x,hx,rfl⟩
      exact ⟨⟨x,hx⟩,Set.mem_univ _,rfl⟩
  have heq : (fun z : Z => auditedSaddleGap X Y (fun x y => phi (joinBlocks x y))
      (primalBlock (z : SaddleSpace dx dy)) (dualBlock (z : SaddleSpace dx dy))) = fun z : Z =>
      sSup ((fun y : Y => phi (joinBlocks (primalBlock (z : SaddleSpace dx dy)) y)) '' Set.univ) -
      sInf ((fun x : X => phi (joinBlocks x (dualBlock (z : SaddleSpace dx dy)))) '' Set.univ) := by
    funext z
    rw [himgY, himgX]
    apply saddle_gap_eq_sup_sub_inf _ hX hY hneX hneY
    · exact hphi.comp (continuous_join_primal _).continuousOn
        (fun x hx => by simpa [productDomain] using And.intro hx z.property.2)
    · exact hphi.comp (continuous_join_dual _).continuousOn
        (fun y hy => by simpa [productDomain] using And.intro z.property.1 hy)
  rw [heq]
  exact hmax.sub hmin

/-- Both actual error functions of the saved run are measurable for every
source-admissible scalar potential. The source class is not strengthened. -/
theorem admissible_actual_errors_measurable {p dx dy N : ℕ} {L D : ℝ}
    {X : Set (Primal dx)} {Y : Set (Dual dy)}
    {Seed : Type*} [MeasurableSpace Seed] {mu : Measure Seed}
    (A : RandomizedScalarPolicy p dx dy N X Y Seed mu)
    {phi : SaddleSpace dx dy → ℝ} (hphi : AdmissibleScalar p L D X Y phi) :
    Measurable (fun seed => auditedTangentResidual (productDomain X Y)
      (scalarSaddleOperator phi)
      (Deterministic.runScalarPolicy (A.policy seed) (exactScalarJet p phi) N [])) ∧
    Measurable (fun seed =>
      let z := Deterministic.runScalarPolicy (A.policy seed) (exactScalarJet p phi) N []
      auditedSaddleGap X Y (fun x y => phi (joinBlocks x y))
        (primalBlock z) (dualBlock z)) := by
  obtain ⟨hZ, _, hcont, _, hF⟩ := admissible_error_analysis hphi
  have hout := admissible_saved_output_measurable A hphi
  have hsub : Measurable (fun seed => (⟨Deterministic.runScalarPolicy
      (A.policy seed) (exactScalarJet p phi) N [],
      Deterministic.runScalarPolicy_feasible _ _ _ _⟩ : productDomain X Y)) :=
    hout.subtype_mk
  rcases hphi with ⟨_, _, _, hneX, hneY, hX, hY, _⟩
  constructor
  · have htan : Measurable (fun z : productDomain X Y =>
        auditedTangentResidual (productDomain X Y) (scalarSaddleOperator phi)
          (z : SaddleSpace dx dy)) :=
      audited_tangent_measurable (E := SaddleSpace dx dy) hZ hF
    have hcomp := Measurable.comp htan hsub
    simpa only [Function.comp_def] using hcomp
  · have hgap := audited_gap_continuous_feasible (dx := dx) (dy := dy)
      (X := X) (Y := Y) hX hY hneX hneY hcont
    have hcomp := Measurable.comp hgap.measurable hsub
    simpa only [Function.comp_def] using hcomp

/-- Actual tangent-success events used by the minimax definition are Borel. -/
theorem admissible_tangent_success_event_measurable {p dx dy N : ℕ} {L D : ℝ}
    {X : Set (Primal dx)} {Y : Set (Dual dy)}
    {Seed : Type*} [MeasurableSpace Seed] {mu : Measure Seed}
    (A : RandomizedScalarPolicy p dx dy N X Y Seed mu)
    {phi : SaddleSpace dx dy → ℝ} (hphi : AdmissibleScalar p L D X Y phi) (eps : ℝ) :
    MeasurableSet {seed | auditedTangentResidual (productDomain X Y)
      (scalarSaddleOperator phi)
      (Deterministic.runScalarPolicy (A.policy seed) (exactScalarJet p phi) N []) ≤ eps} :=
  measurableSet_le (admissible_actual_errors_measurable A hphi).1 measurable_const

/-- Actual saddle-gap-success events used by the minimax definition are Borel. -/
theorem admissible_gap_success_event_measurable {p dx dy N : ℕ} {L D : ℝ}
    {X : Set (Primal dx)} {Y : Set (Dual dy)}
    {Seed : Type*} [MeasurableSpace Seed] {mu : Measure Seed}
    (A : RandomizedScalarPolicy p dx dy N X Y Seed mu)
    {phi : SaddleSpace dx dy → ℝ} (hphi : AdmissibleScalar p L D X Y phi) (eps : ℝ) :
    MeasurableSet {seed |
      let z := Deterministic.runScalarPolicy (A.policy seed) (exactScalarJet p phi) N []
      auditedSaddleGap X Y (fun x y => phi (joinBlocks x y))
        (primalBlock z) (dualBlock z) ≤ eps} :=
  measurableSet_le (admissible_actual_errors_measurable A hphi).2 measurable_const

end
end MinimaxAudit
