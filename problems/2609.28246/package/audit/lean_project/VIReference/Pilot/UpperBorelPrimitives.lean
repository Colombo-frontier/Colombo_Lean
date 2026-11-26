import VIReference.Pilot.UpperBoost
import VIReference.Pilot.UpperHalvingExecution

open Set MeasureTheory
open scoped RealInnerProductSpace

namespace VIReference.Pilot

noncomputable section

universe u v

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
/-- The graph of the normal-cone correspondence is closed. -/
theorem isClosed_upperNormalConeGraph (X : Set E) :
    IsClosed {z : E × E | z.2 ∈ normalCone X z.1} := by
  rw [show {z : E × E | z.2 ∈ normalCone X z.1} =
      ⋂ y, ⋂ (_hy : y ∈ X),
        {z : E × E | inner ℝ z.2 (y - z.1) ≤ 0} by
    ext z
    simp [normalCone]]
  apply isClosed_iInter
  intro y
  apply isClosed_iInter
  intro hy
  apply isClosed_le
  · fun_prop
  · fun_prop

theorem isClosed_normalCone_graph_feasible (data : VIPublicData E) :
    IsClosed {z : data.X × E | z.2 ∈ normalCone data.X z.1.1} := by
  exact (isClosed_upperNormalConeGraph data.X).preimage
    ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)

/-- Reading the zeroth component of a normed jet is continuous. -/
theorem continuous_symmetricJetValue_upperNorm (data : VIPublicData E) :
    Continuous (symmetricJetValue data) := by
  unfold symmetricJetValue
  fun_prop

section Measurable

variable [MeasurableSpace E] [BorelSpace E]

set_option linter.defProp false in
/-- Local second-countability glue for the finite family of multilinear-map
spaces making up a jet. -/
@[reducible] noncomputable def upperCmlmSecondCountableTopology :
    (n : ℕ) → SecondCountableTopology (E [×n]→L[ℝ] E)
  | 0 =>
      (continuousMultilinearCurryFin0 ℝ E E).toHomeomorph.secondCountableTopology
  | n + 1 => by
      letI : SecondCountableTopology (E [×n]→L[ℝ] E) :=
        upperCmlmSecondCountableTopology n
      exact (continuousMultilinearCurryLeftEquiv ℝ
        (fun _ : Fin (n + 1) => E) E).toHomeomorph.secondCountableTopology

omit [MeasurableSpace E] [BorelSpace E] in
/-- The componentwise oracle sigma algebra agrees with the norm-Borel jet
sigma algebra in finite dimension. -/
theorem upperSymmetricExactJet_measurable_eq_normBorel (p : ℕ) :
    (inferInstance : MeasurableSpace (SymmetricExactJet E p)) =
      upperJetBorelMeasurableSpace p := by
  letI (n : ℕ) : SecondCountableTopology (E [×n]→L[ℝ] E) :=
    upperCmlmSecondCountableTopology n
  exact BorelSpace.measurable_eq

/-- The default feasible-subtype sigma algebra is the named upper one. -/
theorem upperFeasible_measurable_eq_normBorel (data : VIPublicData E) :
    (inferInstance : MeasurableSpace data.X) =
      upperFeasibleBorelMeasurableSpace data := by
  simpa [upperFeasibleBorelMeasurableSpace] using congrArg
    (fun m : MeasurableSpace E =>
      @Subtype.instMeasurableSpace E (fun x => x ∈ data.X) m)
    (show (inferInstance : MeasurableSpace E) = borel E from
      BorelSpace.measurable_eq)

theorem measurableSet_normalCone_graph (X : Set E) :
    MeasurableSet {z : E × E | z.2 ∈ normalCone X z.1} :=
    (isClosed_upperNormalConeGraph X).measurableSet

theorem measurableSet_normalCone_graph_feasible (data : VIPublicData E) :
    MeasurableSet {z : data.X × E | z.2 ∈ normalCone data.X z.1.1} :=
  (isClosed_normalCone_graph_feasible data).measurableSet

theorem measurable_normalCone_graph_predicate (X : Set E) :
    Measurable (fun z : E × E => z.2 ∈ normalCone X z.1) := by
  exact measurableSet_setOf.mp (measurableSet_normalCone_graph X)

theorem measurable_normalCone_graph_feasible_predicate (data : VIPublicData E) :
    Measurable (fun z : data.X × E => z.2 ∈ normalCone data.X z.1.1) := by
  exact measurableSet_setOf.mp (measurableSet_normalCone_graph_feasible data)

/-- Zeroth-jet evaluation is measurable for the named norm-Borel upper space. -/
theorem measurable_symmetricJetValue_upperBorel (data : VIPublicData E) :
    @Measurable (SymmetricExactJet E data.p) E
      (upperJetBorelMeasurableSpace data.p) (inferInstance)
      (symmetricJetValue data) := by
  letI : MeasurableSpace (SymmetricExactJet E data.p) :=
    upperJetBorelMeasurableSpace data.p
  letI : BorelSpace (SymmetricExactJet E data.p) := ⟨rfl⟩
  exact (continuous_symmetricJetValue_upperNorm data).measurable

/-- Zeroth-jet evaluation is also measurable for the componentwise oracle
measurable structure. -/
theorem measurable_symmetricJetValue_componentwise (data : VIPublicData E) :
    Measurable (symmetricJetValue data) := by
  unfold symmetricJetValue
  fun_prop

omit [MeasurableSpace E] [BorelSpace E] in
/-- The continuous ambient model selector is jointly norm-Borel measurable. -/
theorem measurable_knownModelStep_upperBorel (data : VIPublicData E) :
    @Measurable (data.X × SymmetricExactJet E data.p) (data.X × E)
      ((upperFeasibleBorelMeasurableSpace data).prod
        (upperJetBorelMeasurableSpace data.p))
      ((upperFeasibleBorelMeasurableSpace data).prod (borel E))
      (fun a => knownModelStep data a.1 a.2) := by
  letI : MeasurableSpace E := borel E
  letI : BorelSpace E := ⟨rfl⟩
  letI : MeasurableSpace data.X := upperFeasibleBorelMeasurableSpace data
  letI : BorelSpace data.X := Subtype.borelSpace (fun x : E => x ∈ data.X)
  letI : MeasurableSpace (SymmetricExactJet E data.p) :=
    upperJetBorelMeasurableSpace data.p
  letI : BorelSpace (SymmetricExactJet E data.p) := ⟨rfl⟩
  exact (continuous_knownModelStep data).measurable

theorem measurable_knownModelStep_componentwise (data : VIPublicData E) :
    Measurable (fun input : data.X × SymmetricExactJet E data.p =>
      knownModelStep data input.1 input.2) := by
  have h := measurable_knownModelStep_upperBorel data
  rw [← upperSymmetricExactJet_measurable_eq_normBorel data.p,
    ← upperFeasible_measurable_eq_normBorel data,
    ← BorelSpace.measurable_eq] at h
  exact h

/-! ### Halving outputs -/

/-- Product coordinates used to put the canonical Borel structure on a
halving result. -/
def HalvingOutput.coordinates (data : VIPublicData E) :
    HalvingOutput data → E × Bool × E × E :=
  fun out => (out.point, out.early, out.normal, out.value)

noncomputable instance halvingOutputMeasurableSpace (data : VIPublicData E) :
    MeasurableSpace (HalvingOutput data) :=
  MeasurableSpace.comap (HalvingOutput.coordinates data) inferInstance

omit [BorelSpace E] in
theorem measurable_halvingOutput_mk (data : VIPublicData E) {P : Type v}
    [MeasurableSpace P] {point : P → E} {early : P → Bool}
    {normal value : P → E} (hp : Measurable point) (he : Measurable early)
    (hn : Measurable normal) (hv : Measurable value) :
    Measurable (fun p => ({
      point := point p
      early := early p
      normal := normal p
      value := value p } : HalvingOutput data)) := by
  rw [measurable_comap_iff]
  simpa [HalvingOutput.coordinates, Function.comp_def] using
    (hp.prodMk (he.prodMk (hn.prodMk hv)))

/-! ### Feasible-state maps -/

omit [MeasurableSpace E] [BorelSpace E] in
/-- The canonical projection into the compact convex feasible set is
continuous (indeed, nonexpansive). -/
theorem continuous_compactProjection (data : VIPublicData E) :
    Continuous (compactProjection data) := by
  have hp : LipschitzWith 1 (compactConvexProjection data.X data.X_nonempty
      data.X_compact data.X_convex) := by
    apply LipschitzWith.mk_one
    intro x y
    simpa [dist_eq_norm] using compactConvexProjection_dist_le data.X
      data.X_nonempty data.X_compact data.X_convex x y
  exact hp.continuous.subtype_mk _

omit [MeasurableSpace E] [BorelSpace E] in
/-- Norm-Borel measurability of the canonical feasible projection. -/
theorem measurable_compactProjection_upperBorel (data : VIPublicData E) :
    @Measurable E data.X (borel E)
      (upperFeasibleBorelMeasurableSpace data) (compactProjection data) := by
  letI : MeasurableSpace E := borel E
  letI : BorelSpace E := ⟨rfl⟩
  letI : MeasurableSpace data.X := upperFeasibleBorelMeasurableSpace data
  letI : BorelSpace data.X := Subtype.borelSpace (fun x : E => x ∈ data.X)
  exact (continuous_compactProjection data).measurable

omit [MeasurableSpace E] [BorelSpace E] in
/-- Each ordinary feasible Halpern state update is continuous. -/
theorem continuous_feasibleHalpernUpdate (data : VIPublicData E) (t : ℕ) :
    Continuous (feasibleHalpernUpdate data t) := by
  unfold feasibleHalpernUpdate
  fun_prop

omit [MeasurableSpace E] [BorelSpace E] in
/-- Norm-Borel measurability of each feasible Halpern state update. -/
theorem measurable_feasibleHalpernUpdate_upperBorel
    (data : VIPublicData E) (t : ℕ) :
    @Measurable data.X data.X (upperFeasibleBorelMeasurableSpace data)
      (upperFeasibleBorelMeasurableSpace data) (feasibleHalpernUpdate data t) := by
  letI : MeasurableSpace E := borel E
  letI : BorelSpace E := ⟨rfl⟩
  letI : MeasurableSpace data.X := upperFeasibleBorelMeasurableSpace data
  letI : BorelSpace data.X := Subtype.borelSpace (fun x : E => x ∈ data.X)
  exact (continuous_feasibleHalpernUpdate data t).measurable

/-! ### Regularized jet arithmetic -/

omit [MeasurableSpace E] [BorelSpace E] in
/-- The exact jet of the affine regularizer depends continuously on its
query point in the norm topology. -/
theorem continuous_affineRegularizerJet (p : ℕ) (eta : ℝ) (center : E) :
    Continuous (affineRegularizerJet p eta center) := by
  apply continuous_pi
  intro j
  apply Continuous.subtype_mk
  change Continuous (fun point : E =>
    iteratedFDeriv ℝ j.1 (affineRegularizer eta center) point)
  by_cases hj : j.1 = 0
  · rw [hj]
    have hregularizer : Continuous (affineRegularizer eta center) := by
      unfold affineRegularizer
      fun_prop
    have hu : Continuous (fun point : E =>
        ContinuousMultilinearMap.uncurry0 ℝ E
          (affineRegularizer eta center point)) :=
      (continuousMultilinearCurryFin0 ℝ E E).symm.continuous.comp hregularizer
    convert hu using 1
    funext point
    ext v
    simp [iteratedFDeriv_zero_apply]
  · have hjpos : 0 < j.1 := Nat.pos_of_ne_zero hj
    have heq : (fun point : E =>
        iteratedFDeriv ℝ j.1 (affineRegularizer eta center) point) =
        fun _ => iteratedFDeriv ℝ j.1 (affineRegularizer eta center) 0 := by
      funext point
      exact affineRegularizer_iteratedFDeriv_independent eta center j.1
        hjpos point 0
    rw [heq]
    exact continuous_const

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Pointwise jet addition is jointly continuous in the norm topology. -/
theorem continuous_addSymmetricJet (p : ℕ) :
    Continuous (fun pair : SymmetricExactJet E p × SymmetricExactJet E p =>
      addSymmetricJet pair.1 pair.2) := by
  apply continuous_pi
  intro j
  apply Continuous.subtype_mk
  change Continuous (fun pair :
    SymmetricExactJet E p × SymmetricExactJet E p =>
      (pair.1 j).1 + (pair.2 j).1)
  fun_prop

omit [MeasurableSpace E] [BorelSpace E] in
/-- The local transformation from a base jet and its query point to the
regularized jet is jointly continuous. -/
theorem continuous_regularizedJetAnswer (p : ℕ) (eta : ℝ) (center : E) :
    Continuous (fun input : E × SymmetricExactJet E p =>
      regularizedJetAnswer p eta center input.1 input.2) := by
  exact (continuous_addSymmetricJet (E := E) p).comp
    (continuous_snd.prodMk
      ((continuous_affineRegularizerJet (E := E) p eta center).comp
        continuous_fst))

omit [MeasurableSpace E] [BorelSpace E] in
/-- Joint norm-Borel measurability of the regularized jet transformation. -/
theorem measurable_regularizedJetAnswer_upperBorel
    (p : ℕ) (eta : ℝ) (center : E) :
    @Measurable (E × SymmetricExactJet E p) (SymmetricExactJet E p)
      ((borel E).prod (upperJetBorelMeasurableSpace p))
      (upperJetBorelMeasurableSpace p)
      (fun input => regularizedJetAnswer p eta center input.1 input.2) := by
  letI : MeasurableSpace E := borel E
  letI : BorelSpace E := ⟨rfl⟩
  letI : MeasurableSpace (SymmetricExactJet E p) :=
    upperJetBorelMeasurableSpace p
  letI : BorelSpace (SymmetricExactJet E p) := ⟨rfl⟩
  exact (continuous_regularizedJetAnswer (E := E) p eta center).measurable

omit [MeasurableSpace E] [BorelSpace E] in
/-- Feasible-query specialization of regularized-jet measurability. -/
theorem measurable_regularizedJetAnswer_feasible_upperBorel
    (data : VIPublicData E) (eta : ℝ) (center : E) :
    @Measurable (data.X × SymmetricExactJet E data.p)
      (SymmetricExactJet E data.p)
      ((upperFeasibleBorelMeasurableSpace data).prod
        (upperJetBorelMeasurableSpace data.p))
      (upperJetBorelMeasurableSpace data.p)
      (fun input => regularizedJetAnswer data.p eta center input.1.1 input.2) := by
  letI : MeasurableSpace E := borel E
  letI : BorelSpace E := ⟨rfl⟩
  letI : MeasurableSpace data.X := upperFeasibleBorelMeasurableSpace data
  letI : BorelSpace data.X := Subtype.borelSpace (fun x : E => x ∈ data.X)
  letI : MeasurableSpace (SymmetricExactJet E data.p) :=
    upperJetBorelMeasurableSpace data.p
  letI : BorelSpace (SymmetricExactJet E data.p) := ⟨rfl⟩
  exact (continuous_regularizedJetAnswer (E := E) data.p eta center).measurable.comp
    ((continuous_subtype_val.comp continuous_fst).measurable.prodMk measurable_snd)

/-! ### Evaluated certificates -/

/-- The field tuple underlying an evaluated normal certificate. -/
def evaluatedNormalCertificateEquiv (data : VIPublicData E) :
    EvaluatedNormalCertificate data ≃ data.X × E × E where
  toFun cert := (cert.point, cert.normal, cert.value)
  invFun fields :=
    { point := fields.1, normal := fields.2.1, value := fields.2.2 }
  left_inv cert := by cases cert; rfl
  right_inv fields := by rcases fields with ⟨point, normal, value⟩; rfl

/-- Product Borel structure on evaluated certificates, named to avoid a
global instance that could interfere with lower-bound measurable spaces. -/
@[reducible] noncomputable def upperEvaluatedNormalCertificateMeasurableSpace
    (data : VIPublicData E) :
    MeasurableSpace (EvaluatedNormalCertificate data) :=
  MeasurableSpace.comap (evaluatedNormalCertificateEquiv data)
    ((upperFeasibleBorelMeasurableSpace data).prod
      ((borel E).prod (borel E)))

local instance upperEvaluatedNormalCertificateMeasurableSpaceInst
    (data : VIPublicData E) :
    MeasurableSpace (EvaluatedNormalCertificate data) :=
  upperEvaluatedNormalCertificateMeasurableSpace data

/-- The certificate/product identification is a measurable equivalence. -/
noncomputable def evaluatedNormalCertificateMeasurableEquiv
    (data : VIPublicData E) :
    @MeasurableEquiv (EvaluatedNormalCertificate data) (data.X × E × E)
      (upperEvaluatedNormalCertificateMeasurableSpace data)
      ((upperFeasibleBorelMeasurableSpace data).prod
        ((borel E).prod (borel E))) := by
  letI : MeasurableSpace E := borel E
  letI : BorelSpace E := ⟨rfl⟩
  letI : MeasurableSpace data.X := upperFeasibleBorelMeasurableSpace data
  letI : MeasurableSpace (data.X × E × E) :=
    (upperFeasibleBorelMeasurableSpace data).prod
      ((borel E).prod (borel E))
  letI : MeasurableSpace (EvaluatedNormalCertificate data) :=
    upperEvaluatedNormalCertificateMeasurableSpace data
  exact
    { toEquiv := evaluatedNormalCertificateEquiv data
      measurable_toFun := comap_measurable _
      measurable_invFun := by
        rw [measurable_comap_iff]
        simpa using (measurable_id : Measurable (fun x : data.X × E × E => x)) }

omit [MeasurableSpace E] [BorelSpace E] in
theorem measurable_evaluatedNormalCertificate_point (data : VIPublicData E) :
    @Measurable (EvaluatedNormalCertificate data) data.X
      (upperEvaluatedNormalCertificateMeasurableSpace data)
      (upperFeasibleBorelMeasurableSpace data)
      EvaluatedNormalCertificate.point := by
  letI : MeasurableSpace E := borel E
  letI : BorelSpace E := ⟨rfl⟩
  letI : MeasurableSpace data.X := upperFeasibleBorelMeasurableSpace data
  letI : MeasurableSpace (data.X × E × E) :=
    (upperFeasibleBorelMeasurableSpace data).prod
      ((borel E).prod (borel E))
  exact measurable_fst.comp
    (evaluatedNormalCertificateMeasurableEquiv data).measurable

omit [MeasurableSpace E] [BorelSpace E] in
theorem measurable_evaluatedNormalCertificate_normal (data : VIPublicData E) :
    @Measurable (EvaluatedNormalCertificate data) E
      (upperEvaluatedNormalCertificateMeasurableSpace data) (borel E)
      EvaluatedNormalCertificate.normal := by
  letI : MeasurableSpace E := borel E
  letI : BorelSpace E := ⟨rfl⟩
  letI : MeasurableSpace data.X := upperFeasibleBorelMeasurableSpace data
  letI : MeasurableSpace (data.X × E × E) :=
    (upperFeasibleBorelMeasurableSpace data).prod
      ((borel E).prod (borel E))
  exact (measurable_fst.comp measurable_snd).comp
    (evaluatedNormalCertificateMeasurableEquiv data).measurable

omit [MeasurableSpace E] [BorelSpace E] in
theorem measurable_evaluatedNormalCertificate_value (data : VIPublicData E) :
    @Measurable (EvaluatedNormalCertificate data) E
      (upperEvaluatedNormalCertificateMeasurableSpace data) (borel E)
      EvaluatedNormalCertificate.value := by
  letI : MeasurableSpace E := borel E
  letI : BorelSpace E := ⟨rfl⟩
  letI : MeasurableSpace data.X := upperFeasibleBorelMeasurableSpace data
  letI : MeasurableSpace (data.X × E × E) :=
    (upperFeasibleBorelMeasurableSpace data).prod
      ((borel E).prod (borel E))
  exact (measurable_snd.comp measurable_snd).comp
    (evaluatedNormalCertificateMeasurableEquiv data).measurable

omit [MeasurableSpace E] [BorelSpace E] in
theorem measurable_evaluatedNormalCertificate_mk
    {A : Type v} {mA : MeasurableSpace A} (data : VIPublicData E)
    {point : A → data.X} {normal value : A → E}
    (hpoint : @Measurable A data.X mA
      (upperFeasibleBorelMeasurableSpace data) point)
    (hnormal : @Measurable A E mA (borel E) normal)
    (hvalue : @Measurable A E mA (borel E) value) :
    @Measurable A (EvaluatedNormalCertificate data) mA
      (upperEvaluatedNormalCertificateMeasurableSpace data)
      (fun a => ({ point := point a, normal := normal a, value := value a } :
        EvaluatedNormalCertificate data)) := by
  rw [measurable_comap_iff]
  exact hpoint.prodMk (hnormal.prodMk hvalue)

omit [MeasurableSpace E] [BorelSpace E] in
theorem measurable_certificate_normal_predicate (data : VIPublicData E) :
    @Measurable (EvaluatedNormalCertificate data) Prop
      (upperEvaluatedNormalCertificateMeasurableSpace data) (inferInstance)
      (fun cert => cert.normal ∈ normalCone data.X cert.point.1) := by
  letI : MeasurableSpace E := borel E
  letI : BorelSpace E := ⟨rfl⟩
  letI : MeasurableSpace data.X := upperFeasibleBorelMeasurableSpace data
  exact (measurable_normalCone_graph_feasible_predicate data).comp
    ((measurable_evaluatedNormalCertificate_point data).prodMk
      (measurable_evaluatedNormalCertificate_normal data))

omit [MeasurableSpace E] [BorelSpace E] in
theorem measurableSet_certificate_normal (data : VIPublicData E) :
    @MeasurableSet (EvaluatedNormalCertificate data)
      (upperEvaluatedNormalCertificateMeasurableSpace data)
      {cert | cert.normal ∈ normalCone data.X cert.point.1} := by
  exact measurableSet_setOf.mpr (measurable_certificate_normal_predicate data)

omit [MeasurableSpace E] [BorelSpace E] in
theorem measurable_certificate_residual (data : VIPublicData E) :
    @Measurable (EvaluatedNormalCertificate data) ℝ
      (upperEvaluatedNormalCertificateMeasurableSpace data) (borel ℝ)
      (fun cert => ‖cert.value + cert.normal‖) := by
  letI : MeasurableSpace E := borel E
  letI : BorelSpace E := ⟨rfl⟩
  exact ((measurable_evaluatedNormalCertificate_value data).add
    (measurable_evaluatedNormalCertificate_normal data)).norm

omit [MeasurableSpace E] [BorelSpace E] in
theorem measurableSet_certificate_residual_le
    (data : VIPublicData E) (delta : ℝ) :
    @MeasurableSet (EvaluatedNormalCertificate data)
      (upperEvaluatedNormalCertificateMeasurableSpace data)
      {cert | ‖cert.value + cert.normal‖ ≤ delta} := by
  exact measurableSet_le (measurable_certificate_residual data) measurable_const

/-- Apply both public checks and retain exactly the certificates that pass. -/
noncomputable def checkedEvaluatedNormalCertificate
    (data : VIPublicData E) (delta : ℝ)
    (cert : EvaluatedNormalCertificate data) :
    Option (EvaluatedNormalCertificate data) := by
  classical
  exact if cert.normal ∈ normalCone data.X cert.point.1 then
    if ‖cert.value + cert.normal‖ ≤ delta then some cert else none
  else none

/-- The measurable structure on optional checked certificates induced by
`Option α ≃ α ⊕ PUnit`. -/
@[reducible] noncomputable def upperOptionalEvaluatedNormalCertificateMeasurableSpace
    (data : VIPublicData E) :
    MeasurableSpace (Option (EvaluatedNormalCertificate data)) :=
  MeasurableSpace.comap
    (Equiv.optionEquivSumPUnit.{0, u} (EvaluatedNormalCertificate data))
    (@Sum.instMeasurableSpace (EvaluatedNormalCertificate data) PUnit.{1}
      (upperEvaluatedNormalCertificateMeasurableSpace data) inferInstance)

local instance upperOptionalEvaluatedNormalCertificateMeasurableSpaceInst
    (data : VIPublicData E) :
    MeasurableSpace (Option (EvaluatedNormalCertificate data)) :=
  upperOptionalEvaluatedNormalCertificateMeasurableSpace data

omit [MeasurableSpace E] [BorelSpace E] in
theorem measurable_checkedEvaluatedNormalCertificate
    (data : VIPublicData E) (delta : ℝ) :
    Measurable (checkedEvaluatedNormalCertificate data delta) := by
  classical
  rw [measurable_comap_iff]
  unfold checkedEvaluatedNormalCertificate
  change Measurable (fun cert : EvaluatedNormalCertificate data =>
    (Equiv.optionEquivSumPUnit.{0, u} (EvaluatedNormalCertificate data))
      (if cert.normal ∈ normalCone data.X cert.point.1 then
        if ‖cert.value + cert.normal‖ ≤ delta then some cert else none
      else none))
  simp only [apply_ite, Equiv.optionEquivSumPUnit_some,
    Equiv.optionEquivSumPUnit_none]
  apply Measurable.ite (measurableSet_certificate_normal data)
  · apply Measurable.ite (measurableSet_certificate_residual_le data delta)
    · simpa using
        (measurable_inl.comp (measurable_id : Measurable
          (fun cert : EvaluatedNormalCertificate data => cert)))
    · exact measurable_inr.comp (measurable_const : Measurable
        (fun _ : EvaluatedNormalCertificate data => PUnit.unit))
  · exact measurable_inr.comp (measurable_const : Measurable
      (fun _ : EvaluatedNormalCertificate data => PUnit.unit))

/-- Total feasible output used after a checked call: successful certificates
project their point and failure uses the public fallback. -/
def evaluatedNormalCertificateOutput (data : VIPublicData E)
    (fallback : data.X) :
    Option (EvaluatedNormalCertificate data) → data.X
  | some cert => cert.point
  | none => fallback

omit [MeasurableSpace E] [BorelSpace E] in
theorem measurable_evaluatedNormalCertificateOutput
    (data : VIPublicData E) (fallback : data.X) :
    @Measurable (Option (EvaluatedNormalCertificate data)) data.X
      (upperOptionalEvaluatedNormalCertificateMeasurableSpace data)
      (upperFeasibleBorelMeasurableSpace data)
      (evaluatedNormalCertificateOutput data fallback) := by
  letI : MeasurableSpace E := borel E
  letI : BorelSpace E := ⟨rfl⟩
  letI : MeasurableSpace data.X := upperFeasibleBorelMeasurableSpace data
  letI : MeasurableSpace (EvaluatedNormalCertificate data) :=
    upperEvaluatedNormalCertificateMeasurableSpace data
  letI : MeasurableSpace (EvaluatedNormalCertificate data ⊕ PUnit.{1}) :=
    @Sum.instMeasurableSpace (EvaluatedNormalCertificate data) PUnit.{1}
      (upperEvaluatedNormalCertificateMeasurableSpace data) inferInstance
  letI : MeasurableSpace (Option (EvaluatedNormalCertificate data)) :=
    upperOptionalEvaluatedNormalCertificateMeasurableSpace data
  have hsum : Measurable (fun value :
      EvaluatedNormalCertificate data ⊕ PUnit.{1} =>
      value.elim EvaluatedNormalCertificate.point (fun _ => fallback)) := by
    apply measurable_fun_sum
    · change Measurable (EvaluatedNormalCertificate.point :
        EvaluatedNormalCertificate data → data.X)
      exact measurable_evaluatedNormalCertificate_point data
    · change Measurable (fun _ : PUnit.{1} => fallback)
      exact measurable_const
  have heq :
      (fun value : EvaluatedNormalCertificate data ⊕ PUnit.{1} =>
        value.elim EvaluatedNormalCertificate.point (fun _ => fallback)) ∘
          (Equiv.optionEquivSumPUnit.{0, u}
            (EvaluatedNormalCertificate data)) =
        evaluatedNormalCertificateOutput data fallback := by
    funext value
    cases value <;> rfl
  rw [← heq]
  exact hsum.comp (comap_measurable
    (Equiv.optionEquivSumPUnit.{0, u} (EvaluatedNormalCertificate data)))

/-! ### Recovery and final certificate checks -/

omit [MeasurableSpace E] [BorelSpace E] in
/-- Removing the known affine regularizer from a saved certificate is
Borel measurable. -/
theorem measurable_recoverBaseCertificate (data : VIPublicData E)
    (eta : ℝ) (center : E) :
    @Measurable (EvaluatedNormalCertificate data)
      (EvaluatedNormalCertificate data)
      (upperEvaluatedNormalCertificateMeasurableSpace data)
      (upperEvaluatedNormalCertificateMeasurableSpace data)
      (recoverBaseCertificate data eta center) := by
  letI : MeasurableSpace E := borel E
  letI : BorelSpace E := ⟨rfl⟩
  letI : MeasurableSpace data.X := upperFeasibleBorelMeasurableSpace data
  letI : BorelSpace data.X := Subtype.borelSpace (fun x : E => x ∈ data.X)
  have hregularizer : @Measurable E E (borel E) (borel E)
      (affineRegularizer eta center) := by
    exact (by
      unfold affineRegularizer
      fun_prop : Continuous (affineRegularizer eta center)).measurable
  have hpointVal : @Measurable (EvaluatedNormalCertificate data) E
      (upperEvaluatedNormalCertificateMeasurableSpace data) (borel E)
      (fun cert => cert.point.1) :=
    continuous_subtype_val.measurable.comp
      (measurable_evaluatedNormalCertificate_point data)
  convert measurable_evaluatedNormalCertificate_mk data
      (measurable_evaluatedNormalCertificate_point data)
      (measurable_evaluatedNormalCertificate_normal data)
      ((measurable_evaluatedNormalCertificate_value data).sub
        (hregularizer.comp hpointVal)) using 1
  funext cert
  rfl

omit [MeasurableSpace E] [BorelSpace E] in
/-- The residual norm after removing the known affine regularizer is
measurable. -/
theorem measurable_recoveredCertificate_residual (data : VIPublicData E)
    (eta : ℝ) (center : E) :
    @Measurable (EvaluatedNormalCertificate data) ℝ
      (upperEvaluatedNormalCertificateMeasurableSpace data) (borel ℝ)
      (fun cert =>
        ‖(recoverBaseCertificate data eta center cert).value +
          (recoverBaseCertificate data eta center cert).normal‖) :=
  (measurable_certificate_residual data).comp
    (measurable_recoverBaseCertificate data eta center)

omit [MeasurableSpace E] [BorelSpace E] in
theorem measurableSet_recoveredCertificate_residual_le
    (data : VIPublicData E) (eta epsilon : ℝ) (center : E) :
    @MeasurableSet (EvaluatedNormalCertificate data)
      (upperEvaluatedNormalCertificateMeasurableSpace data)
      {cert |
        ‖(recoverBaseCertificate data eta center cert).value +
          (recoverBaseCertificate data eta center cert).normal‖ ≤ epsilon} := by
  exact measurableSet_le
    (measurable_recoveredCertificate_residual data eta center) measurable_const

/-- The final recovery check is Borel, including its explicit failure
branch. -/
theorem measurable_checkedRecoveredCertificate (data : VIPublicData E)
    (eta epsilon : ℝ) (center : E) :
    @Measurable (EvaluatedNormalCertificate data)
      (Option (EvaluatedNormalCertificate data))
      (upperEvaluatedNormalCertificateMeasurableSpace data)
      (upperOptionalEvaluatedNormalCertificateMeasurableSpace data)
      (checkedRecoveredCertificate data eta epsilon center) := by
  classical
  rw [measurable_comap_iff]
  unfold checkedRecoveredCertificate
  change Measurable (fun cert : EvaluatedNormalCertificate data =>
    (Equiv.optionEquivSumPUnit.{0, u} (EvaluatedNormalCertificate data))
      (if ‖(recoverBaseCertificate data eta center cert).value +
          (recoverBaseCertificate data eta center cert).normal‖ ≤ epsilon then
        some (recoverBaseCertificate data eta center cert)
      else none))
  simp only [apply_ite, Equiv.optionEquivSumPUnit_some,
    Equiv.optionEquivSumPUnit_none]
  apply Measurable.ite
    (measurableSet_recoveredCertificate_residual_le data eta epsilon center)
  · exact measurable_inl.comp
      (measurable_recoverBaseCertificate data eta center)
  · exact measurable_inr.comp (measurable_const : Measurable
      (fun _ : EvaluatedNormalCertificate data => PUnit.unit))

/-- A checked recovered certificate followed by the total feasible-output
projection is measurable. -/
theorem measurable_checkedRecoveredCertificateOutput
    (data : VIPublicData E) (eta epsilon : ℝ) (center : E)
    (fallback : data.X) :
    @Measurable (EvaluatedNormalCertificate data) data.X
      (upperEvaluatedNormalCertificateMeasurableSpace data)
      (upperFeasibleBorelMeasurableSpace data)
      (fun cert => evaluatedNormalCertificateOutput data fallback
        (checkedRecoveredCertificate data eta epsilon center cert)) :=
  (measurable_evaluatedNormalCertificateOutput data fallback).comp
    (measurable_checkedRecoveredCertificate data eta epsilon center)

end Measurable

end
end VIReference.Pilot
