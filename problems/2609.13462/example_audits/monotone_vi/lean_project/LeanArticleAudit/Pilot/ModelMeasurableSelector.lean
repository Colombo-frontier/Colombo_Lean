import LeanArticleAudit.Pilot.ModelExistenceClaim
import Mathlib.Analysis.Complex.Tietze

open Set Filter Topology MeasureTheory
open scoped RealInnerProductSpace BigOperators

namespace LeanArticleAudit.Pilot
noncomputable section
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

abbrev AmbientModelParameter (data : VIPublicData E) :=
  data.X × SymmetricExactJet E data.p

def IsValidModelParameter (data : VIPublicData E)
    (a : AmbientModelParameter data) : Prop :=
  ∀ u ∈ data.X, ∀ v ∈ data.X,
    -(data.Lp / (Nat.factorial (data.p - 1) : ℝ) *
        max (‖u - a.1.1‖ ^ (data.p - 1))
          (‖v - a.1.1‖ ^ (data.p - 1))) * ‖u - v‖ ^ 2 ≤
      inner ℝ
        (symmetricJetTaylor data.p a.1.1 a.2 u -
          symmetricJetTaylor data.p a.1.1 a.2 v) (u - v)

theorem isClosed_validModelParameter (data : VIPublicData E) :
    IsClosed {a : AmbientModelParameter data | IsValidModelParameter data a} := by
  rw [show {a : AmbientModelParameter data | IsValidModelParameter data a} =
      ⋂ u, ⋂ (_hu : u ∈ data.X), ⋂ v, ⋂ (_hv : v ∈ data.X),
        {a | -(data.Lp / (Nat.factorial (data.p - 1) : ℝ) *
          max (‖u - a.1.1‖ ^ (data.p - 1))
            (‖v - a.1.1‖ ^ (data.p - 1))) * ‖u - v‖ ^ 2 ≤
          inner ℝ
            (symmetricJetTaylor data.p a.1.1 a.2 u -
              symmetricJetTaylor data.p a.1.1 a.2 v) (u - v)} by
    ext a
    simp [IsValidModelParameter]]
  apply isClosed_iInter
  intro u
  apply isClosed_iInter
  intro hu
  apply isClosed_iInter
  intro v
  apply isClosed_iInter
  intro hv
  apply isClosed_le
  · fun_prop
  · unfold symmetricJetTaylor
    fun_prop

theorem genuineJet_validModelParameter (data : VIPublicData E) (G : E → E)
    (hG : IsAdmissibleOperator data G)
    (oracle : FeasibleExactSymmetricJetOracle data G) (center : data.X) :
    IsValidModelParameter data (center, oracle.answer center) := by
  intro u hu v hv
  let C : ℝ := data.Lp / (Nat.factorial (data.p - 1) : ℝ)
  let T := symmetricJetTaylor data.p center.1 (oracle.answer center)
  have hbase := inner_sub_lower_of_fderiv_close G T u v
    (C * max (‖u - center.1‖ ^ (data.p - 1))
      (‖v - center.1‖ ^ (data.p - 1)))
  apply hbase
  · exact hG.monotone_on u hu v hv
  · intro z hz
    obtain ⟨U, hU, hXU, hreg⟩ := hG.regularity
    have hcd := hreg.contDiffAt (hU.mem_nhds
      (hXU (data.X_convex.segment_subset hu hv hz)))
    have hpgt : (1 : WithTop ℕ∞) < (data.p : WithTop ℕ∞) := by
      apply WithTop.coe_lt_coe.mpr
      exact ENat.coe_lt_coe.mpr
        (lt_of_lt_of_le (by omega : 1 < 2) data.p_ge_two)
    exact hcd.differentiableAt (tsub_pos_iff_lt.mpr hpgt).ne'
  · intro z hz
    exact (symmetricJetTaylor_contDiff_one data.p center.1
      (oracle.answer center)).differentiable one_ne_zero z
  · intro z hz
    have hzX := data.X_convex.segment_subset hu hv hz
    have hrem := genuineJet_fderiv_model_close data G hG oracle center hzX
    have hnorm : ‖z - center.1‖ ≤
        max ‖u - center.1‖ ‖v - center.1‖ := by
      rw [segment_eq_image'] at hz
      obtain ⟨t, ht, rfl⟩ := hz
      have ht0 : 0 ≤ t := ht.1
      have ht1 : t ≤ 1 := ht.2
      rw [show u + t • (v - u) - center.1 =
          (1 - t) • (u - center.1) + t • (v - center.1) by module]
      calc
        ‖(1 - t) • (u - center.1) + t • (v - center.1)‖ ≤
            ‖(1 - t) • (u - center.1)‖ +
              ‖t • (v - center.1)‖ := norm_add_le _ _
        _ = (1 - t) * ‖u - center.1‖ + t * ‖v - center.1‖ := by
          simp [norm_smul, abs_of_nonneg ht0,
            abs_of_nonneg (sub_nonneg.mpr ht1)]
        _ ≤ (1 - t) * max ‖u - center.1‖ ‖v - center.1‖ +
            t * max ‖u - center.1‖ ‖v - center.1‖ := by gcongr <;> simp
        _ = max ‖u - center.1‖ ‖v - center.1‖ := by ring
    have hpow : ‖z - center.1‖ ^ (data.p - 1) ≤
        max (‖u - center.1‖ ^ (data.p - 1))
          (‖v - center.1‖ ^ (data.p - 1)) := by
      calc
        ‖z - center.1‖ ^ (data.p - 1) ≤
            (max ‖u - center.1‖ ‖v - center.1‖) ^ (data.p - 1) :=
          pow_le_pow_left₀ (norm_nonneg _) hnorm _
        _ = max (‖u - center.1‖ ^ (data.p - 1))
            (‖v - center.1‖ ^ (data.p - 1)) := by
          rcases le_total ‖u - center.1‖ ‖v - center.1‖ with huv | hvu
          · rw [max_eq_right huv, max_eq_right
              (pow_le_pow_left₀ (norm_nonneg _) huv _)]
          · rw [max_eq_left hvu, max_eq_left
              (pow_le_pow_left₀ (norm_nonneg _) hvu _)]
    exact hrem.trans (mul_le_mul_of_nonneg_left hpow
      (div_nonneg data.Lp_pos.le (by positivity)))

abbrev ValidModelParameter (data : VIPublicData E) :=
  {a : AmbientModelParameter data // IsValidModelParameter data a}

theorem validModel_strictMonotone (data : VIPublicData E)
    (a : ValidModelParameter data) {u v : E}
    (hu : u ∈ data.X) (hv : v ∈ data.X) (huv : u ≠ v) :
    0 < inner ℝ
      (exactJetModel data.p data.Lp a.1.1.1 a.1.2 u -
        exactJetModel data.p data.Lp a.1.1.1 a.1.2 v) (u - v) := by
  rw [exactJetModel_eq_stabilizedModel]
  apply stabilizedModel_strictMonotone_of_taylor_lower
    (data.p - 1) (data.Lp / (Nat.factorial (data.p - 1) : ℝ))
      (div_pos data.Lp_pos (by positivity)) a.1.1.1
      (symmetricJetTaylor data.p a.1.1.1 a.1.2) huv
  convert a.2 u hu v hv using 1 <;> ring

theorem validModel_monotone (data : VIPublicData E)
    (a : ValidModelParameter data) {u v : E}
    (hu : u ∈ data.X) (hv : v ∈ data.X) :
    0 ≤ inner ℝ
      (exactJetModel data.p data.Lp a.1.1.1 a.1.2 u -
        exactJetModel data.p data.Lp a.1.1.1 a.1.2 v) (u - v) := by
  by_cases h : u = v
  · subst v; simp
  · exact (validModel_strictMonotone data a hu hv h).le

theorem validModel_existsUnique (data : VIPublicData E)
    (a : ValidModelParameter data) :
    ∃! y, SolvesModelVI data.X
      (exactJetModel data.p data.Lp a.1.1.1 a.1.2) y := by
  obtain ⟨y, hy⟩ := continuous_monotone_vi_exists data.X data.X_nonempty
    data.X_compact data.X_convex _
    (exactJetModel_continuous data.p data.Lp a.1.1.1 a.1.2).continuousOn
    (exactJetModel_locallyLipschitz data.p data.Lp a.1.1.1 a.1.2).locallyLipschitzOn
    (fun u hu v hv ↦ validModel_monotone data a hu hv)
  refine ⟨y, hy, ?_⟩
  intro z hz
  exact solvesModelVI_unique
    (fun u hu v hv huv ↦ validModel_strictMonotone data a hu hv huv) hz hy

noncomputable def validModelSolution (data : VIPublicData E)
    (a : ValidModelParameter data) : E :=
  Classical.choose (validModel_existsUnique data a)

theorem validModelSolution_spec (data : VIPublicData E)
    (a : ValidModelParameter data) :
    SolvesModelVI data.X (exactJetModel data.p data.Lp a.1.1.1 a.1.2)
      (validModelSolution data a) :=
  (Classical.choose_spec (validModel_existsUnique data a)).1

theorem continuous_validModelSolution (data : VIPublicData E) :
    Continuous (validModelSolution data) := by
  let M : ValidModelParameter data → E → E := fun a ↦
    exactJetModel data.p data.Lp a.1.1.1 a.1.2
  have hM : Continuous (fun q : ValidModelParameter data × E ↦ M q.1 q.2) := by
    exact (continuous_exactJetModel_parameter data).comp
      ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
  exact continuous_unique_vi_solution data.X data.X_compact M hM
    (validModelSolution data) (validModelSolution_spec data)
    (fun a y hy ↦ (validModel_existsUnique data a).unique hy
      (validModelSolution_spec data a))

def validModelParameterSet (data : VIPublicData E) :
    Set (AmbientModelParameter data) :=
  {a | IsValidModelParameter data a}

noncomputable def ambientModelExtension (data : VIPublicData E) :
    C(AmbientModelParameter data, E) := by
  let f : C(ValidModelParameter data, E) :=
    ⟨validModelSolution data, continuous_validModelSolution data⟩
  exact Classical.choose
    (ContinuousMap.exists_restrict_eq (isClosed_validModelParameter data) f)

theorem ambientModelExtension_eq (data : VIPublicData E)
    (a : ValidModelParameter data) :
    ambientModelExtension data a.1 = validModelSolution data a := by
  let f : C(ValidModelParameter data, E) :=
    ⟨validModelSolution data, continuous_validModelSolution data⟩
  have h := Classical.choose_spec
    (ContinuousMap.exists_restrict_eq (isClosed_validModelParameter data) f)
  exact DFunLike.congr_fun h a

private theorem compactConvexProjection_eq_self
    (data : VIPublicData E) {x : E} (hx : x ∈ data.X) :
    compactConvexProjection data.X data.X_nonempty data.X_compact
      data.X_convex x = x := by
  let y := compactConvexProjection data.X data.X_nonempty data.X_compact
    data.X_convex x
  have hvar := compactConvexProjection_variational data.X data.X_nonempty
    data.X_compact data.X_convex x x hx
  change inner ℝ (x - y) (x - y) ≤ 0 at hvar
  rw [real_inner_self_eq_norm_sq] at hvar
  have hnorm : ‖x - y‖ = 0 := by nlinarith [norm_nonneg (x - y)]
  have hzero := norm_eq_zero.mp hnorm
  exact sub_eq_zero.mp hzero |>.symm

noncomputable def ambientModelPoint (data : VIPublicData E)
    (a : AmbientModelParameter data) : E :=
  compactConvexProjection data.X data.X_nonempty data.X_compact data.X_convex
    (ambientModelExtension data a)

theorem ambientModelPoint_mem (data : VIPublicData E)
    (a : AmbientModelParameter data) : ambientModelPoint data a ∈ data.X :=
  compactConvexProjection_mem data.X data.X_nonempty data.X_compact
    data.X_convex _

theorem continuous_ambientModelPoint (data : VIPublicData E) :
    Continuous (ambientModelPoint data) := by
  have hp : LipschitzWith 1 (compactConvexProjection data.X data.X_nonempty
      data.X_compact data.X_convex) := by
    apply LipschitzWith.mk_one
    intro x y
    simpa [dist_eq_norm] using compactConvexProjection_dist_le data.X
      data.X_nonempty data.X_compact data.X_convex x y
  exact hp.continuous.comp (ambientModelExtension data).continuous

theorem ambientModelPoint_eq_valid (data : VIPublicData E)
    (a : ValidModelParameter data) :
    ambientModelPoint data a.1 = validModelSolution data a := by
  rw [ambientModelPoint, ambientModelExtension_eq]
  exact compactConvexProjection_eq_self data (validModelSolution_spec data a).1

noncomputable def borelKnownModelStep (data : VIPublicData E)
    (a : AmbientModelParameter data) : data.X × E :=
  let y := ambientModelPoint data a
  (⟨y, ambientModelPoint_mem data a⟩,
    -exactJetModel data.p data.Lp a.1.1 a.2 y)

theorem continuous_borelKnownModelStep (data : VIPublicData E) :
    Continuous (borelKnownModelStep data) := by
  have hy := continuous_ambientModelPoint data
  have hmodel : Continuous (fun a : AmbientModelParameter data ↦
      exactJetModel data.p data.Lp a.1.1 a.2 (ambientModelPoint data a)) := by
    exact (continuous_exactJetModel_parameter data).comp
      (continuous_id.prodMk hy)
  exact (hy.subtype_mk _).prodMk hmodel.neg

theorem borelKnownModelStep_valid_spec (data : VIPublicData E)
    (a : ValidModelParameter data) :
    IsKnownModelStep data a.1.1 a.1.2 (borelKnownModelStep data a.1) := by
  have hsol := validModelSolution_spec data a
  have hpoint := ambientModelPoint_eq_valid data a
  constructor
  · intro z hz
    dsimp [borelKnownModelStep]
    rw [hpoint, inner_neg_left]
    exact neg_nonpos.mpr (hsol.2 z hz)
  · dsimp [borelKnownModelStep]
    rw [hpoint, ← exactJetModel_eq_knownModel data a.1.1.1 a.1.2]
    abel

theorem borelKnownModelStep_genuine_spec (data : VIPublicData E) (G : E → E)
    (hG : IsAdmissibleOperator data G)
    (oracle : FeasibleExactSymmetricJetOracle data G) (center : data.X) :
    IsKnownModelStep data center (oracle.answer center)
      (borelKnownModelStep data (center, oracle.answer center)) := by
  exact borelKnownModelStep_valid_spec data
    ⟨(center, oracle.answer center), genuineJet_validModelParameter data G hG oracle center⟩

section Measurable

variable [MeasurableSpace E] [BorelSpace E]

/-- Canonical norm-Borel structure used by upper-program policies.  It is
named rather than installed globally so existing componentwise lower-bound
measurability proofs retain their product sigma algebra. -/
@[reducible] noncomputable def upperFeasibleBorelMeasurableSpace
    (data : VIPublicData E) : MeasurableSpace data.X :=
  @Subtype.instMeasurableSpace E (fun x => x ∈ data.X) (borel E)

@[reducible] noncomputable def upperJetBorelMeasurableSpace (p : ℕ) :
    MeasurableSpace (SymmetricExactJet E p) := borel _

local instance upperJetMeasurableSpace (p : ℕ) :
    MeasurableSpace (SymmetricExactJet E p) :=
  upperJetBorelMeasurableSpace p

local instance upperJetBorelSpace (p : ℕ) :
    BorelSpace (SymmetricExactJet E p) := ⟨rfl⟩

theorem measurable_borelKnownModelStep (data : VIPublicData E) :
    Measurable (borelKnownModelStep data) :=
  (continuous_borelKnownModelStep data).measurable

theorem measurable_borelKnownModelStep_fixedCenter
    (data : VIPublicData E) (center : data.X) :
    Measurable (fun jet : SymmetricExactJet E data.p ↦
      borelKnownModelStep data (center, jet)) := by
  exact (measurable_borelKnownModelStep data).comp
    (measurable_const.prodMk measurable_id)

theorem measurable_borelKnownModelPoint_fixedCenter
    (data : VIPublicData E) (center : data.X) :
    Measurable (fun jet : SymmetricExactJet E data.p ↦
      (borelKnownModelStep data (center, jet)).1) :=
  measurable_fst.comp (measurable_borelKnownModelStep_fixedCenter data center)

end Measurable

end
end LeanArticleAudit.Pilot
