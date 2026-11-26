import Bilevel.CachedAnchorProcedure
import Bilevel.CachedTiltError

/-! Canonical anchor certificates for the actually stored refresh output. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace Bilevel.CachedAnchorProcedure
open Stateful PrimitiveGeometry

variable {X Y : Type*}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
  {μ Lf Lg Cf ρ : ℝ}
  (P : Model.Primitive (X := X) (Y := Y) μ Lf Lg Cf ρ) [FiniteDimensional ℝ Y]

def Certificate (x : X) (rA η : ℝ) (z : Stored X Y) : Prop :=
  ‖z.1-P.canonicalResponse.y x‖ ≤ rA ∧
  ‖z.2.1-P.fx x (P.canonicalResponse.y x)‖ ≤ η+Lf*rA ∧
  ‖z.2.2.1-P.fy x (P.canonicalResponse.y x)‖ ≤ η+Lf*rA ∧
  ‖z.2.2.2-P.fy x (P.canonicalResponse.y x)‖ ≤ η+Lf*rA ∧ ‖z.2.2.2‖ ≤ Cf

theorem store_certificate (x : X) (rA η : ℝ) (z : Raw X Y)
    (hy : ‖z.1-P.canonicalResponse.y x‖ ≤ rA)
    (hu : ‖z.2-pack (P.fx x z.1) (P.fy x z.1)‖ ≤ η) :
    Certificate P x rA η (store Cf z) := by
  have hbx : ‖z.2.fst-P.fx x z.1‖ ≤ η :=
    (WithLp.norm_fst_le X (z.2-pack (P.fx x z.1) (P.fy x z.1))).trans hu
  have hby : ‖z.2.snd-P.fy x z.1‖ ≤ η :=
    (WithLp.norm_snd_le X (z.2-pack (P.fx x z.1) (P.fy x z.1))).trans hu
  have hfx : ‖z.2.fst-P.fx x (P.canonicalResponse.y x)‖ ≤ η+Lf*rA := by
    calc
      _ ≤ ‖z.2.fst-P.fx x z.1‖ + ‖P.fx x z.1-P.fx x (P.canonicalResponse.y x)‖ := by
        simpa only [dist_eq_norm] using dist_triangle z.2.fst (P.fx x z.1) (P.fx x (P.canonicalResponse.y x))
      _ ≤ η+Lf*rA := add_le_add hbx
        ((P.fx_lipschitz_y x z.1 _).trans (mul_le_mul_of_nonneg_left hy P.Lf_nonneg))
  have hfy : ‖z.2.snd-P.fy x (P.canonicalResponse.y x)‖ ≤ η+Lf*rA := by
    calc
      _ ≤ ‖z.2.snd-P.fy x z.1‖ + ‖P.fy x z.1-P.fy x (P.canonicalResponse.y x)‖ := by
        simpa only [dist_eq_norm] using dist_triangle z.2.snd (P.fy x z.1) (P.fy x (P.canonicalResponse.y x))
      _ ≤ η+Lf*rA := add_le_add hby
        ((P.fy_lipschitz_y x z.1 _).trans (mul_le_mul_of_nonneg_left hy P.Lf_nonneg))
  exact ⟨hy,hfx,hfy,
    (Clipping.error_nonincreasing Cf P.Cf_nonneg z.2.snd _ (P.upper_bound x _)).trans hfy,
    store_clipped_bound Cf P.Cf_nonneg z⟩

/-- Transport of a valid anchor certificate to any current point within R. -/
theorem certificate_cached_error (x anchor : X) (rA η R : ℝ) (z : Stored X Y)
    (hz : Certificate P anchor rA η z) (hx : ‖anchor-x‖ ≤ R) :
    ‖z.2.1-P.fx x (P.canonicalResponse.y x)‖ + Lg/μ *
      ‖Clipping.clip Cf z.2.2.1-P.fy x (P.canonicalResponse.y x)‖ ≤
      (1+Lg/μ) * (η+Lf*rA+Lf*(1+Lg/μ)*R) := by
  have hk : 0 ≤ Lg/μ := div_nonneg P.Lg_nonneg P.μ_pos.le
  have he := P.cached_anchor_error P.canonicalResponse x anchor
    (P.canonicalResponse.y anchor) z.2.2.1 z.2.1 hz.2.1 hz.2.2.1
  simp only [sub_self,norm_zero,mul_zero,add_zero] at he
  apply he.trans
  gcongr
  exact mul_nonneg P.Lf_nonneg (by linarith)

theorem canonical_upper_continuous :
    Continuous (fun x => P.fx x (P.canonicalResponse.y x)) ∧
      Continuous (fun x => P.fy x (P.canonicalResponse.y x)) := by
  have hk : 0 ≤ Lf*(1+Lg/μ) := mul_nonneg P.Lf_nonneg
    (by have := div_nonneg P.Lg_nonneg P.μ_pos.le; linarith)
  have hb (x y : X) := P.upper_component_bounds x y
    (P.canonicalResponse.y x) (P.canonicalResponse.y y)
  have hg (x y : X) := mul_le_mul_of_nonneg_left
    (P.response_joint_distance P.canonicalResponse x y) P.Lf_nonneg
  constructor
  · have hl : LipschitzWith ⟨Lf*(1+Lg/μ),hk⟩
        (fun x => P.fx x (P.canonicalResponse.y x)) := by
      apply LipschitzWith.of_dist_le_mul
      intro x y
      simpa only [dist_eq_norm,NNReal.coe_mk,mul_assoc] using (hb x y).1.trans (hg x y)
    exact hl.continuous
  · have hl : LipschitzWith ⟨Lf*(1+Lg/μ),hk⟩
        (fun x => P.fy x (P.canonicalResponse.y x)) := by
      apply LipschitzWith.of_dist_le_mul
      intro x y
      simpa only [dist_eq_norm,NNReal.coe_mk,mul_assoc] using (hb x y).2.trans (hg x y)
    exact hl.continuous

variable {History : Type*} [MeasurableSpace History]
  [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
  [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y]
  [MeasurableSpace (Joint X Y)] [BorelSpace (Joint X Y)] [SecondCountableTopology (Joint X Y)]
  [Nontrivial Y] {σf σg : ℝ}
  (O : HistorySFO (Query := X × Y) (History := History) (X := X) (Y := Y) σf σg)

omit [MeasurableSpace (Joint X Y)] [BorelSpace (Joint X Y)] [SecondCountableTopology (Joint X Y)]
  [Nontrivial Y] [SecondCountableTopology X] [SecondCountableTopology Y] in
theorem certificate_measurable (x : X) (rA η : ℝ) :
    MeasurableSet {z : Stored X Y | Certificate P x rA η z} := by
  unfold Certificate
  apply MeasurableSet.inter
  · exact measurableSet_le (measurable_fst.sub_const _).norm measurable_const
  apply MeasurableSet.inter
  · exact measurableSet_le ((measurable_fst.comp measurable_snd).sub_const _).norm measurable_const
  apply MeasurableSet.inter
  · exact measurableSet_le ((measurable_fst.comp (measurable_snd.comp measurable_snd)).sub_const _).norm measurable_const
  apply MeasurableSet.inter
  · exact measurableSet_le ((measurable_snd.comp (measurable_snd.comp measurable_snd)).sub_const _).norm measurable_const
  · exact measurableSet_le (measurable_snd.comp (measurable_snd.comp measurable_snd)).norm measurable_const

omit [MeasurableSpace (Joint X Y)] [BorelSpace (Joint X Y)] [SecondCountableTopology (Joint X Y)]
  [Nontrivial Y] in
theorem certificate_joint_measurable (rA η : ℝ) :
    MeasurableSet {p : X × Stored X Y | Certificate P p.1 rA η p.2} := by
  have hy : Measurable (fun p : X × Stored X Y => P.canonicalResponse.y p.1) :=
    (P.response_continuous P.canonicalResponse).measurable.comp measurable_fst
  have hfx : Measurable (fun p : X × Stored X Y => P.fx p.1 (P.canonicalResponse.y p.1)) :=
    (canonical_upper_continuous P).1.measurable.comp measurable_fst
  have hfy : Measurable (fun p : X × Stored X Y => P.fy p.1 (P.canonicalResponse.y p.1)) :=
    (canonical_upper_continuous P).2.measurable.comp measurable_fst
  unfold Certificate
  apply MeasurableSet.inter
  · exact measurableSet_le ((measurable_fst.comp measurable_snd).sub hy).norm measurable_const
  apply MeasurableSet.inter
  · exact measurableSet_le ((measurable_fst.comp (measurable_snd.comp measurable_snd)).sub hfx).norm measurable_const
  apply MeasurableSet.inter
  · exact measurableSet_le ((measurable_fst.comp (measurable_snd.comp (measurable_snd.comp measurable_snd))).sub hfy).norm measurable_const
  apply MeasurableSet.inter
  · exact measurableSet_le ((measurable_snd.comp (measurable_snd.comp (measurable_snd.comp measurable_snd))).sub hfy).norm measurable_const
  · exact measurableSet_le (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp measurable_snd))).norm measurable_const

/-- The anchor actually output by refresh has all canonical upper-gradient
and clipped-direction certificates except on a probability at most 2e^-q/8. -/
theorem refresh_certificate_probability
    (hfx : ∀ x y, O.upper.truth_x (x,y) = P.fx x y)
    (hfy : ∀ x y, O.upper.truth_y (x,y) = P.fy x y)
    (hgy : ∀ x y, O.lower.truth_y (x,y) = P.gy x y)
    (D rA η : ℝ) (hr : 0 < rA) (hη : 0 < η) (q : ℕ) [NeZero q]
    (p : Input X Y) (hinit : ‖p.2-P.canonicalResponse.y p.1‖ ≤ D) (h : History) :
    ((refresh O μ Lg Cf D rA η q).law (p,h)).real
      {z | ¬ Certificate P p.1 rA η z.1} ≤ 2 * Real.exp (-(q:ℝ)/8) := by
  have hm : Measurable (fun z : Outcome (Raw X Y) History => (store Cf z.1,z.2)) :=
    ((store_measurable Cf).comp measurable_fst).prodMk measurable_snd
  have hs : MeasurableSet {z : Outcome (Stored X Y) History | ¬ Certificate P p.1 rA η z.1} :=
    ((certificate_measurable P p.1 rA η).preimage measurable_fst).compl
  rw [refresh,Procedure.map_law,measureReal_def,Measure.map_apply hm hs]
  change ((refreshRaw O μ Lg D rA η q).law (p,h)).real
    {z | ¬ Certificate P p.1 rA η (store Cf z.1)} ≤ _
  apply (measureReal_mono (μ := (refreshRaw O μ Lg D rA η q).law (p,h))
    (s₂ := {z : Outcome (Raw X Y) History |
      z.1 ∈ badEvent O p.1 (P.canonicalResponse.y p.1) rA η}) ?_).trans
      (refreshRaw_confidence O P hgy D rA η hr hη q p hinit h)
  intro z hz
  by_contra hb
  have hgood : ‖z.1.1-P.canonicalResponse.y p.1‖ ≤ rA ∧
      ‖z.1.2-O.fullUpper.truth (p.1,z.1.1)‖ ≤ η := by
    simpa only [badEvent,Set.mem_setOf_eq,not_or,not_lt] using hb
  have htruth : O.fullUpper.truth (p.1,z.1.1) = pack (P.fx p.1 z.1.1) (P.fy p.1 z.1.1) := by
    change pack (O.upper.truth_x (p.1,z.1.1)) (O.upper.truth_y (p.1,z.1.1)) = _
    rw [hfx,hfy]
  exact hz (store_certificate P p.1 rA η z.1 hgood.1 (by simpa only [htruth] using hgood.2))

theorem refresh_certificate_probability_of_tail_le
    (hfx : ∀ x y, O.upper.truth_x (x,y) = P.fx x y)
    (hfy : ∀ x y, O.upper.truth_y (x,y) = P.fy x y)
    (hgy : ∀ x y, O.lower.truth_y (x,y) = P.gy x y)
    (D rA η : ℝ) (hr : 0 < rA) (hη : 0 < η) (q : ℕ) [NeZero q]
    (p : Input X Y) (hinit : ‖p.2-P.canonicalResponse.y p.1‖ ≤ D) (h : History)
    (β : ℝ) (hβ : Real.exp (-(q:ℝ)/8) ≤ β) :
    ((refresh O μ Lg Cf D rA η q).law (p,h)).real
      {z | ¬ Certificate P p.1 rA η z.1} ≤ 2 * β :=
  (refresh_certificate_probability P O hfx hfy hgy D rA η hr hη q p hinit h).trans
    (mul_le_mul_of_nonneg_left hβ (by norm_num))

end Bilevel.CachedAnchorProcedure
