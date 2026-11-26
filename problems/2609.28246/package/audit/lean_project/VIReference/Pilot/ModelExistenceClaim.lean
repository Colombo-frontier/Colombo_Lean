import VIReference.Pilot.SymmetricJetModel
import VIReference.Pilot.KnownModelStep

open Set Filter Topology
open scoped RealInnerProductSpace BigOperators

namespace VIReference.Pilot

noncomputable section

universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- The source model, expressed only through a center, a returned symmetric
jet, and the public constants. -/
noncomputable def exactJetModel (p : ℕ) (Lp : ℝ) (center : E)
    (jet : SymmetricExactJet E p) (z : E) : E :=
  symmetricJetTaylor p center jet z +
    (2 * (Lp / (Nat.factorial (p - 1) : ℝ))) •
      radialPower (p - 1) (z - center)

theorem exactJetModel_eq_stabilizedModel (p : ℕ) (Lp : ℝ) (center : E)
    (jet : SymmetricExactJet E p) :
    exactJetModel p Lp center jet =
      stabilizedModel (p - 1) (Lp / (Nat.factorial (p - 1) : ℝ)) center
        (symmetricJetTaylor p center jet) := by
  funext z
  simp [exactJetModel, stabilizedModel]

private theorem locallyLipschitz_norm_pow (q : ℕ) :
    LocallyLipschitz (fun z : E ↦ ‖z‖ ^ q) := by
  have hpow : LocallyLipschitz (fun r : ℝ ↦ r ^ q) := by
    have hcd : ContDiff ℝ 1 (fun r : ℝ ↦ r ^ q) := by fun_prop
    exact hcd.locallyLipschitz
  exact hpow.comp (lipschitzWith_one_norm (E := E)).locallyLipschitz

theorem radialPower_locallyLipschitz (q : ℕ) :
    LocallyLipschitz (radialPower (E := E) q) := by
  change LocallyLipschitz (fun z : E ↦ ‖z‖ ^ q • z)
  have hsmul : LocallyLipschitz (fun z : ℝ × E ↦ z.1 • z.2) := by
    have hcd : ContDiff ℝ 1 (fun z : ℝ × E ↦ z.1 • z.2) := by fun_prop
    exact hcd.locallyLipschitz
  have hp := locallyLipschitz_norm_pow (E := E) q
  convert hsmul.comp (hp.prodMk LocallyLipschitz.id) using 1 <;> rfl

theorem centeredRadialPower_locallyLipschitz (q : ℕ) (center : E) :
    LocallyLipschitz (fun z : E ↦ radialPower q (z - center)) := by
  exact (radialPower_locallyLipschitz (E := E) q).comp
    (LocallyLipschitz.id.sub (LocallyLipschitz.const center))

theorem symmetricJetTaylor_contDiff_one (p : ℕ) (center : E)
    (jet : SymmetricExactJet E p) :
    ContDiff ℝ 1 (symmetricJetTaylor p center jet) := by
  unfold symmetricJetTaylor
  apply ContDiff.sum
  intro j hj
  let A : E [×j.1]→L[ℝ] E := (jet j).1
  change ContDiff ℝ 1 (fun z : E ↦
    (Nat.factorial j.1 : ℝ)⁻¹ • A (fun _ ↦ z - center))
  have hA : ContDiff ℝ 1 (A : (Fin j.1 → E) → E) := A.contDiff
  have hdiag : ContDiff ℝ 1 (fun z : E ↦ (fun _ : Fin j.1 ↦ z - center)) := by
    fun_prop
  exact (hA.comp hdiag).const_smul _

theorem exactJetModel_locallyLipschitz (p : ℕ) (Lp : ℝ) (center : E)
    (jet : SymmetricExactJet E p) :
    LocallyLipschitz (exactJetModel p Lp center jet) := by
  change LocallyLipschitz (fun z : E ↦ symmetricJetTaylor p center jet z +
    (2 * (Lp / (Nat.factorial (p - 1) : ℝ))) •
      radialPower (p - 1) (z - center))
  have ht := (symmetricJetTaylor_contDiff_one p center jet).locallyLipschitz
  have hr := centeredRadialPower_locallyLipschitz (E := E) (p - 1) center
  have hscale : LocallyLipschitz
      (fun z : E ↦ (2 * (Lp / (Nat.factorial (p - 1) : ℝ))) •
        radialPower (p - 1) (z - center)) := by
    have hlin : LocallyLipschitz (fun z : E ↦
        (2 * (Lp / (Nat.factorial (p - 1) : ℝ))) • z) := by
      have hcd : ContDiff ℝ 1 (fun z : E ↦
          (2 * (Lp / (Nat.factorial (p - 1) : ℝ))) • z) := by fun_prop
      exact hcd.locallyLipschitz
    exact hlin.comp hr
  exact ht.add hscale

theorem exactJetModel_continuous (p : ℕ) (Lp : ℝ) (center : E)
    (jet : SymmetricExactJet E p) : Continuous (exactJetModel p Lp center jet) :=
  (exactJetModel_locallyLipschitz p Lp center jet).continuous

private theorem norm_sub_center_le_max_of_mem_segment (center u v z : E)
    (hz : z ∈ segment ℝ u v) :
    ‖z - center‖ ≤ max ‖u - center‖ ‖v - center‖ := by
  rw [segment_eq_image'] at hz
  obtain ⟨t, ht, rfl⟩ := hz
  have ht0 : 0 ≤ t := ht.1
  have ht1 : t ≤ 1 := ht.2
  have heq : u + t • (v - u) - center =
      (1 - t) • (u - center) + t • (v - center) := by module
  rw [heq]
  calc
    ‖(1 - t) • (u - center) + t • (v - center)‖ ≤
        ‖(1 - t) • (u - center)‖ + ‖t • (v - center)‖ := norm_add_le _ _
    _ = (1 - t) * ‖u - center‖ + t * ‖v - center‖ := by
      simp [norm_smul, abs_of_nonneg ht0, abs_of_nonneg (sub_nonneg.mpr ht1)]
    _ ≤ (1 - t) * max ‖u - center‖ ‖v - center‖ +
        t * max ‖u - center‖ ‖v - center‖ := by
      gcongr <;> simp
    _ = max ‖u - center‖ ‖v - center‖ := by ring

/-- Exact derivative remainder for a Taylor polynomial reconstructed from a
genuine feasible symmetric oracle answer. -/
theorem genuineJet_fderiv_model_close (data : VIPublicData E) (G : E → E)
    (hG : IsAdmissibleOperator data G)
    (oracle : FeasibleExactSymmetricJetOracle data G) (center : data.X)
    {z : E} (hz : z ∈ data.X) :
    ‖fderiv ℝ G z - fderiv ℝ
        (symmetricJetTaylor data.p center.1 (oracle.answer center)) z‖ ≤
      data.Lp / (Nat.factorial (data.p - 1) : ℝ) *
        ‖z - center.1‖ ^ (data.p - 1) := by
  obtain ⟨U, hU, hXU, hreg⟩ := hG.regularity
  have ht := (taylorRemainderClaim_proof data.p data.Lp data.X U G
    data.p_ge_two data.Lp_pos.le hU hXU data.X_convex hreg
    hG.top_derivative_lipschitz center center.2 z hz).2
  rw [symmetricJetTaylor_eq_taylorModel data.p G center.1
    (oracle.answer center) (oracle.exact center)]
  rw [fderiv_taylorModel_eq_taylorModelDerivative_of_exactSymmetricJet'
    data.p (le_trans (by omega : 1 ≤ 2) data.p_ge_two) G center.1
      (oracle.answer center) (oracle.exact center) z]
  exact ht

theorem genuineJetModel_strictMonotone (data : VIPublicData E) (G : E → E)
    (hG : IsAdmissibleOperator data G)
    (oracle : FeasibleExactSymmetricJetOracle data G) (center : data.X)
    {u v : E} (hu : u ∈ data.X) (hv : v ∈ data.X) (huv : u ≠ v) :
    0 < inner ℝ
      (exactJetModel data.p data.Lp center.1 (oracle.answer center) u -
        exactJetModel data.p data.Lp center.1 (oracle.answer center) v) (u - v) := by
  let C : ℝ := data.Lp / (Nat.factorial (data.p - 1) : ℝ)
  have hC : 0 < C := div_pos data.Lp_pos (by positivity)
  let T := symmetricJetTaylor data.p center.1 (oracle.answer center)
  have hT : -(C * max (‖u - center.1‖ ^ (data.p - 1))
        (‖v - center.1‖ ^ (data.p - 1))) * ‖u - v‖ ^ 2 ≤
      inner ℝ (T u - T v) (u - v) := by
    have hbase := inner_sub_lower_of_fderiv_close G T u v
      (C * max (‖u - center.1‖ ^ (data.p - 1))
        (‖v - center.1‖ ^ (data.p - 1)))
    apply hbase
    · exact hG.monotone_on u hu v hv
    · intro z hz
      obtain ⟨U, hU, hXU, hreg⟩ := hG.regularity
      have hcd := hreg.contDiffAt (hU.mem_nhds (hXU
        (data.X_convex.segment_subset hu hv hz)))
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
      have hnorm := norm_sub_center_le_max_of_mem_segment center.1 u v z hz
      have hpow : ‖z - center.1‖ ^ (data.p - 1) ≤
          max (‖u - center.1‖ ^ (data.p - 1))
            (‖v - center.1‖ ^ (data.p - 1)) := by
        calc
          ‖z - center.1‖ ^ (data.p - 1) ≤
              (max ‖u - center.1‖ ‖v - center.1‖) ^ (data.p - 1) :=
            pow_le_pow_left₀ (norm_nonneg _) hnorm _
          _ = max (‖u - center.1‖ ^ (data.p - 1))
              (‖v - center.1‖ ^ (data.p - 1)) := by
            rcases le_total ‖u - center.1‖ ‖v - center.1‖ with huvnorm | hvunorm
            · rw [max_eq_right huvnorm, max_eq_right
                (pow_le_pow_left₀ (norm_nonneg _) huvnorm _)]
            · rw [max_eq_left hvunorm, max_eq_left
                (pow_le_pow_left₀ (norm_nonneg _) hvunorm _)]
      exact hrem.trans (mul_le_mul_of_nonneg_left hpow hC.le)
  rw [exactJetModel_eq_stabilizedModel]
  have hT' : -C * max (‖u - center.1‖ ^ (data.p - 1))
        (‖v - center.1‖ ^ (data.p - 1)) * ‖u - v‖ ^ 2 ≤
      inner ℝ (T u - T v) (u - v) := by
    convert hT using 1 <;> ring
  exact stabilizedModel_strictMonotone_of_taylor_lower
    (data.p - 1) C hC center.1 T huv hT'

theorem genuineJetModel_monotone (data : VIPublicData E) (G : E → E)
    (hG : IsAdmissibleOperator data G)
    (oracle : FeasibleExactSymmetricJetOracle data G) (center : data.X)
    {u v : E} (hu : u ∈ data.X) (hv : v ∈ data.X) :
    0 ≤ inner ℝ
      (exactJetModel data.p data.Lp center.1 (oracle.answer center) u -
        exactJetModel data.p data.Lp center.1 (oracle.answer center) v) (u - v) := by
  by_cases huv : u = v
  · subst v
    simp
  · exact (genuineJetModel_strictMonotone data G hG oracle center hu hv huv).le

/-- The genuine known model has exactly one VI solution on the public compact
convex domain. -/
theorem genuineJetModel_existsUnique (data : VIPublicData E) (G : E → E)
    (hG : IsAdmissibleOperator data G)
    (oracle : FeasibleExactSymmetricJetOracle data G) (center : data.X) :
    ∃! y : E, SolvesModelVI data.X
      (exactJetModel data.p data.Lp center.1 (oracle.answer center)) y := by
  let M := exactJetModel data.p data.Lp center.1 (oracle.answer center)
  obtain ⟨y, hy⟩ := continuous_monotone_vi_exists data.X data.X_nonempty
    data.X_compact data.X_convex M
    (exactJetModel_continuous data.p data.Lp center.1
      (oracle.answer center)).continuousOn
    (exactJetModel_locallyLipschitz data.p data.Lp center.1
      (oracle.answer center)).locallyLipschitzOn
    (fun u hu v hv ↦ genuineJetModel_monotone data G hG oracle center hu hv)
  refine ⟨y, hy, ?_⟩
  intro z hz
  exact solvesModelVI_unique
    (fun u hu v hv huv ↦
      genuineJetModel_strictMonotone data G hG oracle center hu hv huv) hz hy

private theorem source_beta_eq (p : ℕ) (hp : 1 ≤ p) (Lp : ℝ) :
    tensorBetaCoefficient p * Lp =
      2 * (Lp / (Nat.factorial (p - 1) : ℝ)) := by
  obtain ⟨q, rfl⟩ : ∃ q : ℕ, p = q + 1 := ⟨p - 1, by omega⟩
  unfold tensorBetaCoefficient
  rw [Nat.factorial_succ]
  push_cast
  field_simp

theorem exactJetModel_eq_knownModel (data : VIPublicData E) (center : E)
    (jet : SymmetricExactJet E data.p) (z : E) :
    exactJetModel data.p data.Lp center jet z =
      taylorModelFromJet data center jet z +
        (tensorBetaCoefficient data.p * data.Lp * ‖z - center‖ ^ (data.p - 1)) •
          (z - center) := by
  rw [exactJetModel, symmetricJetTaylor, taylorModelFromJet, radialPower]
  rw [source_beta_eq data.p
    (le_trans (by omega : 1 ≤ 2) data.p_ge_two) data.Lp]
  module

/-- A solution of the genuine model VI produces the exact normal and displayed
model identity used by the executable known-model operation. -/
theorem genuineJetModel_exists_knownPair (data : VIPublicData E) (G : E → E)
    (hG : IsAdmissibleOperator data G)
    (oracle : FeasibleExactSymmetricJetOracle data G) (center : data.X) :
    ∃ yn : data.X × E, IsKnownModelStep data center (oracle.answer center) yn := by
  obtain ⟨y, hy, _⟩ := genuineJetModel_existsUnique data G hG oracle center
  let n : E := -exactJetModel data.p data.Lp center.1 (oracle.answer center) y
  refine ⟨(⟨y, hy.1⟩, n), ?_, ?_⟩
  · intro z hz
    dsimp [n]
    rw [inner_neg_left]
    exact neg_nonpos.mpr (hy.2 z hz)
  · dsimp [n]
    rw [← exactJetModel_eq_knownModel data center.1 (oracle.answer center) y]
    abel

private theorem solvesModelVI_parameter_limit
    {P : Type*} [TopologicalSpace P]
    (X : Set E) (hcpt : IsCompact X) (M : P → E → E)
    (hM : Continuous (fun q : P × E ↦ M q.1 q.2))
    {a : ℕ → P} {a₀ : P} {y : ℕ → E} {y₀ : E}
    (ha : Tendsto a atTop (𝓝 a₀)) (hy : Tendsto y atTop (𝓝 y₀))
    (hsolve : ∀ n, SolvesModelVI X (M (a n)) (y n)) :
    SolvesModelVI X (M a₀) y₀ := by
  have hyX : y₀ ∈ X := hcpt.isClosed.mem_of_tendsto hy
    (Eventually.of_forall fun n ↦ (hsolve n).1)
  refine ⟨hyX, ?_⟩
  intro z hz
  have harg : Tendsto (fun n ↦ (a n, y n)) atTop (𝓝 (a₀, y₀)) :=
    ha.prodMk_nhds hy
  have hMy : Tendsto (fun n ↦ M (a n) (y n)) atTop (𝓝 (M a₀ y₀)) :=
    hM.continuousAt.tendsto.comp harg
  have hi : Tendsto (fun n ↦ inner ℝ (M (a n) (y n)) (z - y n)) atTop
      (𝓝 (inner ℝ (M a₀ y₀) (z - y₀))) :=
    Filter.Tendsto.inner hMy (tendsto_const_nhds.sub hy)
  exact ge_of_tendsto' hi fun n ↦ (hsolve n).2 z hz

/-- A reusable closed-graph/compactness principle: a jointly continuous VI
operator with a unique selected solution on a compact domain has continuous
solution selection. -/
theorem continuous_unique_vi_solution
    {P : Type*} [TopologicalSpace P] [SequentialSpace P]
    (X : Set E) (hcpt : IsCompact X) (M : P → E → E)
    (hM : Continuous (fun q : P × E ↦ M q.1 q.2))
    (sol : P → E)
    (hsol : ∀ a, SolvesModelVI X (M a) (sol a))
    (hunique : ∀ a y, SolvesModelVI X (M a) y → y = sol a) :
    Continuous sol := by
  rw [continuous_iff_seqContinuous]
  intro a a₀ ha
  rw [Metric.tendsto_atTop]
  intro ε hε
  by_contra hbad
  push Not at hbad
  let K : Set E := X ∩ {y | ε ≤ dist y (sol a₀)}
  have hKcompact : IsCompact K := hcpt.inter_right
    (isClosed_le continuous_const (continuous_id.dist continuous_const))
  have hfreq : ∃ᶠ n in atTop, sol (a n) ∈ K := by
    rw [Filter.frequently_atTop]
    intro N
    obtain ⟨n, hn, hdist⟩ := hbad N
    exact ⟨n, hn, (hsol (a n)).1, hdist⟩
  obtain ⟨y, hyK, φ, hφ, hφy⟩ := hKcompact.tendsto_subseq' hfreq
  have hφa : Tendsto (fun n ↦ a (φ n)) atTop (𝓝 a₀) :=
    ha.comp hφ.tendsto_atTop
  have hylim : SolvesModelVI X (M a₀) y :=
    solvesModelVI_parameter_limit X hcpt M hM hφa hφy
      (fun n ↦ hsol (a (φ n)))
  have hyEq : y = sol a₀ := hunique a₀ y hylim
  have hdist : ε ≤ dist y (sol a₀) := hyK.2
  rw [hyEq, dist_self] at hdist
  linarith

/-- A center--jet pair is admissible when it is the actual returned answer of
some feasible exact oracle for an admissible operator.  No model solution is
stored in this predicate. -/
def IsAdmissibleCenterJet (data : VIPublicData E)
    (a : data.X × SymmetricExactJet E data.p) : Prop :=
  ∃ (G : E → E) (oracle : FeasibleExactSymmetricJetOracle data G),
    IsAdmissibleOperator data G ∧ oracle.answer a.1 = a.2

abbrev AdmissibleCenterJet (data : VIPublicData E) :=
  {a : data.X × SymmetricExactJet E data.p // IsAdmissibleCenterJet data a}

theorem admissibleCenterJet_existsUnique (data : VIPublicData E)
    (a : AdmissibleCenterJet data) :
    ∃! y : E, SolvesModelVI data.X
      (exactJetModel data.p data.Lp a.1.1.1 a.1.2) y := by
  obtain ⟨G, oracle, hG, heq⟩ := a.2
  rw [← heq]
  exact genuineJetModel_existsUnique data G hG oracle a.1.1

/-- Analysis-level unique model solution on the admissible parameter
subspace. -/
noncomputable def admissibleModelSolution (data : VIPublicData E)
    (a : AdmissibleCenterJet data) : E :=
  Classical.choose (admissibleCenterJet_existsUnique data a)

theorem admissibleModelSolution_spec (data : VIPublicData E)
    (a : AdmissibleCenterJet data) :
    SolvesModelVI data.X (exactJetModel data.p data.Lp a.1.1.1 a.1.2)
      (admissibleModelSolution data a) :=
  (Classical.choose_spec (admissibleCenterJet_existsUnique data a)).1

theorem admissibleModelSolution_unique (data : VIPublicData E)
    (a : AdmissibleCenterJet data) {y : E}
    (hy : SolvesModelVI data.X
      (exactJetModel data.p data.Lp a.1.1.1 a.1.2) y) :
    y = admissibleModelSolution data a :=
  (admissibleCenterJet_existsUnique data a).unique hy
    (admissibleModelSolution_spec data a)

theorem continuous_exactJetModel_parameter (data : VIPublicData E) :
    Continuous (fun a : (data.X × SymmetricExactJet E data.p) × E ↦
      exactJetModel data.p data.Lp a.1.1.1 a.1.2 a.2) := by
  unfold exactJetModel symmetricJetTaylor radialPower
  fun_prop

/-- The unique model solution depends continuously on the center and all
returned tensor coefficients along the admissible center--jet subspace. -/
theorem continuous_admissibleModelSolution (data : VIPublicData E) :
    Continuous (admissibleModelSolution data) := by
  let M : AdmissibleCenterJet data → E → E := fun a ↦
    exactJetModel data.p data.Lp a.1.1.1 a.1.2
  have hM : Continuous (fun q : AdmissibleCenterJet data × E ↦ M q.1 q.2) := by
    exact (continuous_exactJetModel_parameter data).comp
      ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
  exact continuous_unique_vi_solution data.X data.X_compact M hM
    (admissibleModelSolution data) (admissibleModelSolution_spec data)
    (fun a y hy ↦ admissibleModelSolution_unique data a hy)

/-- Analytic core of `lem:model-existence`: every genuine queried model has
exactly one VI solution and the solution varies continuously on the
admissible center--coefficient subspace.  The ambient total measurable
selector is constructed in `ModelMeasurableSelector`. -/
def ModelExistenceClaim (data : VIPublicData E) : Prop :=
  (∀ (G : E → E) (hG : IsAdmissibleOperator data G)
      (oracle : FeasibleExactSymmetricJetOracle data G) (center : data.X),
    ∃! y : E, SolvesModelVI data.X
      (exactJetModel data.p data.Lp center.1 (oracle.answer center)) y) ∧
  Continuous (admissibleModelSolution data)

theorem modelExistenceClaim_proof (data : VIPublicData E) :
    ModelExistenceClaim data := by
  refine ⟨?_, continuous_admissibleModelSolution data⟩
  · intro G hG oracle center
    exact genuineJetModel_existsUnique data G hG oracle center

end
end VIReference.Pilot
