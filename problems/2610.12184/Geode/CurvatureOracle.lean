import Geode.CurvatureScaling
import Geode.OracleConjugacy
import Geode.PartialMain

/-! Exact oracle and minimax equivalence for the rescaled hyperboloid.
The physical model uses partial decision rules, so internal divergence is
included. Complete selected vectors and the entire ordered history are mapped. -/
namespace Geode.Rescaled

open Geode.OracleReplay
open scoped ENNReal

variable {k : ℝ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Fact (0 < k)]

abbrev FirstOrderAlgorithm (k : ℝ) (E : Type*) [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] := PartialStoppingAlgorithm (Point k E) (Reply E)

noncomputable def normalizeAlgorithm (A : FirstOrderAlgorithm k E) :
    Lorentz.PartialFirstOrderAlgorithm E :=
  conjugatePartialAlgorithm pointEquiv (replyEquiv (k := k)) A

noncomputable def physicalAlgorithm (A : Lorentz.PartialFirstOrderAlgorithm E) :
    FirstOrderAlgorithm k E :=
  conjugatePartialAlgorithm pointEquiv.symm (replyEquiv (k := k)).symm A

def physicalFunction (f : Lorentz.Point E → ℝ) : Point k E → ℝ := fun x => f x.normalized

noncomputable def physicalOracle (O : Lorentz.Point E → Lorentz.FirstOrderReply E) :
    Point k E → Reply E := fun x => (replyEquiv (k := k)).symm (O x.normalized)

@[simp] theorem normalize_physicalFunction (f : Lorentz.Point E → ℝ) :
    normalizeFunction (physicalFunction (k := k) f) = f := rfl

@[simp] theorem physical_normalizeFunction (f : Point k E → ℝ) :
    physicalFunction (normalizeFunction f) = f := rfl

@[simp] theorem normalize_physicalOracle (O : Lorentz.Point E → Lorentz.FirstOrderReply E) :
    normalizeOracle (physicalOracle (k := k) O) = O := by
  funext x
  exact (replyEquiv (k := k)).apply_symm_apply (O x)

@[simp] theorem physical_normalizeOracle (O : Point k E → Reply E) :
    physicalOracle (normalizeOracle O) = O := by
  funext x
  exact (replyEquiv (k := k)).symm_apply_apply (O x)

theorem normalize_run (A : FirstOrderAlgorithm k E) (O : Point k E → Reply E)
    (N : ℕ) (h : History (Point k E) (Reply E)) :
    partialRun (normalizeAlgorithm A) (fixedResponder (normalizeOracle O)) N
      (historyEquiv pointEquiv (replyEquiv (k := k)) h) =
      partialResultEquiv pointEquiv (replyEquiv (k := k)) (partialRun A (fixedResponder O) N h) :=
  partialRun_conjugate pointEquiv (replyEquiv (k := k)) A O N h

def Guarantees (o : Point k E) (r L ε : ℝ) (N : ℕ) (A : FirstOrderAlgorithm k E) : Prop :=
  ∀ f : Point k E → ℝ, AdmissibleObjective o r L f →
    ∀ O : Point k E → Reply E, LegalOracle f O →
      ∃ history output, partialRun A (fixedResponder O) N [] = .finished history output ∧
        ∀ p : Point k E, (∀ y, f p ≤ f y) → f output - f p ≤ ε * L * r

theorem Guarantees.normalize {o : Point k E} {r L ε : ℝ} {N : ℕ}
    {A : FirstOrderAlgorithm k E} (hA : Guarantees o r L ε N A) :
    Lorentz.PartialGuarantees o.normalized (k * r) (L / k) ε N (normalizeAlgorithm A) := by
  intro f hf O hO
  have hfp : AdmissibleObjective o r L (physicalFunction f) := (admissible_iff _ _ _ _).mpr hf
  have hOp : LegalOracle (physicalFunction (k := k) f) (physicalOracle O) :=
    (legalOracle_iff _ _).mpr (by simpa only [normalize_physicalFunction, normalize_physicalOracle] using hO)
  obtain ⟨h, x, hrun, hgap⟩ := hA _ hfp _ hOp
  refine ⟨historyEquiv pointEquiv (replyEquiv (k := k)) h, x.normalized, ?_, ?_⟩
  · have hh := conjugate_partial_finished pointEquiv (replyEquiv (k := k)) A
      (physicalOracle O) N [] h x hrun
    change partialRun (normalizeAlgorithm A) (fixedResponder (normalizeOracle (physicalOracle O))) N [] = _ at hh
    simpa only [normalize_physicalOracle] using hh
  · intro p hp
    simpa only [physicalFunction, tolerance_identity] using hgap ⟨p⟩ (fun y => hp y.normalized)

theorem guarantees_physical {o : Point k E} {r L ε : ℝ} {N : ℕ}
    {A : Lorentz.PartialFirstOrderAlgorithm E}
    (hA : Lorentz.PartialGuarantees o.normalized (k * r) (L / k) ε N A) :
    Guarantees o r L ε N (physicalAlgorithm A) := by
  intro f hf O hO
  obtain ⟨h, x, hrun, hgap⟩ := hA _ ((admissible_iff _ _ _ _).mp hf)
    _ ((legalOracle_iff _ _).mp hO)
  refine ⟨historyEquiv pointEquiv.symm (replyEquiv (k := k)).symm h, ⟨x⟩, ?_, ?_⟩
  · have hh := conjugate_partial_finished (pointEquiv (k := k)).symm (replyEquiv (k := k)).symm A
      (normalizeOracle O) N [] h x hrun
    change partialRun (physicalAlgorithm A) (fixedResponder (physicalOracle (normalizeOracle O))) N [] = _ at hh
    simpa only [physical_normalizeOracle] using hh
  · intro p hp
    simpa only [normalizeFunction, tolerance_identity] using hgap p.normalized (fun y => hp ⟨y⟩)

def FeasibleBudget (o : Point k E) (r L ε : ℝ) (N : ℕ) : Prop :=
  ∃ A : FirstOrderAlgorithm k E, Guarantees o r L ε N A

theorem feasibleBudget_iff (o : Point k E) (r L ε : ℝ) (N : ℕ) :
    FeasibleBudget o r L ε N ↔ Lorentz.PartialFeasibleBudget o.normalized (k * r) (L / k) ε N := by
  constructor
  · rintro ⟨A, hA⟩
    exact ⟨normalizeAlgorithm A, hA.normalize⟩
  · rintro ⟨A, hA⟩
    exact ⟨physicalAlgorithm A, guarantees_physical hA⟩

noncomputable def queryComplexity (o : Point k E) (r L ε : ℝ) : ℝ≥0∞ :=
  ⨅ (N : ℕ) (_ : FeasibleBudget o r L ε N), (N : ℝ≥0∞)

theorem queryComplexity_eq (o : Point k E) (r L ε : ℝ) :
    queryComplexity o r L ε = Lorentz.queryComplexity o.normalized (k * r) (L / k) ε := by
  rw [← Lorentz.partialQueryComplexity_eq]
  simp only [queryComplexity, Lorentz.partialQueryComplexity, feasibleBudget_iff]

noncomputable def uniformComplexity (r L ε : ℝ) : ℝ≥0∞ :=
  ⨆ (d : ℕ) (_ : 2 ≤ d), queryComplexity
    (⟨Lorentz.origin⟩ : Point k (EuclideanSpace ℝ (Fin d))) r L ε

theorem uniformComplexity_eq (r L ε : ℝ) :
    uniformComplexity (k := k) r L ε = Lorentz.uniformComplexity (k * r) (L / k) ε := by
  simp only [uniformComplexity, Lorentz.uniformComplexity, Lorentz.dimensionComplexity,
    queryComplexity_eq]

def StrictGuarantees (o : Point k E) (r L ε : ℝ) (N : ℕ)
    (A : FirstOrderAlgorithm k E) : Prop :=
  ∀ f : Point k E → ℝ, StrictAdmissibleObjective o r L f →
    ∀ O : Point k E → Reply E, LegalOracle f O →
      ∃ history output, partialRun A (fixedResponder O) N [] = .finished history output ∧
        ∀ p : Point k E, (∀ y, f p ≤ f y) → f output - f p ≤ ε * L * r

theorem StrictGuarantees.normalize {o : Point k E} {r L ε : ℝ} {N : ℕ}
    {A : FirstOrderAlgorithm k E} (hA : StrictGuarantees o r L ε N A) :
    Lorentz.PartialStrictGuarantees o.normalized (k * r) (L / k) ε N (normalizeAlgorithm A) := by
  intro f hf O hO
  have hfp : StrictAdmissibleObjective o r L (physicalFunction f) := (strict_admissible_iff _ _ _ _).mpr hf
  have hOp : LegalOracle (physicalFunction (k := k) f) (physicalOracle O) :=
    (legalOracle_iff _ _).mpr (by simpa only [normalize_physicalFunction, normalize_physicalOracle] using hO)
  obtain ⟨h, x, hrun, hgap⟩ := hA _ hfp _ hOp
  refine ⟨historyEquiv pointEquiv (replyEquiv (k := k)) h, x.normalized, ?_, ?_⟩
  · have hh := conjugate_partial_finished pointEquiv (replyEquiv (k := k)) A
      (physicalOracle O) N [] h x hrun
    change partialRun (normalizeAlgorithm A) (fixedResponder (normalizeOracle (physicalOracle O))) N [] = _ at hh
    simpa only [normalize_physicalOracle] using hh
  · intro p hp
    simpa only [physicalFunction, tolerance_identity] using hgap ⟨p⟩ (fun y => hp y.normalized)

theorem strictGuarantees_physical {o : Point k E} {r L ε : ℝ} {N : ℕ}
    {A : Lorentz.PartialFirstOrderAlgorithm E}
    (hA : Lorentz.PartialStrictGuarantees o.normalized (k * r) (L / k) ε N A) :
    StrictGuarantees o r L ε N (physicalAlgorithm A) := by
  intro f hf O hO
  obtain ⟨h, x, hrun, hgap⟩ := hA _ ((strict_admissible_iff _ _ _ _).mp hf)
    _ ((legalOracle_iff _ _).mp hO)
  refine ⟨historyEquiv pointEquiv.symm (replyEquiv (k := k)).symm h, ⟨x⟩, ?_, ?_⟩
  · have hh := conjugate_partial_finished (pointEquiv (k := k)).symm (replyEquiv (k := k)).symm A
      (normalizeOracle O) N [] h x hrun
    change partialRun (physicalAlgorithm A) (fixedResponder (physicalOracle (normalizeOracle O))) N [] = _ at hh
    simpa only [physical_normalizeOracle] using hh
  · intro p hp
    simpa only [normalizeFunction, tolerance_identity] using hgap p.normalized (fun y => hp ⟨y⟩)

def StrictFeasibleBudget (o : Point k E) (r L ε : ℝ) (N : ℕ) : Prop :=
  ∃ A : FirstOrderAlgorithm k E, StrictGuarantees o r L ε N A

theorem strictFeasibleBudget_iff (o : Point k E) (r L ε : ℝ) (N : ℕ) :
    StrictFeasibleBudget o r L ε N ↔ Lorentz.PartialStrictFeasibleBudget o.normalized (k * r) (L / k) ε N := by
  constructor
  · rintro ⟨A, hA⟩
    exact ⟨normalizeAlgorithm A, hA.normalize⟩
  · rintro ⟨A, hA⟩
    exact ⟨physicalAlgorithm A, strictGuarantees_physical hA⟩

noncomputable def strictQueryComplexity (o : Point k E) (r L ε : ℝ) : ℝ≥0∞ :=
  ⨅ (N : ℕ) (_ : StrictFeasibleBudget o r L ε N), (N : ℝ≥0∞)

theorem strictQueryComplexity_eq (o : Point k E) (r L ε : ℝ) :
    strictQueryComplexity o r L ε = Lorentz.strictQueryComplexity o.normalized (k * r) (L / k) ε := by
  rw [← Lorentz.partialStrictQueryComplexity_eq]
  simp only [strictQueryComplexity, Lorentz.partialStrictQueryComplexity, strictFeasibleBudget_iff]

noncomputable def strictUniformComplexity (r L ε : ℝ) : ℝ≥0∞ :=
  ⨆ (d : ℕ) (_ : 2 ≤ d), strictQueryComplexity
    (⟨Lorentz.origin⟩ : Point k (EuclideanSpace ℝ (Fin d))) r L ε

theorem strictUniformComplexity_eq (r L ε : ℝ) :
    strictUniformComplexity (k := k) r L ε = Lorentz.strictUniformComplexity (k * r) (L / k) ε := by
  simp only [strictUniformComplexity, Lorentz.strictUniformComplexity, Lorentz.strictDimensionComplexity,
    strictQueryComplexity_eq]

/-- Matching complexity on the actual rescaled metric, depending on `ρ = k r`. -/
theorem matching_complexity {r L ε : ℝ}
    (hr : 0 < r) (hL : 0 < L) (hε : 0 < ε) (hεmax : ε ≤ 1 / 64) :
    ENNReal.ofReal (Geode.curvatureFactor (k * r) / (260 * ε ^ 2)) ≤
        uniformComplexity (k := k) r L ε ∧
      uniformComplexity (k := k) r L ε ≤ (⌈3 * Geode.curvatureFactor (k * r) / ε ^ 2⌉₊ : ℝ≥0∞) := by
  rw [uniformComplexity_eq, ← Lorentz.partialUniformComplexity_eq]
  exact Lorentz.partial_matching_complexity (mul_pos scale_pos hr) (div_pos hL scale_pos) hε hεmax

/-- Strict localization on the same rescaled metric and full partial oracle model. -/
theorem strict_localization {r L ε : ℝ}
    (hr : 0 < r) (hL : 0 < L) (hε : 0 < ε) (hεmax : ε ≤ 1 / 64) :
    ENNReal.ofReal (3 * Geode.curvatureFactor (k * r) / (1040 * ε ^ 2)) ≤
        strictUniformComplexity (k := k) r L ε ∧
      strictUniformComplexity (k := k) r L ε ≤ (⌈3 * Geode.curvatureFactor (k * r) / ε ^ 2⌉₊ : ℝ≥0∞) := by
  rw [strictUniformComplexity_eq, ← Lorentz.partialStrictUniformComplexity_eq]
  exact Lorentz.partial_strict_localization (mul_pos scale_pos hr) (div_pos hL scale_pos) hε hεmax

/-- The precise failure assertion transfers to the physical metric, retaining
one fixed objective, one fixed selected-vector oracle, and a unique minimizer
at physical distance `r`. The bound counts actual oracle queries. -/
theorem precise_failure_witness [FiniteDimensional ℝ E]
    (o : Point k E) {r L ε : ℝ}
    (hr : 0 < r) (hL : 0 < L) (hε : 0 < ε) (hεmax : ε ≤ 1 / 64)
    (hdim : Geode.queryHorizon (k * r) ε + 3 ≤ Module.finrank ℝ (Lorentz.Ambient E))
    (A : FirstOrderAlgorithm k E) :
    ∃ (f : Point k E → ℝ) (O : Point k E → Reply E) (p : Point k E),
      AdmissibleObjective o r L f ∧ LegalOracle f O ∧
      (∀ y, (∀ z, f y ≤ f z) ↔ y = p) ∧ f p = 0 ∧ dist o p = r ∧
      PartialRunFails (fun output => 2 * ε * L * r ≤ f output - f p)
        (partialRun A (fixedResponder O) (Geode.queryHorizon (k * r) ε) []) := by
  obtain ⟨f, O, p, hf, hO, hmin, hzero, hp, hfail⟩ :=
    Lorentz.precise_failure_witness_partial o.normalized (mul_pos (scale_pos (k := k)) hr)
      (div_pos hL (scale_pos (k := k))) hε hεmax hdim (normalizeAlgorithm A)
  refine ⟨physicalFunction (k := k) f, physicalOracle (k := k) O, ⟨p⟩,
    (admissible_iff o r L (physicalFunction (k := k) f)).mpr hf,
    (legalOracle_iff (physicalFunction (k := k) f) (physicalOracle (k := k) O)).mpr ?_,
    ?_, hzero, ?_, ?_⟩
  · simpa only [normalize_physicalFunction, normalize_physicalOracle] using hO
  · intro y
    constructor
    · intro hy
      apply Point.ext
      exact (hmin y.normalized).mp (fun z => hy ⟨z⟩)
    · intro hy
      subst y
      intro z
      exact (hmin p).mpr rfl z.normalized
  · change dist o.normalized p / k = r
    rw [hp, mul_div_cancel_left₀ _ scale_pos.ne']
  · have hh := normalize_run A (physicalOracle O) (Geode.queryHorizon (k * r) ε) []
    rw [normalize_physicalOracle] at hh
    have hfail' : PartialRunFails (fun q => 2 * ε * L * r ≤ f q - f p)
        (partialResultEquiv pointEquiv (replyEquiv (k := k))
          (partialRun A (fixedResponder (physicalOracle O)) (Geode.queryHorizon (k * r) ε) [])) := by
      rw [← hh]
      simpa only [historyEquiv_nil, tolerance_identity] using hfail
    cases hrun : partialRun A (fixedResponder (physicalOracle O)) (Geode.queryHorizon (k * r) ε) [] <;>
      simpa only [hrun, PartialRunFails, partialResultEquiv, pointEquiv, physicalFunction] using hfail'

end Geode.Rescaled
