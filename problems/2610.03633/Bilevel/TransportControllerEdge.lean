import Bilevel.TransportEdgeAngle
import Bilevel.TransportNetworkReconstruction

/-! Actual adaptive paired-edge execution with non-observed angle monitors.
A monitor does not reveal its outcome to the algorithm. Forward and reverse
actions update pairs for the same fixed orthogonal map. The finite failure
bound is derived by conditioning each actual response, not by postulating
an entire good-angle event. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace Bilevel.TransportControllerEdge
open EuclideanGaussian OrthogonalAction ProjectionGeometry TransportObserver
open TransportEdgePosterior
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000

inductive Program (D : ℕ) (β : Type*) : ℕ → Type _
  | halt {m : ℕ} (value : β) : Program D β m
  | check {m : ℕ} (W R : Submodule ℝ (Space D)) (next : Program D β m) : Program D β (m+1)
  | forward {m : ℕ} (q : Space D) (next : Space D → Program D β m) : Program D β (m+1)
  | reverse {m : ℕ} (q : Space D) (next : Space D → Program D β m) : Program D β (m+1)

def angleBad {D : ℕ} (W R : Submodule ℝ (Space D)) (O : OrthogonalHaar.Group D) : Prop :=
  ∃ u : R, ‖u‖/8 < ‖project W (O • (u : Space D))‖

theorem angleBad_measurable {D : ℕ} (W R : Submodule ℝ (Space D)) :
    MeasurableSet {O | angleBad W R O} := by
  have he : {O : OrthogonalHaar.Group D | angleBad W R O} =
      ⋃ u : R, {O | ‖u‖/8 < ‖project W (O • (u : Space D))‖} := by
    ext O; simp [angleBad]
  rw [he]
  apply IsOpen.measurableSet
  apply isOpen_iUnion
  intro u
  have hproj : Continuous (project W) := W.subtypeL.continuous.comp W.orthogonalProjection.continuous
  letI : ContinuousSMul (OrthogonalHaar.Group D) (Space D) := ⟨action_continuous D⟩
  have ha : Continuous (fun O : OrthogonalHaar.Group D => O • (u : Space D)) :=
    continuous_id.smul continuous_const
  have hp : Continuous (fun O : OrthogonalHaar.Group D => project W (O • (u : Space D))) := hproj.comp ha
  exact isOpen_lt continuous_const hp.norm

def bad {D : ℕ} {β : Type*} : {m : ℕ} → Program D β m → OrthogonalHaar.Group D → Prop
  | _,.halt _,_ => False
  | _,.check W R next,O => angleBad W R O ∨ bad next O
  | _,.forward q next,O => bad (next (O • q)) O
  | _,.reverse q next,O => bad (next (O⁻¹ • q)) O

def Regular {D : ℕ} {β : Type*} : {m : ℕ} → Program D β m → Prop
  | _,.halt _ => True
  | _,.check _ _ next => Regular next
  | _,.forward _ next =>
      MeasurableSet {p : Space D × OrthogonalHaar.Group D | bad (next p.1) p.2} ∧ ∀ y, Regular (next y)
  | _,.reverse _ next =>
      MeasurableSet {p : Space D × OrthogonalHaar.Group D | bad (next p.1) p.2} ∧ ∀ y, Regular (next y)

def Valid {D : ℕ} {β : Type*} (d : ℕ) : {m : ℕ} → Program D β m → Pairs D → Prop
  | _,.halt _,_ => True
  | _,.check W R next,L =>
      R ≤ (domain L)ᗮ ∧ Module.finrank ℝ R ≤ d ∧ Module.finrank ℝ W ≤ d ∧ Valid d next L
  | _,.forward q next,L => ∀ y, Valid d (next y) ((q,y)::L)
  | _,.reverse q next,L => ∀ x, Valid d (next x) ((x,q)::L)

def erase {D : ℕ} {β : Type*} : {m : ℕ} → Program D β m → TransportNetwork.EdgeProgram D β m
  | _,.halt x => .halt x
  | _,.check _ _ next => .skip (erase next)
  | _,.forward q next => .forward q (fun y => erase (next y))
  | _,.reverse q next => .reverse q (fun y => erase (next y))

def finalPairs {D : ℕ} {β : Type*} : {m : ℕ} → Program D β m → Pairs D → OrthogonalHaar.Group D → Pairs D
  | _,.halt _,L,_ => L
  | _,.check _ _ next,L,O => finalPairs next L O
  | _,.forward q next,L,O => finalPairs (next (O • q)) ((q,O • q)::L) O
  | _,.reverse q next,L,O => finalPairs (next (O⁻¹ • q)) ((O⁻¹ • q,q)::L) O

theorem finalPairs_supported {D m : ℕ} {β : Type*} (P : Program D β m)
    (L : Pairs D) (O : OrthogonalHaar.Group D) (hL : Supports L O) : Supports (finalPairs P L O) O := by
  induction P generalizing L with
  | halt _ => exact hL
  | check _ _ next ih => exact ih L hL
  | forward q next ih => exact ih (O • q) ((q,O • q)::L) ⟨rfl,hL⟩
  | reverse q next ih => exact ih (O⁻¹ • q) ((O⁻¹ • q,q)::L) ⟨smul_inv_smul O q,hL⟩

theorem range_rank_cons {D : ℕ} (L : Pairs D) (q y : Space D) :
    Module.finrank ℝ (range ((q,y)::L)) ≤ Module.finrank ℝ (range L)+1 :=
  ProjectionQuery.finrank_insert_le _ _

theorem bad_measurable {D m : ℕ} {β : Type*} (P : Program D β m) (hP : Regular P) :
    MeasurableSet {O | bad P O} := by
  cases P with
  | halt _ => exact MeasurableSet.empty
  | check W R next => exact (angleBad_measurable W R).union (bad_measurable next hP)
  | forward q next => exact ((forward_measurable q).prodMk measurable_id) hP.1
  | reverse q next => exact ((reverse_measurable q).prodMk measurable_id) hP.1

theorem observation_tail {D : ℕ} (μ : Measure (OrthogonalHaar.Group D)) [IsProbabilityMeasure μ]
    (o : OrthogonalHaar.Group D → Space D) (ho : Measurable o)
    (b : Space D → OrthogonalHaar.Group D → Prop)
    (hb : MeasurableSet {p : Space D × OrthogonalHaar.Group D | b p.1 p.2}) (c : ℝ≥0∞)
    (hc : ∀ᵐ y ∂μ.map o, condDistrib id o μ y {O | b y O} ≤ c) :
    μ {O | b (o O) O} ≤ c := by
  letI : IsProbabilityMeasure (μ.map o) := isProbabilityMeasure_map ho.aemeasurable
  have he := ConditionalSupport.event_disintegration μ o ho _ hb
  change μ {O | b (o O) O} = ∫⁻ y, condDistrib id o μ y {O | b y O} ∂μ.map o at he
  rw [he]
  calc
    _ ≤ ∫⁻ _y, c ∂μ.map o := lintegral_mono_ae hc
    _ = _ := by simp

def budget (d r : ℕ) : ℝ≥0∞ := ENNReal.ofReal (64*(d:ℝ)^2/(r:ℝ))

theorem finite_angle_failure {D m : ℕ} {β : Type*} (P : Program D β m)
    (d r : ℕ) (hr : 0 < r) :
    ∀ (L : Pairs D), Module.finrank ℝ (range L)+m+r ≤ D →
      ∀ (μ : Measure (OrthogonalHaar.Group D)) [IsProbabilityMeasure μ],
        Invariant (range L) μ → (∀ᵐ O ∂μ, Supports L O) → Regular P → Valid d P L →
        μ {O | bad P O} ≤ (m:ℝ≥0∞)*budget d r := by
  induction P with
  | halt x =>
    intro L hdim μ _ hμ hL hP hV
    simp only [bad,Set.setOf_false,measure_empty]
    exact zero_le _
  | @check m W R next ih =>
    intro L hdim μ _ hμ hL hP hV
    have hres := TransportObserver.residual_dimension_real D (range L)
    have hrR : (0:ℝ) < r := by exact_mod_cast hr
    have hden : (r:ℝ) ≤ (Module.finrank ℝ (range L)ᗮ : ℝ) := by
      have hh : Module.finrank ℝ (range L)+r ≤ D := by omega
      have hh' : (Module.finrank ℝ (range L):ℝ)+r ≤ D := by exact_mod_cast hh
      linarith
    have hpos : 0 < Module.finrank ℝ (range L)ᗮ := by
      have hh : (0:ℝ) < (Module.finrank ℝ (range L)ᗮ : ℝ) := hrR.trans_le hden
      exact_mod_cast hh
    have hh := paired_operator_failure L W hpos μ hμ hL R hV.1 (id : R → R) (fun _ => le_rfl)
    have hRW : (Module.finrank ℝ R:ℝ)*(Module.finrank ℝ W:ℝ) ≤ (d:ℝ)^2 := by
      have hR : (Module.finrank ℝ R:ℝ) ≤ d := by exact_mod_cast hV.2.1
      have hW : (Module.finrank ℝ W:ℝ) ≤ d := by exact_mod_cast hV.2.2.1
      simpa only [pow_two] using mul_le_mul hR hW (Nat.cast_nonneg _) (Nat.cast_nonneg d)
    have hheadR : μ.real {O | angleBad W R O} ≤ 64*(d:ℝ)^2/(r:ℝ) := by
      apply hh.trans
      calc
        _ ≤ 64*((d:ℝ)^2/(Module.finrank ℝ (range L)ᗮ : ℝ)) :=
          mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hRW (Nat.cast_nonneg _)) (by norm_num)
        _ ≤ 64*((d:ℝ)^2/(r:ℝ)) := mul_le_mul_of_nonneg_left
          (div_le_div_of_nonneg_left (sq_nonneg _) hrR hden) (by norm_num)
        _ = _ := by ring
    have hhead : μ {O | angleBad W R O} ≤ budget d r := by
      simpa only [budget,Measure.real,ENNReal.ofReal_toReal (measure_ne_top _ _)] using
        ENNReal.ofReal_le_ofReal hheadR
    have htail := ih L (by omega) μ hμ hL hP hV.2.2.2
    change μ ({O | angleBad W R O} ∪ {O | bad next O}) ≤ _
    apply (measure_union_le _ _).trans
    simpa only [Nat.cast_add,Nat.cast_one,add_mul,one_mul,add_comm] using add_le_add hhead htail
  | @forward m q next ih =>
    intro L hdim μ _ hμ hL hP hV
    have ht : μ {O | bad (next (O • q)) O} ≤ (m:ℝ≥0∞)*budget d r := by
      apply observation_tail μ (TransportEdgePosterior.forward q) (forward_measurable q)
        (fun y O => bad (next y) O) hP.1
      filter_upwards [forward_posterior_pairs L μ hμ hL q] with y hy
      exact ih y ((q,y)::L) (by have hh := range_rank_cons L q y; omega)
        _ hy.1 hy.2 (hP.2 y) (hV y)
    exact ht.trans (mul_le_mul_right' (by exact_mod_cast Nat.le_succ m) _)
  | @reverse m q next ih =>
    intro L hdim μ _ hμ hL hP hV
    have ht : μ {O | bad (next (O⁻¹ • q)) O} ≤ (m:ℝ≥0∞)*budget d r := by
      apply observation_tail μ (TransportEdgePosterior.reverse q) (reverse_measurable q)
        (fun y O => bad (next y) O) hP.1
      filter_upwards [reverse_posterior_pairs L μ hμ hL q] with x hx
      exact ih x ((x,q)::L) (by have hh := range_rank_cons L x q; omega)
        _ hx.1 hx.2 (hP.2 x) (hV x)
    exact ht.trans (mul_le_mul_right' (by exact_mod_cast Nat.le_succ m) _)

end Bilevel.TransportControllerEdge
