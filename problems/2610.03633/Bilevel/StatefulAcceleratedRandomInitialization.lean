import Bilevel.StatefulAcceleratedSolver

/-! The accelerated solver from a random initial point and its correlated
full history. Only the initial mean squared distance is bounded. The existing
public schedule and its early-return branch are used without modification. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace BigOperators
namespace Bilevel.StatefulAccelerated
open Stateful AcceleratedInner

variable {History Obs E : Type*} [MeasurableSpace History] [MeasurableSpace Obs]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  {σ : ℝ} (O : HistoryOracle (Query := E) (History := History) (Obs := Obs) (E := E) σ)

/-- Unlike the certified-start bound, this holds for every initial state.
Its dependence on the initial potential is affine and can be integrated. -/
theorem stages_potential_affine (F : E → ℝ) (g : E → E) {μ M α U : ℝ} (shift : E)
    (hM : 0 < M) (hμ : 0 < μ) (hα : 0 < α) (hα1 : α ≤ 1) (hU : 0 < U)
    (hrel : α ^ 2 * M = μ) (htruth : ∀ y, O.truth y + shift = g y)
    (hg : ∀ y, HasGradientAt F (g y) y)
    (hlip : ∀ u v, ‖g u-g v‖ ≤ M*‖u-v‖)
    (hstrong : ∀ u v, F u+⟪g u,v-u⟫+μ/2*‖v-u‖^2 ≤ F v)
    (ys : E) (hmin : ∀ y, F ys ≤ F y) (s : E×E) (h : History) (S : ℕ) :
    Integrable (fun z => potential F μ ys z.1.1 z.1.2)
      ((stages O μ M α shift U S).law (s,h)) ∧
    (∫ z, potential F μ ys z.1.1 z.1.2 ∂(stages O μ M α shift U S).law (s,h)) ≤
      (1/4:ℝ)^S * potential F μ ys s.1 s.2 + stageBudget U S - (1/4:ℝ)^S*U := by
  have hF : Continuous F := continuous_iff_continuousAt.mpr
    (fun y => (hg y).differentiableAt.continuousAt)
  let V : E×E → ℝ := fun z => potential F μ ys z.1 z.2
  have hV : Measurable V := by dsimp [V,potential]; fun_prop
  have hn (z : E×E) : 0 ≤ V z :=
    add_nonneg (sub_nonneg.mpr (hmin z.1)) (by positivity)
  induction S with
  | zero =>
    rw [stages,Procedure.pure_law]
    have hm : StronglyMeasurable (fun z : Outcome (E×E) History => V z.1) :=
      (hV.comp measurable_fst).stronglyMeasurable
    refine ⟨integrable_dirac' hm,?_⟩
    rw [integral_dirac' _ _ hm]
    simp only [id_eq,pow_zero,one_mul,stageBudget,div_one,add_sub_cancel_right,V,le_refl]
  | succ S ih =>
    let B := stageBatch M α σ (stageBudget U (S+1))
    have hB : 0 < B := stageBatch_pos _ _ _ _
    have hnext (z : E×E) (hz : History) := run_potential O F g shift hM hμ hα hα1 hrel
      htruth hg hlip hstrong B hB ys hmin z hz (stageLength α)
    have hquarter (z : E×E) (hz : History) :
        (∫ w,V w.1 ∂(run O μ M α shift B (stageLength α)).law (z,hz)) ≤
          (1/4)*V z + stageBudget U (S+1)/2 := by
      have hr := (hnext z hz).2
      have hfloor := stageBatch_floor (σ := σ) hM hα (stageBudget_pos hU (S+1))
      have hf0 : 0 ≤ σ^2/((B:ℝ)*M*α) := by positivity
      have hpow : 0 ≤ (1-α)^stageLength α := pow_nonneg (sub_nonneg.mpr hα1) _
      have hfactor := mul_le_mul_of_nonneg_right (stageLength_contracts hα hα1) (hn z)
      dsimp [B] at hr hf0
      dsimp [V] at hfactor ⊢
      nlinarith
    have hb := Procedure.bind_output_bound (stages O μ M α shift U S)
      ((run O μ M α shift B (stageLength α)).reparam Prod.snd measurable_snd) s h V hV hn
      (fun z => (1/4)*V z+stageBudget U (S+1)/2)
      ((ih.1.const_mul (1/4)).add (integrable_const _))
      (fun z => (hnext z.1 z.2.1).1) (fun z => hquarter z.1 z.2.1)
    refine ⟨hb.1,hb.2.trans ?_⟩
    rw [integral_add (ih.1.const_mul (1/4)) (integrable_const _),integral_const_mul,
      integral_const,measureReal_univ_eq_one,one_smul]
    have hhalf := stageBudget_half U S
    rw [pow_succ]
    linarith [ih.2]

theorem stages_distance_affine (F : E → ℝ) (g : E → E) {μ M α U : ℝ} (shift : E)
    (hM : 0 < M) (hμ : 0 < μ) (hα : 0 < α) (hα1 : α ≤ 1) (hU : 0 < U)
    (hrel : α^2*M=μ) (htruth : ∀ y,O.truth y+shift=g y)
    (hg : ∀ y,HasGradientAt F (g y) y)
    (hlip : ∀ u v,‖g u-g v‖≤M*‖u-v‖)
    (hstrong : ∀ u v,F u+⟪g u,v-u⟫+μ/2*‖v-u‖^2≤F v)
    (ys : E) (hmin : ∀ y,F ys≤F y) (hstationary : g ys=0)
    (s : E×E) (h : History) (S : ℕ) :
    Integrable (fun z => ‖z.1.1-ys‖^2) ((stages O μ M α shift U S).law (s,h)) ∧
    (∫ z,‖z.1.1-ys‖^2 ∂(stages O μ M α shift U S).law (s,h)) ≤
      (2/μ)*((1/4:ℝ)^S*potential F μ ys s.1 s.2+stageBudget U S-(1/4:ℝ)^S*U) := by
  have hp := stages_potential_affine O F g shift hM hμ hα hα1 hU hrel htruth hg hlip hstrong
    ys hmin s h S
  have hcoef : 0≤2/μ := by positivity
  have hb (z : Outcome (E×E) History) :
      ‖z.1.1-ys‖^2 ≤ (2/μ)*potential F μ ys z.1.1 z.1.2 := by
    have hc := potential_controls_distance F g hμ.le hstrong z.1.1 z.1.2 ys hstationary
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hμ).mpr
    nlinarith
  have hm : Measurable (fun z : Outcome (E×E) History => ‖z.1.1-ys‖^2) := by fun_prop
  have hi : Integrable (fun z => ‖z.1.1-ys‖^2) ((stages O μ M α shift U S).law (s,h)) := by
    apply (hp.1.const_mul (2/μ)).mono' hm.aestronglyMeasurable
    filter_upwards with z
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact hb z
  refine ⟨hi,?_⟩
  have hh := integral_mono hi (hp.1.const_mul (2/μ)) hb
  rw [integral_const_mul] at hh
  exact hh.trans (mul_le_mul_of_nonneg_left hp.2 hcoef)

variable {Param : Type*} [MeasurableSpace Param]

/-- Run the existing solver after an arbitrary initialization procedure.
The entering point and complete entering history may be correlated. -/
def solveAfter (I : Procedure Param History E) (μ M α : ℝ) (shift : E) (R r : ℝ) :
    Procedure Param History E :=
  I.bind ((solve O μ M α shift R r).reparam Prod.snd measurable_snd)

omit [CompleteSpace E] in
theorem solveAfter_calls (I : Procedure Param History E) (c : Param → ℕ)
    (hI : I.CallsEq c) (μ M α : ℝ) (shift : E) (R r : ℝ) :
    (solveAfter O I μ M α shift R r).CallsEq (fun p => c p+solveCalls μ M α σ R r) :=
  Procedure.CallsEq.bind I _ c (fun _ => solveCalls μ M α σ R r) hI
    (Procedure.CallsEq.reparam _ _ (solve_calls O μ M α shift R r) _ measurable_snd)

/-- Source `acc:lem:inner` with only an initial MSE bound. This is a local
statement at an arbitrary preceding input and history; no independence of
the initialized point from its returned history is assumed. -/
theorem solveAfter_distance (I : Procedure Param History E)
    (F : E → ℝ) (g : E → E) {μ M α R r : ℝ} (shift : E)
    (hM : 0<M) (hμ : 0<μ) (hμM : μ≤M)
    (hα : 0<α) (hα1 : α≤1) (hrel : α^2*M=μ)
    (htruth : ∀ y,O.truth y+shift=g y)
    (hg : ∀ y,HasGradientAt F (g y) y)
    (hlip : ∀ u v,‖g u-g v‖≤M*‖u-v‖)
    (hstrong : ∀ u v,F u+⟪g u,v-u⟫+μ/2*‖v-u‖^2≤F v)
    (ys : E) (hmin : ∀ y,F ys≤F y) (hstationary : g ys=0)
    (hR : 0≤R) (hr : 0<r) (p : Param) (h : History)
    (hinit : Integrable (fun z => ‖z.1-ys‖^2) (I.law (p,h)) ∧
      (∫ z,‖z.1-ys‖^2 ∂I.law (p,h)) ≤ R^2) :
    Integrable (fun z => ‖z.1-ys‖^2) ((solveAfter O I μ M α shift R r).law (p,h)) ∧
      (∫ z,‖z.1-ys‖^2 ∂(solveAfter O I μ M α shift R r).law (p,h)) ≤ r^2 := by
  have hf : Measurable (fun v : E => ‖v-ys‖^2) := by fun_prop
  have hfo : StronglyMeasurable (fun z : Outcome E History => ‖z.1-ys‖^2) :=
    (hf.comp measurable_fst).stronglyMeasurable
  by_cases hearly : R≤r
  · have hlocal (u : E) (hh : History) :
        Integrable (fun z => ‖z.1-ys‖^2) ((solve O μ M α shift R r).law (u,hh)) ∧
        (∫ z,‖z.1-ys‖^2 ∂(solve O μ M α shift R r).law (u,hh)) ≤ ‖u-ys‖^2 := by
      rw [solve,if_pos hearly,Procedure.pure_law]
      refine ⟨integrable_dirac' hfo,?_⟩
      rw [integral_dirac' _ _ hfo]
      exact le_rfl
    have hb := Procedure.bind_output_bound I
      ((solve O μ M α shift R r).reparam Prod.snd measurable_snd) p h
      (fun v => ‖v-ys‖^2) hf (fun _ => sq_nonneg _) (fun v => ‖v-ys‖^2) hinit.1
      (fun z => (hlocal z.1 z.2.1).1) (fun z => (hlocal z.1 z.2.1).2)
    refine ⟨hb.1,hb.2.trans (hinit.2.trans ?_)⟩
    nlinarith
  · have hRpos : 0<R := hr.trans (lt_of_not_ge hearly)
    let U := M*R^2
    let S := dyadicStageCount U (μ*r^2/4)
    let a : ℝ := (1/4)^S
    let T := stageBudget U S
    let b : E → ℝ := fun u => (2/μ)*(a*(M*‖u-ys‖^2)+T-a*U)
    have hU : 0<U := by dsimp [U]; positivity
    have ha : 0≤a := pow_nonneg (by norm_num) _
    have hc : 0≤2/μ := by positivity
    have hlocal (u : E) (hh : History) :
        Integrable (fun z => ‖z.1-ys‖^2) ((solve O μ M α shift R r).law (u,hh)) ∧
        (∫ z,‖z.1-ys‖^2 ∂(solve O μ M α shift R r).law (u,hh)) ≤ b u := by
      have hd := stages_distance_affine O F g shift hM hμ hα hα1 hU hrel htruth hg hlip
        hstrong ys hmin hstationary (u,u) hh S
      have hin := initial_potential_bound F g hM.le hμM hg hlip u ys hstationary
        (le_refl (‖u-ys‖^2))
      constructor
      · rw [solve,if_neg hearly,Procedure.map_output_integrable_iff _ _ _ _ _ _ hf.stronglyMeasurable]
        exact hd.1
      · rw [solve,if_neg hearly,Procedure.map_output_integral _ _ _ _ _ _ hf.stronglyMeasurable]
        apply hd.2.trans
        exact mul_le_mul_of_nonneg_left
          (sub_le_sub_right (add_le_add_right (mul_le_mul_of_nonneg_left hin ha) T) (a*U)) hc
    have hbint : Integrable (fun z => b z.1) (I.law (p,h)) :=
      ((((hinit.1.const_mul M).const_mul a).add (integrable_const T)).sub
        (integrable_const (a*U))).const_mul (2/μ)
    have hb := Procedure.bind_output_bound I
      ((solve O μ M α shift R r).reparam Prod.snd measurable_snd) p h
      (fun v => ‖v-ys‖^2) hf (fun _ => sq_nonneg _) b hbint
      (fun z => (hlocal z.1 z.2.1).1) (fun z => (hlocal z.1 z.2.1).2)
    refine ⟨hb.1,hb.2.trans ?_⟩
    have heval : (∫ z,b z.1 ∂I.law (p,h)) =
        (2/μ)*(a*(M*(∫ z,‖z.1-ys‖^2 ∂I.law (p,h)))+T-a*U) := by
      have hsum : Integrable (fun z => a*(M*‖z.1-ys‖^2)+T) (I.law (p,h)) :=
        ((hinit.1.const_mul M).const_mul a).add (integrable_const T)
      dsimp only [b]
      rw [integral_const_mul,
        integral_sub hsum (integrable_const (a*U)),
        integral_add ((hinit.1.const_mul M).const_mul a) (integrable_const T),
        integral_const_mul,integral_const_mul]
      simp only [integral_const,measureReal_univ_eq_one,one_smul]
    rw [heval]
    have hT : 0<μ*r^2/4 := by positivity
    have hTU : μ*r^2/4<U := by
      have hrr : r^2<R^2 := by nlinarith [lt_of_not_ge hearly]
      have h1 := mul_lt_mul_of_pos_left hrr hM
      have h2 := mul_le_mul_of_nonneg_right hμM (sq_nonneg r)
      dsimp [U]
      nlinarith
    have ht : T≤μ*r^2/4 := (dyadicStageCount_bounds hT hTU).2.1
    calc
      _ ≤ (2/μ)*(a*(M*R^2)+T-a*U) :=
        mul_le_mul_of_nonneg_left
          (sub_le_sub_right (add_le_add_right
            (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hinit.2 hM.le) ha) T) (a*U)) hc
      _ = (2/μ)*T := by dsimp [U]; ring
      _ ≤ (2/μ)*(μ*r^2/4) := mul_le_mul_of_nonneg_left ht hc
      _ = r^2/2 := by field_simp; ring
      _ ≤ r^2 := by nlinarith [sq_nonneg r]

end Bilevel.StatefulAccelerated
