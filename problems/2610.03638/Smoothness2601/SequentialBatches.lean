import Smoothness2601.InnerBatch
import Bilevel.StatefulAffineMean

/-! Actual sequential batches of original conditional oracle calls. The input
history is threaded through every sample, and centering is proved from the
oracle mean assumption rather than assumed of node averages. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace Smoothness2601.SequentialBatches
open Bilevel.Stateful

variable {Query History Obs E Param : Type*} [MeasurableSpace Query]
  [MeasurableSpace History] [MeasurableSpace Obs] [MeasurableSpace Param]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  {σ : ℝ} (O : HistoryOracle (Query := Query) (History := History) (Obs := Obs) (E := E) σ)

theorem sum_mean (n : ℕ) (q : Query) (h : History) (center : E) :
    Integrable (fun z => z.1-center) ((O.sum n).law (q,h)) ∧
    (∫ z, z.1-center ∂(O.sum n).law (q,h)) = (n : ℝ) • O.truth q-center := by
  have hs : StronglyMeasurable (fun z : Outcome E History => z.1-center) :=
    (by fun_prop : Measurable (fun z : Outcome E History => z.1-center)).stronglyMeasurable
  have hi := ((memLp_two_iff_integrable_sq_norm hs.aestronglyMeasurable).mpr
    (InnerBatch.sum_center_error O n q h center).1).integrable (by norm_num)
  refine ⟨hi, ?_⟩
  induction n generalizing center with
  | zero =>
    simp only [HistoryOracle.sum, Procedure.pure_law, Nat.cast_zero, zero_smul]
    rw [integral_dirac' _ _ hs]
  | succ n ih =>
    rw [HistoryOracle.sum, Procedure.integral_bind _ _ q h _ hs hi]
    have he (z : Outcome E History) :
        (∫ w, (Procedure.combine (z,w)).1-center ∂O.sumStep.law ((q,z.1),z.2.1)) =
          z.1-(center-O.truth q) := by
      have hm := (O.step_mean Prod.fst measurable_fst Prod.snd measurable_snd
        (fun _ => -1) measurable_const (q,z.1) z.2.1 center).2
      exact hm.trans (by simp only [neg_smul, one_smul, sub_neg_eq_add]; abel)
    simp_rw [he]
    have hs' : StronglyMeasurable (fun z : Outcome E History => z.1-(center-O.truth q)) :=
      (by fun_prop : Measurable (fun z : Outcome E History => z.1-(center-O.truth q))).stronglyMeasurable
    have hi' := ((memLp_two_iff_integrable_sq_norm hs'.aestronglyMeasurable).mpr
      (InnerBatch.sum_center_error O n q h (center-O.truth q)).1).integrable (by norm_num)
    rw [ih _ hs' hi']
    simp only [Nat.cast_add, Nat.cast_one, add_smul, one_smul]
    abel

theorem affineBatch_mean (n : ℕ) (hn : 0 < n) (α : ℝ)
    (q : Query) (d center : E) (h : History) :
    Integrable (fun z => z.1-center) ((InnerBatch.affineBatch O n α).law ((q,d),h)) ∧
    (∫ z, z.1-center ∂(InnerBatch.affineBatch O n α).law ((q,d),h)) =
      d-α • O.truth q-center := by
  have hn' : (n : ℝ) ≠ 0 := (Nat.cast_pos.mpr hn).ne'
  have hs := sum_mean O n q h 0
  simp only [sub_zero] at hs
  have hg : StronglyMeasurable (fun y : E => y-center) :=
    (by fun_prop : Measurable (fun y : E => y-center)).stronglyMeasurable
  constructor
  · rw [InnerBatch.affineBatch, Procedure.map_output_integrable_iff _ _ _ _ _ _ hg]
    change Integrable (fun z => d-(α/(n:ℝ)) • z.1-center) ((O.sum n).law (q,h))
    exact ((integrable_const _).sub (hs.1.smul _)).sub (integrable_const _)
  · rw [InnerBatch.affineBatch, Procedure.map_output_integral _ _ _ _ _ _ hg]
    change (∫ z, d-(α/(n:ℝ)) • z.1-center ∂(O.sum n).law (q,h)) = _
    have hd := integrable_const (μ := (O.sum n).law (q,h)) d
    have hc := integrable_const (μ := (O.sum n).law (q,h)) center
    have hm := hs.1.smul (α/(n:ℝ))
    have he := integral_sub (hd.sub hm) hc
    have he' := integral_sub hd hm
    simp only [Pi.sub_apply, Pi.smul_apply] at he he'
    rw [he, he', integral_smul, hs.2]
    simp only [integral_const, measureReal_univ_eq_one, one_smul, smul_smul,
      div_mul_cancel₀ _ hn']

variable (q : ℕ → Param → Query) (hq : ∀ j, Measurable (q j)) (d : ℕ → ℝ) (batch : ℕ → ℕ)

def nodeStep (j : ℕ) : Procedure (Param × E) History E :=
  (InnerBatch.affineBatch O (batch j) (-d j)).reparam
    (fun z => (q j z.1,z.2)) ((hq j).comp measurable_fst |>.prodMk measurable_snd)

def run : ℕ → Procedure Param History E
  | 0 => Procedure.pure (fun _ => 0) measurable_const
  | n+1 => (run n).bind (nodeStep O q hq d batch n)

def mean (n : ℕ) (p : Param) : E := ∑ j ∈ Finset.range n, d j • O.truth (q j p)
def varianceBudget (n : ℕ) : ℝ := ∑ j ∈ Finset.range n, d j ^ 2 * σ ^ 2 / (batch j : ℝ)
def sampleCount (n : ℕ) : ℕ := ∑ j ∈ Finset.range n, batch j

omit [CompleteSpace E] in
theorem run_calls (n : ℕ) : (run O q hq d batch n).CallsEq (fun _ => sampleCount batch n) := by
  induction n with
  | zero => exact Procedure.calls_pure _ _
  | succ n ih =>
    have hn := Procedure.CallsEq.reparam _ _ (InnerBatch.affineBatch_calls O (batch n) (-d n))
      (fun z : Param × E => (q n z.1,z.2)) ((hq n).comp measurable_fst |>.prodMk measurable_snd)
    simpa only [sampleCount, Finset.sum_range_succ] using
      Procedure.CallsEq.bind _ _ (fun _ => sampleCount batch n) (fun _ => batch n) ih hn

theorem run_center_error (hbatch : ∀ j, 0 < batch j) (hd : ∀ j, d j ≠ 0)
    (n : ℕ) (p : Param) (h : History) (center : E) :
    Integrable (fun z => ‖z.1-center‖ ^ 2) ((run O q hq d batch n).law (p,h)) ∧
    (∫ z, ‖z.1-center‖ ^ 2 ∂(run O q hq d batch n).law (p,h)) ≤
      ‖mean O q d n p-center‖ ^ 2 + varianceBudget (σ := σ) d batch n := by
  induction n generalizing center with
  | zero =>
    simp only [run, Procedure.pure_law, mean, varianceBudget, Finset.range_zero,
      Finset.sum_empty, add_zero]
    have hm : StronglyMeasurable (fun z : Outcome E History => ‖z.1-center‖^2) :=
      (by fun_prop : Measurable (fun z : Outcome E History => ‖z.1-center‖^2)).stronglyMeasurable
    exact ⟨integrable_dirac' hm, by rw [integral_dirac' _ _ hm]⟩
  | succ n ih =>
    have hp := ih (center-d n • O.truth (q n p))
    have he (u : E) : u-(-d n) • O.truth (q n p)-center =
        u-(center-d n • O.truth (q n p)) := by module
    have hs (z : Outcome E History) := InnerBatch.affineBatch_error O (batch n) (hbatch n)
      (neg_ne_zero.mpr (hd n)) (q n p) z.1 center z.2.1
    have hb := Procedure.bind_output_bound (run O q hq d batch n) (nodeStep O q hq d batch n) p h
      (fun u => ‖u-center‖^2) (by fun_prop) (fun _ => sq_nonneg _)
      (fun u => ‖u-(center-d n • O.truth (q n p))‖^2+d n^2*σ^2/(batch n:ℝ))
      (hp.1.add (integrable_const _)) (fun z => (hs z).1)
      (fun z => by simpa only [he, neg_sq] using (hs z).2)
    refine ⟨hb.1, hb.2.trans ?_⟩
    rw [integral_add hp.1 (integrable_const _)]
    simp only [integral_const, measureReal_univ_eq_one, one_smul]
    have hm : mean O q d n p-(center-d n • O.truth (q n p)) =
        mean O q d (n+1) p-center := by
      simp only [mean, Finset.sum_range_succ]
      abel
    rw [hm] at hp
    simp only [varianceBudget, Finset.sum_range_succ] at hp ⊢
    linarith [hp.2]

theorem run_mean (hbatch : ∀ j, 0 < batch j) (hd : ∀ j, d j ≠ 0)
    (n : ℕ) : (run O q hq d batch n).Mean (mean O q d n) := by
  intro p h
  have hs : StronglyMeasurable (fun z : Outcome E History => z.1-mean O q d n p) :=
    (by fun_prop : Measurable (fun z : Outcome E History => z.1-mean O q d n p)).stronglyMeasurable
  have hi := ((memLp_two_iff_integrable_sq_norm hs.aestronglyMeasurable).mpr
    (run_center_error O q hq d batch hbatch hd n p h _).1).integrable (by norm_num)
  refine ⟨hi, ?_⟩
  induction n with
  | zero =>
    simp only [run, Procedure.pure_law, mean, Finset.range_zero, Finset.sum_empty]
    change StronglyMeasurable (fun z : Outcome E History => z.1-(0:E)) at hs
    rw [integral_dirac' _ _ hs]
    simp
  | succ n ih =>
    rw [run, Procedure.integral_bind _ _ p h _ hs hi]
    have he (z : Outcome E History) :
        (∫ w, (Procedure.combine (z,w)).1-mean O q d (n+1) p
          ∂(nodeStep O q hq d batch n).law ((p,z.1),z.2.1)) = z.1-mean O q d n p := by
      have hm := (affineBatch_mean O (batch n) (hbatch n) (-d n) (q n p) z.1
        (mean O q d (n+1) p) z.2.1).2
      exact hm.trans (by simp only [mean, Finset.sum_range_succ]; module)
    simp_rw [he]
    have hs' : StronglyMeasurable (fun z : Outcome E History => z.1-mean O q d n p) :=
      (by fun_prop : Measurable (fun z : Outcome E History => z.1-mean O q d n p)).stronglyMeasurable
    have hi' := ((memLp_two_iff_integrable_sq_norm hs'.aestronglyMeasurable).mpr
      (run_center_error O q hq d batch hbatch hd n p h _).1).integrable (by norm_num)
    exact ih hs' hi'

end Smoothness2601.SequentialBatches
