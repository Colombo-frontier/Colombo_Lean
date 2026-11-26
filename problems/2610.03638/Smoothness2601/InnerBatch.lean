import Bilevel.StatefulBatch

/-! Affine updates using an actual finite batch of original history-threaded
calls. Conditional laws can depend on the full history at every sample. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace Smoothness2601.InnerBatch
open Bilevel.Stateful

variable {Query History Obs E : Type*} [MeasurableSpace Query]
  [MeasurableSpace History] [MeasurableSpace Obs]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  {σ : ℝ} (O : HistoryOracle (Query := Query) (History := History) (Obs := Obs) (E := E) σ)

theorem sum_center_error (n : ℕ) (q : Query) (h : History) (center : E) :
    Integrable (fun z => ‖z.1-center‖ ^ 2) ((O.sum n).law (q,h)) ∧
    (∫ z, ‖z.1-center‖ ^ 2 ∂(O.sum n).law (q,h)) ≤
      ‖(n : ℝ) • O.truth q-center‖ ^ 2 + (n : ℝ) * σ ^ 2 := by
  induction n generalizing center with
  | zero =>
    simp only [HistoryOracle.sum, Procedure.pure_law, Nat.cast_zero, zero_smul, zero_mul, add_zero]
    have hm : StronglyMeasurable (fun z : Outcome E History => ‖z.1-center‖ ^ 2) :=
      (by fun_prop : Measurable (fun z : Outcome E History => ‖z.1-center‖ ^ 2)).stronglyMeasurable
    exact ⟨integrable_dirac' hm, by rw [integral_dirac' _ _ hm]⟩
  | succ n ih =>
    have hprev := ih (center - O.truth q)
    have hs (z : Outcome E History) := O.step_error Prod.fst measurable_fst
      Prod.snd measurable_snd (fun _ => -1) measurable_const (q,z.1) z.2.1 center
    have he (u : E) : u - (-1 : ℝ) • O.truth q-center = u-(center-O.truth q) := by
      simp only [neg_smul, one_smul, sub_neg_eq_add]
      abel
    have hb := Procedure.bind_output_bound (O.sum n) O.sumStep q h
      (fun y => ‖y-center‖ ^ 2) (by fun_prop) (fun _ => sq_nonneg _)
      (fun y => ‖y-(center-O.truth q)‖ ^ 2 + σ ^ 2)
      (hprev.1.add (integrable_const _))
      (fun z => (hs z).1) (fun z => by simpa only [he, neg_one_sq, one_mul] using (hs z).2)
    refine ⟨hb.1, hb.2.trans ?_⟩
    rw [integral_add hprev.1 (integrable_const (σ ^ 2))]
    simp only [integral_const, measureReal_univ_eq_one, one_smul]
    have hv : (n : ℝ) • O.truth q - (center - O.truth q) =
        ((n+1 : ℕ) : ℝ) • O.truth q - center := by
      simp only [Nat.cast_add, Nat.cast_one, add_smul, one_smul]
      abel
    rw [hv] at hprev
    push_cast at hprev ⊢
    linarith [hprev.2]

def affineBatch (n : ℕ) (α : ℝ) : Procedure (Query × E) History E :=
  ((O.sum n).reparam Prod.fst measurable_fst).map
    (fun z => z.1.2 - (α / (n : ℝ)) • z.2) (by fun_prop)

omit [CompleteSpace E] in
theorem affineBatch_calls (n : ℕ) (α : ℝ) :
    (affineBatch O n α).CallsEq (fun _ => n) :=
  Procedure.CallsEq.map _ _
    (Procedure.CallsEq.reparam _ _ (O.sum_calls n) Prod.fst measurable_fst) _ _

theorem affineBatch_error (n : ℕ) (hn : 0 < n) {α : ℝ} (hα : α ≠ 0)
    (q : Query) (d center : E) (h : History) :
    Integrable (fun z => ‖z.1-center‖ ^ 2) ((affineBatch O n α).law ((q,d),h)) ∧
    (∫ z, ‖z.1-center‖ ^ 2 ∂(affineBatch O n α).law ((q,d),h)) ≤
      ‖d - α • O.truth q-center‖ ^ 2 + α ^ 2 * σ ^ 2 / (n : ℝ) := by
  have hn' : (n : ℝ) ≠ 0 := (Nat.cast_pos.mpr hn).ne'
  let c := ((n : ℝ) / α) • (d-center)
  have hc : (α / (n : ℝ)) * ((n : ℝ) / α) = 1 := by field_simp
  have he (u : E) : ‖d - (α / (n : ℝ)) • u - center‖ ^ 2 =
      (α / (n : ℝ)) ^ 2 * ‖u-c‖ ^ 2 := by
    have hv : d - (α / (n : ℝ)) • u - center = -(α / (n : ℝ)) • (u-c) := by
      dsimp [c]
      rw [smul_sub, smul_smul, neg_mul, hc, neg_one_smul]
      module
    rw [hv, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, neg_sq]
  have hs := sum_center_error O n q h c
  have hg : StronglyMeasurable (fun y : E => ‖y-center‖ ^ 2) :=
    (by fun_prop : Measurable (fun y : E => ‖y-center‖ ^ 2)).stronglyMeasurable
  have hmean : (α / (n : ℝ)) ^ 2 * ‖(n : ℝ) • O.truth q-c‖ ^ 2 =
      ‖d-α • O.truth q-center‖ ^ 2 := by
    rw [← he]
    congr 2
    rw [smul_smul, div_mul_cancel₀ _ hn']
  constructor
  · rw [affineBatch, Procedure.map_output_integrable_iff _ _ _ _ _ _ hg]
    change Integrable (fun z => ‖d - (α / (n : ℝ)) • z.1-center‖ ^ 2) ((O.sum n).law (q,h))
    simp_rw [he]
    exact hs.1.const_mul _
  · rw [affineBatch, Procedure.map_output_integral _ _ _ _ _ _ hg]
    change (∫ z, ‖d - (α / (n : ℝ)) • z.1-center‖ ^ 2 ∂(O.sum n).law (q,h)) ≤ _
    simp_rw [he]
    rw [integral_const_mul]
    have hb := mul_le_mul_of_nonneg_left hs.2 (sq_nonneg (α / (n : ℝ)))
    rw [mul_add, hmean] at hb
    have hnvar : (α / (n : ℝ)) ^ 2 * ((n : ℝ) * σ ^ 2) =
        α ^ 2 * σ ^ 2 / (n : ℝ) := by field_simp; ring
    rwa [hnvar] at hb

end Smoothness2601.InnerBatch
