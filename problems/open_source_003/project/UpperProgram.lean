import UpperQueryLedger
import UpperSeed
import UpperOptimization
import ScalarClipping

/-!
The actual paired-query algorithm, reconstructed from its paid transcript.
No basis-goodness test or instance-dependent choice occurs in this program.
-/

open MeasureTheory Metric Set
open scoped BigOperators

namespace Task006.Full

theorem scalarClip_eq_max_min {b : ℝ} (hb : 0 ≤ b) (x : ℝ) :
    scalarClip b x = max (-b) (min x b) := by
  by_cases hx : x = 0
  · simp [scalarClip, hx, hb, neg_nonpos.mpr hb]
  · rcases lt_or_gt_of_ne hx with hn | hp
    · have hxb : x ≤ b := le_trans hn.le hb
      simp only [scalarClip, sign_neg hn, abs_of_neg hn]
      simp only [SignType.coe_neg, SignType.coe_one, neg_one_mul, min_eq_left hxb]
      by_cases hcase : -x ≤ b
      · rw [min_eq_left hcase, neg_neg, max_eq_right (by linarith)]
      · rw [min_eq_right (le_of_not_ge hcase), max_eq_left (by linarith)]
    · have hmin : 0 ≤ min x b := le_min hp.le hb
      simp only [scalarClip, sign_pos hp, SignType.coe_one, one_mul, abs_of_pos hp]
      exact (max_eq_right (le_trans (neg_nonpos.mpr hb) hmin)).symm

theorem scalarClip_continuous {b : ℝ} (hb : 0 ≤ b) : Continuous (scalarClip b) := by
  have heq : scalarClip b = fun x => max (-b) (min x b) := funext (scalarClip_eq_max_min hb)
  rw [heq]
  fun_prop

/-- Public numerical parameters; the final assembly supplies the paper's
specific formulas. Positivity and the inner-ball domain are checked here. -/
structure UpperProgramParameters where
  R : ℝ
  ρ : ℝ
  δ : ℝ
  η : ℝ
  b : ℝ
  rho_nonneg : 0 ≤ ρ
  delta_pos : 0 < δ
  eta_pos : 0 < η
  clip_nonneg : 0 ≤ b
  inner_nonneg : 0 ≤ R - (ρ + δ)

def upperReplyCount (d T : ℕ) : ℕ := 2 * d * T

/-- Totalized lookup is used only to define a function on all finite
transcripts. Every secant used in a valid round has both indices in range. -/
def transcriptValue {N : ℕ} (h : Transcript N) (k : ℕ) : ℝ :=
  if hk : k < N then h ⟨k, hk⟩ else 0

theorem transcriptValue_measurable {N : ℕ} (k : ℕ) :
    Measurable (fun h : Transcript N => transcriptValue h k) := by
  by_cases hk : k < N
  · simpa only [transcriptValue, dif_pos hk] using measurable_pi_apply (⟨k, hk⟩ : Fin N)
  · simp only [transcriptValue, dif_neg hk]
    exact measurable_const

theorem transcriptValue_eq_of_past {N B : ℕ} {h h' : Transcript N}
    (hh : ∀ i : Fin N, i.val < B → h i = h' i) {k : ℕ} (hk : k < B) :
    transcriptValue h k = transcriptValue h' k := by
  by_cases hkN : k < N
  · simp only [transcriptValue, dif_pos hkN]
    exact hh ⟨k, hkN⟩ hk
  · simp only [transcriptValue, dif_neg hkN]

noncomputable def upperDirection {d T : ℕ} (P : UpperProgramParameters)
    (block : UpperBlockSeed d) (h : Transcript (upperReplyCount d T)) (t : ℕ) : Space d :=
  ∑ i : Fin d, scalarClip P.b
    ((transcriptValue h (2 * (t * d + i.val) + 1) -
      transcriptValue h (2 * (t * d + i.val))) / (2 * P.δ)) •
        Task006.HaarRebalancing.column block.1 i

noncomputable def upperIterate {d T : ℕ} (P : UpperProgramParameters)
    (seed : UpperSeed d T) (h : Transcript (upperReplyCount d T)) : ℕ → Space d
  | 0 => 0
  | t + 1 => if ht : t < T then
      ballProj (P.R - (P.ρ + P.δ)) P.inner_nonneg
        (upperIterate P seed h t - P.η • upperDirection P (seed ⟨t, ht⟩) h t)
    else upperIterate P seed h t

theorem upperIterate_norm_le {d T : ℕ} (P : UpperProgramParameters)
    (seed : UpperSeed d T) (h : Transcript (upperReplyCount d T)) (t : ℕ) :
    ‖upperIterate P seed h t‖ ≤ P.R - (P.ρ + P.δ) := by
  induction t with
  | zero => simpa only [upperIterate, norm_zero] using P.inner_nonneg
  | succ t ih =>
    rw [upperIterate]
    split_ifs with ht
    · simpa only [mem_closedBall, dist_zero_right] using
        ballProj_mem (P.R - (P.ρ + P.δ)) P.inner_nonneg
          (upperIterate P seed h t - P.η • upperDirection P (seed ⟨t, ht⟩) h t)
    · exact ih

theorem upperDirection_past {d T : ℕ} (P : UpperProgramParameters)
    (block : UpperBlockSeed d) {h h' : Transcript (upperReplyCount d T)} (t : ℕ)
    (hh : ∀ i : Fin (upperReplyCount d T), i.val < 2 * d * (t + 1) → h i = h' i) :
    upperDirection P block h t = upperDirection P block h' t := by
  unfold upperDirection
  apply Finset.sum_congr rfl
  intro i _
  have hk0 : 2 * (t * d + i.val) < 2 * d * (t + 1) := by nlinarith [i.isLt]
  have hk1 : 2 * (t * d + i.val) + 1 < 2 * d * (t + 1) := by nlinarith [i.isLt]
  rw [transcriptValue_eq_of_past hh hk0, transcriptValue_eq_of_past hh hk1]

theorem upperIterate_past {d T : ℕ} (P : UpperProgramParameters)
    (seed : UpperSeed d T) {h h' : Transcript (upperReplyCount d T)} (t : ℕ)
    (hh : ∀ i : Fin (upperReplyCount d T), i.val < 2 * d * t → h i = h' i) :
    upperIterate P seed h t = upperIterate P seed h' t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    have hmono : 2 * d * t ≤ 2 * d * (t + 1) := Nat.mul_le_mul_left _ (Nat.le_succ t)
    have hprev : ∀ i : Fin (upperReplyCount d T), i.val < 2 * d * t → h i = h' i :=
      fun i hi => hh i (lt_of_lt_of_le hi hmono)
    rw [upperIterate, upperIterate]
    split_ifs with ht
    · rw [ih hprev, upperDirection_past P (seed ⟨t, ht⟩) t hh]
    · exact ih hprev

theorem upperDirection_measurable {d T : ℕ} (P : UpperProgramParameters) (t : Fin T) :
    Measurable (fun sh : UpperSeed d T × Transcript (upperReplyCount d T) =>
      upperDirection P (sh.1 t) sh.2 t.val) := by
  unfold upperDirection
  apply Finset.measurable_sum
  intro i _
  have hp : Measurable (fun sh : UpperSeed d T × Transcript (upperReplyCount d T) =>
      transcriptValue sh.2 (2 * (t.val * d + i.val) + 1)) :=
    (transcriptValue_measurable (N := upperReplyCount d T)
      (2 * (t.val * d + i.val) + 1)).comp measurable_snd
  have hm : Measurable (fun sh : UpperSeed d T × Transcript (upperReplyCount d T) =>
      transcriptValue sh.2 (2 * (t.val * d + i.val))) :=
    (transcriptValue_measurable (N := upperReplyCount d T)
      (2 * (t.val * d + i.val))).comp measurable_snd
  have hs := ((scalarClip_continuous P.clip_nonneg).measurable).comp ((hp.sub hm).div_const (2 * P.δ))
  have hblock : Measurable (fun sh : UpperSeed d T × Transcript (upperReplyCount d T) => sh.1 t) :=
    (measurable_pi_apply t).comp measurable_fst
  have hcolumn := (Task006.HaarRebalancing.measurable_column i).comp (measurable_fst.comp hblock)
  exact hs.smul hcolumn

theorem upperIterate_measurable {d T : ℕ} (P : UpperProgramParameters) (t : ℕ) :
    Measurable (fun sh : UpperSeed d T × Transcript (upperReplyCount d T) =>
      upperIterate P sh.1 sh.2 t) := by
  induction t with
  | zero => exact measurable_const
  | succ t ih =>
    by_cases ht : t < T
    · simp only [upperIterate, dif_pos ht]
      exact (ballProj_lipschitz P.inner_nonneg).continuous.measurable.comp
        (ih.sub ((upperDirection_measurable P ⟨t, ht⟩).const_smul P.η))
    · simpa only [upperIterate, dif_neg ht] using ih

def upperRound {d T : ℕ} (hd : 0 < d) (n : Fin (upperReplyCount d T)) : Fin T :=
  ⟨n.val / (2 * d), (Nat.div_lt_iff_lt_mul (by omega : 0 < 2 * d)).mpr (by
    have hn := n.isLt
    unfold upperReplyCount at hn
    nlinarith)⟩

def upperCoordinate {d T : ℕ} (hd : 0 < d) (n : Fin (upperReplyCount d T)) : Fin d :=
  ⟨(n.val / 2) % d, Nat.mod_lt _ hd⟩

noncomputable def upperQueryPoint {d T : ℕ} (P : UpperProgramParameters) (hd : 0 < d)
    (n : Fin (upperReplyCount d T)) (seed : UpperSeed d T)
    (h : Transcript (upperReplyCount d T)) : Space d :=
  upperIterate P seed h (upperRound hd n).val +
    P.ρ • ((seed (upperRound hd n)).2 (upperCoordinate hd n)).val +
    (if n.val % 2 = 0 then -P.δ else P.δ) •
      Task006.HaarRebalancing.column (seed (upperRound hd n)).1 (upperCoordinate hd n)

theorem upperQueryPoint_past {d T : ℕ} (P : UpperProgramParameters) (hd : 0 < d)
    (n : Fin (upperReplyCount d T)) (seed : UpperSeed d T)
    {h h' : Transcript (upperReplyCount d T)}
    (hh : ∀ i : Fin (upperReplyCount d T), i.val < n.val → h i = h' i) :
    upperQueryPoint P hd n seed h = upperQueryPoint P hd n seed h' := by
  have hb : 2 * d * (upperRound hd n).val ≤ n.val := by
    simpa only [upperRound, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
      using Nat.div_mul_le_self n.val (2 * d)
  unfold upperQueryPoint
  rw [upperIterate_past P seed (upperRound hd n).val
    (fun i hi => hh i (lt_of_lt_of_le hi hb))]

theorem upperQueryPoint_measurable {d T : ℕ} (P : UpperProgramParameters) (hd : 0 < d)
    (n : Fin (upperReplyCount d T)) :
    Measurable (fun sh : UpperSeed d T × Transcript (upperReplyCount d T) =>
      upperQueryPoint P hd n sh.1 sh.2) := by
  have hblock : Measurable (fun sh : UpperSeed d T × Transcript (upperReplyCount d T) =>
      sh.1 (upperRound hd n)) := (measurable_pi_apply _).comp measurable_fst
  have hu := measurable_subtype_coe.comp
    ((measurable_pi_apply (upperCoordinate hd n)).comp (measurable_snd.comp hblock))
  have hq := (Task006.HaarRebalancing.measurable_column (upperCoordinate hd n)).comp
    (measurable_fst.comp hblock)
  exact ((upperIterate_measurable P (upperRound hd n).val).add (hu.const_smul P.ρ)).add
    (hq.const_smul (if n.val % 2 = 0 then -P.δ else P.δ))

theorem upperQueryPoint_norm_le {d T : ℕ} (P : UpperProgramParameters) (hd : 0 < d)
    (n : Fin (upperReplyCount d T)) (seed : UpperSeed d T)
    (h : Transcript (upperReplyCount d T)) : ‖upperQueryPoint P hd n seed h‖ ≤ P.R := by
  have hx := upperIterate_norm_le P seed h (upperRound hd n).val
  have hu := upper_seed_smoothing_legal d T seed (upperRound hd n) (upperCoordinate hd n)
  have hq := (Task006.HaarRebalancing.orthonormal_column
    (seed (upperRound hd n)).1).norm_eq_one (upperCoordinate hd n)
  have hru : ‖P.ρ • ((seed (upperRound hd n)).2 (upperCoordinate hd n)).val‖ ≤ P.ρ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg P.rho_nonneg]
    nlinarith [P.rho_nonneg]
  have hsign : |if n.val % 2 = 0 then -P.δ else P.δ| = P.δ := by
    split_ifs <;> simp [P.delta_pos.le]
  have hdq : ‖(if n.val % 2 = 0 then -P.δ else P.δ) •
      Task006.HaarRebalancing.column (seed (upperRound hd n)).1 (upperCoordinate hd n)‖ = P.δ := by
    rw [norm_smul, Real.norm_eq_abs, hsign, hq, mul_one]
  unfold upperQueryPoint
  have h₁ := norm_add_le (upperIterate P seed h (upperRound hd n).val)
    (P.ρ • ((seed (upperRound hd n)).2 (upperCoordinate hd n)).val)
  have h₂ := norm_add_le
    (upperIterate P seed h (upperRound hd n).val +
      P.ρ • ((seed (upperRound hd n)).2 (upperCoordinate hd n)).val)
    ((if n.val % 2 = 0 then -P.δ else P.δ) •
      Task006.HaarRebalancing.column (seed (upperRound hd n)).1 (upperCoordinate hd n))
  linarith

noncomputable def upperOutput {d T : ℕ} (P : UpperProgramParameters) (seed : UpperSeed d T)
    (h : Transcript (upperReplyCount d T)) : Space d :=
  iterateAverage (upperIterate P seed h) T

theorem upperOutput_measurable {d T : ℕ} (P : UpperProgramParameters) :
    Measurable (fun sh : UpperSeed d T × Transcript (upperReplyCount d T) =>
      upperOutput P sh.1 sh.2) := by
  unfold upperOutput iterateAverage
  exact ((Finset.range T).measurable_sum
    (fun t _ => upperIterate_measurable (d := d) (T := T) P t)).const_smul (T : ℝ)⁻¹

theorem upperOutput_norm_le {d T : ℕ} (P : UpperProgramParameters) (hT : 0 < T)
    (seed : UpperSeed d T) (h : Transcript (upperReplyCount d T)) :
    ‖upperOutput P seed h‖ ≤ P.R - (P.ρ + P.δ) := by
  have hTreal : 0 < (T : ℝ) := by exact_mod_cast hT
  unfold upperOutput iterateAverage
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr hTreal.le)]
  calc
    _ ≤ (T : ℝ)⁻¹ * ∑ t ∈ Finset.range T, ‖upperIterate P seed h t‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (inv_nonneg.mpr hTreal.le)
    _ ≤ (T : ℝ)⁻¹ * ∑ _t ∈ Finset.range T, (P.R - (P.ρ + P.δ)) :=
      mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum (fun t _ => upperIterate_norm_le P seed h t))
        (inv_nonneg.mpr hTreal.le)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      field_simp [hTreal.ne']
      <;> ring

noncomputable def upperPairedProgram {d T : ℕ} (P : UpperProgramParameters) (hd : 0 < d) :
    PairedQueryProgram d (upperReplyCount d T) (UpperSeed d T) where
  point := upperQueryPoint P hd
  point_measurable := upperQueryPoint_measurable P hd
  point_past n seed _ _ hh := upperQueryPoint_past P hd n seed hh
  postprocess := upperOutput P
  postprocess_measurable := upperOutput_measurable P

theorem upperProgram_execution_legal {d T : ℕ} (P : UpperProgramParameters) (hd : 0 < d) (hT : 0 < T)
    {Ω : Type*} (F : Space d → Ω → ℝ) (tape : ℕ → Ω) (seed : UpperSeed d T) :
    (upperPairedProgram P hd).toAlgorithm.executionLegal F tape seed P.R := by
  have hR : 0 ≤ P.R := by linarith [P.inner_nonneg, P.rho_nonneg, P.delta_pos]
  apply PairedQueryProgram.execution_legal
  · intro n s h
    change dist (upperQueryPoint P hd n s h) 0 ≤ 2 * P.R
    rw [dist_zero_right]
    linarith [upperQueryPoint_norm_le P hd n s h]
  · intro s h
    change dist (upperOutput P s h) 0 ≤ P.R
    rw [dist_zero_right]
    linarith [upperOutput_norm_le P hT s h, P.rho_nonneg, P.delta_pos]

#print axioms scalarClip_eq_max_min
#print axioms upperIterate_norm_le
#print axioms upperIterate_past
#print axioms upperIterate_measurable
#print axioms upperQueryPoint_past
#print axioms upperProgram_execution_legal

end Task006.Full
