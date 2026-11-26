import SampleReuse.IntegralDriftCharging
import SecondOrder.PredictableMartingaleReindex
import SecondOrder.BinaryEnergy

/-! Truncated drift charging at bounded stopping-time checkpoints.
Stopping events imply predictability of the interval indicators, from which
the martingale isometry and integrability are derived. -/

open MeasureTheory Filter SecondOrder
open scoped BigOperators InnerProductSpace Classical

namespace SampleReuse
noncomputable section

def intervalIncrement {Ω E : Type*} [Zero E] {T : ℕ}
    (s t : Ω → ℕ) (u : Fin T → Ω → E) (k : Fin T) (w : Ω) : E :=
  if s w ≤ k.val ∧ k.val < t w then u k w else 0

theorem stopping_interval_predictable {Ω : Type*} (past : ℕ → MeasurableSpace Ω)
    (s t : Ω → ℕ)
    (hs : ∀ k, MeasurableSet[past k] {w | s w ≤ k})
    (ht : ∀ k, MeasurableSet[past k] {w | t w ≤ k}) (k : ℕ) :
    MeasurableSet[past k] {w | s w ≤ k ∧ k < t w} := by
  have hnot : MeasurableSet[past k] {w | k < t w} := by
    simpa only [Set.compl_setOf, not_le] using (ht k).compl
  exact (hs k).inter hnot

theorem intervalIncrement_eq_indicator {Ω E : Type*} [Zero E] {T : ℕ}
    (s t : Ω → ℕ) (u : Fin T → Ω → E) (k : Fin T) :
    intervalIncrement s t u k = {w | s w ≤ k.val ∧ k.val < t w}.indicator (u k) := by
  funext w
  by_cases h : s w ≤ k.val ∧ k.val < t w <;> simp [intervalIncrement, Set.indicator, h]

variable {Ω E : Type*} {m₀ : MeasurableSpace Ω} [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [CompleteSpace E] {μ : Measure Ω} [IsProbabilityMeasure μ]

theorem stopped_interval_orthogonal {T : ℕ} (s t : Ω → ℕ)
    (past : ℕ → MeasurableSpace Ω) (hp : ∀ k, past k ≤ m₀) (hmono : Monotone past)
    (hs : ∀ k, MeasurableSet[past k] {w | s w ≤ k})
    (ht : ∀ k, MeasurableSet[past k] {w | t w ≤ k})
    (z : Fin T → Ω → E) (hz : ∀ k, MemLp (z k) 2 μ)
    (hadapt : ∀ i j, i < j → AEStronglyMeasurable[past j.val] (z i) μ)
    (hzero : ∀ j, μ[z j | past j.val] =ᵐ[μ] (fun _ => 0))
    (i j : Fin T) (hne : i ≠ j) :
    (∫ w, ⟪intervalIncrement s t z i w, intervalIncrement s t z j w⟫_ℝ ∂μ) = 0 := by
  let label (k : Fin T) (w : Ω) : Bool := decide (s w ≤ k.val ∧ k.val < t w)
  have hl (r : Bool) (k : Fin T) : MeasurableSet[past k.val] {w | label k w = r} := by
    have h := stopping_interval_predictable past s t hs ht k.val
    cases r
    · simpa [label, Set.compl_setOf] using h.compl
    · simpa [label] using h
  have hcross (i j : Fin T) (hij : i < j) := selectedMartingale_cross_lt z label
    (fun k => past k.val) (fun k => hp k.val) (fun _ _ h => hmono h) hz hadapt hzero hl
    true true i j hij
  rcases lt_or_gt_of_ne hne with hij | hij
  · simpa [selectedMartingaleIncrement, label, intervalIncrement] using hcross i j hij
  · simpa [selectedMartingaleIncrement, label, intervalIncrement, real_inner_comm] using hcross j i hij

omit [InnerProductSpace ℝ E] [CompleteSpace E] [IsProbabilityMeasure μ] in
theorem stopped_increment_integrable {T : ℕ} (s t : Ω → ℕ)
    (past : ℕ → MeasurableSpace Ω) (hp : ∀ k, past k ≤ m₀)
    (hs : ∀ k, MeasurableSet[past k] {w | s w ≤ k})
    (ht : ∀ k, MeasurableSet[past k] {w | t w ≤ k})
    (u : Fin T → Ω → E) (hu : ∀ k, Integrable (u k) μ) (k : Fin T) :
    Integrable (intervalIncrement s t u k) μ := by
  rw [intervalIncrement_eq_indicator]
  exact (hu k).indicator (hp k.val _ (stopping_interval_predictable past s t hs ht k.val))

omit [InnerProductSpace ℝ E] [CompleteSpace E] [IsProbabilityMeasure μ] in
theorem stopped_increment_memLp {T : ℕ} (s t : Ω → ℕ)
    (past : ℕ → MeasurableSpace Ω) (hp : ∀ k, past k ≤ m₀)
    (hs : ∀ k, MeasurableSet[past k] {w | s w ≤ k})
    (ht : ∀ k, MeasurableSet[past k] {w | t w ≤ k})
    (u : Fin T → Ω → E) (hu : ∀ k, MemLp (u k) 2 μ) (k : Fin T) :
    MemLp (intervalIncrement s t u k) 2 μ := by
  rw [intervalIncrement_eq_indicator]
  exact (hu k).indicator (hp k.val _ (stopping_interval_predictable past s t hs ht k.val))

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
theorem stopped_interval_telescopes {T : ℕ} (s t : Ω → ℕ)
    (hst : ∀ w, s w ≤ t w) (hcap : ∀ w, t w ≤ T)
    (x : Ω → ℕ → E) (a z : Fin T → Ω → E)
    (hx : ∀ w k, x w (k.val + 1) - x w k.val = a k w + z k w) (w : Ω) :
    (∑ k, (intervalIncrement s t a k w + intervalIncrement s t z k w)) =
      x w (t w) - x w (s w) := by
  have he : (∑ k : Fin T, (intervalIncrement s t a k w + intervalIncrement s t z k w)) =
      ∑ k ∈ Finset.Ico (s w) (t w), (x w (k + 1) - x w k) := by
    have hinc (k : Fin T) : intervalIncrement s t a k w + intervalIncrement s t z k w =
        if s w ≤ k.val ∧ k.val < t w then x w (k.val + 1) - x w k.val else 0 := by
      by_cases h : s w ≤ k.val ∧ k.val < t w <;> simp [intervalIncrement, h, hx]
    simp_rw [hinc]
    rw [← Finset.sum_filter]
    apply Finset.sum_bij (fun k _ => k.val)
    · intro k hk
      exact Finset.mem_Ico.mpr (Finset.mem_filter.mp hk).2
    · intro k _ j _ hkj
      exact Fin.ext hkj
    · intro k hk
      have hki := Finset.mem_Ico.mp hk
      exact ⟨⟨k, hki.2.trans_le (hcap w)⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hki⟩, rfl⟩
    · intro k hk
      rfl
  rw [he]
  exact Finset.sum_Ico_sub (x w) (hst w)

/-- One bounded stopping interval, with no orthogonality postulate for the
selected increments. Its isometry follows from the original filtration. -/
theorem integral_stopped_interval {T : ℕ} (s t : Ω → ℕ)
    (hst : ∀ w, s w ≤ t w) (hcap : ∀ w, t w ≤ T)
    (past : ℕ → MeasurableSpace Ω) (hp : ∀ k, past k ≤ m₀) (hmono : Monotone past)
    (hs : ∀ k, MeasurableSet[past k] {w | s w ≤ k})
    (ht : ∀ k, MeasurableSet[past k] {w | t w ≤ k})
    (x : Ω → ℕ → E) (a z : Fin T → Ω → E)
    (hx : ∀ w k, x w (k.val + 1) - x w k.val = a k w + z k w)
    (ha : ∀ k, Integrable (a k) μ) (hz : ∀ k, MemLp (z k) 2 μ)
    (hadapt : ∀ i j, i < j → AEStronglyMeasurable[past j.val] (z i) μ)
    (hzero : ∀ j, μ[z j | past j.val] =ᵐ[μ] (fun _ => 0))
    {σ L : ℝ} (hσ : 0 ≤ σ) (hL : 0 ≤ L) :
    Integrable (fun w => min (σ ^ 2) (L ^ 2 * ‖x w (t w) - x w (s w)‖ ^ 2)) μ ∧
    (∫ w, min (σ ^ 2) (L ^ 2 * ‖x w (t w) - x w (s w)‖ ^ 2) ∂μ) ≤
      2 * σ * L * (∫ w, ∑ k, ‖intervalIncrement s t a k w‖ ∂μ) +
      2 * L ^ 2 * (∫ w, ∑ k, ‖intervalIncrement s t z k w‖ ^ 2 ∂μ) := by
  have hA := stopped_increment_integrable s t past hp hs ht a ha
  have hZ := stopped_increment_memLp s t past hp hs ht z hz
  have hZ1 (k) := (hZ k).integrable (show (1 : ENNReal) ≤ 2 by norm_num)
  have hZ2 (k) := (memLp_two_iff_integrable_sq_norm (hZ k).1).mp (hZ k)
  have he := stopped_interval_telescopes s t hst hcap x a z hx
  have hsum := integrable_finset_sum Finset.univ (fun k _ => (hA k).add (hZ1 k))
  have hi := integrable_truncated_norm hsum.aestronglyMeasurable σ L
  simp only [Pi.add_apply] at hi
  simp_rw [he] at hi
  refine ⟨hi, ?_⟩
  have hb := integral_truncated_interval Finset.univ (intervalIncrement s t a)
    (intervalIncrement s t z) hσ hL (fun k _ => hA k) (fun k _ => hZ1 k)
    (fun k _ => hZ2 k) (fun i _ j _ hne =>
      stopped_interval_orthogonal s t past hp hmono hs ht z hz hadapt hzero i j hne)
  simp_rw [he] at hb
  rw [integral_finset_sum Finset.univ (fun k _ => (hA k).norm),
    integral_finset_sum Finset.univ (fun k _ => hZ2 k)]
  exact hb

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
theorem interval_overlap_charge {ι : Type*} [Fintype ι] {T : ℕ}
    (s t : ι → Ω → ℕ) (depth : ℕ) (w : Ω) (v : Fin T → ℝ)
    (hv : ∀ k, 0 ≤ v k)
    (hdepth : ∀ k : Fin T,
      (Finset.univ.filter (fun i => s i w ≤ k.val ∧ k.val < t i w)).card ≤ depth) :
    (∑ i, ∑ k : Fin T, if s i w ≤ k.val ∧ k.val < t i w then v k else 0) ≤
      (depth : ℝ) * ∑ k, v k := by
  let I (i : ι) := Finset.univ.filter (fun k : Fin T => s i w ≤ k.val ∧ k.val < t i w)
  have hi (k : Fin T) : (Finset.univ.filter (fun i => k ∈ I i)).card ≤ depth := by
    simpa only [I, Finset.mem_filter, Finset.mem_univ, true_and] using hdepth k
  simpa only [I, Finset.sum_filter] using bounded_overlap_sum I depth hi v hv

theorem integral_stopped_overlap {ι : Type*} [Fintype ι] {T : ℕ}
    (s t : ι → Ω → ℕ) (depth : ℕ)
    (hst : ∀ i w, s i w ≤ t i w) (hcap : ∀ i w, t i w ≤ T)
    (past : ℕ → MeasurableSpace Ω) (hp : ∀ k, past k ≤ m₀) (hmono : Monotone past)
    (hs : ∀ i k, MeasurableSet[past k] {w | s i w ≤ k})
    (ht : ∀ i k, MeasurableSet[past k] {w | t i w ≤ k})
    (hdepth : ∀ w (k : Fin T),
      (Finset.univ.filter (fun i => s i w ≤ k.val ∧ k.val < t i w)).card ≤ depth)
    (x : Ω → ℕ → E) (a z : Fin T → Ω → E)
    (hx : ∀ w k, x w (k.val + 1) - x w k.val = a k w + z k w)
    (ha : ∀ k, Integrable (a k) μ) (hz : ∀ k, MemLp (z k) 2 μ)
    (hadapt : ∀ i j, i < j → AEStronglyMeasurable[past j.val] (z i) μ)
    (hzero : ∀ j, μ[z j | past j.val] =ᵐ[μ] (fun _ => 0))
    {σ L : ℝ} (hσ : 0 ≤ σ) (hL : 0 ≤ L) :
    (∫ w, ∑ i, min (σ ^ 2) (L ^ 2 * ‖x w (t i w) - x w (s i w)‖ ^ 2) ∂μ) ≤
      2 * (depth : ℝ) * (σ * L * (∫ w, ∑ k, ‖a k w‖ ∂μ) +
        L ^ 2 * (∫ w, ∑ k, ‖z k w‖ ^ 2 ∂μ)) := by
  have hnode (i : ι) := integral_stopped_interval (s i) (t i) (hst i) (hcap i)
    past hp hmono (hs i) (ht i) x a z hx ha hz hadapt hzero hσ hL
  have hA (i : ι) (k : Fin T) :=
    (stopped_increment_integrable (s i) (t i) past hp (hs i) (ht i) a ha k).norm
  have hZ (i : ι) (k : Fin T) := stopped_increment_memLp (s i) (t i) past hp (hs i) (ht i) z hz k
  have hZ2 (i : ι) (k : Fin T) := (memLp_two_iff_integrable_sq_norm (hZ i k).1).mp (hZ i k)
  have hAD (i : ι) := integrable_finset_sum Finset.univ (fun k _ => hA i k)
  have hZV (i : ι) := integrable_finset_sum Finset.univ (fun k _ => hZ2 i k)
  have hD := integrable_finset_sum Finset.univ (fun k _ => (ha k).norm)
  have hV := integrable_finset_sum Finset.univ (fun k _ =>
    (memLp_two_iff_integrable_sq_norm (hz k).1).mp (hz k))
  have hpointD (w : Ω) :
      (∑ i, ∑ k, ‖intervalIncrement (s i) (t i) a k w‖) ≤ (depth : ℝ) * ∑ k, ‖a k w‖ := by
    have hn (i : ι) (k : Fin T) : ‖intervalIncrement (s i) (t i) a k w‖ =
        if s i w ≤ k.val ∧ k.val < t i w then ‖a k w‖ else 0 := by
      unfold intervalIncrement
      split_ifs <;> simp
    simp_rw [hn]
    exact interval_overlap_charge s t depth w _ (fun k => norm_nonneg _) (hdepth w)
  have hpointV (w : Ω) :
      (∑ i, ∑ k, ‖intervalIncrement (s i) (t i) z k w‖ ^ 2) ≤
        (depth : ℝ) * ∑ k, ‖z k w‖ ^ 2 := by
    have hn (i : ι) (k : Fin T) : ‖intervalIncrement (s i) (t i) z k w‖ ^ 2 =
        if s i w ≤ k.val ∧ k.val < t i w then ‖z k w‖ ^ 2 else 0 := by
      unfold intervalIncrement
      split_ifs <;> simp
    simp_rw [hn]
    exact interval_overlap_charge s t depth w _ (fun k => sq_nonneg _) (hdepth w)
  have hDb := integral_mono (integrable_finset_sum Finset.univ (fun i _ => hAD i))
    (hD.const_mul (depth : ℝ)) hpointD
  have hVb := integral_mono (integrable_finset_sum Finset.univ (fun i _ => hZV i))
    (hV.const_mul (depth : ℝ)) hpointV
  rw [integral_finset_sum Finset.univ (fun i _ => hAD i), integral_const_mul] at hDb
  rw [integral_finset_sum Finset.univ (fun i _ => hZV i), integral_const_mul] at hVb
  rw [integral_finset_sum Finset.univ (fun i _ => (hnode i).1)]
  have hb := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => (hnode i).2)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hb
  nlinarith [mul_le_mul_of_nonneg_left hDb (by positivity : 0 ≤ 2 * σ * L),
    mul_le_mul_of_nonneg_left hVb (by positivity : 0 ≤ 2 * L ^ 2)]

theorem stopped_dyadic_overlap (M depth : ℕ) (τ : ℕ → Ω → ℕ)
    (hmono : ∀ w, Monotone (fun j => τ j w)) (w : Ω) (k : ℕ) :
    (Finset.univ.filter (fun i : completedNodes depth M =>
      τ (nodeLeft i.val) w ≤ k ∧ k < τ (nodeRight i.val) w)).card ≤ depth := by
  let S := Finset.univ.filter (fun i : completedNodes depth M =>
    τ (nodeLeft i.val) w ≤ k ∧ k < τ (nodeRight i.val) w)
  have hinj : (S : Set (completedNodes depth M)).InjOn (fun i => i.val.1) := by
    intro i hi j hj he
    change i.val.1 = j.val.1 at he
    have hi' := (Finset.mem_filter.mp hi).2
    have hj' := (Finset.mem_filter.mp hj).2
    apply Subtype.ext
    apply Prod.ext he
    rcases lt_trichotomy i.val.2 j.val.2 with hij | hij | hij
    · have horder : nodeRight i.val ≤ nodeLeft j.val := by
        dsimp [nodeRight, nodeLeft]
        rw [he]
        exact Nat.mul_le_mul_right _ (Nat.succ_le_of_lt hij)
      have ht : τ (nodeRight i.val) w ≤ τ (nodeLeft j.val) w := hmono w horder
      omega
    · exact hij
    · have horder : nodeRight j.val ≤ nodeLeft i.val := by
        dsimp [nodeRight, nodeLeft]
        rw [he]
        exact Nat.mul_le_mul_right _ (Nat.succ_le_of_lt hij)
      have ht : τ (nodeRight j.val) w ≤ τ (nodeLeft i.val) w := hmono w horder
      omega
  have hc := Finset.card_le_card_of_injOn (s := S) (t := Finset.univ)
    (fun i => i.val.1) (fun _ _ => Finset.mem_univ _) hinj
  simpa only [Finset.card_univ, Fintype.card_fin] using hc

/-- Bounded stopping-time checkpoints with repeated terminal checkpoints
allowed. The dyadic overlap and stopped martingale isometry are both proved.
Every binary-ancestor edge is one of these completed dyadic intervals. -/
theorem stopped_checkpoint_charging (T M depth : ℕ) (τ : ℕ → Ω → ℕ)
    (hτmono : ∀ w, Monotone (fun j => τ j w)) (hcap : ∀ w, τ M w ≤ T)
    (past : ℕ → MeasurableSpace Ω) (hp : ∀ k, past k ≤ m₀) (hmono : Monotone past)
    (hτ : ∀ j k, MeasurableSet[past k] {w | τ j w ≤ k})
    (x : Ω → ℕ → E) (a z : Fin T → Ω → E)
    (hx : ∀ w k, x w (k.val + 1) - x w k.val = a k w + z k w)
    (ha : ∀ k, Integrable (a k) μ) (hz : ∀ k, MemLp (z k) 2 μ)
    (hadapt : ∀ i j, i < j → AEStronglyMeasurable[past j.val] (z i) μ)
    (hzero : ∀ j, μ[z j | past j.val] =ᵐ[μ] (fun _ => 0))
    {σ L : ℝ} (hσ : 0 ≤ σ) (hL : 0 ≤ L) :
    (∫ w, ∑ i : completedNodes depth M,
      min (σ ^ 2) (L ^ 2 * ‖x w (τ (nodeRight i.val) w) - x w (τ (nodeLeft i.val) w)‖ ^ 2) ∂μ) ≤
      2 * (depth : ℝ) * (σ * L * (∫ w, ∑ k, ‖a k w‖ ∂μ) +
        L ^ 2 * (∫ w, ∑ k, ‖z k w‖ ^ 2 ∂μ)) := by
  apply integral_stopped_overlap (fun i : completedNodes depth M => τ (nodeLeft i.val))
    (fun i : completedNodes depth M => τ (nodeRight i.val)) depth
    (fun i w => hτmono w (nodeLeft_lt_right i.val).le)
    (fun i w => (hτmono w ((mem_completedNodes i.val).mp i.property)).trans (hcap w))
    past hp hmono (fun i k => hτ _ k) (fun i k => hτ _ k)
    (fun w k => stopped_dyadic_overlap M depth τ hτmono w k.val)
    x a z hx ha hz hadapt hzero hσ hL

/-- Selection may depend on the whole trajectory. Nonnegative domination is
applied before integration; no conditional independence on selection is used.
This permits retaining only binary-ancestor edges and actual checkpoints. -/
theorem selected_stopped_checkpoint_charging (T M depth : ℕ) (τ : ℕ → Ω → ℕ)
    (hτmono : ∀ w, Monotone (fun j => τ j w)) (hcap : ∀ w, τ M w ≤ T)
    (past : ℕ → MeasurableSpace Ω) (hp : ∀ k, past k ≤ m₀) (hmono : Monotone past)
    (hτ : ∀ j k, MeasurableSet[past k] {w | τ j w ≤ k})
    (x : Ω → ℕ → E) (a z : Fin T → Ω → E)
    (hx : ∀ w k, x w (k.val + 1) - x w k.val = a k w + z k w)
    (ha : ∀ k, Integrable (a k) μ) (hz : ∀ k, MemLp (z k) 2 μ)
    (hadapt : ∀ i j, i < j → AEStronglyMeasurable[past j.val] (z i) μ)
    (hzero : ∀ j, μ[z j | past j.val] =ᵐ[μ] (fun _ => 0))
    (selected : Ω → completedNodes depth M → Prop)
    (hselected : ∀ i, MeasurableSet {w | selected w i})
    {σ L : ℝ} (hσ : 0 ≤ σ) (hL : 0 ≤ L) :
    (∫ w, ∑ i : completedNodes depth M, if selected w i then
      min (σ ^ 2) (L ^ 2 * ‖x w (τ (nodeRight i.val) w) - x w (τ (nodeLeft i.val) w)‖ ^ 2)
        else 0 ∂μ) ≤
      2 * (depth : ℝ) * (σ * L * (∫ w, ∑ k, ‖a k w‖ ∂μ) +
        L ^ 2 * (∫ w, ∑ k, ‖z k w‖ ^ 2 ∂μ)) := by
  let cost (i : completedNodes depth M) (w : Ω) :=
    min (σ ^ 2) (L ^ 2 * ‖x w (τ (nodeRight i.val) w) - x w (τ (nodeLeft i.val) w)‖ ^ 2)
  have hi (i : completedNodes depth M) : Integrable (cost i) μ :=
    (integral_stopped_interval (τ (nodeLeft i.val)) (τ (nodeRight i.val))
      (fun w => hτmono w (nodeLeft_lt_right i.val).le)
      (fun w => (hτmono w ((mem_completedNodes i.val).mp i.property)).trans (hcap w))
      past hp hmono (hτ _) (hτ _) x a z hx ha hz hadapt hzero hσ hL).1
  have hsi (i : completedNodes depth M) :
      Integrable (fun w => if selected w i then cost i w else 0) μ := by
    simpa only [Set.indicator, Set.mem_setOf_eq] using (hi i).indicator (hselected i)
  have hb : (∫ w, ∑ i : completedNodes depth M, if selected w i then cost i w else 0 ∂μ) ≤
      ∫ w, ∑ i : completedNodes depth M, cost i w ∂μ := by
    apply integral_mono (integrable_finset_sum Finset.univ (fun i _ => hsi i))
      (integrable_finset_sum Finset.univ (fun i _ => hi i))
    intro w
    apply Finset.sum_le_sum
    intro i _
    split_ifs
    · exact le_rfl
    · exact le_min (sq_nonneg σ) (by dsimp [cost]; positivity)
  exact hb.trans (stopped_checkpoint_charging T M depth τ hτmono hcap past hp hmono hτ
    x a z hx ha hz hadapt hzero hσ hL)

end
end SampleReuse
