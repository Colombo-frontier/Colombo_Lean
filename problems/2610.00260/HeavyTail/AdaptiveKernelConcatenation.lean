import HeavyTail.AdaptiveKernelOutputKernel

/-! Concatenation of actual causal policies. The second policy receives the
first policy's output as its seed; every response is still a charged fresh
call to the same unknown kernel. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace HeavyTail.AdaptiveKernel
universe u v w

namespace History
variable {Seed Seed' Reply : Type u} [MeasurableSpace Seed]
  [MeasurableSpace Seed'] [MeasurableSpace Reply]

def cast {m n : ℕ} (h : m = n) : History Seed Reply m → History Seed Reply n :=
  h ▸ id

theorem cast_measurable {m n : ℕ} (h : m = n) :
    Measurable (cast (Seed := Seed) (Reply := Reply) h) := by
  subst n
  exact measurable_id

@[simp] theorem cast_rfl (n : ℕ) :
    cast (Seed := Seed) (Reply := Reply) (rfl : n = n) = id := rfl

def mapSeed (f : Seed → Seed') : (n : ℕ) → History Seed Reply n → History Seed' Reply n
  | 0 => f
  | n + 1 => fun h => (mapSeed f n h.1, h.2)

theorem mapSeed_measurable {f : Seed → Seed'} (hf : Measurable f) (n : ℕ) :
    Measurable (mapSeed (Reply := Reply) f n) := by
  induction n with
  | zero => exact hf
  | succ n ih => exact (ih.comp measurable_fst).prodMk measurable_snd

def split (m : ℕ) : (n : ℕ) → History Seed Reply (m + n) → History (History Seed Reply m) Reply n
  | 0 => id
  | n + 1 => fun h => (split m n h.1, h.2)

theorem split_measurable (m n : ℕ) : Measurable (split (Seed := Seed) (Reply := Reply) m n) := by
  induction n with
  | zero => exact measurable_id
  | succ n ih => exact (ih.comp measurable_fst).prodMk measurable_snd

end History

namespace Policy
variable {Seed Mid Reply : Type u} {Query : Type v} {Output : Type w}
  [MeasurableSpace Seed] [MeasurableSpace Mid] [MeasurableSpace Reply]
  [MeasurableSpace Query] [MeasurableSpace Output] {m n : ℕ}

def continuationHistory (A : Policy Seed Query Reply Mid m) (k : ℕ) :
    History Seed Reply (m + k) → History Mid Reply k :=
  History.mapSeed A.output k ∘ History.split m k

theorem continuationHistory_measurable (A : Policy Seed Query Reply Mid m) (k : ℕ) :
    Measurable (A.continuationHistory k) :=
  (History.mapSeed_measurable A.output_measurable k).comp (History.split_measurable m k)

def chain (A : Policy Seed Query Reply Mid m) (B : Policy Mid Query Reply Output n) :
    Policy Seed Query Reply Output (m + n) where
  query t := if ht : t < m then A.query t else fun h =>
    B.query (t - m) (A.continuationHistory (t - m)
      (History.cast (Nat.add_sub_of_le (Nat.le_of_not_gt ht)).symm h))
  query_measurable t := by
    split_ifs with ht
    · exact A.query_measurable t
    · exact (B.query_measurable (t - m)).comp
        ((A.continuationHistory_measurable (t - m)).comp (History.cast_measurable _))
  output := B.output ∘ A.continuationHistory n
  output_measurable := B.output_measurable.comp (A.continuationHistory_measurable n)

theorem chain_query_before (A : Policy Seed Query Reply Mid m)
    (B : Policy Mid Query Reply Output n) {t : ℕ} (ht : t < m) :
    (A.chain B).query t = A.query t := by simp only [chain, dif_pos ht]

theorem chain_query_after (A : Policy Seed Query Reply Mid m)
    (B : Policy Mid Query Reply Output n) (k : ℕ) :
    (A.chain B).query (m + k) = B.query k ∘ A.continuationHistory k := by
  have aux (j : ℕ) (hj : j = k) (e : m + k = m + j) :
      (fun h => B.query j (A.continuationHistory j (History.cast e h))) =
        B.query k ∘ A.continuationHistory k := by
    subst j
    rfl
  dsimp only [chain]
  rw [dif_neg (Nat.not_lt.mpr (Nat.le_add_right m k))]
  exact aux _ (Nat.add_sub_cancel_left m k) _

theorem compProd_comap_map (μ : Measure Seed) [IsProbabilityMeasure μ]
    (K : Kernel Mid Reply) [IsMarkovKernel K] (f : Seed → Mid) (hf : Measurable f) :
    (μ.compProd (K.comap f hf)).map (fun z : Seed × Reply => (f z.1, z.2)) =
      (μ.map f).compProd K := by
  ext s hs
  have hm : Measurable (fun z : Seed × Reply => (f z.1, z.2)) :=
    (hf.comp measurable_fst).prodMk measurable_snd
  rw [Measure.map_apply hm hs, Measure.compProd_apply (hm hs),
    Measure.compProd_apply hs, lintegral_map (K.measurable_kernel_prodMk_left hs) hf]
  apply lintegral_congr
  intro x
  rfl

theorem chain_historyLaw_prefix (A : Policy Seed Query Reply Mid m)
    (B : Policy Mid Query Reply Output n) (μ : Measure Seed) (K : Kernel Query Reply)
    (t : ℕ) (ht : t ≤ m) : (A.chain B).historyLaw μ K t = A.historyLaw μ K t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [historyLaw_succ, historyLaw_succ, ih (Nat.le_trans (Nat.le_succ t) ht)]
    have hq := A.chain_query_before B (Nat.lt_of_lt_of_le (Nat.lt_succ_self t) ht)
    simp only [replyKernel, hq]

theorem chain_continuationLaw (A : Policy Seed Query Reply Mid m)
    (B : Policy Mid Query Reply Output n) (μ : Measure Seed) [IsProbabilityMeasure μ]
    (K : Kernel Query Reply) [IsMarkovKernel K] (k : ℕ) :
    ((A.chain B).historyLaw μ K (m + k)).map (A.continuationHistory k) =
      B.historyLaw (A.outputLaw μ K) K k := by
  induction k with
  | zero =>
    change ((A.chain B).historyLaw μ K m).map A.output = A.outputLaw μ K
    rw [chain_historyLaw_prefix A B μ K m le_rfl]
    rfl
  | succ k ih =>
    change (((A.chain B).historyLaw μ K (m + k)).compProd
      ((A.chain B).replyKernel K (m + k))).map
      (fun z => (A.continuationHistory k z.1, z.2)) =
        (B.historyLaw (A.outputLaw μ K) K k).compProd (B.replyKernel K k)
    have hK : (A.chain B).replyKernel K (m + k) =
        (B.replyKernel K k).comap (A.continuationHistory k) (A.continuationHistory_measurable k) := by
      simp only [replyKernel, chain_query_after]
      rfl
    rw [hK, compProd_comap_map _ _ _ (A.continuationHistory_measurable k), ih]

theorem chain_outputLaw (A : Policy Seed Query Reply Mid m)
    (B : Policy Mid Query Reply Output n) (μ : Measure Seed) [IsProbabilityMeasure μ]
    (K : Kernel Query Reply) [IsMarkovKernel K] :
    (A.chain B).outputLaw μ K = B.outputLaw (A.outputLaw μ K) K := by
  change ((A.chain B).historyLaw μ K (m + n)).map
    (B.output ∘ A.continuationHistory n) = _
  rw [← Measure.map_map B.output_measurable (A.continuationHistory_measurable n),
    chain_continuationLaw]
  rfl

theorem chain_outputLaw_kernel (A : Policy Seed Query Reply Mid m)
    (B : Policy Mid Query Reply Output n) (μ : Measure Seed) [IsProbabilityMeasure μ]
    (K : Kernel Query Reply) [IsMarkovKernel K] :
    (A.chain B).outputLaw μ K = B.outputKernel K ∘ₘ A.outputLaw μ K := by
  rw [chain_outputLaw, B.outputLaw_eq_outputKernel]

end Policy
end HeavyTail.AdaptiveKernel
