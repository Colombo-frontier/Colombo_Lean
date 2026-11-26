import SecondOrder.BlockEntryFastBound
import SecondOrder.KernelEntryDecomposition
import SecondOrder.KernelPublicEntry

open MeasureTheory ProbabilityTheory InformationTheory
open scoped Classical ENNReal BigOperators

universe u
namespace SecondOrder
noncomputable section
variable {T : ℕ} {H X S A : Type u} [MeasurableSpace H] [MeasurableSpace X]
  [MeasurableSpace S] [MeasurableSpace A]

theorem blockTargetFastSet_disjoint_unentered (active : Fin T → H → X → Prop)
    (query : ∀ n, FiniteHistory S A n → X) (Θ : Fin T → H) (j : Fin T) (cap N : ℕ) :
    Disjoint (blockTargetFastSet active query Θ j cap N)
      (finiteHistoryMapInitial Prod.snd N ⁻¹' kernelSurvivalSet (blockPreEntrySet active query Θ j) N) := by
  apply Set.disjoint_left.mpr
  intro h hf hh
  have hp := kernelSurvivalSet_subset (blockPreEntrySet active query Θ j) N hh
  have hΘ : ∀ i : Fin T, i.val<blockComparisonProgress active query Θ N (finiteHistoryMapInitial Prod.snd N h)+1 →
      Θ i=Function.update Θ j (finiteHistoryInitial N h).1 i := by
    intro i hi
    exact (Function.update_of_ne (by intro he; subst i; have := hp.1; omega) _ _).symm
  have he := blockComparisonProgress_prefix active query Θ _ N (finiteHistoryMapInitial Prod.snd N h) hΘ
  have hi := blockComparisonIndex_prefix active query Θ _ N (finiteHistoryMapInitial Prod.snd N h) hΘ
  have hc := hf.2
  rw [←he,←hi] at hc
  exact (not_lt_of_ge (max_le hp.1.le hp.2.le)) hc

theorem rarity_log_mono_horizon {δ L : ℝ} (hδ : 0<δ) {n N : ℕ} (hn : n≤N)
    (hlog : L≤Real.log (1/((N+1:ℕ)*δ))) : L≤Real.log (1/((n+1:ℕ)*δ)) := by
  apply hlog.trans
  apply Real.log_le_log (by positivity)
  apply one_div_le_one_div_of_le (by positivity)
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.add_le_add_right hn 1) hδ.le

/-- The complete original fast-completion event, not a separately
assumed stage experiment, is bounded after summing all random entries.
The entry masses telescope, so no horizon multiplier is lost. -/
theorem blockTarget_fast_probability (ρ : Measure H) [IsProbabilityMeasure ρ]
    (μ : Measure S) [IsProbabilityMeasure μ] [MeasurableSpace.CountablyGenerated A]
    (active : Fin T → H → X → Prop) (ha : ∀ i, MeasurableSet {z : H × X | active i z.1 z.2})
    (query : ∀ n, FiniteHistory S A n → X) (hq : ∀ n, Measurable (query n))
    (O : ℕ → Kernel ((Fin T → H) × X) A) [∀ p, IsMarkovKernel (O p)]
    (R : Kernel ((Fin T → H) × X) A) [IsMarkovKernel R]
    (hO : ∀ p Θ Θ' x, (∀ i : Fin T, i.val<p+1 → Θ i=Θ' i) → O p (Θ,x)=O p (Θ',x))
    (Θ : Fin T → H) (j : Fin T)
    (hR : ∀ Θ Θ' x, (∀ i : Fin T, i.val<j.val → Θ i=Θ' i) → R (Θ,x)=R (Θ',x))
    {κ : ℝ} (hκ : 0≤κ) (hKL : ∀ Θ x, klDiv (O j.val (Θ,x)) (R (Θ,x))≤ENNReal.ofReal κ)
    (cap N : ℕ) {δ L : ℝ} (hδ : 0<δ) (htail : ∀ x, ρ.real {θ | active j θ x}≤δ)
    (hL : 0<L) (hlog : L≤Real.log (1/((N+1:ℕ)*δ))) :
    (adaptiveKernelLaw (ρ.prod μ) (blockTargetKernel active ha query hq O Θ j) N).real
      (blockTargetFastSet active query Θ j cap N)≤((cap:ℝ)*κ+Real.log 2)/L := by
  let K := blockTargetKernel active ha query hq O Θ j
  let Q := blockFixedKernel active ha query hq O Θ
  let safe := blockPreEntrySet active query Θ j
  let q : ℝ := ((cap:ℝ)*κ+Real.log 2)/L
  have hq₀ : 0≤q := div_nonneg (add_nonneg (mul_nonneg (Nat.cast_nonneg _) hκ)
    (Real.log_nonneg (by norm_num))) hL.le
  have hs := blockPreEntrySet_measurable active ha query hq Θ j
  have he := adaptiveKernelLaw_entry_event (ρ.prod μ) K
    (fun n => finiteHistoryMapInitial Prod.snd n ⁻¹' safe n)
    (fun n => (hs n).preimage (finiteHistoryMapInitial_measurable measurable_snd n)) N
    (blockTargetFastSet_measurable active ha query hq Θ j cap N)
    (by rw [kernelSurvivalSet_mapInitial]; exact blockTargetFastSet_disjoint_unentered active query Θ j cap N)
  have hb : ∀ n ∈ Finset.range (N+1),
      ((kernelToTime K n N ∘ₘ (adaptiveKernelLaw (ρ.prod μ) K n).restrict
        (finiteHistoryMapInitial Prod.snd n ⁻¹' kernelFirstExitSet safe n))
        (blockTargetFastSet active query Θ j cap N)).toReal≤
      q*(adaptiveKernelLaw μ Q n).real (kernelFirstExitSet safe n) := by
    intro n hn
    have hn' : n≤N := by have := Finset.mem_range.mp hn; omega
    obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hn'
    rw [kernelToTime_add]
    have hk := blockTarget_firstEntry_fast_bound ρ μ active ha query hq O R hO Θ j hR hκ hKL n cap k hδ htail hL
      (rarity_log_mono_horizon hδ (Nat.le_add_left k n) hlog)
    have hi := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)) hk
    simpa only [ENNReal.toReal_mul,ENNReal.toReal_ofReal (show 0≤((cap:ℝ)*κ+Real.log 2)/L from hq₀)] using hi
  have hfinite : ∀ n ∈ Finset.range (N+1),
      (kernelToTime K n N ∘ₘ (adaptiveKernelLaw (ρ.prod μ) K n).restrict
        (finiteHistoryMapInitial Prod.snd n ⁻¹' kernelFirstExitSet safe n))
        (blockTargetFastSet active query Θ j cap N)≠∞ := by
    intro n hn
    letI := kernelToTime_markov K (show n≤N from by have := Finset.mem_range.mp hn; omega)
    exact measure_ne_top _ _
  simp only [kernelFirstExitSet_mapInitial] at he
  change (adaptiveKernelLaw (ρ.prod μ) K N (blockTargetFastSet active query Θ j cap N)).toReal≤q
  rw [he,ENNReal.toReal_sum hfinite]
  calc
    _ ≤ ∑ n ∈ Finset.range (N+1), q*(adaptiveKernelLaw μ Q n).real (kernelFirstExitSet safe n) := Finset.sum_le_sum hb
    _ = q*∑ n ∈ Finset.range (N+1), (adaptiveKernelLaw μ Q n).real (kernelFirstExitSet safe n) := (Finset.mul_sum _ _ _).symm
    _ ≤ q*1 := mul_le_mul_of_nonneg_left (adaptiveKernelLaw_firstExit_sum_le_one μ Q safe hs N) hq₀
    _ = q := mul_one _

end
end SecondOrder
