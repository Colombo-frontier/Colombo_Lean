import NCBall.SplitLatents
import NCBall.RealEventMeasurable
import NCBall.HardFiber

/-! # The same experiment with the hidden instance in the outer integral -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace NCBall

def fixedDirections {n M : ℕ} (scale : ℝ) (u : HiddenTable n M) : ℕ → Space n :=
  finiteRoomExtension (fun a => transverseEmbed n (scale • a)) u

theorem combined_latentDirections {n H M : ℕ} (scale : ℝ)
    (u : HiddenTable n M) (z : SampleTable n H M) :
    latentDirections scale ((splitRoomEquiv n H M).symm (u, z)) = fixedDirections scale u := by
  funext k
  unfold latentDirections fixedDirections finiteRoomExtension
  split_ifs
  · change transverseEmbed n (scale • (((splitRoomEquiv n H M).symm (u, z) _) 0)) = _
    rw [combined_hidden_block]
  · rfl

def fixedGoodEvent {n M : ℕ} (scale : ℝ) : Set (HiddenTable n M) :=
  {u | ∀ j < M, ‖fixedDirections scale u j‖ ≤ 2}

theorem fixedGoodEvent_measurable {n M : ℕ} (scale : ℝ) :
    MeasurableSet (fixedGoodEvent (n := n) (M := M) scale) := by
  unfold fixedGoodEvent
  simp only [setOf_forall]
  apply MeasurableSet.iInter
  intro j
  apply MeasurableSet.iInter
  intro _
  have hm : Measurable (fun u : HiddenTable n M => fixedDirections scale u j) :=
    finiteRoomExtension_measurable _ ((transverseEmbed n).continuous.measurable.comp
      (measurable_id.const_smul scale)) j
  exact measurableSet_le hm.norm measurable_const

theorem fixed_good_event_probability {n M : ℕ} (hn : 0 < n)
    (hlog : 2 * Real.log (8 * ((M : ℝ) + 1)) ≤ n) :
    (7 / 8 : ℝ≥0∞) ≤ (hiddenTableLaw n M) (fixedGoodEvent (Real.sqrt (n : ℝ))⁻¹) := by
  let scale := (Real.sqrt (n : ℝ))⁻¹
  have he : (hiddenTableLaw n M) (fixedGoodEvent scale) =
      (roomLatentLaw n 0 M) (latentGoodEvent scale) := by
    have hl := combineRoomEquiv_law n 0 M
    rw [← hl.map_eq, Measure.map_apply hl.measurable (latentGoodEvent_measurable scale)]
    have hset : (splitRoomEquiv n 0 M).symm ⁻¹' latentGoodEvent scale = fixedGoodEvent scale ×ˢ univ := by
      ext ⟨u, z⟩
      simp only [mem_preimage, latentGoodEvent, fixedGoodEvent, mem_setOf_eq,
        combined_latentDirections, mem_prod, mem_univ, and_true]
    rw [hset, Measure.prod_prod, measure_univ, mul_one]
  rw [he]
  have hg := ENNReal.ofReal_le_ofReal (latent_good_event_probability (H := 0) hn hlog)
  simpa only [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _),
    ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 8), ENNReal.ofReal_ofNat] using hg

def experimentFromSplit {R : Type*} {n H M : ℕ}
    (w : HiddenTable n M × (R × SampleTable n H M)) : R × RoomLatents n H M :=
  (w.2.1, (splitRoomEquiv n H M).symm (w.1, w.2.2))

theorem experimentFromSplit_law {R : Type*} [MeasurableSpace R]
    (ν : Measure R) [IsProbabilityMeasure ν] (n H M : ℕ) :
    MeasurePreserving (experimentFromSplit (R := R) (n := n) (H := H) (M := M))
      ((hiddenTableLaw n M).prod (ν.prod (sampleTableLaw n H M)))
      (ν.prod (roomLatentLaw n H M)) := by
  let μ := hiddenTableLaw n M
  let τ := sampleTableLaw n H M
  have h1 := (measurePreserving_prodAssoc μ ν τ).symm
  have h2 := (Measure.measurePreserving_swap (μ := μ) (ν := ν)).prod (MeasurePreserving.id τ)
  have h3 := measurePreserving_prodAssoc ν μ τ
  have h4 := (MeasurePreserving.id ν).prod (combineRoomEquiv_law n H M)
  exact h4.comp (h3.comp (h2.comp h1))

theorem exists_fixed_hard_terminal {R : Type*} [MeasurableSpace R]
    {n H M q₀ N : ℕ} (ν : Measure R) [IsProbabilityMeasure ν]
    (p : RoomQueryPolicy R n H) (hq : 0 < q₀) (hN : N < M * q₀) (hn : 0 < n)
    {ρ σ : ℝ} (hρ : 0 < ρ) (hσ : 0 < σ) (γ lam : ℝ)
    (hqcap : (q₀ : ℝ) ≤ n * σ ^ 2 / 16)
    (hlog : 40 * Real.log (2 + (M * q₀ : ℕ)) ≤ n)
    (hgoodlog : 2 * Real.log (8 * ((M : ℝ) + 1)) ≤ n)
    (out : LinearHistory R N → Space n) (hout : Measurable out) :
    ∃ u ∈ fixedGoodEvent (Real.sqrt (n : ℝ))⁻¹,
      (ν.prod (sampleTableLaw n H M))
        {rz | experimentFromSplit (u, rz) ∈
          fullRealTerminalEvent p ρ γ lam σ (Real.sqrt (n : ℝ))⁻¹ N out} < 1 / 2 := by
  let scale := (Real.sqrt (n : ℝ))⁻¹
  let A := fullRealTerminalEvent (M := M) p ρ γ lam σ scale N out
  have ha : MeasurableSet A := fullRealTerminalEvent_measurable p ρ γ lam σ scale N out hout
  have hl := experimentFromSplit_law ν n H M
  have hb : ((hiddenTableLaw n M).prod (ν.prod (sampleTableLaw n H M)))
      (experimentFromSplit ⁻¹' A) ≤ 1 / 4 := by
    rw [← Measure.map_apply hl.measurable ha, hl.map_eq]
    exact full_chain_terminal_quarter ν p hq hN hn hρ hσ γ lam hqcap hlog out hout
  exact exists_good_hard_fiber (hiddenTableLaw n M) (ν.prod (sampleTableLaw n H M))
    (fixedGoodEvent scale) (fixedGoodEvent_measurable scale) (experimentFromSplit ⁻¹' A)
    (hl.measurable ha) (fixed_good_event_probability hn hgoodlog) hb

end NCBall
